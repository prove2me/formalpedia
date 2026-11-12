-- Prove2me | Definitions.Def_FourMsgQMA_FHE
-- name    : FourMsgQMA_FHE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:32:04.384198+00:00
-- url     : https://prove2.me/theorems/abe85465-26ea-4294-9e54-f033d36e9a3e
-- title:
--   Leveled FHE: syntax, uniform correctness (Def. 3.14), compactness, IND-CPA (Def. 3.15)
-- statement:
--   A **leveled bit-encryption scheme** consists of $(PK,SK)\leftarrow\mathrm{Gen}(1^\lambda,1^L)$, $\mathrm{ct}\leftarrow\mathrm{Enc}(PK,\mu)$ with an explicit encryption tape, deterministic $\mathrm{Eval}(PK,C,(\mathrm{ct}_j)_j)$ for NAND circuits $C$, and deterministic total $\mathrm{Dec}(SK,\mathrm{ct})$. Its properties:
--
--   1. **$\mathrm{Good}(PK,SK)$** (Definition 3.14) for bounds $(L,n,S)$: for every bit string $\mu$ with at most $n$ bits, all encryption tapes $\omega$ and every supported circuit $C$ (depth $\le L$, size $\le S$, $n_C=|\mu|$), with $\mathrm{ct}_j:=\mathrm{Enc}(PK,\mu_j;\omega_j)$: $\mathrm{Dec}(SK,\mathrm{ct}_j)=\mu_j$ and $\mathrm{Dec}(SK,\mathrm{Eval}(PK,C,(\mathrm{ct}_j)_j))=C(\mu)$;
--   2. **uniform statistical correctness**: for all polynomial bounds $(L,n,S)$ there is a negligible $\nu$ with $\Pr[\neg\mathrm{Good}(PK,SK)]\le\nu(\lambda)$ over $\mathrm{Gen}(1^\lambda,1^L)$;
--   3. **compactness**: one polynomial bounds, at $p(\lambda,L)$, the coin lengths, $|PK|$, $|SK|$, fresh ciphertexts and every evaluated ciphertext, independently of $|C|$ and $n_C$; all algorithms are polynomial time;
--   4. **IND-CPA** (Definition 3.15): for every polynomial $L$ and every QPT $(A_1,A_2)$, $\Pr[\hat b=b]\le\frac12+\nu(\lambda)$ in the game where $A_1(PK)$ names bits $(\mu_0,\mu_1)$ and $A_2$ receives $\mathrm{Enc}(PK,\mu_b)$ with its retained state;
--   5. **shallow decryption**: there is $c$ such that $\mathrm{Dec}(SK,\cdot)$, as a function of $SK$ followed by a ciphertext of any fixed length, is computed by a NAND circuit of depth at most $c\lceil\log_2(\lambda+L+2)\rceil^c$, on every input including malformed ones.
--
--   **Formalization Note** Pinned-down version (operator request): "time" is polynomial-time computability plus the length bounds; probabilities over key generation are averages over explicit coins; adversaries are `IsQPT`.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.9, pp.17–18 (PDF 19–20): Definitions 3.14, 3.15, Compactness and efficiency; Theorem 3.16, p.18

import Mathlib
import Definitions.Def_FourMsgQMA_NandCircuit

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.9 (pp.17–18, PDF 19–20): leveled
fully homomorphic bit encryption `FHE = (Gen, Enc, Eval, Dec)`, uniform correctness
(Definition 3.14), compactness and efficiency, post-quantum IND-CPA security (Definition 3.15).

Pinned-down version (operator request): "PPT"/"time at most p" are polynomial-time computability
(`QAlgorithms.Complexity.PolyTimeComputable`) of the algorithms on their packed inputs together
with the stated length bounds; adversaries are the published `TightPQRepetition.Main.IsQPT`
families; probabilities over key generation are averages over explicit uniform coins.
-/

open Classical QAlgorithms.Complexity TightPQRepetition.Main

/-- A leveled bit-encryption scheme (§3.9, p.17). -/
structure FHE where
  /-- Coins of `Gen(1^λ, 1^L)`. -/
  genCoins : ℕ → ℕ → ℕ
  /-- `(PK, SK) ← Gen(1^λ, 1^L)`, with coins; `PK` includes the evaluation key. -/
  gen : ℕ → ℕ → Bits → Bits × Bits
  /-- The length of an encryption tape at `(λ, L)`. -/
  encCoins : ℕ → ℕ → ℕ
  /-- `ct ← Enc(PK, µ)` for a bit `µ`, with explicit encryption tape. -/
  enc : Bits → Bool → Bits → Bits
  /-- `ct_C := Eval(PK, C, (ct_j)_{j ∈ [n_C]})`, deterministic. -/
  eval : Bits → NandCircuit → List Bits → Bits
  /-- `Dec(SK, ct) ∈ {0,1}`, deterministic and total. -/
  dec : Bits → Bits → Bool

/-- A circuit is supported at depth bound `L` and size bound `S`: well formed, NAND basis, depth
at most `L`, at most `S` gates. -/
def NandCircuit.Supported (C : NandCircuit) (L S : ℕ) : Prop :=
  C.WellFormed ∧ C.depth ≤ L ∧ C.size ≤ S

/-- `Good(PK, SK)` of Definition 3.14 (p.17) for the bounds `L` (depth), `n` (number of encrypted
inputs) and `S` (circuit size): for every bit string `µ` with at most `n` bits, every collection of
encryption tapes `ω` and every supported circuit `C` with `n_C = |µ|`, writing
`ct_j := Enc(PK, µ_j; ω_j)`: `Dec(SK, ct_j) = µ_j` for every `j`, and
`Dec(SK, Eval(PK, C, (ct_j)_j)) = C(µ)`. -/
def FHE.Good (E : FHE) (lam L n S : ℕ) (PK SK : Bits) : Prop :=
  ∀ μ : List Bool, μ.length ≤ n → ∀ ω : List Bits, ω.length = μ.length →
    (∀ t ∈ ω, t.length = E.encCoins lam L) →
    let cts := (μ.zip ω).map fun p => E.enc PK p.1 p.2
    (∀ j : Fin μ.length, E.dec SK (cts.getD j []) = μ[j]) ∧
    ∀ C : NandCircuit, C.Supported L S → C.nIn = μ.length → E.dec SK (E.eval PK C cts) = C.eval μ

/-- Uniform statistical correctness, Definition 3.14 (p.17): for all polynomial bounds on the
depth `L`, the number of encrypted inputs and the circuit size, there is a negligible `ν` with
`Pr[¬Good(PK, SK) : (PK, SK) ← Gen(1^λ, 1^L)] ≤ ν(λ)`. -/
def FHE.UniformlyCorrect (E : FHE) : Prop :=
  ∀ Lb nb Sb : ℕ → ℕ, PolyBound Lb → PolyBound nb → PolyBound Sb →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      avgCoins (E.genCoins lam (Lb lam)) (fun r =>
        if E.Good lam (Lb lam) (nb lam) (Sb lam) (E.gen lam (Lb lam) r).1
          (E.gen lam (Lb lam) r).2 then 0 else 1) ≤ ν lam

/-- Uniformity: every algorithm and the coin lengths are polynomial-time computable on their
packed inputs. With `Compact`, this gives "Key generation, single-bit encryption, and decryption
take time at most `p(λ, L)`" and "Evaluation takes time polynomial in `(λ, L, |C|)`" (p.17). -/
def FHE.IsUniform (E : FHE) : Prop :=
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam L,
      g (pack [unary lam, unary L]) = pack [unary (E.genCoins lam L), unary (E.encCoins lam L)]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam L r,
      g (pack [unary lam, unary L, r]) = pack [(E.gen lam L r).1, (E.gen lam L r).2]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ PK b t, g (pack [PK, [b], t]) = E.enc PK b t) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ PK C cts,
      g (pack [PK, C.encode, pack cts]) = E.eval PK C cts) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ SK ct, g (pack [SK, ct]) = [E.dec SK ct])

/-- Compactness (p.17): one polynomial `p` bounds, at `P = p(λ, L, 0, 0)`, the coin lengths, the
public-key, secret-key and single-bit ciphertext lengths, and the length of every evaluated
single-output ciphertext, independently of `|C|` and `n_C`. -/
def FHE.Compact (E : FHE) : Prop :=
  ∃ p : MvPolynomial (Fin 4) ℕ, ∀ lam L : ℕ,
    E.genCoins lam L ≤ eval4 p lam L 0 0 ∧ E.encCoins lam L ≤ eval4 p lam L 0 0 ∧
    ∀ r : Bits, r.length = E.genCoins lam L →
      (E.gen lam L r).1.length ≤ eval4 p lam L 0 0 ∧ (E.gen lam L r).2.length ≤ eval4 p lam L 0 0 ∧
      (∀ b (t : Bits), t.length = E.encCoins lam L →
        (E.enc (E.gen lam L r).1 b t).length ≤ eval4 p lam L 0 0) ∧
      ∀ C : NandCircuit, C.WellFormed → C.depth ≤ L → ∀ cts : List Bits,
        (E.eval (E.gen lam L r).1 C cts).length ≤ eval4 p lam L 0 0

/-- Theorem 3.16 (p.18): "Its total decryption circuit has depth polylog(λ + L), including on
malformed inputs": there is `c` such that for every `λ, L`, every secret-key length `a` and every
ciphertext length `b`, **one** NAND circuit `D` of depth at most `c · ⌈log₂(λ + L + 2)⌉^c` on
`a + b` inputs computes `Dec(SK, ct)` from `SK ++ ct`, for every secret key `SK` of length `a` in
the support of `Gen(1^λ, 1^L)` and every `ct` of length `b`. The circuit is chosen before the key:
it is the decryption circuit, not a circuit with the key hardwired. -/
def FHE.ShallowDec (E : FHE) : Prop :=
  ∃ c : ℕ, ∀ lam L a b : ℕ,
    ∃ D : NandCircuit, D.WellFormed ∧ D.nIn = a + b ∧ D.depth ≤ c * clog2 (lam + L + 2) ^ c ∧
      ∀ r : Bits, r.length = E.genCoins lam L → (E.gen lam L r).2.length = a →
        ∀ ct : Bits, ct.length = b → D.eval ((E.gen lam L r).2 ++ ct) = E.dec (E.gen lam L r).2 ct

/-- The IND-CPA experiment of Definition 3.15 (p.17) at depth bound `L(λ)`, as a published
`TightPQRepetition.Main.Verifier` (semantic carrier): coins `(r, t, b)`; the adversary receives
`PK` and answers `(µ₀, µ₁)` (its first two bits); it receives `ct = Enc(PK, µ_b; t)` and answers
`b̂` (its first bit); the verdict is `b̂ = b`. -/
def FHE.cpaVerifier (E : FHE) (L : ℕ → ℕ) : Verifier where
  rounds := fun _ => 2
  coins := fun lam => E.genCoins lam (L lam) + E.encCoins lam (L lam) + 1
  qLen := fun _ _ => 0
  query := fun lam r j as =>
    let PK := (E.gen lam (L lam) (r.take (E.genCoins lam (L lam)))).1
    let t := (r.drop (E.genCoins lam (L lam))).take (E.encCoins lam (L lam))
    let b := r.getD (E.genCoins lam (L lam) + E.encCoins lam (L lam)) false
    let a := as.headD []
    if j = 0 then PK else E.enc PK (if b then a.getD 1 false else a.getD 0 false) t
  verdict := fun lam r τ =>
    decide ((τ.getD 1 ([], [])).2.getD 0 false = r.getD (E.genCoins lam (L lam) + E.encCoins lam (L lam)) false)

/-- Post-quantum IND-CPA security, Definition 3.15 (p.17): for every polynomial level bound `L`
and every QPT adversary `(A₁, A₂)` (one `IsQPT` strategy whose two rounds are the stages, with
quantum advice and retained state), `Pr[b̂ = b] ≤ 1/2 + ν(λ)` for a negligible `ν`. -/
def FHE.INDCPA (E : FHE) : Prop :=
  ∀ L : ℕ → ℕ, PolyBound L → ∀ Adv : ℕ → Strategy, IsQPT Adv →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, (Adv lam).acceptProb (E.cpaVerifier L) lam ≤ 1 / 2 + ν lam

end FourMsgQMA


