-- Prove2me | Definitions.Def_NoisyOWMPC_Supplement_constructionD3
-- name    : NoisyOWMPC_Supplement_constructionD3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:59:06.957467+00:00
-- url     : https://prove2.me/theorems/aea069b4-1635-4bce-883e-eae0755a800b
-- title:
--   Construction D.3: random string OT over string erasures (with the Fig. 11 program)
-- statement:
--   **Construction D.3** realizes $\mathrm{ROT}^\ell$ over $N$ uses of $\mathrm{SEC}^{N,L}_{1/2}$ and one noiseless message. Fix a message length $\ell$, a string length $L$, a block length $N$, a selector on $[N]$ (key sampler $\mathrm{Gen_{sel}}$, guard $\mathrm{Guard_{sel}}$, coin $b_K$), an obfuscator, a generator of the program below and a pad size.
--
--   The **program** $P[(m_0,m_1), x, K, \pi]$ of Fig. 11 parses its input as a partial word $u \in (\{0,1\}^L \cup \{\perp\})^N$ (rejecting malformed inputs), sets $U = \{v \in [N] : u_v = x_v\}$, rejects if $\mathrm{Guard_{sel}}(U) = 0$, and otherwise returns $(c, m_c)$ with $c = b_K(U) \oplus \pi$.
--
--   1. **Sender** $S(1^\lambda, m_0, m_1)$: sample $x_1, \dots, x_N \leftarrow \{0,1\}^L$, $K \leftarrow \mathrm{Gen_{sel}}(1^\lambda)$ and $\pi \leftarrow \{0,1\}$; build the program, pad it to the common size, obfuscate it, submit $x$ to the erasure channel and send the obfuscation $\tilde P$ (length-prefixed and padded) as $\tau$.
--   2. **Receiver** $R(1^\lambda, \tilde P, x|_V)$: evaluate $\tilde P$ on $x|_V$ and return its output, or $\mathsf{fail}$ on rejection.
--
--   This is the protocol of Theorem D.4.
--
--   **Formalization Note** The paper fixes no circuit for Fig. 11, so the construction takes any polynomial-time generator whose circuits compute the program on every input of the fixed length; queries and outputs use fixed-length encodings with a validity bit. Obfuscations are length-prefixed and padded to the obfuscator's public length bound, as in Construction 5.23.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Construction D.3 and Fig. 11, p.58

import Mathlib
import Definitions.Def_NoisyOWMPC_Supplement_SECProtocol
import Definitions.Def_NoisyOWMPC_construction

namespace NoisyOWMPC.Supplement

open KarpLiptonOM LaconicBarrier

/-- The sampled constants of the Fig. 11 program other than the messages (Ishai, Lu, Zafar, STOC
2027 submission (manuscript sha256 3a9569fa…), Fig. 11, p.58: "strings `x ∈ ({0,1}^L)^N`, a selector
key `K`, and a mask `π ∈ {0,1}`"). -/
abbrev D3Consts (Ls N : ℕ → ℕ) (S : SelHalf N) (lam : ℕ) : Type :=
  (Fin (N lam) → Fin (Ls lam) → Bool) × S.Key lam × Bool

open Classical in
/-- **The evaluation program for random string OT**, on parsed queries (Fig. 11, p.58): on a
partial word `u ∈ ({0,1}^L ∪ {⊥})^N` set `U = {v ∈ [N] : u_v = x_v}`; reject if `Guard_sel(U) = 0`;
otherwise compute `c = b_K(U) ⊕ π` and return `(c, m_c)`. `none` is rejection. -/
noncomputable def fig11 (ℓ Ls N : ℕ → ℕ) (S : SelHalf N) (lam : ℕ)
    (x : Fin ((rotF ℓ).lx lam) → Bool) (c : D3Consts Ls N S lam)
    (u : Fin (N lam) → Option (Fin (Ls lam) → Bool)) : Option (Fin (ℓ lam + 1) → Bool) :=
  let U : Finset (Fin (N lam)) := Finset.univ.filter fun v => u v = some (c.1 v)
  if S.guard lam U = false then none
  else some ((rotF ℓ).f lam 0 x (fun _ => xor (S.coin lam c.2.1 U) c.2.2))

/-- The fixed input length `N(L + 1)` of the Fig. 11 program (one symbol code per position). -/
def inLen11 (Ls N : ℕ → ℕ) (lam : ℕ) : ℕ := N lam * (Ls lam + 1)

/-- The fixed output length of the Fig. 11 program: a validity bit and the output `(c, m_c)`. -/
def outLen11 (ℓ : ℕ → ℕ) (lam : ℕ) : ℕ := 1 + (ℓ lam + 1)

/-- The validity-tagged output encoding `1 c m_c`; the all-zero output denotes rejection. -/
def outEnc11 {n : ℕ} (v : Fin n → Bool) : List Bool := true :: bits v

open Classical in
/-- The **bit-level function of Fig. 11** (Fig. 11, step 1, p.58: "Parse `u` and reject if it is
malformed"): on a string that encodes a partial word (`secObsEnc`), the encoding of the program's
answer; on every other string, the all-zero output. -/
noncomputable def fig11Bits (ℓ Ls N : ℕ → ℕ) (S : SelHalf N) (lam : ℕ)
    (x : Fin ((rotF ℓ).lx lam) → Bool) (c : D3Consts Ls N S lam) (w : List Bool) : List Bool :=
  if h : ∃ u : Fin (N lam) → Option (Fin (Ls lam) → Bool), secObsEnc u = w then
    match fig11 ℓ Ls N S lam x c h.choose with
    | none => List.replicate (outLen11 ℓ lam) false
    | some v => outEnc11 v
  else List.replicate (outLen11 ℓ lam) false

/-- The encoding of the Fig. 11 constants other than the messages: the strings, the key, the mask. -/
def constsEnc11 {Ls N : ℕ → ℕ} {S : SelHalf N} {lam : ℕ} (c : D3Consts Ls N S lam) : List Bool :=
  QAdvFew.PoQOracle.tup [secInEnc c.1, S.enc lam c.2.1, [c.2.2]]

/-- A **program generator for Fig. 11**: from `λ`, `(m₀, m₁)` and the constants, a circuit with
`N(L + 1)` inputs. -/
abbrev ProgGen11 (ℓ Ls N : ℕ → ℕ) (S : SelHalf N) : Type :=
  (lam : ℕ) → (Fin ((rotF ℓ).lx lam) → Bool) → D3Consts Ls N S lam → MCircuit (inLen11 Ls N lam)

/-- `gen` is a **deterministic polynomial-time generator of the Fig. 11 program** (Construction D.3,
p.58: "Construct the program of Fig. 11"): one machine computes the description of `gen λ m c` from
`(1^λ, m, c)` in polynomial time, and the circuit computes `fig11Bits` on every input of length
`N(L + 1)`.

**Formalization Note** The paper fixes no circuit for Fig. 11; the construction is stated for every
such generator. -/
def IsFig11Gen (ℓ Ls N : ℕ → ℕ) (S : SelHalf N) (gen : ProgGen11 ℓ Ls N S) : Prop :=
  PolyTimeOn (ι := (lam : ℕ) × (Fin ((rotF ℓ).lx lam) → Bool) × D3Consts Ls N S lam)
    (fun z => [unary z.1, bits z.2.1, constsEnc11 z.2.2]) (fun z => (gen z.1 z.2.1 z.2.2).code) ∧
  ∀ lam x c (w : List Bool), w.length = inLen11 Ls N lam →
    (gen lam x c).eval w = fig11Bits ℓ Ls N S lam x c w

/-- The public bound on the description length of an obfuscated circuit with `n` inputs and size
`z` (the obfuscator's public length bound, §5 Conventions, p.21). -/
def maxLen (O : IOScheme) (n z : ℕ → ℕ) (lam : ℕ) : ℕ := O.len lam (n lam) (z lam)

/-- The fixed public transmission length: a length field and the longest description. -/
def txLenG (O : IOScheme) (n z : ℕ → ℕ) (lam : ℕ) : ℕ :=
  Nat.size (maxLen O n z lam) + maxLen O n z lam

/-- The transmitted form of a description `d` (§5 Conventions, p.21: "Obfuscations are
length-prefixed and padded to a fixed public length for transmission"). -/
def txEncG (O : IOScheme) (n z : ℕ → ℕ) (lam : ℕ) (d : List Bool) : Fin (txLenG O n z lam) → Bool :=
  fun p => (binW (Nat.size (maxLen O n z lam)) d.length ++ d).getD p.val false

/-- The size of the padded Fig. 11 program: `s` gates and the output wires. -/
def size11 (ℓ s : ℕ → ℕ) (lam : ℕ) : ℕ := s lam + outLen11 ℓ lam

open Classical in
/-- **Construction D.3 (Random string OT over string erasures)** (STOC 2027 submission (manuscript
sha256 3a9569fa…), p.58), for message length `ℓ`, string length `L_s`, block length `N`, a selector
`S` on `[N]` (its protocol half), an obfuscator `O`, a Fig. 11 generator `gen` and a pad size `s`:
* `S(1^λ, m₀, m₁)`: sample `x₁, …, x_N ← {0,1}^{L_s}`, `K ← Gen_sel(1^λ)` and `π ← {0,1}`,
  construct the program of Fig. 11, pad it to `s` gates, sample `P̃ ← iO(1^λ, P)`; submit `x` to
  `SEC^{N,L_s}_{1/2}` and send `P̃` (length-prefixed and padded) as `τ`;
* `R(1^λ, P̃, x|_V)`: parse `τ` as a circuit, evaluate it on the encoding of `x|_V`, and return the
  decoded output, or `fail` on rejection or if parsing or output validation fails.

**Formalization Note** The sender's coins are the constants (uniform strings, the key with its exact
reference law, a uniform mask) and the obfuscator's coins for a circuit of size `s + outLen`. -/
noncomputable def constructionD3 (ℓ Ls N : ℕ → ℕ) (S : SelHalf N) (O : IOScheme)
    (gen : ProgGen11 ℓ Ls N S) (s : ℕ → ℕ) : SECProtocol (rotF ℓ) where
  RS lam := D3Consts Ls N S lam × (Fin (O.coins lam (inLen11 Ls N lam) (size11 ℓ s lam)) → Bool)
  wS lam r := (1 / 2 : ℝ) ^ (N lam * Ls lam) * S.genW lam r.1.2.1 * (1 / 2 : ℝ) *
    (1 / 2 : ℝ) ^ (O.coins lam (inLen11 Ls N lam) (size11 ℓ s lam))
  encRS lam r := QAdvFew.PoQOracle.tup [constsEnc11 r.1, bits r.2]
  L := txLenG O (inLen11 Ls N) (size11 ℓ s)
  N := N
  Ls := Ls
  send lam x r := (txEncG O (inLen11 Ls N) (size11 ℓ s) lam
    (O.obf lam (inLen11 Ls N lam) (size11 ℓ s lam) (padC (s lam) (gen lam x r.1)) r.2).code, r.1.1)
  recv lam τ u :=
    if h : ∃ Pc : MCircuit (inLen11 Ls N lam),
        Pc.code.length ≤ maxLen O (inLen11 Ls N) (size11 ℓ s) lam ∧
          txEncG O (inLen11 Ls N) (size11 ℓ s) lam Pc.code = τ then
      if h' : ∃ v : Fin (ℓ lam + 1) → Bool, outEnc11 v = h.choose.eval (secObsEnc u)
      then some h'.choose else none
    else none

end NoisyOWMPC.Supplement


