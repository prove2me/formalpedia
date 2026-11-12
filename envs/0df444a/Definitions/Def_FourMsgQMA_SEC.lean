-- Prove2me | Definitions.Def_FourMsgQMA_SEC
-- name    : FourMsgQMA_SEC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:28.14402+00:00
-- url     : https://prove2.me/theorems/e192d789-9d31-43f8-bda6-f2237443f21a
-- title:
--   Somewhere-extractable block commitments (Definitions 3.17, 3.18)
-- statement:
--   A **somewhere-extractable block commitment** consists of $(hk,td)\leftarrow\mathrm{Setup}(1^\lambda,k,m,i^*)$ for an index $i^*\in[k]$, deterministic $\alpha:=\mathrm{Com}(hk,y)$ for $y\in(\{0,1\}^m)^k$, $\rho:=\mathrm{Open}(hk,y,i)$, $\mathrm{Verify}(hk,\alpha,i,y_i,\rho)$, and a total extractor $y^*:=\mathrm{Extract}(td,\alpha)$. Its properties:
--
--   1. **perfect completeness**: $\mathrm{Good}_{SC}(hk)$ for every setup outcome, i.e. $\mathrm{Verify}(hk,\mathrm{Com}(hk,y),i,y_i,\mathrm{Open}(hk,y,i))=1$ for every $y$ and $i\in[k]$;
--   2. **statistical extraction consistency** (the strong form of Definition 3.18): for polynomial $k,m$ and every $i^*$ fixed before setup,
--   $$
--   \Pr\big[\exists\alpha,y,\rho:\ \mathrm{Verify}(hk,\alpha,i^*,y,\rho)=1\wedge\mathrm{Extract}(td,\alpha)\ne y\big]\le\nu(\lambda);
--   $$
--   3. **index hiding** (Definition 3.17): a QPT adversary that names $(i_0,i_1)$ and receives $hk$ for $i_b$ guesses $b$ with probability at most $\frac12+\nu(\lambda)$;
--   4. **succinctness**: keys, trapdoors, digests and openings have length $\mathrm{poly}(\lambda,m,\log(k+1))$; verification and extraction circuits have the same size; setup, commitment and opening are polynomial time.
--
--   **Formalization Note** Pinned-down version (operator request). Indices are the paper's $1,\dots,k$; in the hiding game an invalid index is read as $1$ ("choosing valid indices").
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.10, pp.18–19 (PDF 20–21): Completeness, Succinctness, Definitions 3.17, 3.18

import Mathlib
import Definitions.Def_FourMsgQMA_ComputedOn

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.10 (pp.18–19, PDF 20–21):
somewhere-extractable block commitments `(Setup, Com, Open, Verify, Extract)`, completeness,
succinctness, index hiding (Definition 3.17) and extraction consistency (Definition 3.18).

Pinned-down version (operator request): indices are the paper's `[k] = {1, …, k}` as natural
numbers; a block vector is a list of `k` blocks of `m` bits; "PPT"/"time" are polynomial-time
computability and circuit size; adversaries are the published `TightPQRepetition.Main.IsQPT`.
-/

open Classical QAlgorithms.Complexity TightPQRepetition.Main

/-- A somewhere-extractable block commitment (§3.10, p.18). -/
structure SEC where
  /-- Coins of `Setup(1^λ, k, m, i*)` at `(λ, k, m)`. -/
  setupCoins : ℕ → ℕ → ℕ → ℕ
  /-- `(hk, td) ← Setup(1^λ, k, m, i*)`, with coins. -/
  setup : ℕ → ℕ → ℕ → ℕ → Bits → Bits × Bits
  /-- `α := Com(hk, y)`, deterministic. -/
  com : Bits → List Bits → Bits
  /-- `ρ := Open(hk, y, i)`, deterministic. -/
  opn : Bits → List Bits → ℕ → Bits
  /-- `Verify(hk, α, i, y_i, ρ) ∈ {0,1}`, deterministic. -/
  verify : Bits → Bits → ℕ → Bits → Bits → Bool
  /-- `y* := Extract(td, α)`, deterministic and total. -/
  extract : Bits → Bits → Bits

/-- `Good_SC(hk)` (p.18): for every block vector `y ∈ ({0,1}^m)^k` and every `i ∈ [k]`,
`Verify(hk, Com(hk, y), i, y_i, Open(hk, y, i)) = 1`. -/
def SEC.Good (S : SEC) (k m : ℕ) (hk : Bits) : Prop :=
  ∀ y : List Bits, y.length = k → (∀ b ∈ y, b.length = m) →
    ∀ i : ℕ, 1 ≤ i → i ≤ k → S.verify hk (S.com hk y) i (y.getD (i - 1) []) (S.opn hk y i) = true

/-- Perfect completeness (p.18): `Good_SC(hk)` for every setup outcome, for all `λ, k, m` and
`i* ∈ [k]`. -/
def SEC.PerfectlyComplete (S : SEC) : Prop :=
  ∀ lam k m i, 1 ≤ i → i ≤ k → ∀ r : Bits, r.length = S.setupCoins lam k m →
    S.Good k m (S.setup lam k m i r).1

/-- Statistical extraction consistency, the stronger form of Definition 3.18 used by the paper
(p.19): for all polynomial `k, m` and every `i* ∈ [k]` fixed before setup (a sequence `i*(λ)`),
there is a negligible `ν` with
`Pr[∃ α, y, ρ : Verify(hk, α, i*, y, ρ) = 1 ∧ Extract(td, α) ≠ y : (hk, td) ← Setup] ≤ ν(λ)`,
`y` ranging over `m`-bit blocks and `α, ρ` over all strings. -/
def SEC.StatExtractConsistent (S : SEC) : Prop :=
  ∀ k m : ℕ → ℕ, PolyBound k → PolyBound m → ∀ istar : ℕ → ℕ,
    (∀ lam, 1 ≤ istar lam ∧ istar lam ≤ k lam) →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      avgCoins (S.setupCoins lam (k lam) (m lam)) (fun r =>
        let o := S.setup lam (k lam) (m lam) (istar lam) r
        if ∃ (α y ρ : Bits), y.length = m lam ∧ S.verify o.1 α (istar lam) y ρ = true ∧
            S.extract o.2 α ≠ y then 1 else 0) ≤ ν lam

/-- An index in `[k]` read from an adversary's string (binary, least significant bit first); an
invalid index is replaced by `1`. -/
def readIndex (k : ℕ) (a : Bits) : ℕ := if 1 ≤ bitsVal a ∧ bitsVal a ≤ k then bitsVal a else 1

/-- The index-hiding experiment of Definition 3.17 (p.19) for `(k(λ), m(λ))`, as a published
`TightPQRepetition.Main.Verifier` (semantic carrier): the adversary first names `(i₀, i₁)` (its
first answer, `pack [i₀, i₁]`), then receives `hk` for `(hk, td) ← Setup(1^λ, k, m, i_b)` and
answers `b̂` (its first bit); the verdict is `b̂ = b`. The trapdoor is not given out. -/
def SEC.hidingVerifier (S : SEC) (k m : ℕ → ℕ) : Verifier where
  rounds := fun _ => 2
  coins := fun lam => S.setupCoins lam (k lam) (m lam) + 1
  qLen := fun _ _ => 0
  query := fun lam r j as =>
    let b := r.getD (S.setupCoins lam (k lam) (m lam)) false
    let ii := unpack (as.headD [])
    let i := readIndex (k lam) (if b then ii.getD 1 [] else ii.getD 0 [])
    if j = 0 then [] else (S.setup lam (k lam) (m lam) i (r.take (S.setupCoins lam (k lam) (m lam)))).1
  verdict := fun lam r τ =>
    decide ((τ.getD 1 ([], [])).2.getD 0 false = r.getD (S.setupCoins lam (k lam) (m lam)) false)

/-- Commitment index hiding, Definition 3.17 (p.19): for all polynomial `k, m` and every QPT
adversary `(A₁, A₂)` choosing indices, `Pr[b̂ = b] ≤ 1/2 + ν(λ)` for a negligible `ν`.

**Formalization Note** "choosing valid indices" is encoded by reading an invalid index as `1`. -/
def SEC.IndexHiding (S : SEC) : Prop :=
  ∀ k m : ℕ → ℕ, PolyBound k → PolyBound m → ∀ Adv : ℕ → Strategy, IsQPT Adv →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      (Adv lam).acceptProb (S.hidingVerifier k m) lam ≤ 1 / 2 + ν lam

/-- Uniformity: setup (with its coin length), commitment and opening are polynomial-time in their
packed inputs (with `λ, k, m, i` in unary), so "Setup, commitment, and opening generation take time
poly(λ, k, m)" (p.18). -/
def SEC.IsUniform (S : SEC) : Prop :=
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam k m,
      g (pack [unary lam, unary k, unary m]) = unary (S.setupCoins lam k m)) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam k m i r,
      g (pack [unary lam, unary k, unary m, unary i, r]) =
        pack [(S.setup lam k m i r).1, (S.setup lam k m i r).2]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ hk y, g (pack [hk, pack y]) = S.com hk y) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ hk y i, g (pack [hk, pack y, unary i]) = S.opn hk y i)

/-- Succinctness (p.18): one polynomial `p` such that, at `P = p(λ, m, ⌈log₂(k+1)⌉, 0)`, public
keys, trapdoors, digests and openings of honest executions have length at most `P`, and local
verification and extraction are computed by circuits of size at most `P` on the inputs that occur
(keys from setup, an index in `[k]`, an `m`-bit block, digests and openings of length at most
`P`). -/
def SEC.Succinct (S : SEC) : Prop :=
  ∃ p : MvPolynomial (Fin 4) ℕ, ∀ lam k m : ℕ,
    let P := eval4 p lam m (clog2 (k + 1)) 0
    (∀ i (r : Bits), 1 ≤ i → i ≤ k → r.length = S.setupCoins lam k m →
      let o := S.setup lam k m i r
      o.1.length ≤ P ∧ o.2.length ≤ P ∧
      ∀ y : List Bits, y.length = k → (∀ b ∈ y, b.length = m) →
        (S.com o.1 y).length ≤ P ∧ ∀ j, 1 ≤ j → j ≤ k → (S.opn o.1 y j).length ≤ P) ∧
    (∀ n, ComputedOn (fun w => let l := unpack w
        [S.verify (l.getD 0 []) (l.getD 1 []) (bitsVal (l.getD 2 [])) (l.getD 3 []) (l.getD 4 [])])
      {w | ∃ (i j : ℕ) (r α y ρ : Bits), 1 ≤ i ∧ i ≤ k ∧ 1 ≤ j ∧ j ≤ k ∧
        r.length = S.setupCoins lam k m ∧ α.length ≤ P ∧ y.length = m ∧ ρ.length ≤ P ∧
        w = pack [(S.setup lam k m i r).1, α, List.ofFn fun b : Fin (clog2 (k + 1)) => j.testBit b, y, ρ]}
      n P) ∧
    (∀ n, ComputedOn (fun w => let l := unpack w; S.extract (l.getD 0 []) (l.getD 1 []))
      {w | ∃ (i : ℕ) (r α : Bits), 1 ≤ i ∧ i ≤ k ∧ r.length = S.setupCoins lam k m ∧ α.length ≤ P ∧
        w = pack [(S.setup lam k m i r).2, α]} n P)

end FourMsgQMA


