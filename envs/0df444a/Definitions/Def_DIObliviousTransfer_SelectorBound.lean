-- Prove2me | Definitions.Def_DIObliviousTransfer_SelectorBound
-- name    : DIObliviousTransfer_SelectorBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:04:22.631014+00:00
-- url     : https://prove2.me/theorems/e2015828-a689-47a7-81de-d4a5e0fc0e88
-- title:
--   The selector game $G^{\mathrm{sel}}$ and the selector bound
-- statement:
--   In one copy of the selector game $G^{\mathrm{sel}}_1$, the verifier sends independent uniform trits $X^{\mathrm{in}},Y$ to Charlie and Dave. Charlie returns an even row $A^{\mathrm{in}}$. Dave's instrument freezes an odd column $B$ and a selector bit $J$ and keeps quantum memory. Only then is $C\sim\mathrm{Bern}(1-\delta_*)$ sampled: Dave receives $X^{\mathrm{in}}$ if $C=1$ and an erasure symbol otherwise, and returns a guess $\hat A[0,1]$. The scores are
--   $$W=(1-C)+C\,\mathbb I\{\hat A[0,1]=A^{\mathrm{in}}[0,1]\}\,\mathrm{MS}(X^{\mathrm{in}},Y,A^{\mathrm{in}},B),\qquad L=C(1-\mathrm{MS}(X^{\mathrm{in}},Y,A^{\mathrm{in}},B)).$$
--   In the $n$-copy game the questions are product-distributed, the parties may use arbitrary entanglement and joint operations, and $C$ is sampled after all first-round outputs are fixed.
--
--   **SelectorBound**$(\delta,r_{\min},r_{\max},\gamma,\eta)$ says that for all large $n$ and every $n$-copy strategy, with $K=\{j:J_j=1\}$,
--   $$\Pr\Big[r_{\min}n\le|K|\le r_{\max}n,\ \sum_j L_j\le\eta n,\ \sum_{j\in K}W_j\ge|K|-\eta n\Big]\le2^{-\gamma n}.$$
--   This is the conclusion of Lemma 31, which fixes the constants $\gamma,\eta_{\mathrm{MS}}$ of the schedule.
--
--   **Formalization Note** Strategies are finite-dimensional. The late measurement may depend on Dave's questions, his first-round outcome and the revealed string.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), §8.1, p.62; p.63; Lemma 31, p.68

import Mathlib
import Definitions.Def_DIObliviousTransfer_MS

namespace DIObliviousTransfer

open Matrix
open scoped Kronecker ComplexOrder

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), §8.1, p.62 and the
n-copy convention of p.63: the selector game `G^sel` with late erasures, its scores (35)–(36), and
the selector bound of Lemma 31 (p.68) used to fix the constants of the schedule (p.27).

"In `G^sel_1` the verifier sends independent uniform trits `X^in, Y` to Charlie and Dave. Charlie
returns an even row `A^in`; Dave's `Y`-controlled instrument freezes `F = (B, J)` … Only then does
the verifier sample `C ← Bern(1 − δ∗)` and send Dave `X̂ = X^in` if `C = 1`, and `X̂ = ∗`
otherwise. Dave returns `Â[0, 1]`." (p.62). "In the n-copy game, the first-round questions are
sampled productwise, both parties may use arbitrary entangled states and joint first-round
operations, Dave may use one joint second-round operation on all the revealed questions and his
residual state, and C is sampled after all first-round outputs, including J, are fixed." (p.63)

**Formalization Note** (decision D2). An n-copy strategy is finite-dimensional: a state on
`H_C ⊗ H_D`; Charlie's joint POVM for each row-question string; Dave's joint first-round
instrument (Kraus form, into `H_D'`) for each column-question string, with outcome the column
string `B` and selector string `J`; and Dave's joint late POVM on `H_D'`, which may depend on his
questions, his first-round outcome and the revealed string `X̂` (`none` is the erasure `∗`).
Rows and columns are two recorded bits completed by parity (`rowOf`, `colOf`). `C_i = true`
means `C_i = 1`, of probability `1 − δ∗`.
-/

/-- An allowed strategy for `n` parallel copies of `G^sel_1` (p.62–63). -/
structure SelStrategy (n : ℕ) where
  HC : Type
  HD : Type
  HD' : Type
  κ : Type
  [fHC : Fintype HC] [dHC : DecidableEq HC]
  [fHD : Fintype HD] [dHD : DecidableEq HD]
  [fHD' : Fintype HD'] [dHD' : DecidableEq HD']
  [fκ : Fintype κ]
  ρ : Matrix (HC × HD) (HC × HD) ℂ
  hρ : IsState ρ
  /-- Charlie's joint POVM for the row questions `x`, outcome the rows. -/
  M : (Fin n → Fin 3) → (Fin n → Bool × Bool) → Matrix HC HC ℂ
  hM : ∀ x, IsPOVM (M x)
  /-- Dave's joint first-round instrument for the column questions `y`, outcome `(B, J)`. -/
  K : (Fin n → Fin 3) → (Fin n → Bool × Bool) × (Fin n → Bool) → κ → Matrix HD' HD ℂ
  hK : ∀ y, ∑ o, ∑ k, (K y o k)ᴴ * K y o k = 1
  /-- Dave's joint late POVM, given `y`, `(B, J)` and the revealed `X̂`; outcome `Â[0, 1]`. -/
  N : (Fin n → Fin 3) → (Fin n → Bool × Bool) × (Fin n → Bool) → (Fin n → Option (Fin 3)) →
    (Fin n → Bool × Bool) → Matrix HD' HD' ℂ
  hN : ∀ y o xh, IsPOVM (N y o xh)

attribute [instance] SelStrategy.fHC SelStrategy.dHC SelStrategy.fHD SelStrategy.dHD
  SelStrategy.fHD' SelStrategy.dHD' SelStrategy.fκ

namespace SelStrategy

variable {n : ℕ} (S : SelStrategy n)

/-- Dave's subnormalized post-instrument state on `H_C ⊗ H_D'`. -/
noncomputable def post (y : Fin n → Fin 3) (o : (Fin n → Bool × Bool) × (Fin n → Bool)) :
    Matrix (S.HC × S.HD') (S.HC × S.HD') ℂ :=
  ∑ k, ((1 : Matrix S.HC S.HC ℂ) ⊗ₖ S.K y o k) * S.ρ * ((1 : Matrix S.HC S.HC ℂ) ⊗ₖ S.K y o k)ᴴ

/-- The revealed late question `X̂_i = X^in_i` if `C_i = 1`, and `∗` (`none`) otherwise. -/
def reveal (x : Fin n → Fin 3) (c : Fin n → Bool) : Fin n → Option (Fin 3) :=
  fun i => if c i then some (x i) else none

end SelStrategy

/-- The probability of an outcome, given questions, coins and all answers. -/
abbrev SelEvent (n : ℕ) :=
  (Fin n → Fin 3) → (Fin n → Fin 3) → (Fin n → Bool) → (Fin n → Bool × Bool) →
    (Fin n → Bool × Bool) → (Fin n → Bool) → (Fin n → Bool × Bool) → Prop

/-- The probability of an event `E(X^in, Y, C, A^in, B, J, Â)` in the n-copy game with
anchoring probability `δ∗` (`Pr[C_i = 1] = 1 − δ∗`, independently): uniform product questions,
then Charlie's and Dave's first-round outcomes, then `C`, then Dave's late outcome. -/
noncomputable def selProb {n : ℕ} (δ : ℝ) (S : SelStrategy n) (E : SelEvent n) : ℝ := by
  classical
  exact ∑ x : Fin n → Fin 3, ∑ y : Fin n → Fin 3, ∑ c : Fin n → Bool,
    ((1 / 9 : ℝ) ^ n * ∏ i, (if c i then 1 - δ else δ)) *
    ∑ a : Fin n → Bool × Bool, ∑ o : (Fin n → Bool × Bool) × (Fin n → Bool),
      ∑ ah : Fin n → Bool × Bool,
        if E x y c a o.1 o.2 ah then
          ((S.M x a ⊗ₖ S.N y o (SelStrategy.reveal x c) ah) * S.post y o).trace.re
        else 0

/-- The loss score `L_i = C_i (1 − MS(X^in_i, Y_i, A^in_i, B_i))` of (36), as a Boolean. -/
def selL {n : ℕ} (x y : Fin n → Fin 3) (c : Fin n → Bool) (a b : Fin n → Bool × Bool)
    (i : Fin n) : Bool :=
  c i && !(MS (x i) (y i) (rowOf (a i)) (colOf (b i)))

/-- The win score `W_i = (1 − C_i) + C_i 𝕀{Â_i[0,1] = A^in_i[0,1]} MS(X^in_i, Y_i, A^in_i, B_i)`
of (35), as a Boolean. -/
def selW {n : ℕ} (x y : Fin n → Fin 3) (c : Fin n → Bool) (a b ah : Fin n → Bool × Bool)
    (i : Fin n) : Bool :=
  !(c i) || (decide (ah i = a i) && MS (x i) (y i) (rowOf (a i)) (colOf (b i)))

/-- Number of `true` entries. -/
def cnt {n : ℕ} (f : Fin n → Bool) : ℕ := (Finset.univ.filter fun i => f i = true).card

/-- The selector bound produced by **Lemma 31** (p.68) on the density interval
`[r_min, r_max]` with anchoring probability `δ`, guessing exponent `γ` and loss threshold `η`:
for all sufficiently large `n` and every allowed n-copy strategy, writing `K = {j : J_j = 1}`,
`Pr[r_min n ≤ |K| ≤ r_max n, Σ_j L_j ≤ η n, Σ_{j ∈ K} W_j ≥ |K| − η n] ≤ 2^{−γ n}`. -/
def SelectorBound (δ rmin rmax γ η : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ S : SelStrategy n,
    selProb δ S (fun x y c a b j ah =>
      rmin * n ≤ (cnt j : ℝ) ∧ (cnt j : ℝ) ≤ rmax * n ∧
      (cnt (selL x y c a b) : ℝ) ≤ η * n ∧
      (cnt j : ℝ) - η * n ≤ (cnt (fun i => j i && selW x y c a b ah i) : ℝ))
      ≤ (2 : ℝ) ^ (-(γ * n))

end DIObliviousTransfer


