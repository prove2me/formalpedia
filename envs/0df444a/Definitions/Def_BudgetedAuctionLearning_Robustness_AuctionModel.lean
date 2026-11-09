-- Prove2me | Definitions.Def_BudgetedAuctionLearning_Robustness_AuctionModel
-- name    : BudgetedAuctionLearning_Robustness_AuctionModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:08.116662+00:00
-- url     : https://prove2.me/theorems/f4789515-68e6-4661-a816-00b32cf40808
-- title:
--   §3 — two-bidder budgeted auction, controller (3), fake values and their expected utility and payments
-- statement:
--   Each round draws a pair $(v_L,v_O)\in[0,1]^2$ from a Borel probability law $D$, with arbitrary correlation within the round. At actual bids $b_O,b_L$ the optimizer wins if and only if $b_O>b_L$, so ties favour the learner. In a first-price auction the winner pays her own bid; in a second-price auction she pays the loser's bid.
--
--   The learner's multiplier follows the exact unprojected controller
--
--   $$\lambda^{(t+1)}=\lambda^{(t)}+\eta\,(\rho_L-p_L^{(t)}),\qquad b_L^{(t)}=\lambda^{(t)}v_L^{(t)}.$$
--
--   A fake value map is a measurable $\hat v_O:[0,1]\to\mathbb R_{\ge0}$, with bid $\lambda\hat v_O(v_O)$. With $w=\mathbf 1\{\hat v_O(v_O)>v_L\}$, the unscaled quantities are $U_O=v_Ow$; $P_O=v_Lw$, $P_L=\hat v_O(v_O)(1-w)$ in second-price; and $P_O=\hat v_O(v_O)w$, $P_L=v_L(1-w)$ in first-price. A randomized map is encoded by its conditional bid law given $v_O$, a Markov kernel from $[0,1]$ to $\mathbb R_{\ge0}$. Expectations of these quantities are extended nonnegative integrals, because first-price payments can be infinite.
--
--   The file also defines $E[v_L]$, $E[v_O]$, $E[v_O\mathbf 1_{v_L=0}]$ and the condition $P[0<v_L<v_O\varepsilon]=0$. These are the objects every later statement uses.
--
--   **Formalization Note.** Rounds are $0$-indexed, so `lam 0` is the source's $\lambda^{(1)}$. Pairs are ordered $(v_L,v_O)$. There is no cap on bids and no return-on-investment constraint (footnote 6).
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), §3, printed pp. 7–8 (PDF pp. 8–9), Eq. (3); footnote 6, printed p. 10 (PDF p. 11); Theorem 3.4, printed p. 9 (PDF p. 10)

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- The two auction formats of §3 (STOC 2027 submission #310, printed p. 7). -/
inductive AuctionFormat
  | firstPrice
  | secondPrice
  deriving DecidableEq

/-- A round's value pair `(v_L, v_O) ∈ [0,1] × [0,1]`; first coordinate learner, second optimizer. -/
abbrev ValuePair := I × I

/-- Optimizer's payment at actual bids `bO, bL`. The optimizer wins iff `bL < bO`: ties favour the
learner (printed p. 8). First-price: the winner pays her bid. Second-price: the loser's bid. -/
noncomputable def auctionPayO (fmt : AuctionFormat) (bO bL : ℝ) : ℝ :=
  if bL < bO then
    match fmt with
    | .firstPrice => bO
    | .secondPrice => bL
  else 0

/-- Learner's payment at actual bids `bO, bL`; the learner wins iff `bO ≤ bL`. -/
noncomputable def auctionPayL (fmt : AuctionFormat) (bO bL : ℝ) : ℝ :=
  if bL < bO then 0
  else
    match fmt with
    | .firstPrice => bL
    | .secondPrice => bO

/-- The controller of Eq. (3), exact and unprojected. `lam 0` is the source's `λ^(1)`; round `t`
(0-based) has optimizer bid `bO t`, learner bid `lam t * vL t`, and
`lam (t+1) = lam t + η (ρ_L - p_L^(t))`. Nonnegativity is Lemma 3.1, not part of this definition. -/
noncomputable def pacingController (fmt : AuctionFormat) (ρL η lam₁ : ℝ) (bO : ℕ → ℝ≥0) (vL : ℕ → I) :
    ℕ → ℝ
  | 0 => lam₁
  | t + 1 =>
    pacingController fmt ρL η lam₁ bO vL t +
      η * (ρL - auctionPayL fmt (bO t) (pacingController fmt ρL η lam₁ bO vL t * (vL t : ℝ)))

/-- A measurable fake-value map `v̂_O : [0,1] → ℝ_{≥0}`; no bound, monotonicity or continuity. -/
structure FakeValue where
  toFun : I → ℝ≥0
  measurable_toFun : Measurable toFun

/-- A randomized fake-value map, encoded by its conditional bid law given `v_O`: a Markov kernel
from `[0,1]` to `ℝ_{≥0}`. All of the source's quantities `U_O(V̂_O), P_O(V̂_O), P_L(V̂_O)` depend on a
distribution over maps only through this conditional law. -/
structure RandomizedFakeValue where
  kernel : Kernel I ℝ≥0
  isMarkov : IsMarkovKernel kernel

/-- Per-round unscaled utility `U_O = v_O 1{b > v_L}` at fake value `b`: value, not value minus
payment. -/
noncomputable def roundValue (b : ℝ≥0) (v : ValuePair) : ℝ :=
  (v.2 : ℝ) * if (v.1 : ℝ) < (b : ℝ) then 1 else 0

/-- Per-round unscaled optimizer payment `P_O(b, v_L)`: `v_L 1{b > v_L}` in second-price and
`b 1{b > v_L}` in first-price. -/
noncomputable def roundPayO (fmt : AuctionFormat) (b : ℝ≥0) (v : ValuePair) : ℝ :=
  auctionPayO fmt b v.1

/-- Per-round unscaled learner payment `P_L(b, v_L)`: `b 1{b ≤ v_L}` in second-price and
`v_L 1{b ≤ v_L}` in first-price. -/
noncomputable def roundPayL (fmt : AuctionFormat) (b : ℝ≥0) (v : ValuePair) : ℝ :=
  auctionPayL fmt b v.1

/-- `U_O(v̂_O) = E_D[U_O(v̂_O, v_O, v_L)]`. -/
noncomputable def expValue (D : Measure ValuePair) (a : FakeValue) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (roundValue (a.toFun v.2) v) ∂D

/-- `P_O(v̂_O)`, an extended nonnegative integral: it can be `+∞` in first-price. -/
noncomputable def expPayO (fmt : AuctionFormat) (D : Measure ValuePair) (a : FakeValue) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (roundPayO fmt (a.toFun v.2) v) ∂D

/-- `P_L(v̂_O)`; its integrand is at most `1` under the auction rules. -/
noncomputable def expPayL (fmt : AuctionFormat) (D : Measure ValuePair) (a : FakeValue) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (roundPayL fmt (a.toFun v.2) v) ∂D

/-- `U_O(V̂_O)` for a randomized fake-value map. -/
noncomputable def randValue (D : Measure ValuePair) (V : RandomizedFakeValue) : ℝ≥0∞ :=
  ∫⁻ v, ∫⁻ b, ENNReal.ofReal (roundValue b v) ∂(V.kernel v.2) ∂D

/-- `P_O(V̂_O)` for a randomized fake-value map; it can be `+∞` in first-price. -/
noncomputable def randPayO (fmt : AuctionFormat) (D : Measure ValuePair) (V : RandomizedFakeValue) :
    ℝ≥0∞ :=
  ∫⁻ v, ∫⁻ b, ENNReal.ofReal (roundPayO fmt b v) ∂(V.kernel v.2) ∂D

/-- `P_L(V̂_O)` for a randomized fake-value map. -/
noncomputable def randPayL (fmt : AuctionFormat) (D : Measure ValuePair) (V : RandomizedFakeValue) :
    ℝ≥0∞ :=
  ∫⁻ v, ∫⁻ b, ENNReal.ofReal (roundPayL fmt b v) ∂(V.kernel v.2) ∂D

/-- `E[v_L]`. The integrand is bounded and measurable, so this Bochner integral is genuine. -/
noncomputable def meanLearnerValue (D : Measure ValuePair) : ℝ := ∫ v, (v.1 : ℝ) ∂D

/-- `E[v_O]`. The integrand is bounded and measurable, so this Bochner integral is genuine. -/
noncomputable def meanOptimizerValue (D : Measure ValuePair) : ℝ := ∫ v, (v.2 : ℝ) ∂D

/-- `E[v_O 1{v_L = 0}]`. The integrand is bounded and measurable. -/
noncomputable def zeroLearnerValueMass (D : Measure ValuePair) : ℝ :=
  ∫ v, (v.2 : ℝ) * (if (v.1 : ℝ) = 0 then 1 else 0) ∂D

/-- The distributional condition `P[0 < v_L < v_O ε] = 0`. -/
def ValueGap (D : Measure ValuePair) (ε : ℝ) : Prop :=
  D {v | 0 < (v.1 : ℝ) ∧ (v.1 : ℝ) < (v.2 : ℝ) * ε} = 0

end BudgetedAuctionLearning.Robustness


