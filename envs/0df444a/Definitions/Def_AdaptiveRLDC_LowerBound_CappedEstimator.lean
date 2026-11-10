-- Prove2me | Definitions.Def_AdaptiveRLDC_LowerBound_CappedEstimator
-- name    : AdaptiveRLDC_LowerBound_CappedEstimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:57:44.235203+00:00
-- url     : https://prove2.me/theorems/c7ffa7f0-b831-4a8f-a3dc-2db7af348474
-- title:
--   Coordinate-capped Horvitz–Thompson optimization
-- statement:
--   For sub-distribution weights $\mu$, $p\in(0,1]$ and $\Gamma>0$, define
--   $$\overline R_{\mu,p,\Gamma}(x)=\sup\left\{\sum_Sw_S:0\le w_S\le\mu(S)p^{-|S|}x_S,\ \sum_{S\ni i}w_S\le\Gamma\ \forall i\right\}.$$
--   This is the optimization over all real feasible weights. Structural lemmas establish that its objective set is nonempty and bounded above on this domain. The finite closed bounded feasible polytope attains the supremum, so this equals the source maximum. The empty-set weight has its coefficient bound and occurs in no coordinate cap. This definition computes the estimator from its inputs and contains no assumed concentration or bias guarantee.
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Definition 4.5, printed p.17, PDF p.18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Mathlib
import Definitions.Def_AdaptiveRLDC_LowerBound_HorvitzThompson

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

open Classical

/-- Definition 4.5: caps apply to coordinate sums, including all sets containing that coordinate. -/
def CHTFeasible {n : ℕ} (μ : Sets n → ℝ) (p Γ : ℝ) (x : Cube n)
    (w : Sets n → ℝ) : Prop :=
  (∀ S, 0 ≤ w S ∧ w S ≤ htTerm μ p x S) ∧
    ∀ i : Fin n, (∑ S : Sets n, if i ∈ S then w S else 0) ≤ Γ

/-- The objective values of the actual finite-dimensional feasible polytope. -/
def chtValues {n : ℕ} (μ : Sets n → ℝ) (p Γ : ℝ) (x : Cube n) : Set ℝ :=
  {v | ∃ w : Sets n → ℝ, CHTFeasible μ p Γ x w ∧ v = ∑ S, w S}

/-- Computed supremum; the following structural facts rule out empty/unbounded defaults
on the source domain. Finite closed bounded feasibility also gives attainment. -/
def cht {n : ℕ} (μ : Sets n → ℝ) (p Γ : ℝ) (x : Cube n) : ℝ :=
  sSup (chtValues μ p Γ x)

/-- Every feasible objective is bounded by the sum of its finite coordinate bounds. -/
theorem chtValues_bddAbove {n : ℕ} (μ : Sets n → ℝ) (p Γ : ℝ) (x : Cube n) :
    BddAbove (chtValues μ p Γ x) := by
  refine ⟨ht μ p x, ?_⟩
  rintro v ⟨w, hw, rfl⟩
  exact Finset.sum_le_sum (fun S _ => (hw.1 S).2)

/-- Zero is feasible on the source domain, including the empty universe. -/
theorem chtValues_nonempty {n : ℕ} (μ : Sets n → ℝ) (hμ : IsSubdistribution μ)
    (p Γ : ℝ) (hp : 0 < p) (hΓ : 0 ≤ Γ) (x : Cube n) :
    (chtValues μ p Γ x).Nonempty := by
  refine ⟨0, (fun _ => 0), ⟨?_, ?_⟩, by simp⟩
  · intro S
    refine ⟨le_rfl, mul_nonneg (div_nonneg (hμ.1 S) (pow_nonneg hp.le _)) ?_⟩
    exact Finset.prod_nonneg (fun i _ => by split <;> norm_num)
  · intro i
    simpa using hΓ

end AdaptiveRLDC.LowerBound


