-- Prove2me | Definitions.Def_GEPPGrowth_Main_Wishart
-- name    : GEPPGrowth_Main_Wishart
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:35:00.444846+00:00
-- url     : https://prove2.me/theorems/8a922e2d-8036-4530-ad15-5385340aa2a2
-- title:
--   Definition 4.9 — real Wishart law
-- statement:
--   For positive integers $p,n$ and a real positive semidefinite $p\times p$ covariance $V$, draw $n$ independent columns with law $N(0,V)$ and assemble them into $G\in\mathbb R^{p\times n}$. The real Wishart distribution is
--
--   $$W_p(V,n)=\operatorname{Law}(GG^\top).$$
--
--   This construction retains singular covariances and imposes no invertibility assumption. It supplies the determinant law in Lemma 4.10. The unused zero-dimensional extensions are defined by the same finite-product formula.
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Definition 4.9, printed p.9, PDF p.10

import Definitions.Def_GEPPGrowth_Main_Gaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Definition 4.9: real Wishart law from independent N(0,V) columns. -/
noncomputable def wishart {p : ℕ} (V : Mat p) (n : ℕ) : Measure (Mat p) :=
  (columnsLaw V n).map (fun G : Matrix (Fin p) (Fin n) ℝ => G * G.transpose)

instance wishart_isProbabilityMeasure {p : ℕ} (V : Mat p) (n : ℕ) :
    IsProbabilityMeasure (wishart V n) := by
  unfold wishart
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  change Measurable (fun G : Fin p → Fin n → ℝ => fun i j => ∑ k, G i k * G j k)
  fun_prop

end GEPPGrowth.Main


