-- Prove2me | Definitions.Def_ProcessingNetworks_LyapunovCriteria_FluidEquationData
-- name    : ProcessingNetworks_LyapunovCriteria_FluidEquationData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:54:51.796646+00:00
-- url     : https://prove2.me/theorems/eedf2d47-3d83-49de-a836-3c9c4d426970
-- title:
--   Fluid equations (6.1)-(6.6), restated (cf. mission III)
-- statement:
--   This mission (like mission IV) restates mission III's fluid-equation model data and the
--   fluid equations (6.1)-(6.6) locally, since drafts in this series do not import one another.
--   See mission III's `MODERATION_NOTES.md` for the per-conjunct correspondence to (6.1)-(6.6);
--   this is an unmodified restatement, used here as the ambient notion of "a fluid model
--   consisting of (6.1)-(6.6) plus possibly other equations" that Lemma 8.3 and Lemma 8.5 both
--   refer to.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 106, Eqs. (6.1)-(6.6) (restated)

import Mathlib

namespace ProcessingNetworks.LyapunovCriteria

/-- Fluid-equation model data, restated from mission III's `FluidEquationData` (drafts in this
series do not import one another): `I` buffers, `J` activities, `K` server pools, the `I × J`
material-requirement matrix `B` and expected-output matrix `Γ`, the vector `m` of mean service
times, the `K × J` capacity-consumption matrix `A` and `K`-vector `b` of server-pool capacities,
and the vector `lam` of external arrival rates. -/
structure FluidEquationData (I J K : ℕ) where
  B : Matrix (Fin I) (Fin J) ℝ
  Γ : Matrix (Fin I) (Fin J) ℝ
  m : Fin J → ℝ
  A : Matrix (Fin K) (Fin J) ℝ
  b : Fin K → ℝ
  lam : Fin I → ℝ

/-- The fluid equations (6.1)-(6.6), restated from mission III's `IsFluidModelSolution` (see that
mission's `MODERATION_NOTES.md` for the per-conjunct correspondence to (6.1)-(6.6)). -/
def IsFluidModelSolution {I J K : ℕ} (dat : FluidEquationData I J K)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ i, Zh t i = Zh 0 i + dat.lam i * t + ∑ j, dat.Γ i j * Fh t j - Dh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = ∑ j, dat.B i j * Fh t j) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ j, dat.m j * Fh t j = Th t j) ∧
  (Th 0 = 0 ∧ Monotone Th) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ k, ∑ j, dat.A k j * (Th t j - Th s j) ≤ dat.b k * (t - s))

end ProcessingNetworks.LyapunovCriteria


