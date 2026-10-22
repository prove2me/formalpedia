-- Prove2me | Definitions.Def_BirkhoffGlobalSection_ConvexModelOrdinaryPage
-- name    : BirkhoffGlobalSection_ConvexModelOrdinaryPage
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-09-30T16:26:57.773548+00:00
-- url     : https://prove2.me/theorems/ad5c3e98-5a2b-4fd7-913b-ba29e8edf715
-- title:
--   Ordinary disk pages in a convex regularization model
-- statement:
--   Let M be a smooth convex regularization model of a Levi–Civita energy component, and let D identify a complete Levi–Civita flow with a complete model Hamiltonian flow through increasing onto clocks. For a periodic orbit gamma of the Levi–Civita flow, an ordinary model page is a smooth embedded immersed closed disk in the model boundary, with boundary exactly the model image of gamma. Its interior is transverse to the model Hamiltonian vector field, and every trajectory outside the binding meets this single disk at arbitrarily large positive and negative model times.
--
--   These data serve as the input for smooth coordinate and time-change transport of ordinary global sections. They assert no existence of a page and include no antipodal return alternative.
-- source:
--   Ordinary-page adaptation of caleb’s accepted BirkhoffGlobalSection.model_rational_page_pulls_back proof, submission f60b661a-fad7-4713-aa8b-33ee4b295579, https://prove2.me/api/v1/submissions/f60b661a-fad7-4713-aa8b-33ee4b295579/solution. Uses the existing smooth regularization and complete-clock interfaces. This is an auxiliary transport result for Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Theorems 1.2 and 1.5; not a verbatim source theorem or a page-existence claim.

import Definitions.Def_BirkhoffGlobalSection_ConvexModelDynamics

namespace BirkhoffGlobalSection

open scoped ContDiff

/-- An ordinary disk page in the convex model. Every trajectory off the given
binding returns to this page itself, at unbounded times in both directions.
This is input data for coordinate/time transport, not an existence assertion.
The regularization and clock data are the existing platform interfaces. -/
structure ConvexModelOrdinaryPage {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    {φ : Flow ℝ (LeftEnergyState μ c)} (D : ConvexModelDynamics M φ)
    (γ : PeriodicOrbit φ) where
  page : Plane → Phase
  mapsTo : ∀ u ∈ closedUnitDisk, page u ∈ frontier M.body
  smooth : ∀ u ∈ closedUnitDisk, ContDiffAt ℝ ∞ page u
  injective : Set.InjOn page closedUnitDisk
  immersion : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ page u)
  transverse : ∀ u ∈ openUnitDisk,
    hamiltonianVectorField M.modelHamiltonian (page u) ∉
      Set.range (fderiv ℝ page u)
  boundary : page '' unitCircle = M.toModel '' orbitSet γ
  returns : ∀ y : ConvexModelState M, (y : Phase) ∉ M.toModel '' orbitSet γ →
    (∀ R : ℝ, ∃ t : ℝ, R < t ∧
      ((D.flow t y : ConvexModelState M) : Phase) ∈ page '' openUnitDisk) ∧
    (∀ R : ℝ, ∃ t : ℝ, t < R ∧
      ((D.flow t y : ConvexModelState M) : Phase) ∈ page '' openUnitDisk)

end BirkhoffGlobalSection


