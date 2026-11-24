-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QIsoAtRight
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QIsoAtRight
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:49.330776+00:00
-- url     : https://prove2.me/theorems/821d90fd-cc30-4b33-b217-b3af6327d9ed
-- title:
--   QIso At Right
-- statement:
--   Definitions and structural lemmas for QIso At Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QIsoAtRight.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
namespace GlobalTheory.CompanionTheory.QCalc
section Linear
variable {R A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ : Type} [CommRing R]
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂]
  [Module R A₀] [Module R A₁] [Module R A₂]
  [Module R B₀] [Module R B₁] [Module R B₂]
  [Module R C₀] [Module R C₁] [Module R C₂]
  {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂}
  {c₀ : C₀ →ₗ[R] C₁} {c₁ : C₁ →ₗ[R] C₂}
  {f₀ : A₀ →ₗ[R] B₀} {f₁ : A₁ →ₗ[R] B₁} {f₂ : A₂ →ₗ[R] B₂}
  {g₀ : B₀ →ₗ[R] C₀} {g₁ : B₁ →ₗ[R] C₁} {g₂ : B₂ →ₗ[R] C₂} {k : A₁ →ₗ[R] C₁}
end Linear
end GlobalTheory.CompanionTheory.QCalc


