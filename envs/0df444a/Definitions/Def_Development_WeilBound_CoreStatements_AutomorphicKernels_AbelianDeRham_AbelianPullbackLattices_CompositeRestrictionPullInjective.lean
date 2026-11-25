-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:46.656954+00:00
-- url     : https://prove2.me/theorems/ae9f82ef-d81a-4fba-bcee-924f29ef18ba
-- title:
--   Composite Restriction Pull Injective
-- statement:
--   Definitions and structural lemmas for Composite Restriction Pull Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianPullbackLattices/CompositeRestrictionPullInjective.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
namespace MainStatements.Hodge.Pf.AXO
def USt {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module R M],
    (∀ m : M, (∀ T, m ⊗ₜ[R] (1 : F.obj T) = 0) → m = 0) ∧
    ∀ y : ∀ T, M ⊗[R] F.obj T, (∀ (T T' : C) (φ : T ⟶ T'), ((mp F φ).toLinearMap.lTensor M) (y T) = y T') →
      ∃ m : M, ∀ T, y T = m ⊗ₜ[R] 1
section Tri
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}
end Tri
variable {R : Type} [CommRing R]
def pO {Y Z : Over (Sp R)} (f : Y ⟶ Z) : HO1 Z.hom →ₗ[R] HO1 Y.hom := pullHO1 (wOver f)
end MainStatements.Hodge.Pf.AXO


