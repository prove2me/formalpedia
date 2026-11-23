-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:41.083872+00:00
-- url     : https://prove2.me/theorems/eb419f29-fb91-4f93-bc29-0414bdecc42b
-- title:
--   Exists Local Unit Of Weight
-- statement:
--   Definitions and structural lemmas for Exists Local Unit Of Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace TorsorUnit
section Algebra
variable {X : Type} [AddCommGroup X] {A C R R' : Type} [CommRing A] [CommRing C] [CommRing R]
  [CommRing R']
noncomputable def ev (θ : C →+* R) (φ : Multiplicative X →* Rˣ) : AddMonoidAlgebra C X →+* R :=
  AddMonoidAlgebra.liftNCRingHom θ ((Units.coeHom R).comp φ) fun _ _ => Commute.all _ _
variable (C X) in

noncomputable def univ : Multiplicative X →* (AddMonoidAlgebra C X)ˣ :=
  (AddMonoidAlgebra.of C X).toHomUnits
variable (C X) in

noncomputable abbrev cst : C →+* AddMonoidAlgebra C X := AddMonoidAlgebra.singleZeroRingHom
variable (R) in

def IsTorsorOn (α : A →+* C) (ρ : C →+* AddMonoidAlgebra C X) : Prop :=
  (∀ (θ : C →+* R) (φ φ' : Multiplicative X →* Rˣ),
    (ev θ (φ * φ')).comp ρ = (ev ((ev θ φ').comp ρ) φ).comp ρ) ∧
  (∀ (θ : C →+* R) (φ : Multiplicative X →* Rˣ), ((ev θ φ).comp ρ).comp α = θ.comp α) ∧
  (∀ (θ : C →+* R) (φ φ' : Multiplicative X →* Rˣ),
    (ev θ φ).comp ρ = (ev θ φ').comp ρ → φ = φ') ∧
  (∀ θ θ' : C →+* R, θ.comp α = θ'.comp α → ∃ φ : Multiplicative X →* Rˣ, θ' = (ev θ φ).comp ρ)
end Algebra
section Points
variable {Y Z Z' : Scheme.{0}} {U : Y.Opens}
noncomputable def pt (hU : IsAffineOpen U) (θ : Γ(Y, U) →+* Γ(Z, ⊤)) : Z ⟶ Y :=
  Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec
end Points
section Action
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G}
open SplitTorusPoints
end Action
end TorsorUnit
end GlobalTheory


