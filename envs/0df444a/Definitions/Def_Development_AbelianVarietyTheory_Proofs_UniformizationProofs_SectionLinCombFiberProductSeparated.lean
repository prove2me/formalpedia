-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:02.440523+00:00
-- url     : https://prove2.me/theorems/c6b5c66e-3a60-4c90-87ca-ccee52d538d2
-- title:
--   Section Lin Comb Fiber Product Separated
-- statement:
--   Definitions and structural lemmas for Section Lin Comb Fiber Product Separated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionLinCombFiberProductSeparated.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct TopologicalSpace
noncomputable section
namespace GlobalTheory.SectionsProduct
section Algebra
variable {F : Type} [CommRing F]
section
variable {P Q : Type} [Finite P] [Finite Q] {A : P → Type} {B : Q → Type}
  [∀ p, AddCommGroup (A p)] [∀ p, Module F (A p)] [∀ p, AddCommGroup (B p)] [∀ p, Module F (B p)]
end
end Algebra
open GlobalTheory.KuennethOne
variable {B Y T S X₁ X₂ W : Scheme.{0}} {L : LB B} {K : Type} [Fintype K]
def twist (i : Y ⟶ S) (φ : K → (Y ⟶ B)) (ε : K → ℤ) {U U' : Y.Opens} {j j' : K → L.ι}
    (hU : U ≤ LB.wchart L φ j) (hU' : U' ≤ LB.wchart L φ j') : Fn i U' →ₗ[Γ(S, ⊤)] Fn i (U ⊓ U') :=
  LinearMap.mulLeft Γ(S, ⊤) (show Fn i (U ⊓ U') from rs (inf_le_inf hU hU') ((LB.LinComb L φ ε).g j j').val) ∘ₗ
    (rsA i (inf_le_right : U ⊓ U' ≤ U')).toLinearMap
variable {p : W ⟶ X₁} {q : W ⟶ X₂} {i₁ : X₁ ⟶ S} {i₂ : X₂ ⟶ S} (H : IsPullback p q i₁ i₂)
def prodFn (U : X₁.Opens) (V : X₂.Opens) (t : Fn i₁ U ⊗[Γ(S, ⊤)] Fn i₂ V) : Γ(W, p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) :=
  mm H U V (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) inf_le_left inf_le_right t
section
variable {U U' : X₁.Opens} {V V' : X₂.Opens} (r : T ⟶ W) (z : T) (hz : r z ∈ p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V)
include hz
end
variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (X₁ ⟶ B)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (X₂ ⟶ B)) (ε₂ : K₂ → ℤ)
end GlobalTheory.SectionsProduct


