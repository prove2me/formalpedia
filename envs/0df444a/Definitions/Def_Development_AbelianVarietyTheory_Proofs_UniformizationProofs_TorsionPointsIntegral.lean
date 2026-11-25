-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:07:41.813346+00:00
-- url     : https://prove2.me/theorems/882060f3-dfac-468e-9d78-8a79683c1e83
-- title:
--   Torsion Points Integral
-- statement:
--   Definitions and structural lemmas for Torsion Points Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory
namespace TorsionIntegral
def fracUnits {A S : Type} [CommRing A] [CommRing S] (ρ : A →+* S) : Subgroup Sˣ where
  carrier := {v | ∃ a b : A, IsUnit (ρ b) ∧ v.val * ρ b = ρ a}
  one_mem' := ⟨1, 1, by simp, by simp⟩
  mul_mem' := by
    rintro v v' ⟨a, b, hb, e⟩ ⟨a', b', hb', e'⟩
    exact ⟨a * a', b * b', by rw [map_mul]; exact hb.mul hb', by
      rw [map_mul, map_mul, Units.val_mul, ← e, ← e']; ring⟩
  inv_mem' := by
    rintro v ⟨a, b, hb, e⟩
    exact ⟨b, a, e ▸ v.isUnit.mul hb, by rw [← e, Units.inv_mul_cancel_left]⟩
section Values
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
def germTop (φ : Z ⟶ Y) (z : Z) : Γ(Y, ⊤) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (φ ⁻¹ᵁ ⊤) z trivial).hom.comp (φ.app ⊤).hom
end Values
section Points
open ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (z : (TF (R := R) F).left)
def Restricts (g' : GtPt D T) (g : GtPtF D F) : Prop :=
  φ ≫ g'.b = g.b ∧ ∀ χ J, Good D.P.L z J → val (g'.s χ) φ.left z J = val (g.s χ) (𝟙 _) z J
variable (hd : ∀ (U : T.left.Opens) (y : T.left), y ∈ U → φ.left z ∈ U)
  (hi : ∀ (U : T.left.Opens), φ.left z ∈ U → Function.Injective (gm φ.left z U))
  (he : ∀ ψ ψ' : T.left ⟶ D.P.A.left, φ.left ≫ ψ = φ.left ≫ ψ' → ψ = ψ')
include hd hi he
variable {J₀ : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι} (hJ₀ : Good D.P.L z J₀)
  (h₀ : ∀ (q : T.left ⟶ D.P.A.left) (y : T.left), q y ∈ D.P.L.U (J₀ (φ.left ≫ q)))
include hJ₀ h₀
end Points
def toStalkField (F : Type) [Field F] (z : Spec (CommRingCat.of F)) : F →+* (Spec (CommRingCat.of F)).presheaf.stalk z :=
  ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
end TorsionIntegral
end GlobalTheory


