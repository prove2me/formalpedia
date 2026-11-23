-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationUniformisedAbelianVarietyUniqueVec
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationUniformisedAbelianVarietyUniqueVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:48.314787+00:00
-- url     : https://prove2.me/theorems/8bf37dc3-fcc7-4b53-97f8-a2f8ec951fd4
-- title:
--   Germ Derivation Uniformised Abelian Variety Unique Vec
-- statement:
--   Definitions and structural lemmas for Germ Derivation Uniformised Abelian Variety Unique Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GermDerivationUniformisedAbelianVarietyUniqueVec.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.TangentAt
def dval {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    DualNumber ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE U ⊤ h).hom f)
theorem dval_comp {X Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (t : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (v ≫ t) ⁻¹ᵁ U) (V : X.Opens) (e : V ≤ t ⁻¹ᵁ U) (hV : ⊤ ≤ v ⁻¹ᵁ V) (f : Γ(Y, U)) :
    dval (v ≫ t) U h f = dval v V hV ((t.appLE U V e).hom f) := by
  simp only [dval, ← Scheme.Hom.appLE_comp_appLE v t U V ⊤ e hV, CommRingCat.hom_comp, RingHom.comp_apply]
variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
def tr (a : Fin g → ℂ) : A ⟶ A := (toUnit A ≫ u.ex a) * 𝟙 A
theorem comp_tr {B : Over (Sp ℂ)} (x : B ⟶ A) (a : Fin g → ℂ) : x ≫ tr u a = (toUnit B ≫ u.ex a) * x := by
  rw [tr, comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit B), Category.comp_id]
theorem ex_tr (a z : Fin g → ℂ) : u.ex z ≫ tr u a = u.ex (a + z) := by
  rw [comp_tr, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, u.ex_add]
def DiffAt (v : Sp (DualNumber ℂ) ⟶ A.left) (z w : Fin g → ℂ) : Prop :=
  ∀ (U : A.left.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(A.left, U)),
    (dval v U h f).snd = fderiv ℂ (fun z' => valAt' (u.ex z').left U f) z w
theorem DiffAt.tr {v : Sp (DualNumber ℂ) ⟶ A.left} {z w : Fin g → ℂ} (h : DiffAt u v z w) (a : Fin g → ℂ) :
    DiffAt u (v ≫ (tr u a).left) (a + z) w := by
  have nat : ∀ {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
      (e : V ≤ φ ⁻¹ᵁ U) (hx : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, U)),
      valAt' x V ((φ.appLE U V e).hom f) = valAt' (x ≫ φ) U f := by
    intro X Y x φ U V e hx f
    have hxφ : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := fun y hy => e (hx hy)
    rw [valAt', dif_pos hx, valAt', dif_pos hxφ, valAt, valAt, ← Scheme.Hom.appLE_comp_appLE x φ U V ⊤ e hx,
      CommRingCat.hom_comp, RingHom.comp_apply]
  intro U h' f
  have hV : ⊤ ≤ v ⁻¹ᵁ ((TangentAt.tr u a).left ⁻¹ᵁ U) := h'
  rw [dval_comp v (TangentAt.tr u a).left U h' _ le_rfl hV f, h]
  have hfun : (fun z' => valAt' (u.ex z').left ((TangentAt.tr u a).left ⁻¹ᵁ U) (((TangentAt.tr u a).left.appLE U _ le_rfl).hom f)) =
      fun z' => valAt' (u.ex (a + z')).left U f := by
    funext z'
    by_cases hz : ⊤ ≤ (u.ex z').left ⁻¹ᵁ ((TangentAt.tr u a).left ⁻¹ᵁ U)
    · rw [nat _ _ _ _ _ hz, ← Over.comp_left, ex_tr]
    · have hz' : ¬ ⊤ ≤ (u.ex (a + z')).left ⁻¹ᵁ U := by
        rw [← ex_tr, Over.comp_left]
        exact hz
      rw [valAt', dif_neg hz, valAt', dif_neg hz']
  rw [hfun]
  exact congrArg (fun L => L w) (fderiv_comp_add_left (𝕜 := ℂ) (f := fun y => valAt' (u.ex y).left U f) a)
end GlobalTheory.KS.TangentAt
end


