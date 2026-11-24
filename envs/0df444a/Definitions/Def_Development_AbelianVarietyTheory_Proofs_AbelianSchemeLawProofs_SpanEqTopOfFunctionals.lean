-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T19:43:14.266963+00:00
-- url     : https://prove2.me/theorems/652dfca0-810b-40ef-ab65-c162029e75cd
-- title:
--   Span Eq Top Of Functionals
-- statement:
--   Definitions and structural lemmas for Span Eq Top Of Functionals, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpanEqTopOfFunctionals.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
section General
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
theorem wchart_le_of_eq {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k)
    (j : K → L.ι) : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
def pullTo {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) : LB.Sec (LB.LinComb L φ' ε) where
  f j := (Y'.presheaf.map (homOfLE (wchart_le_of_eq h e j)).op).hom ((h.app _).hom (s.f j))
  compat := by
    obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
    exact (H1.SectionArithmetic.pullSec s h).compat
end General
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
omit [GrpObj A] in
theorem whisker_snd_left {T T' : Over S} (h : T' ⟶ T) :
    (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by
  rw [← Over.comp_left, whiskerRight_snd]
def pullS (a : ℤ) {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) : LB.Sec (LPow A L a T') :=
  pullTo (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (h ▷ A).left
    (fun _ => whisker_snd_left A h)
abbrev sv {a : ℤ} {T : Over S} (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : Z.presheaf.stalk z :=
  sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z J
def pullM (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⟶ T) :
    SecM A L a T →ₛₗ[h.left.appTop.hom] SecM A L a T' where
  toFun f := SecM.ofSec A (pullS A a h (SecM.toSec A f))
  map_add' f g := Subtype.ext (funext fun j => map_add ((h ▷ A).left.appLE _ _
    (chart_le_res A L (h ▷ A) (whiskerRight_snd h A) a j)).hom (f.1 j) (g.1 j))
  map_smul' c f := Subtype.ext (funext fun j => by
    refine (map_mul ((h ▷ A).left.appLE _ _
      (chart_le_res A L (h ▷ A) (whiskerRight_snd h A) a j)).hom (liftHom A _ c) (f.1 j)).trans ?_
    refine congrArg (· * _) (fn_ext fun y hy => ?_)
    have hy' := chart_le_res A L (h ▷ A) (whiskerRight_snd h A) a j hy
    have e : (h ▷ A).left ≫ (fst T A).left = (fst T' A).left ≫ h.left := by
      rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    refine (gs_res _ y _ hy _).trans ((gs_pull _ _ y _ hy' _).trans ((gs_res _ y le_top hy' _).trans
      ((gs_pull _ _ y ⊤ trivial _).trans (Eq.trans ?_ ((gs_res _ y le_top hy _).trans
        ((gs_pull _ _ y ⊤ trivial _).trans (gs_pull _ h.left y ⊤ trivial _))).symm))))
    rw [Category.assoc, e, Category.assoc])
section Twist
variable {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
end Twist
end GlobalTheory.VVRank


