-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T14:16:25.350951+00:00
-- url     : https://prove2.me/theorems/aa308312-b0b4-4ee4-9113-bea347423916
-- title:
--   Sec Equiv Res M
-- statement:
--   Definitions and structural lemmas for Sec Equiv Res M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SecEquivResM.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.AffGlue
structure Data (T : Scheme.{0}) where

  M : ∀ V : T.Opens, IsAffineOpen V → Type

  grp : ∀ V hV, AddCommGroup (M V hV)

  mod : ∀ V hV, Module Γ(T, V) (M V hV)

  ρ : ∀ {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V'), V' ≤ V → M V hV →+ M V' hV'
  ρ_smul : ∀ {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (a : Γ(T, V)) (m : M V hV), ρ hV hV' h (a • m) = resG T h a • ρ hV hV' h m
  ρ_self : ∀ {V : T.Opens} (hV : IsAffineOpen V) (h : V ≤ V) (m : M V hV), ρ hV hV h m = m
  ρ_ρ : ∀ {V V' V'' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hV'' : IsAffineOpen V'') (h : V' ≤ V) (h' : V'' ≤ V') (m : M V hV),
    ρ hV' hV'' h' (ρ hV hV' h m) = ρ hV hV'' (h'.trans h) m

  loc_surj : ∀ {V : T.Opens} (hV : IsAffineOpen V) (f : Γ(T, V)) (hD : IsAffineOpen (T.basicOpen f))
    (m : M (T.basicOpen f) hD), ∃ (n : ℕ) (x : M V hV),
      resG T (T.basicOpen_le f) f ^ n • m = ρ hV hD (T.basicOpen_le f) x

  loc_inj : ∀ {V : T.Opens} (hV : IsAffineOpen V) (f : Γ(T, V)) (hD : IsAffineOpen (T.basicOpen f))
    (x : M V hV), ρ hV hD (T.basicOpen_le f) x = 0 → ∃ n : ℕ, f ^ n • x = 0
attribute [instance] Data.grp Data.mod
variable {T : Scheme.{0}} (D : Data T)
abbrev AffIn (U : T.Opens) : Type := {W : T.Opens // IsAffineOpen W ∧ W ≤ U}
def fam (U : T.Opens) : AddSubgroup (∀ W : AffIn U, D.M W.1 W.2.1) where
  carrier := {m | ∀ (W W' : AffIn U) (h : W'.1 ≤ W.1), D.ρ W.2.1 W'.2.1 h (m W) = m W'}
  add_mem' {a b} ha hb W W' h := by simp only [Pi.add_apply, map_add, ha W W' h, hb W W' h]
  zero_mem' W W' h := by simp only [Pi.zero_apply, map_zero]
  neg_mem' {a} ha W W' h := by simp only [Pi.neg_apply, map_neg, ha W W' h]
theorem fam_rel {U : T.Opens} (m : fam D U) (W W' : AffIn U) (h : W'.1 ≤ W.1) :
    D.ρ W.2.1 W'.2.1 h (m.1 W) = m.1 W' := m.2 W W' h
theorem resG_resG' {U V W : T.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : W ≤ U) (a : Γ(T, U)) :
    resG T h₂ (resG T h₁ a) = resG T h₃ a := by
  change (T.presheaf.map (homOfLE h₁).op ≫ T.presheaf.map (homOfLE h₂).op).hom a = _
  rw [← T.presheaf.map_comp]
  rfl
instance famModule (U : T.Opens) : Module Γ(T, U) (fam D U) where
  smul a m := ⟨fun W => resG T W.2.2 a • m.1 W, fun W W' h => by
    rw [D.ρ_smul, fam_rel D m W W' h, resG_resG']⟩
  one_smul m := Subtype.ext <| funext fun W => by
    change resG T W.2.2 (1 : Γ(T, U)) • m.1 W = m.1 W
    rw [map_one, one_smul]
  mul_smul a b m := Subtype.ext <| funext fun W => by
    change resG T W.2.2 (a * b) • m.1 W = resG T W.2.2 a • (resG T W.2.2 b • m.1 W)
    rw [map_mul, mul_smul]
  smul_zero a := Subtype.ext <| funext fun W => smul_zero _
  smul_add a m m' := Subtype.ext <| funext fun W => smul_add _ _ _
  add_smul a b m := Subtype.ext <| funext fun W => by
    change resG T W.2.2 (a + b) • m.1 W = resG T W.2.2 a • m.1 W + resG T W.2.2 b • m.1 W
    rw [map_add, add_smul]
  zero_smul m := Subtype.ext <| funext fun W => by
    change resG T W.2.2 (0 : Γ(T, U)) • m.1 W = 0
    rw [map_zero, zero_smul]
@[simp] theorem smul_val {U : T.Opens} (a : Γ(T, U)) (m : fam D U) (W : AffIn U) :
    (a • m).1 W = resG T W.2.2 a • m.1 W := rfl
def famRes {U U' : T.Opens} (h : U' ≤ U) : fam D U →+ fam D U' where
  toFun m := ⟨fun W => m.1 ⟨W.1, W.2.1, W.2.2.trans h⟩, fun W W' h' =>
    m.2 ⟨W.1, W.2.1, W.2.2.trans h⟩ ⟨W'.1, W'.2.1, W'.2.2.trans h⟩ h'⟩
  map_zero' := rfl
  map_add' _ _ := rfl
@[simp] theorem famRes_val {U U' : T.Opens} (h : U' ≤ U) (m : fam D U) (W : AffIn U') :
    (famRes D h m).1 W = m.1 ⟨W.1, W.2.1, W.2.2.trans h⟩ := rfl
theorem famRes_smul {U U' : T.Opens} (h : U' ≤ U) (a : Γ(T, U)) (m : fam D U) :
    famRes D h (a • m) = resG T h a • famRes D h m :=
  Subtype.ext <| funext fun W => by
    change resG T (W.2.2.trans h) a • m.1 ⟨W.1, W.2.1, W.2.2.trans h⟩ =
      resG T W.2.2 (resG T h a) • m.1 ⟨W.1, W.2.1, W.2.2.trans h⟩
    rw [resG_resG']
def famPresheaf : TopCat.Presheaf Ab.{0} T where
  obj U := AddCommGrpCat.of (fam D U.unop)
  map f := AddCommGrpCat.ofHom (famRes D (leOfHom f.unop))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl
def toModules (hD : (famPresheaf D).IsSheaf) : T.Modules :=
  letI : ∀ U, Module (T.ringCatSheaf.obj.obj U) ((famPresheaf D).obj U) :=
    fun U => famModule D U.unop
  { val := PresheafOfModules.ofPresheaf (famPresheaf D) fun _ _ f r m =>
      famRes_smul D (leOfHom f.unop) r m
    isSheaf := hD }
def ofAff {V : T.Opens} (hV : IsAffineOpen V) (x : D.M V hV) : fam D V :=
  ⟨fun W => D.ρ hV W.2.1 W.2.2 x, fun W W' h => D.ρ_ρ hV W.2.1 W'.2.1 W.2.2 h x⟩
def affEquiv {V : T.Opens} (hV : IsAffineOpen V) : fam D V ≃ₗ[Γ(T, V)] D.M V hV where
  toFun m := m.1 ⟨V, hV, le_rfl⟩
  invFun := ofAff D hV
  map_add' _ _ := rfl
  map_smul' a m := by
    change resG T le_rfl a • m.1 ⟨V, hV, le_rfl⟩ = a • m.1 ⟨V, hV, le_rfl⟩
    congr 1
    change (T.presheaf.map (homOfLE le_rfl).op).hom a = a
    rw [show (homOfLE (le_rfl : V ≤ V)).op = 𝟙 (op V) from rfl, T.presheaf.map_id]
    rfl
  left_inv m := Subtype.ext <| funext fun W => fam_rel D m ⟨V, hV, le_rfl⟩ W W.2.2
  right_inv x := D.ρ_self hV le_rfl x
variable {D}
def secEquiv (hD : (famPresheaf D).IsSheaf) {V : T.Opens} (hV : IsAffineOpen V) :
    Γ(toModules D hD, V) ≃ₗ[Γ(T, V)] D.M V hV :=
  affEquiv D hV
end GlobalTheory.AffGlue


