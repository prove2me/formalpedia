-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:41.553652+00:00
-- url     : https://prove2.me/theorems/fe3c9698-a177-490b-90a3-698d65583e82
-- title:
--   Fam Mod
-- statement:
--   Definitions and structural lemmas for Fam Mod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FamMod.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
namespace SecOps
variable {X : Scheme.{0}} {L : LB X}
theorem sec_ext {s t : LB.Sec L} (h : ∀ i, s.f i = t.f i) : s = t := by
  rcases s with ⟨f, hf⟩
  rcases t with ⟨g, hg⟩
  have e : f = g := funext fun i => h i
  subst e
  rfl
theorem resTop_res {W W' : X.Opens} (h : W' ≤ W) (c : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resTop W c) = resTop W' c := by
  simp only [resTop]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl
def secZero : LB.Sec L where
  f := fun _ => 0
  compat := fun i j => by simp only [map_zero, mul_zero]
def secAdd (s t : LB.Sec L) : LB.Sec L where
  f := fun i => s.f i + t.f i
  compat := fun i j => by simp only [map_add, s.compat, t.compat, mul_add]
def secNeg (s : LB.Sec L) : LB.Sec L where
  f := fun i => - s.f i
  compat := fun i j => by simp only [map_neg, s.compat, mul_neg]
def secScale (c : Γ(X, ⊤)) (s : LB.Sec L) : LB.Sec L where
  f := fun i => resTop _ c * s.f i
  compat := fun i j => by
    rw [map_mul, s.compat, resTop_res, map_mul, resTop_res, mul_left_comm]
end SecOps
section Fam
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
  [Algebra (FractionRing R) F]
def gF : F →+* Γ((DegPre.BF D F).left, ⊤) :=
  (fst (TF (R := R) F) D.P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
theorem trF_const (mu : D.X) (ζ : F) (W : (DegPre.BF D F).left.Opens) :
    ((DegPre.trF D F mu).left.app W).hom (resTop W (gF D F ζ)) = resTop _ (gF D F ζ) := by
  have hfp : (DegPre.trF D F mu).left ≫ (fst (TF (R := R) F) D.P.A).left =
      (fst (TF (R := R) F) D.P.A).left := by
    rw [← Over.comp_left]
    simp [DegPre.trF]
  simp only [resTop, gF, RingHom.comp_apply]
  set f := (DegPre.trF D F mu).left with hf
  set p := (fst (TF (R := R) F) D.P.A).left with hp
  set c0 := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ with hc0
  clear_value f p c0
  clear hf hp hc0
  have e3 : Scheme.Hom.app p ⊤ ≫ Scheme.Hom.app f ⊤ = Scheme.Hom.app (f ≫ p) ⊤ := by
    first
      | exact (Scheme.Hom.comp_app f p ⊤).symm
      | exact (Scheme.comp_app f p ⊤).symm
      | simp
  have e2 : Scheme.Hom.app (f ≫ p) ⊤ = Scheme.Hom.app p ⊤ ≫
      (D.BF F).left.presheaf.map (eqToHom (by rw [hfp])).op := by
    first
      | exact Scheme.Hom.congr_app hfp ⊤
      | exact Scheme.congr_app hfp ⊤
  have key : Scheme.Hom.appTop p ≫ (D.BF F).left.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
      Scheme.Hom.app f W =
      Scheme.Hom.appTop p ≫ (D.BF F).left.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ W ≤ ⊤)).op := by
    rw [Scheme.Hom.naturality, ← Category.assoc]
    erw [e3, e2]
    erw [Category.assoc, ← Functor.map_comp]
    rfl
  exact congrArg (fun φ => (CommRingCat.Hom.hom φ) c0) key
variable {D F} {k : ℕ}
theorem fam_ext {s t : Fam D F k} (h : ∀ α j, (s.s α).f j = (t.s α).f j) : s = t := by
  rcases s with ⟨s, hs⟩
  rcases t with ⟨t, ht⟩
  have e : s = t := funext fun α => SecOps.sec_ext fun j => h α j
  subst e
  rfl
instance : Zero (Fam D F k) where
  zero := ⟨fun _ => SecOps.secZero, fun mu α u hu hc j₁ j₂ j₃ hcoh => by
    show _ = _
    erw [map_zero, map_zero, map_zero, zero_mul]⟩
instance : Add (Fam D F k) where
  add s t := ⟨fun α => SecOps.secAdd (s.s α) (t.s α), fun mu α u hu hc j₁ j₂ j₃ hcoh => by
    have h1 := s.fe mu α u hu hc j₁ j₂ j₃ hcoh
    have h2 := t.fe mu α u hu hc j₁ j₂ j₃ hcoh
    show _ = _
    erw [map_add, map_add, map_add, h1, h2, add_mul]⟩
instance : Neg (Fam D F k) where
  neg s := ⟨fun α => SecOps.secNeg (s.s α), fun mu α u hu hc j₁ j₂ j₃ hcoh => by
    have h1 := s.fe mu α u hu hc j₁ j₂ j₃ hcoh
    show _ = _
    erw [map_neg, map_neg, map_neg, h1, neg_mul]⟩
instance : SMul F (Fam D F k) where
  smul ζ s := ⟨fun α => SecOps.secScale (gF D F ζ) (s.s α), fun mu α u hu hc j₁ j₂ j₃ hcoh => by
    have h1 := s.fe mu α u hu hc j₁ j₂ j₃ hcoh
    show _ = _
    erw [map_mul, map_mul, map_mul, h1, SecOps.resTop_res, trF_const, SecOps.resTop_res, _root_.mul_assoc]⟩
@[simp] theorem zero_f (α : D.X) (j) : ((0 : Fam D F k).s α).f j = 0 := rfl
@[simp] theorem add_f (s t : Fam D F k) (α : D.X) (j) : ((s + t).s α).f j = (s.s α).f j + (t.s α).f j := rfl
@[simp] theorem neg_f (s : Fam D F k) (α : D.X) (j) : ((-s).s α).f j = - (s.s α).f j := rfl
@[simp] theorem smul_f (ζ : F) (s : Fam D F k) (α : D.X) (j) :
    ((ζ • s).s α).f j = resTop _ (gF D F ζ) * (s.s α).f j := rfl
instance : AddCommGroup (Fam D F k) where
  add_assoc a b c := fam_ext fun α j => by simp only [add_f, add_assoc]
  zero_add a := fam_ext fun α j => by simp only [add_f, zero_f, zero_add]
  add_zero a := fam_ext fun α j => by simp only [add_f, zero_f, add_zero]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := fam_ext fun α j => by simp only [add_f, neg_f, zero_f, neg_add_cancel]
  add_comm a b := fam_ext fun α j => by simp only [add_f, add_comm]
instance : Module F (Fam D F k) where
  one_smul a := fam_ext fun α j => by simp only [smul_f, map_one, resTop, _root_.one_mul]
  mul_smul x y a := fam_ext fun α j => by simp only [smul_f, map_mul, resTop, _root_.mul_assoc]
  smul_zero x := fam_ext fun α j => by simp only [smul_f, zero_f, mul_zero]
  smul_add x a b := fam_ext fun α j => by simp only [smul_f, add_f, mul_add]
  add_smul x y a := fam_ext fun α j => by simp only [smul_f, add_f, map_add, resTop, add_mul]
  zero_smul a := fam_ext fun α j => by simp only [smul_f, zero_f, map_zero, resTop, zero_mul]
end Fam
end ReciprocityTheory.ChartRestriction.G.DVR


