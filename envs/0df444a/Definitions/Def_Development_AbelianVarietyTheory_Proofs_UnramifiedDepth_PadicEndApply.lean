-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicEndApply
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicEndApply
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:34:02.9458+00:00
-- url     : https://prove2.me/theorems/eeb42cdc-6405-59a9-ad38-f639e9954064
-- title:
--   Padic End Apply
-- statement:
--   Definitions and structural lemmas for Padic End Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PadicEndApply.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PadicOrderAction
def padicEnd (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (hM : ∀ x : M, p • x = 0) :
    ℤ_[p] →+* AddMonoid.End M where
  toFun c := nsmulAddMonoidHom (PadicInt.toZMod c).val
  map_one' := by
    ext x
    change (PadicInt.toZMod (1 : ℤ_[p])).val • x = x
    rw [map_one, ZMod.val_one, one_nsmul]
  map_mul' a b := by
    ext x
    change (PadicInt.toZMod (a * b)).val • x = (PadicInt.toZMod a).val • (PadicInt.toZMod b).val • x
    rw [map_mul, ZMod.val_mul, ← nsmul_eq_mod_nsmul _ (hM x), mul_nsmul']
  map_zero' := by
    ext x
    change (PadicInt.toZMod (0 : ℤ_[p])).val • x = 0
    rw [map_zero, ZMod.val_zero, zero_nsmul]
  map_add' a b := by
    ext x
    change (PadicInt.toZMod (a + b)).val • x = (PadicInt.toZMod a).val • x + (PadicInt.toZMod b).val • x
    rw [map_add, ZMod.val_add, ← nsmul_eq_mod_nsmul _ (hM x), add_nsmul]
def liftInt {A B C : Type} [CommRing A] [CommRing B] [Ring C] (φ : A →+* C) (ψ : B →+* C)
    (h : ∀ a b, φ a * ψ b = ψ b * φ a) : A ⊗[ℤ] B →+* C :=
  (Algebra.TensorProduct.lift φ.toIntAlgHom ψ.toIntAlgHom h).toRingHom
variable {R₀ : Type} [CommRing R₀]
lemma pTorsion_nsmul_eq_zero (B : BX R₀) (p : ℕ) (S : LAlg R₀) (x : torP B p S) : p • x = 0 :=
  Subtype.ext ((mem_torP B p _).1 x.2)
def resEnd {B : BX R₀} {O : LAlg R₀} (e : OEnd B O) (p : ℕ) {S : LAlg R₀} (s : LHom O S) :
    AddMonoid.End (torP B p S) :=
  ((e.f s).comp (torP B p S).subtype).codRestrict (torP B p S) fun x => by
    rw [mem_torP, ← map_nsmul, pTorsion_nsmul_eq_zero, map_zero]
def ordEnd {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) : O₀ →+* AddMonoid.End (torP B p S) :=
  RingHom.mk' (α := O₀) (β := AddMonoid.End (torP B p S))
    { toFun := fun a => resEnd (f a) p s
      map_one' := AddMonoidHom.ext fun x => Subtype.ext (h x).1
      map_mul' := fun a b => AddMonoidHom.ext fun x => Subtype.ext ((h x).2 a b).2 }
    fun a b => AddMonoidHom.ext fun x => Subtype.ext ((h x).2 a b).1
def complEnd {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    [Fact p.Prime] {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) :
    ℤ_[p] ⊗[ℤ] O₀ →+* AddMonoid.End (torP B p S) :=
  liftInt (padicEnd p _ (pTorsion_nsmul_eq_zero B p S)) (ordEnd f p s h) fun c a =>
    AddMonoidHom.ext fun x => (map_nsmul (ordEnd f p s h a) (PadicInt.toZMod c).val x).symm
def complMat {g : ℕ} {O : Type} [CommRing O] {O₀ : Type} [CommRing O₀] (p : ℕ) [Fact p.Prime]
    [Algebra ℤ_[p] O] (dL : O₀ →+* Matrix (Fin g) (Fin g) O) :
    ℤ_[p] ⊗[ℤ] O₀ →+* Matrix (Fin g) (Fin g) O :=
  liftInt (algebraMap ℤ_[p] (Matrix (Fin g) (Fin g) O)) dL fun c a => Algebra.commutes c (dL a)
def kerMul {R S : LAlg R₀} (π : LHom R S) (r : (R : Type)) (i : π.ker) : π.ker :=
  ⟨r * i, Ideal.mul_mem_left (RingHom.ker π.1) r i.2⟩
end GlobalTheory.PadicOrderAction


