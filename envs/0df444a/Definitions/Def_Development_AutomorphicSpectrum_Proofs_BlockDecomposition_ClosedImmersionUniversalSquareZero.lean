-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZero
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZero
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:14:49.842474+00:00
-- url     : https://prove2.me/theorems/6b4aa4c2-224f-478d-bab9-3c3384236854
-- title:
--   Closed Immersion Universal Square Zero
-- statement:
--   Definitions and structural lemmas for Closed Immersion Universal Square Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedImmersionUniversalSquareZero.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
namespace GlobalTheory.CompanionTheory.CotLift
section Ker
variable {R P : Type} [CommRing R] [CommRing P]
def KerW (_ : R →+* P) (ε : P →+* R) : Type := RingHom.ker ε
variable (α : R →+* P) (ε : P →+* R)
instance : AddCommGroup (KerW α ε) := inferInstanceAs (AddCommGroup (RingHom.ker ε))
instance : Module P (KerW α ε) := inferInstanceAs (Module P (RingHom.ker ε))
instance : Module R (KerW α ε) := Module.compHom _ α
instance : Module Rᵐᵒᵖ (KerW α ε) :=
  Module.compHom _ (RingHom.fromOpposite (RingHom.id R) fun _ _ ↦ Commute.all _ _)
instance : IsCentralScalar R (KerW α ε) := ⟨fun _ _ ↦ rfl⟩
variable {α ε}
def KerW.val (w : KerW α ε) : P := Subtype.val (p := fun x ↦ x ∈ RingHom.ker ε) w
theorem KerW.ext' {v w : KerW α ε} (h : v.val = w.val) : v = w := Subtype.ext h
@[simp] theorem KerW.val_add (v w : KerW α ε) : (v + w).val = v.val + w.val := rfl
@[simp] theorem KerW.val_smul (r : R) (w : KerW α ε) : (r • w).val = α r * w.val := rfl
@[simp] theorem KerW.val_op_smul (r : R) (w : KerW α ε) : (MulOpposite.op r • w).val = α r * w.val := rfl
@[simp] theorem KerW.val_zero : (0 : KerW α ε).val = 0 := rfl
theorem KerW.eps_val (w : KerW α ε) : ε w.val = 0 := w.2
def pr (h : ε.comp α = RingHom.id R) (a : P) : KerW α ε :=
  ⟨a - α (ε a), by
    have e : ε (α (ε a)) = ε a := congrArg (fun f ↦ f (ε a)) h
    simp [RingHom.mem_ker, e]⟩
@[simp] theorem pr_val (h : ε.comp α = RingHom.id R) (a : P) : (pr h a).val = a - α (ε a) := rfl
theorem eps_alpha (h : ε.comp α = RingHom.id R) (r : R) : ε (α r) = r := congrArg (fun f ↦ f r) h
def theta (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) :
    P →+* TrivSqZeroExt R (KerW α ε) where
  toFun a := TrivSqZeroExt.inl (ε a) + TrivSqZeroExt.inr (pr h a)
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · apply KerW.ext'; simp
  map_zero' := by
    apply TrivSqZeroExt.ext
    · simp
    · apply KerW.ext'; simp
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · simp
    · apply KerW.ext'; simp; ring
  map_mul' a b := by
    have e := hsq (a - α (ε a)) (b - α (ε b)) (by simp [eps_alpha h]) (by simp [eps_alpha h])
    apply TrivSqZeroExt.ext
    · simp
    · apply KerW.ext'
      simp
      linear_combination e
@[simp] theorem theta_fst (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) (a : P) :
    (theta h hsq a).fst = ε a := by simp [theta]
@[simp] theorem theta_snd (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) (a : P) :
    (theta h hsq a).snd = pr h a := by simp [theta]
end Ker
section Main
variable {R P B M : Type} [CommRing R] [CommRing P] [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] {α : R →+* P} {ε : P →+* R}
def uOf (φ : P →+* TrivSqZeroExt B M) (hα : φ.comp α = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B))
    (hf : ∀ a, (φ a).fst = algebraMap R B (ε a)) : KerW α ε →ₗ[R] M where
  toFun w := (φ w.val).snd
  map_add' v w := by simp
  map_smul' r w := by
    have e : φ (α r) = TrivSqZeroExt.inl (algebraMap R B r) := congrArg (fun f ↦ f r) hα
    have z : (φ w.val).fst = 0 := by rw [hf, KerW.eps_val, map_zero]
    simp only [KerW.val_smul, map_mul, e, RingHom.id_apply, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, smul_zero, add_zero, algebraMap_smul]
end Main
end GlobalTheory.CompanionTheory.CotLift


