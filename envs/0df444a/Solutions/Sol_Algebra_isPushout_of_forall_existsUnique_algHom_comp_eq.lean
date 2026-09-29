-- Prove2me | solution 1 for Algebra.isPushout_of_forall_existsUnique_algHom_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1c22777e-881e-5522-80c1-d7f7e90858ff

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_isPushout_of_forall_existsUnique_algHom_comp_eq

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace IsPushoutOfUnivBody

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']

noncomputable def alphaR : S ⊗[R] R' →ₐ[R] S' :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S S') (IsScalarTower.toAlgHom R R' S')
    (fun _ _ => Commute.all _ _)

lemma alphaR_tmul (s : S) (r : R') :
    (alphaR : S ⊗[R] R' →ₐ[R] S') (s ⊗ₜ r) = algebraMap S S' s * algebraMap R' S' r := by
  simp [alphaR, Algebra.TensorProduct.lift_tmul]

lemma algebraMap_right_apply (r : R') :
    algebraMap R' (S ⊗[R] R') r = (1 : S) ⊗ₜ[R] r := rfl

noncomputable def alpha : S ⊗[R] R' →ₐ[R'] S' :=
  { (alphaR : S ⊗[R] R' →ₐ[R] S').toRingHom with
    commutes' := fun r => by
      change (alphaR : S ⊗[R] R' →ₐ[R] S').toRingHom (algebraMap R' (S ⊗[R] R') r) = _
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, algebraMap_right_apply, alphaR_tmul, map_one,
        one_mul] }

lemma alpha_apply (x : S ⊗[R] R') :
    (alpha : S ⊗[R] R' →ₐ[R'] S') x = (alphaR : S ⊗[R] R' →ₐ[R] S') x := rfl

lemma alpha_tmul (s : S) (r : R') :
    (alpha : S ⊗[R] R' →ₐ[R'] S') (s ⊗ₜ r) = algebraMap S S' s * algebraMap R' S' r := by
  rw [alpha_apply, alphaR_tmul]

lemma alpha_comp_algebraMap :
    (alpha : S ⊗[R] R' →ₐ[R'] S').toRingHom.comp (algebraMap S (S ⊗[R] R')) = algebraMap S S' := by
  ext s
  change (alpha : S ⊗[R] R' →ₐ[R'] S') (algebraMap S (S ⊗[R] R') s) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    alpha_tmul, map_one, mul_one]

lemma includeLeft_compat :
    (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] R').comp (algebraMap R S) =
      (algebraMap R' (S ⊗[R] R')).comp (algebraMap R R') := by
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply, algebraMap_right_apply]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem main
    (h : ∀ (T : Type u) [CommRing T] [Algebra R' T] (g : S →+* T),
      g.comp (algebraMap R S) = (algebraMap R' T).comp (algebraMap R R') →
        ∃! k : S' →ₐ[R'] T, k.toRingHom.comp (algebraMap S S') = g) :
    Algebra.IsPushout R S R' S' := by
  classical

  obtain ⟨β, hβ, -⟩ := h (S ⊗[R] R') Algebra.TensorProduct.includeLeftRingHom includeLeft_compat

  have hcompat : (algebraMap S S').comp (algebraMap R S) =
      (algebraMap R' S').comp (algebraMap R R') := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have hαβ : (alpha : S ⊗[R] R' →ₐ[R'] S').comp β = AlgHom.id R' S' := by
    refine (h S' (algebraMap S S') hcompat).unique ?_ ?_
    · change ((alpha : S ⊗[R] R' →ₐ[R'] S').toRingHom.comp β.toRingHom).comp (algebraMap S S') = _
      rw [RingHom.comp_assoc, hβ]
      ext s
      change (alpha : S ⊗[R] R' →ₐ[R'] S') (s ⊗ₜ 1) = _
      rw [alpha_tmul, map_one, mul_one]
    · rfl

  have hβα : ∀ x : S ⊗[R] R', β ((alpha : S ⊗[R] R' →ₐ[R'] S') x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul s r =>
      rw [alpha_tmul, map_mul, AlgHom.commutes, algebraMap_right_apply]
      have hs : β (algebraMap S S' s) = s ⊗ₜ 1 := by
        have := congrArg (fun φ : S →+* S ⊗[R] R' => φ s) hβ
        simpa using this
      rw [hs, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let e : (S ⊗[R] R') ≃ₐ[R'] S' :=
    AlgEquiv.ofAlgHom (alpha : S ⊗[R] R' →ₐ[R'] S') β hαβ (by ext x; exact hβα x)
  have he : e.toRingHom.comp (algebraMap S (S ⊗[R] R')) = algebraMap S S' :=
    alpha_comp_algebraMap
  have : Algebra.IsPushout R R' S S' :=
    Algebra.IsPushout.of_equiv (h := TensorProduct.isPushout') e he
  exact this.symm

end IsPushoutOfUnivBody

theorem solution
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    (h : ∀ (T : Type u) [CommRing T] [Algebra R' T] (g : S →+* T),
      g.comp (algebraMap R S) = (algebraMap R' T).comp (algebraMap R R') →
        ∃! k : S' →ₐ[R'] T, k.toRingHom.comp (algebraMap S S') = g) :
    Algebra.IsPushout R S R' S' :=
  IsPushoutOfUnivBody.main h

end S_Algebra_isPushout_of_forall_existsUnique_algHom_comp_eq
end P2MW
export P2MW.S_Algebra_isPushout_of_forall_existsUnique_algHom_comp_eq (solution)
