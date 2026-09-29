-- Prove2me | solution 1 for Algebra.IsStandardEtale.exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0198006a-fe08-55bc-be3f-7dbba129f2b8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial

set_option autoImplicit false

open Polynomial

theorem solution
    (k : Type) [Field k] {n : ℕ} (A : Type) [CommRing A] [Algebra k A] [Algebra (MvPolynomial (Fin n) k) A]
    [IsScalarTower k (MvPolynomial (Fin n) k) A] [Algebra.IsStandardEtale (MvPolynomial (Fin n) k) A] :
    ∃ (x : A) (F G : Polynomial (MvPolynomial (Fin n) k)),
      (∀ τ : A →ₐ[k] k,
        (F.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) = 0 ∧
        (G.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) ≠ 0 ∧
        ((Polynomial.derivative F).map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) ≠ 0) ∧
      (∀ τ τ' : A →ₐ[k] k,
        (∀ i : Fin n, τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)) =
          τ' (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i))) → τ x = τ' x → τ = τ') ∧
      (∀ (z : Fin n → k) (w : k), (F.map (MvPolynomial.eval z)).eval w = 0 → (G.map (MvPolynomial.eval z)).eval w ≠ 0 →
        ∃ τ : A →ₐ[k] k, (∀ i : Fin n, τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)) = z i) ∧ τ x = w) ∧
      (∀ s : A, ∃ (h : Polynomial (MvPolynomial (Fin n) k)) (N : ℕ), ∀ τ : A →ₐ[k] k,
        τ s * ((G.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x)) ^ N =
          (h.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x)) := by
  classical
  set R := MvPolynomial (Fin n) k with hR
  obtain ⟨P⟩ := (Algebra.IsStandardEtale.nonempty_standardEtalePresentation :
    Nonempty (StandardEtalePresentation R A))

  have hring : ∀ τ : A →ₐ[k] k, (τ : A →+* k).comp (algebraMap R A) =
      MvPolynomial.eval (fun i : Fin n => τ (algebraMap R A (MvPolynomial.X i))) := by
    intro τ
    apply MvPolynomial.ringHom_ext
    · intro a
      show τ (algebraMap R A (MvPolynomial.C a)) = MvPolynomial.eval _ (MvPolynomial.C a)
      rw [MvPolynomial.eval_C, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgHom.commutes,
        Algebra.algebraMap_self, RingHom.id_apply]
    · intro i
      show τ (algebraMap R A (MvPolynomial.X i)) = MvPolynomial.eval _ (MvPolynomial.X i)
      rw [MvPolynomial.eval_X]
  have hev : ∀ (τ : A →ₐ[k] k) (q : Polynomial R),
      τ (aeval P.x q) = (q.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap R A (MvPolynomial.X i)))).eval (τ P.x) := by
    intro τ q
    rw [aeval_def, show τ (eval₂ (algebraMap R A) P.x q) = (τ : A →+* k) (eval₂ (algebraMap R A) P.x q) from rfl,
      hom_eval₂, hring τ, eval₂_eq_eval_map]
    rfl
  obtain ⟨hf0, hgU⟩ := P.hasMap
  refine ⟨P.x, P.f, P.g, ?_, ?_, ?_, ?_⟩
  ·
    intro τ
    refine ⟨?_, ?_, ?_⟩
    · rw [← hev, hf0, map_zero]
    · rw [← hev]; exact (hgU.map τ).ne_zero
    · rw [← hev]; exact (P.hasMap.isUnit_derivative_f.map τ).ne_zero
  ·
    intro τ τ' hX hx
    letI instk : Algebra R k := (MvPolynomial.eval fun i : Fin n => τ (algebraMap R A (MvPolynomial.X i))).toAlgebra
    have hv : (fun i : Fin n => τ' (algebraMap R A (MvPolynomial.X i)))
        = fun i : Fin n => τ (algebraMap R A (MvPolynomial.X i)) := funext fun i => (hX i).symm
    let τR : A →ₐ[R] k :=
      { toRingHom := (τ : A →+* k)
        commutes' := fun p => by
          show ((τ : A →+* k).comp (algebraMap R A)) p = _
          rw [hring τ]; rfl }
    let τR' : A →ₐ[R] k :=
      { toRingHom := (τ' : A →+* k)
        commutes' := fun p => by
          show ((τ' : A →+* k).comp (algebraMap R A)) p = _
          rw [hring τ', hv]; rfl }
    have hcomp : τR.comp (P.equivRing.symm : P.Ring →ₐ[R] A) = τR'.comp (P.equivRing.symm : P.Ring →ₐ[R] A) := by
      apply StandardEtalePair.hom_ext
      show τ (P.equivRing.symm P.X) = τ' (P.equivRing.symm P.X)
      rw [P.equivRing_symm_X]; exact hx
    apply AlgHom.ext
    intro s
    have := congrArg (fun φ : P.Ring →ₐ[R] k => φ (P.equivRing s)) hcomp
    simp at this
    exact this
  ·
    intro z w hF hG
    letI instk : Algebra R k := (MvPolynomial.eval z).toAlgebra
    have haev : ∀ q : Polynomial R, aeval (R := R) w q = (q.map (MvPolynomial.eval z)).eval w := by
      intro q
      rw [aeval_def, show algebraMap R k = MvPolynomial.eval z from rfl, eval₂_eq_eval_map]
    have hmap : P.HasMap (S := k) w := ⟨by rw [haev]; exact hF, isUnit_iff_ne_zero.2 (by rw [haev]; exact hG)⟩
    let ψ : P.Ring →ₐ[R] k := P.lift w hmap
    let θ : A →ₐ[R] k := ψ.comp (P.equivRing : A ≃ₐ[R] P.Ring).toAlgHom
    let τ : A →ₐ[k] k :=
      { toRingHom := (θ : A →+* k)
        commutes' := fun c => by
          show θ (algebraMap k A c) = c
          rw [IsScalarTower.algebraMap_apply k R A, AlgHom.commutes]
          show MvPolynomial.eval z (algebraMap k R c) = c
          rw [MvPolynomial.algebraMap_eq, MvPolynomial.eval_C] }
    refine ⟨τ, ?_, ?_⟩
    · intro i
      show θ (algebraMap R A (MvPolynomial.X i)) = z i
      rw [AlgHom.commutes]
      show MvPolynomial.eval z (MvPolynomial.X i) = z i
      rw [MvPolynomial.eval_X]
    · show ψ (P.equivRing P.x) = w
      rw [P.equivRing_x]
      exact P.lift_X w hmap
  ·
    intro s
    obtain ⟨p, N, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
    refine ⟨p, N, fun τ => ?_⟩
    have := congrArg τ hp
    rw [map_mul, map_pow, hev, hev] at this
    exact this

end S_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial
end P2MW
export P2MW.S_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial (solution)
