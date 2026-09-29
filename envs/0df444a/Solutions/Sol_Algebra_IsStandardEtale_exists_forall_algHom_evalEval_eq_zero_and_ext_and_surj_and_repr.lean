-- Prove2me | solution 1 for Algebra.IsStandardEtale.exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/84091a25-ce65-5990-9443-28a9bfec25af

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsStandardEtale_exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr

set_option autoImplicit false

open Polynomial
open scoped Polynomial.Bivariate

p2m_open "Polynomial Polynomial.Bivariate.Polynomial"
p2m_open_scoped "Polynomial.Bivariate Polynomial.Bivariate.Polynomial.Bivariate"

theorem solution
    (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A]
    [Algebra.IsStandardEtale k[X] A] :
    ∃ (x : A) (F G : k[X][Y]),
      (∀ τ : A →ₐ[k] k,
        Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) F = 0 ∧
        Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) G ≠ 0 ∧
        Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) (Polynomial.derivative F) ≠ 0) ∧
      (∀ τ τ' : A →ₐ[k] k, τ (algebraMap k[X] A Polynomial.X) = τ' (algebraMap k[X] A Polynomial.X) → τ x = τ' x → τ = τ') ∧
      (∀ z w : k, Polynomial.evalEval z w F = 0 → Polynomial.evalEval z w G ≠ 0 →
        ∃ τ : A →ₐ[k] k, τ (algebraMap k[X] A Polynomial.X) = z ∧ τ x = w) ∧
      (∀ s : A, ∃ (h : k[X][Y]) (n : ℕ), ∀ τ : A →ₐ[k] k,
        τ s * (Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) G) ^ n =
          Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) h) := by
  classical
  obtain ⟨P⟩ := (Algebra.IsStandardEtale.nonempty_standardEtalePresentation :
    Nonempty (StandardEtalePresentation k[X] A))

  have hring : ∀ τ : A →ₐ[k] k, (τ : A →+* k).comp (algebraMap k[X] A) =
      evalRingHom (τ (algebraMap k[X] A Polynomial.X)) := by
    intro τ
    apply Polynomial.ringHom_ext
    · intro a
      show τ (algebraMap k[X] A (C a)) = eval _ (C a)
      rw [eval_C, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    · show τ (algebraMap k[X] A Polynomial.X) = eval _ Polynomial.X
      rw [eval_X]
  have hev : ∀ (τ : A →ₐ[k] k) (q : k[X][Y]),
      τ (aeval P.x q) = q.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ P.x) := by
    intro τ q
    rw [aeval_def, show τ (eval₂ (algebraMap k[X] A) P.x q) = (τ : A →+* k) (eval₂ (algebraMap k[X] A) P.x q) from rfl,
      hom_eval₂, hring τ, eval₂_evalRingHom]
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
    letI instk : Algebra k[X] k := (evalRingHom (τ (algebraMap k[X] A Polynomial.X))).toAlgebra
    let τR : A →ₐ[k[X]] k :=
      { toRingHom := (τ : A →+* k)
        commutes' := fun p => by
          show ((τ : A →+* k).comp (algebraMap k[X] A)) p = _
          rw [hring τ]; rfl }
    let τR' : A →ₐ[k[X]] k :=
      { toRingHom := (τ' : A →+* k)
        commutes' := fun p => by
          show ((τ' : A →+* k).comp (algebraMap k[X] A)) p = _
          rw [hring τ', ← hX]; rfl }
    have hcomp : τR.comp (P.equivRing.symm : P.Ring →ₐ[k[X]] A) = τR'.comp (P.equivRing.symm : P.Ring →ₐ[k[X]] A) := by
      apply StandardEtalePair.hom_ext
      show τ (P.equivRing.symm P.X) = τ' (P.equivRing.symm P.X)
      rw [P.equivRing_symm_X]; exact hx
    apply AlgHom.ext
    intro s
    have := congrArg (fun φ : P.Ring →ₐ[k[X]] k => φ (P.equivRing s)) hcomp
    simp at this
    exact this
  ·
    intro z w hF hG
    letI instk : Algebra k[X] k := (evalRingHom z).toAlgebra
    have haev : ∀ q : k[X][Y], aeval (R := k[X]) w q = q.evalEval z w := by
      intro q
      rw [aeval_def, show algebraMap k[X] k = evalRingHom z from rfl, eval₂_evalRingHom]
    have hmap : P.HasMap (S := k) w := ⟨by rw [haev]; exact hF, isUnit_iff_ne_zero.2 (by rw [haev]; exact hG)⟩
    let ψ : P.Ring →ₐ[k[X]] k := P.lift w hmap
    let θ : A →ₐ[k[X]] k := ψ.comp (P.equivRing : A ≃ₐ[k[X]] P.Ring).toAlgHom
    let τ : A →ₐ[k] k :=
      { toRingHom := (θ : A →+* k)
        commutes' := fun c => by
          show θ (algebraMap k A c) = c
          rw [IsScalarTower.algebraMap_apply k k[X] A, AlgHom.commutes]
          show eval z (algebraMap k k[X] c) = c
          rw [Polynomial.algebraMap_eq, eval_C] }
    refine ⟨τ, ?_, ?_⟩
    · show θ (algebraMap k[X] A Polynomial.X) = z
      rw [AlgHom.commutes]
      show eval z Polynomial.X = z
      rw [eval_X]
    · show ψ (P.equivRing P.x) = w
      rw [P.equivRing_x]
      exact P.lift_X w hmap
  ·
    intro s
    obtain ⟨p, n, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
    refine ⟨p, n, fun τ => ?_⟩
    have := congrArg τ hp
    rw [map_mul, map_pow, hev, hev] at this
    exact this

end S_Algebra_IsStandardEtale_exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr
end P2MW
export P2MW.S_Algebra_IsStandardEtale_exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr (solution)
