-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.exists_isCompact_forall_archWord_eq_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b26a00a5-6ba1-5862-a6f5-f5f57a839b5e

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_archWord_eq_zero_of_not_mem

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem solution
    (L : Type) [Field L] [NumberField L]
    (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L) (hA : Continuous A) (hAs : Continuous A.symm)
    (φ : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφ : HasCompactSupport φ)
    (Ct : Set (InfiniteAdeleRing L)ˣ) (hCt : IsCompact Ct)
    (Kk : Set (GL (Fin 2) (InfiniteAdeleRing L))) (hKk : IsCompact Kk) :
    ∃ Cζ : Set (InfiniteAdeleRing L)ˣ, IsCompact Cζ ∧
      ∀ (y : InfiniteAdeleRing L) (t : (InfiniteAdeleRing L)ˣ) (k : GL (Fin 2) (InfiniteAdeleRing L))
        (ζ : (InfiniteAdeleRing L)ˣ), t ∈ Ct → k ∈ Kk → ζ ∉ Cζ →
        φ (k⁻¹ * unipotentGL2 (y * ((t⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
            diagOne (Units.map A.toRingHom.toMonoidHom t * t⁻¹) *
            Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom ζ) *
            Matrix.GeneralLinearGroup.map A.toRingHom k) = 0 := by
  classical
  letI : Mul (Set (GL (Fin 2) (InfiniteAdeleRing L))) := Set.mul
  letI : Inv (Set (GL (Fin 2) (InfiniteAdeleRing L))) := Set.inv

  have hAm : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) A.toRingHom) := by
    refine Continuous.units_map _ ?_
    exact Continuous.matrix_map continuous_id hA
  have hAsu : Continuous (Units.map A.symm.toRingHom.toMonoidHom :
      (InfiniteAdeleRing L)ˣ → (InfiniteAdeleRing L)ˣ) := Continuous.units_map _ hAs

  have hC1c : IsCompact (Kk * tsupport φ * (Matrix.GeneralLinearGroup.map (n := Fin 2) A.toRingHom '' Kk)⁻¹) :=
    (hKk.mul hφ).mul (hKk.image hAm).inv

  let π : GL (Fin 2) (InfiniteAdeleRing L) → InfiniteAdeleRing L × (InfiniteAdeleRing L)ᵐᵒᵖ := fun g =>
    ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 1 1,
      MulOpposite.op (((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 1 1))
  have hπ : Continuous π := by
    refine Continuous.prodMk ?_ (MulOpposite.continuous_op.comp ?_)
    · exact (Units.continuous_val.matrix_elem 1 1)
    · exact (Units.continuous_coe_inv.matrix_elem 1 1)
  have hCζ'c : IsCompact (Units.embedProduct (InfiniteAdeleRing L) ⁻¹'
      (π '' (Kk * tsupport φ * (Matrix.GeneralLinearGroup.map (n := Fin 2) A.toRingHom '' Kk)⁻¹))) :=
    (Units.isClosedEmbedding_embedProduct).isCompact_preimage (hC1c.image hπ)
  refine ⟨Units.map A.symm.toRingHom.toMonoidHom '' (Units.embedProduct (InfiniteAdeleRing L) ⁻¹'
      (π '' (Kk * tsupport φ * (Matrix.GeneralLinearGroup.map (n := Fin 2) A.toRingHom '' Kk)⁻¹))),
    hCζ'c.image hAsu, ?_⟩
  intro y t k ζ ht hk hζ
  by_contra hne
  apply hζ

  have hW := subset_tsupport φ (Function.mem_support.mpr hne)
  set n₁ := unipotentGL2 (y * ((t⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) with hn₁
  set d₁ := diagOne (Units.map A.toRingHom.toMonoidHom t * t⁻¹) with hd₁
  set s₁ := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom ζ) with hs₁
  set kA := Matrix.GeneralLinearGroup.map A.toRingHom k with hkA
  have hM : k * (k⁻¹ * n₁ * d₁ * s₁ * kA) * kA⁻¹ = n₁ * d₁ * s₁ := by group
  have hMmem : n₁ * d₁ * s₁ ∈
      Kk * tsupport φ * (Matrix.GeneralLinearGroup.map (n := Fin 2) A.toRingHom '' Kk)⁻¹ := by
    rw [← hM]
    refine Set.mul_mem_mul (Set.mul_mem_mul hk hW) ?_
    rw [Set.mem_inv, inv_inv]
    exact ⟨k, hk, hkA.symm⟩
  have hninv : n₁⁻¹ = unipotentGL2 (-(y * ((t⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L))) := by
    rw [hn₁]
    apply inv_eq_of_mul_eq_one_right
    rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero]

  have h11 : ((n₁ * d₁ * s₁ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 1 1 =
      ((Units.map A.toRingHom.toMonoidHom ζ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) := by
    simp [hn₁, hd₁, hs₁, Matrix.mul_apply, diagOne, Matrix.GeneralLinearGroup.scalar,
      Matrix.diagonal, Matrix.vecHead, Matrix.vecTail]
  have h11' : (((n₁ * d₁ * s₁)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 1 1 =
      (((Units.map A.toRingHom.toMonoidHom ζ)⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) := by
    rw [mul_inv_rev, mul_inv_rev, hninv, hd₁, hs₁, ← map_inv, ← map_inv]
    simp [Matrix.mul_apply, diagOne, Matrix.GeneralLinearGroup.scalar,
      Matrix.diagonal, Matrix.vecHead, Matrix.vecTail]
  have hmem' : Units.map A.toRingHom.toMonoidHom ζ ∈ Units.embedProduct (InfiniteAdeleRing L) ⁻¹'
      (π '' (Kk * tsupport φ * (Matrix.GeneralLinearGroup.map (n := Fin 2) A.toRingHom '' Kk)⁻¹)) := by
    refine ⟨n₁ * d₁ * s₁, hMmem, ?_⟩
    simp only [π, Units.embedProduct_apply, h11, h11']
  refine ⟨_, hmem', ?_⟩
  ext
  simp

end S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_archWord_eq_zero_of_not_mem
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_archWord_eq_zero_of_not_mem (solution)
