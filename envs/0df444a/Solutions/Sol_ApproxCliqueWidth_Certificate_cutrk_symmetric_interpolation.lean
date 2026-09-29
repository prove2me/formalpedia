-- Prove2me | solution 1 for ApproxCliqueWidth.Certificate.cutrk_symmetric_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:28:24.931642+00:00
-- url     : https://prove2.me/submissions/409ed6c5-6c2d-4081-8f23-f19c7ec8c868

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation
import Definitions.Def_ApproxCliqueWidth_Certificate_CutRank

namespace ApproxCliqueWidth.Certificate

section aux_csi

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Field K]

/-- The subspace of vectors supported on `Y` whose image under `M` vanishes on `X`. -/
def aux_csi_K (M : Matrix V V K) (X Y : Finset V) : Submodule K (V → K) where
  carrier := {v | (∀ j, j ∉ Y → v j = 0) ∧ ∀ x ∈ X, M.mulVec v x = 0}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun j hj => ?_, fun x hx => ?_⟩
    · simp [ha.1 j hj, hb.1 j hj]
    · simp [Matrix.mulVec_add, ha.2 x hx, hb.2 x hx]
  zero_mem' := by
    refine ⟨fun j _ => rfl, fun x _ => ?_⟩
    simp
  smul_mem' := by
    intro c a ha
    refine ⟨fun j hj => ?_, fun x hx => ?_⟩
    · simp [ha.1 j hj]
    · simp [Matrix.mulVec_smul, ha.2 x hx]

omit [DecidableEq V] in
theorem aux_csi_sum (M : Matrix V V K) (Y : Finset V) (v : V → K)
    (hv : ∀ j, j ∉ Y → v j = 0) (x : V) :
    M.mulVec v x = ∑ y : Y, M x y * v y := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_coe_sort Y (fun j => M x j * v j)]
  symm
  apply Finset.sum_subset (Finset.subset_univ Y)
  intro j _ hj
  simp [hv j hj]

theorem aux_csi_rank_add (M : Matrix V V K) (X Y : Finset V) :
    (M.submatrix (fun x : X => (x : V)) (fun y : Y => (y : V))).rank +
      Module.finrank K (aux_csi_K M X Y) = Y.card := by
  set A := M.submatrix (fun x : X => (x : V)) (fun y : Y => (y : V)) with hA
  have e : LinearMap.ker A.mulVecLin ≃ₗ[K] aux_csi_K M X Y :=
    { toFun := fun w => ⟨fun j => if h : j ∈ Y then (w : Y → K) ⟨j, h⟩ else 0, by
        refine ⟨fun j hj => by simp [hj], fun x hx => ?_⟩
        rw [aux_csi_sum M Y _ (fun j hj => by simp [hj])]
        have hw := w.2
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
        have := congrFun hw ⟨x, hx⟩
        simpa [Matrix.mulVec, dotProduct, hA] using this⟩
      invFun := fun v => ⟨fun y => (v : V → K) y, by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        funext x
        have h1 := v.2.2 x x.2
        rw [aux_csi_sum M Y _ v.2.1] at h1
        simpa [Matrix.mulVec, dotProduct, hA] using h1⟩
      map_add' := by
        intro a b
        ext j
        by_cases h : j ∈ Y <;> simp [h]
      map_smul' := by
        intro c a
        ext j
        by_cases h : j ∈ Y <;> simp [h]
      left_inv := by
        intro w
        ext y
        simp
      right_inv := by
        intro v
        ext j
        by_cases h : j ∈ Y
        · simp [h]
        · simp [h, v.2.1 j h] }
  rw [← e.finrank_eq, Matrix.rank, LinearMap.finrank_range_add_finrank_ker,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

theorem aux_csi_submod (M : Matrix V V K) (A B C D : Finset V) :
    (M.submatrix (fun x : ↥(A ∩ C) => (x : V)) (fun y : ↥(B ∪ D) => (y : V))).rank +
      (M.submatrix (fun x : ↥(A ∪ C) => (x : V)) (fun y : ↥(B ∩ D) => (y : V))).rank ≤
    (M.submatrix (fun x : A => (x : V)) (fun y : B => (y : V))).rank +
      (M.submatrix (fun x : C => (x : V)) (fun y : D => (y : V))).rank := by
  have h1 := aux_csi_rank_add M (A ∩ C) (B ∪ D)
  have h2 := aux_csi_rank_add M (A ∪ C) (B ∩ D)
  have h3 := aux_csi_rank_add M A B
  have h4 := aux_csi_rank_add M C D
  have hc := Finset.card_union_add_card_inter B D
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (aux_csi_K M A B) (aux_csi_K M C D)
  have hsup : aux_csi_K M A B ⊔ aux_csi_K M C D ≤ aux_csi_K M (A ∩ C) (B ∪ D) := by
    apply sup_le
    · intro v hv
      refine ⟨fun j hj => hv.1 j (fun h => hj (Finset.mem_union_left _ h)),
        fun x hx => hv.2 x (Finset.mem_inter.1 hx).1⟩
    · intro v hv
      refine ⟨fun j hj => hv.1 j (fun h => hj (Finset.mem_union_right _ h)),
        fun x hx => hv.2 x (Finset.mem_inter.1 hx).2⟩
  have hinf : aux_csi_K M A B ⊓ aux_csi_K M C D ≤ aux_csi_K M (A ∪ C) (B ∩ D) := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    refine ⟨fun j hj => ?_, fun x hx => ?_⟩
    · by_cases hb : j ∈ B
      · have hd : j ∉ D := fun hd => hj (Finset.mem_inter.2 ⟨hb, hd⟩)
        exact hv2.1 j hd
      · exact hv1.1 j hb
    · rcases Finset.mem_union.1 hx with h | h
      · exact hv1.2 x h
      · exact hv2.2 x h
  have m1 := Submodule.finrank_mono hsup
  have m2 := Submodule.finrank_mono hinf
  omega

end aux_csi

end ApproxCliqueWidth.Certificate

open ApproxCliqueWidth.Certificate

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsSymmetric (cutrk G) ∧ IsSubmodular (cutrk G) ∧
      (∀ X : Finset V, cutrk G ∅ ≤ cutrk G X) ∧ IsInterpolation (cutrk G) (cutrkStar G) := by
  have hsub : ∀ A B C D : Finset V,
      cutrkStar G (A ∩ C) (B ∪ D) + cutrkStar G (A ∪ C) (B ∩ D) ≤
        cutrkStar G A B + cutrkStar G C D := by
    intro A B C D
    unfold cutrkStar
    exact_mod_cast aux_csi_submod (G.adjMatrix (ZMod 2)) A B C D
  have hempty : ∀ Y : Finset V, cutrkStar G ∅ Y = 0 := by
    intro Y
    unfold cutrkStar
    have := Matrix.rank_le_card_height ((G.adjMatrix (ZMod 2)).submatrix
      (fun x : (∅ : Finset V) => (x : V)) (fun y : Y => (y : V)))
    have h0 : ((G.adjMatrix (ZMod 2)).submatrix
      (fun x : (∅ : Finset V) => (x : V)) (fun y : Y => (y : V))).rank = 0 := by
      simpa using this
    simp [h0]
  have hzero : cutrk G ∅ = 0 := hempty _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X
    unfold cutrk cutrkStar
    rw [compl_compl, ← Matrix.rank_transpose, Matrix.transpose_submatrix,
      SimpleGraph.transpose_adjMatrix]
  · intro X Y
    unfold cutrk
    rw [Finset.compl_inter, Finset.compl_union]
    exact hsub X Xᶜ Y Yᶜ
  · intro X
    rw [hzero]
    unfold cutrk cutrkStar
    positivity
  · refine ⟨fun X => rfl, ?_, fun A B C D _ _ => hsub A B C D, ?_⟩
    · intro A B C D _ hAC hBD
      unfold cutrkStar
      have := Matrix.rank_submatrix_le
        ((G.adjMatrix (ZMod 2)).submatrix (fun x : C => (x : V)) (fun y : D => (y : V)))
        (fun a : A => (⟨a.1, hAC a.2⟩ : C)) (fun b : B => (⟨b.1, hBD b.2⟩ : D))
      exact_mod_cast this
    · rw [hzero]
      exact hempty _
