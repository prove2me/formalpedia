-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenBigCell
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenBigCell
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T17:38:28.509188+00:00
-- url     : https://prove2.me/theorems/74a88eb9-674b-4641-afff-4db2be5629a9
-- title:
--   Is Open Big Cell
-- statement:
--   Definitions and structural lemmas for Is Open Big Cell, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenBigCell.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
namespace GlobalTheory.FlagPts
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
def cellMat (b g : Frames k V) (i : ι) (m : ℕ) (hm : m ≤ finrank k (V i)) : Matrix (Fin m) (Fin m) k :=
  fun c a => (b i).repr (g i (Fin.castLE hm a)) (Fin.castLE hm c)
theorem disjoint_step_iff_det_ne_zero (b g : Frames k V) (i : ι) (m : ℕ) (hm : m ≤ finrank k (V i)) :
    Disjoint (g.flags.step i m) (Submodule.span k (b i '' {a | m ≤ (a : ℕ)})) ↔
      (cellMat b g i m hm).det ≠ 0 := by
  have hinj : Function.Injective (Fin.castLE hm) := Fin.castLE_injective hm
  have hrepr (x : Fin m → k) (c : Fin (finrank k (V i))) :
      (b i).repr (∑ a, x a • g i (Fin.castLE hm a)) c =
        ∑ a, (b i).repr (g i (Fin.castLE hm a)) c * x a := by
    simp [map_sum, Finsupp.finset_sum_apply, mul_comm]
  constructor
  · intro hd h0
    obtain ⟨x, hx, hMx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : (∑ a, x a • g i (Fin.castLE hm a)) ∈ g.flags.step i m :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
        (step_flags_le.1 le_rfl _ (by simp))
    have h2 : (∑ a, x a • g i (Fin.castLE hm a)) ∈
        Submodule.span k (b i '' {a | m ≤ (a : ℕ)}) := by
      rw [Basis.mem_span_image]
      intro c hc
      by_contra hlt
      have hlt' : (c : ℕ) < m := not_le.1 hlt
      refine (Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hc)) ?_
      rw [hrepr]
      exact congrFun hMx ⟨c, hlt'⟩
    have h3 := Submodule.disjoint_def.1 hd _ h1 h2
    exact hx (funext (Fintype.linearIndependent_iff.1
      ((g i).linearIndependent.comp _ hinj) x h3))
  · intro hd
    rw [Submodule.disjoint_def]
    intro v h1 h2
    have h1' := mem_step_flags.1 h1
    have hv : v = ∑ a, (g i).repr v (Fin.castLE hm a) • g i (Fin.castLE hm a) := by
      conv_lhs => rw [← (g i).sum_repr v]
      symm
      refine Fintype.sum_of_injective _ hinj _ _ (fun a ha => ?_) fun a => rfl
      have : m ≤ (a : ℕ) := by
        by_contra hlt
        exact ha ⟨⟨a, not_le.1 hlt⟩, Fin.ext rfl⟩
      rw [h1' a this, zero_smul]
    have hMx : (cellMat b g i m hm).mulVec (fun a => (g i).repr v (Fin.castLE hm a)) = 0 := by
      funext c
      have h0 : (b i).repr v (Fin.castLE hm c) = 0 := by
        by_contra hne
        have := ((b i).mem_span_image.1 h2) (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
        have hc := c.2
        simp only [Set.mem_setOf_eq, Fin.val_castLE] at this
        omega
      rw [hv, hrepr] at h0
      simpa [Matrix.mulVec, dotProduct, cellMat] using h0
    have hx := Matrix.eq_zero_of_mulVec_eq_zero hd hMx
    rw [hv]
    exact Finset.sum_eq_zero fun a _ => by rw [congrFun hx a, Pi.zero_apply, zero_smul]
theorem det_cellMat_mem_regFns (b : Frames k V) (i : ι) (m : ℕ) (hm : m ≤ finrank k (V i)) :
    (fun g : Frames k V => (cellMat b g i m hm).det) ∈ regFns k V := by
  have h : (fun g : Frames k V => (cellMat b g i m hm).det) =
      ∑ σ : Equiv.Perm (Fin m), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : k) •
        ∏ c, fun g : Frames k V => (b i).coord (Fin.castLE hm (σ c)) (g i (Fin.castLE hm c)) := by
    funext g
    simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply, cellMat]
  rw [h]
  exact Subalgebra.sum_mem _ fun σ _ => Subalgebra.smul_mem _ (Subalgebra.prod_mem _ fun c _ =>
    Algebra.subset_adjoin (.inl ⟨i, _, _, rfl⟩)) _
theorem isOpen_bigCell (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
    (b : Frames k V) : IsOpen (bigCell b) := by
  refine isOpen_coinduced.2 ?_
  have h : Frames.flags ⁻¹' bigCell b = ⋂ i, ⋂ m : Fin (finrank k (V i) + 1),
      {g : Frames k V | (cellMat b g i m (Nat.lt_succ_iff.1 m.2)).det ≠ 0} := by
    ext g
    simp only [Set.mem_preimage, bigCell, Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun hg i m => (disjoint_step_iff_det_ne_zero b g i m _).1 (hg i m), fun hg i m => ?_⟩
    by_cases hm : m ≤ finrank k (V i)
    · exact (disjoint_step_iff_det_ne_zero b g i m hm).2 (hg i ⟨m, Nat.lt_succ_iff.2 hm⟩)
    · have he : {a : Fin (finrank k (V i)) | m ≤ (a : ℕ)} = ∅ :=
        Set.eq_empty_of_forall_notMem fun a ha => hm (le_trans ha a.2.le)
      rw [he, Set.image_empty, Submodule.span_empty]
      exact disjoint_bot_right
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun m =>
    isOpen_generateFrom_of_mem ⟨_, det_cellMat_mem_regFns b i m _, rfl⟩
example : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), IsOpen (bigCell b) :=
  fun k _ ι _ V _ _ _ b => isOpen_bigCell k ι V b
end GlobalTheory.FlagPts


