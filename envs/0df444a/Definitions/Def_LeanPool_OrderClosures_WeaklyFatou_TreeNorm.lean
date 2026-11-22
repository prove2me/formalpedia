-- Prove2me | Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
-- name    : LeanPool_OrderClosures_WeaklyFatou_TreeNorm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:00:16.239233+00:00
-- url     : https://prove2.me/theorems/85d2b4a1-d070-4579-896f-08b7291d9cc5
-- title:
--   Tree Norm
-- statement:
--   Definitions and structural lemmas for Tree Norm, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_normalize_eval
public import Theorems.Thm_OrderClosures_treeFunction_apply_of_mem
public import Theorems.Thm_OrderClosures_treeFunction_apply_of_notMem
public import Theorems.Thm_OrderConvergesTo_inf
public import Theorems.Thm_OrderConvergesTo_le
public import Theorems.Thm_OrderConvergesTo_nonneg
public import Theorems.Thm_OrderConvergesTo_smul
public import Theorems.Thm_OrderConvergesTo_sup
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_VectorSublattice_subset_generated
public import Theorems.Thm_coe_toCompletionVecLatHom
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_inf
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.normalize_eval
attribute [local simp] Positive.extension_apply
attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_bot
attribute [local simp] VectorSublattice.mem_top
attribute [local simp] coe_toCompletionVecLatHom


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
abbrev TreeCoefficients (n : ℕ) := TreeNode n →₀ ℝ
noncomputable def treeBasis {n : ℕ} (t : TreeNode n) : TreeCoefficients n :=
  Finsupp.single t 1
noncomputable def treeRho (n : ℕ) (w : TreeCoefficients n) : ℝ :=
  w.sum fun t a ↦ (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |a|
noncomputable def treeOperator (n : ℕ) (w : TreeCoefficients n) :
    BoundedContinuousFunction (TreeProduct n) ℝ :=
  w.sum fun t a ↦ a • treeFunction n t
noncomputable def treeSeminorm (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ w : TreeCoefficients n,
    0 ≤ w ∧ |x| ≤ treeOperator n w ∧ treeRho n w = r}
theorem treeRho_nonneg (n : ℕ) (w : TreeCoefficients n) :
    0 ≤ treeRho n w := by
  classical
  exact Finsupp.sum_nonneg' fun t ↦
    mul_nonneg (zpow_nonneg (by norm_num) _) (abs_nonneg _)
theorem treeRho_smul (n : ℕ) (a : ℝ) (w : TreeCoefficients n) :
    treeRho n (a • w) = |a| * treeRho n w := by
  classical
  unfold treeRho
  rw [Finsupp.sum_of_support_subset (a • w) Finsupp.support_smul _ (by simp)]
  simp only [Finsupp.sum, Finsupp.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring
theorem treeRho_add_le (n : ℕ) (u v : TreeCoefficients n) :
    treeRho n (u + v) ≤ treeRho n u + treeRho n v := by
  classical
  rw [treeRho, treeRho, treeRho]
  rw [Finsupp.sum_of_support_subset (u + v) Finsupp.support_add _ (by simp)]
  rw [Finsupp.sum_of_support_subset u
    (show u.support ⊆ u.support ∪ v.support from Finset.subset_union_left) _ (by simp)]
  rw [Finsupp.sum_of_support_subset v
    (show v.support ⊆ u.support ∪ v.support from Finset.subset_union_right) _ (by simp)]
  simp only [Finsupp.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  simpa [mul_add] using
    (mul_le_mul_of_nonneg_left (abs_add_le (u t) (v t))
      (zpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
        (-(TreeNode.level t : ℤ))))
theorem treeOperator_zero (n : ℕ) :
    treeOperator n (0 : TreeCoefficients n) = 0 := by
  simp [treeOperator]
theorem treeOperator_add (n : ℕ) (u v : TreeCoefficients n) :
    treeOperator n (u + v) = treeOperator n u + treeOperator n v := by
  classical
  simp only [treeOperator]
  exact Finsupp.sum_add_index (by simp) (by simp [add_smul])
theorem treeOperator_smul (n : ℕ) (a : ℝ) (w : TreeCoefficients n) :
    treeOperator n (a • w) = a • treeOperator n w := by
  classical
  simp only [treeOperator]
  rw [Finsupp.sum_smul_index (by simp)]
  change (∑ t ∈ w.support, (a * w t) • treeFunction n t) =
    a • ∑ t ∈ w.support, w t • treeFunction n t
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp [smul_smul]
theorem treeOperator_nonneg (n : ℕ) (w : TreeCoefficients n) (hw : 0 ≤ w) :
    0 ≤ treeOperator n w := by
  classical
  change 0 ≤ w.sum fun t a ↦ a • treeFunction n t
  apply Finsupp.sum_nonneg'
  intro t α
  change 0 ≤ w t * treeFunction n t α
  exact mul_nonneg (hw t) (by
    by_cases h : α ∈ treeCylinder n t <;> simp [treeFunction,
      BoundedContinuousFunction.indicator, Set.indicator, h])
theorem treeOperator_single (n : ℕ) (t : TreeNode n) (a : ℝ) :
    treeOperator n (Finsupp.single t a) = a • treeFunction n t := by
  simp [treeOperator]
theorem treeFunction_root (n : ℕ) :
    treeFunction n (TreeNode.root n) = 1 := by
  ext α
  simp [treeFunction, BoundedContinuousFunction.indicator, treeCylinder,
    TreeNode.root, TreeNode.level]
theorem abs_le_norm_smul_root (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    |x| ≤ ‖x‖ • treeFunction n (TreeNode.root n) := by
  rw [treeFunction_root]
  intro α
  change |x α| ≤ ‖x‖ * 1
  simpa using x.norm_coe_le_norm α
theorem treeAdmissible_nonempty (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    {r : ℝ | ∃ w : TreeCoefficients n,
      0 ≤ w ∧ |x| ≤ treeOperator n w ∧ treeRho n w = r}.Nonempty := by
  let w : TreeCoefficients n := Finsupp.single (TreeNode.root n) ‖x‖
  refine ⟨treeRho n w, w, ?_, ?_, rfl⟩
  · exact Finsupp.single_nonneg.mpr (norm_nonneg x)
  · rw [treeOperator_single]
    exact abs_le_norm_smul_root n x
theorem treeAdmissible_bddBelow (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    BddBelow {r : ℝ | ∃ w : TreeCoefficients n,
      0 ≤ w ∧ |x| ≤ treeOperator n w ∧ treeRho n w = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨w, _, _, rfl⟩
  exact treeRho_nonneg n w
theorem treeSeminorm_nonneg (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    0 ≤ treeSeminorm n x := by
  apply le_csInf (treeAdmissible_nonempty n x)
  rintro r ⟨w, _, _, rfl⟩
  exact treeRho_nonneg n w
theorem treeSeminorm_le_of_majorant (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) (w : TreeCoefficients n)
    (hw : 0 ≤ w) (hxw : |x| ≤ treeOperator n w) :
    treeSeminorm n x ≤ treeRho n w := by
  exact csInf_le (treeAdmissible_bddBelow n x) ⟨w, hw, hxw, rfl⟩
theorem treeSeminorm_zero (n : ℕ) :
    treeSeminorm n (0 : BoundedContinuousFunction (TreeProduct n) ℝ) = 0 := by
  apply le_antisymm
  · simpa [treeRho] using
      (treeSeminorm_le_of_majorant n 0 0 (by simp)
        (by simp [treeOperator_zero]))
  · exact treeSeminorm_nonneg n 0
theorem exists_treeMajorant_lt (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : TreeCoefficients n, 0 ≤ w ∧ |x| ≤ treeOperator n w ∧
      treeRho n w < treeSeminorm n x + ε := by
  obtain ⟨r, ⟨w, hw, hxw, hwr⟩, hr⟩ :=
    exists_lt_of_csInf_lt (treeAdmissible_nonempty n x)
      (lt_add_of_pos_right (treeSeminorm n x) hε)
  exact ⟨w, hw, hxw, by simpa [hwr] using hr⟩
theorem treeSeminorm_smul_le (n : ℕ) (a : ℝ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    treeSeminorm n (a • x) ≤ |a| * treeSeminorm n x := by
  by_cases ha : a = 0
  · subst a
    simpa using (treeSeminorm_zero n).le
  apply le_of_forall_pos_le_add
  intro ε hε
  have habs : 0 < |a| := abs_pos.mpr ha
  obtain ⟨w, hw, hxw, hrho⟩ := exists_treeMajorant_lt n x (div_pos hε habs)
  have hmajor : |a • x| ≤ treeOperator n (|a| • w) := by
    rw [treeOperator_smul]
    intro α
    change |a * x α| ≤ |a| * treeOperator n w α
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hxw α) (abs_nonneg a)
  have hwscale : 0 ≤ |a| • w := by
    intro t
    change 0 ≤ |a| * w t
    exact mul_nonneg (abs_nonneg a) (hw t)
  calc
    treeSeminorm n (a • x) ≤ treeRho n (|a| • w) :=
      treeSeminorm_le_of_majorant n _ _ hwscale hmajor
    _ = |a| * treeRho n w := by rw [treeRho_smul, abs_of_nonneg (abs_nonneg a)]
    _ ≤ |a| * treeSeminorm n x + ε := by
      have := mul_lt_mul_of_pos_left hrho habs
      rw [mul_add, mul_div_cancel₀ _ habs.ne'] at this
      exact this.le
theorem treeFunction_norm_le_one (n : ℕ) (t : TreeNode n) :
    ‖treeFunction n t‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le zero_le_one]
  intro α
  by_cases h : α ∈ treeCylinder n t
  · rw [treeFunction_apply_of_mem n t h]
    norm_num
  · rw [treeFunction_apply_of_notMem n t h]
    norm_num
theorem treeOperator_norm_le_sum (n : ℕ) (w : TreeCoefficients n) :
    ‖treeOperator n w‖ ≤ ∑ t ∈ w.support, |w t| := by
  classical
  rw [treeOperator, Finsupp.sum]
  calc
    ‖∑ t ∈ w.support, w t • treeFunction n t‖ ≤
        ∑ t ∈ w.support, ‖w t • treeFunction n t‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ w.support, |w t| := by
      apply Finset.sum_le_sum
      intro t _
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg (w t), treeFunction_norm_le_one n t]
theorem treeRho_controls_sum (n : ℕ) (w : TreeCoefficients n) :
    (∑ t ∈ w.support, |w t|) ≤ (2 : ℝ) ^ n * treeRho n w := by
  classical
  rw [treeRho, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have hc : (1 : ℝ) ≤
      (2 : ℝ) ^ n * (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    apply one_le_zpow₀ (by norm_num)
    exact sub_nonneg.mpr (by exact_mod_cast t.2)
  nlinarith [abs_nonneg (w t)]
theorem norm_le_pow_mul_treeRho (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) (w : TreeCoefficients n)
    (hw : 0 ≤ w) (hxw : |x| ≤ treeOperator n w) :
    ‖x‖ ≤ (2 : ℝ) ^ n * treeRho n w := by
  calc
    ‖x‖ ≤ ‖treeOperator n w‖ := by
      apply norm_le_norm_of_abs_le_abs
      simpa [abs_of_nonneg (treeOperator_nonneg n w hw)] using hxw
    _ ≤ ∑ t ∈ w.support, |w t| := treeOperator_norm_le_sum n w
    _ ≤ (2 : ℝ) ^ n * treeRho n w := treeRho_controls_sum n w
noncomputable def treeLatticeSeminorm (n : ℕ) :
    LatticeSeminorm (BoundedContinuousFunction (TreeProduct n) ℝ) where
  toFun := treeSeminorm n
  map_zero' := by
    exact treeSeminorm_zero n
  add_le' := by
    intro x y
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨u, hu, hxu, hρu⟩ := exists_treeMajorant_lt n x (half_pos hε)
    obtain ⟨v, hv, hyv, hρv⟩ := exists_treeMajorant_lt n y (half_pos hε)
    have hmajor : |x + y| ≤ treeOperator n (u + v) := by
      rw [treeOperator_add]
      exact (abs_add_le x y).trans (add_le_add hxu hyv)
    calc
      treeSeminorm n (x + y) ≤ treeRho n (u + v) :=
        treeSeminorm_le_of_majorant n _ _ (add_nonneg hu hv) hmajor
      _ ≤ treeRho n u + treeRho n v := treeRho_add_le n u v
      _ ≤ treeSeminorm n x + treeSeminorm n y + ε := by linarith
  neg' := by
    intro x
    simp [treeSeminorm]
  smul' := by
    intro a x
    apply le_antisymm
    · exact treeSeminorm_smul_le n a x
    · by_cases ha : a = 0
      · subst a
        simp [treeSeminorm_zero]
      have hinv := treeSeminorm_smul_le n a⁻¹ (a • x)
      have habs : 0 < |a| := abs_pos.mpr ha
      calc
        |a| * treeSeminorm n x =
            |a| * treeSeminorm n (a⁻¹ • (a • x)) := by
              simp [smul_smul, ha]
        _ ≤ |a| * (|a⁻¹| * treeSeminorm n (a • x)) :=
          mul_le_mul_of_nonneg_left hinv habs.le
        _ = treeSeminorm n (a • x) := by
          rw [abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr ha), one_mul]
  monotone_abs' := by
    intro x y hxy
    apply le_csInf (treeAdmissible_nonempty n y)
    rintro r ⟨w, hw, hyw, rfl⟩
    exact treeSeminorm_le_of_majorant n x w hw (hxy.trans hyw)
theorem treeSeminorm_norm_comparison
    (n : ℕ) (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    treeSeminorm n x ≤ ‖x‖ ∧ ‖x‖ ≤ (2 : ℝ) ^ n * treeSeminorm n x := by
  constructor
  · let w : TreeCoefficients n := Finsupp.single (TreeNode.root n) ‖x‖
    have hw : 0 ≤ w := Finsupp.single_nonneg.mpr (norm_nonneg x)
    have hxw : |x| ≤ treeOperator n w := by
      rw [treeOperator_single]
      exact abs_le_norm_smul_root n x
    calc
      treeSeminorm n x ≤ treeRho n w := treeSeminorm_le_of_majorant n x w hw hxw
      _ = ‖x‖ := by simp [w, treeRho, TreeNode.root, TreeNode.level]
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
    obtain ⟨w, hw, hxw, hrho⟩ :=
      exists_treeMajorant_lt n x (div_pos hε hpow)
    have hnorm := norm_le_pow_mul_treeRho n x w hw hxw
    have hscaled := mul_lt_mul_of_pos_left hrho hpow
    rw [mul_add, mul_div_cancel₀ _ hpow.ne'] at hscaled
    exact hnorm.trans hscaled.le
noncomputable def treeSublattice (n : ℕ) :
    VectorSublattice (BoundedContinuousFunction (TreeProduct n) ℝ) :=
  (VectorSublattice.generated (Set.range (treeFunction n))).topologicalClosure
abbrev TreeComponent (n : ℕ) := ↥(treeSublattice n).toSubmodule
noncomputable instance treeComponentLattice (n : ℕ) : Lattice (TreeComponent n) where
  le := fun x y ↦ x.1 ≤ y.1
  le_refl := fun _ ↦ le_rfl
  le_trans := fun _ _ _ hxy hyz ↦ hxy.trans hyz
  le_antisymm := fun x y hxy hyx ↦ Subtype.ext (le_antisymm hxy hyx)
  sup := fun x y ↦ ⟨x.1 ⊔ y.1, (treeSublattice n).sup_mem x.2 y.2⟩
  le_sup_left := fun _ _ ↦ le_sup_left
  le_sup_right := fun _ _ ↦ le_sup_right
  sup_le := fun _ _ _ hx hz ↦ sup_le hx hz
  inf := fun x y ↦ ⟨x.1 ⊓ y.1, (treeSublattice n).inf_mem x.2 y.2⟩
  inf_le_left := fun _ _ ↦ inf_le_left
  inf_le_right := fun _ _ ↦ inf_le_right
  le_inf := fun _ _ _ hx hz ↦ le_inf hx hz
instance treeComponentIsOrderedAddMonoid (n : ℕ) :
    IsOrderedAddMonoid (TreeComponent n) where
  add_le_add_left a b hab c := by
    intro p
    simpa [add_comm] using add_le_add_right (hab p) (c.1 p)
noncomputable instance treeComponentVectorLattice (n : ℕ) :
    VectorLattice (TreeComponent n) where
  smul_le_smul_of_nonneg_left := by
    intro a ha x y hxy
    exact smul_le_smul_of_nonneg_left hxy ha
noncomputable def componentLatticeNorm (n : ℕ) : PaperLatticeNorm (TreeComponent n) where
  toFun := fun x ↦ treeSeminorm n x.1
  nonneg := by
    intro x
    exact apply_nonneg (treeLatticeSeminorm n).toSeminorm x.1
  eq_zero_iff := by
    intro x
    constructor
    · intro hx
      apply Subtype.ext
      apply norm_eq_zero.mp
      have hle := (treeSeminorm_norm_comparison n x.1).2
      rw [hx, mul_zero] at hle
      exact le_antisymm hle (norm_nonneg _)
    · rintro rfl
      exact map_zero (treeLatticeSeminorm n).toSeminorm
  add_le := by
    intro x y
    exact map_add_le_add (treeLatticeSeminorm n).toSeminorm x.1 y.1
  smul := by
    intro a x
    rw [← Real.norm_eq_abs]
    exact map_smul_eq_mul (treeLatticeSeminorm n).toSeminorm a x.1
  solid := by
    intro x y hxy
    exact (treeLatticeSeminorm n).monotone_abs' hxy
noncomputable def componentRoot (n : ℕ) : TreeComponent n :=
  ⟨treeFunction n (TreeNode.root n), by
    change treeFunction n (TreeNode.root n) ∈
      closure (VectorSublattice.generated (Set.range (treeFunction n)) :
        Set (BoundedContinuousFunction (TreeProduct n) ℝ))
    apply subset_closure
    exact VectorSublattice.subset_generated _ ⟨TreeNode.root n, rfl⟩⟩
noncomputable def componentTreeFunction (n : ℕ) (t : TreeNode n) : TreeComponent n :=
  ⟨treeFunction n t, by
    change treeFunction n t ∈
      closure (VectorSublattice.generated (Set.range (treeFunction n)) :
        Set (BoundedContinuousFunction (TreeProduct n) ℝ))
    apply subset_closure
    exact VectorSublattice.subset_generated _ ⟨t, rfl⟩⟩
end OrderClosures


