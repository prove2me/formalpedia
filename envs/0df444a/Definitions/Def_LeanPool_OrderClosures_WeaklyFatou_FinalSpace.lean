-- Prove2me | Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FinalSpace
-- name    : LeanPool_OrderClosures_WeaklyFatou_FinalSpace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:03:19.629799+00:00
-- url     : https://prove2.me/theorems/7ef508b2-00b8-4291-92f6-3b3f45b034d0
-- title:
--   Final Space
-- statement:
--   Definitions and structural lemmas for Final Space, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
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
public import Theorems.Thm_OrderConvergesTo_add
public import Theorems.Thm_OrderConvergesTo_inf
public import Theorems.Thm_OrderConvergesTo_le
public import Theorems.Thm_OrderConvergesTo_nonneg
public import Theorems.Thm_OrderConvergesTo_smul
public import Theorems.Thm_OrderConvergesTo_sup
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
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
def terminalTreeFunctions (n : ℕ) : Set (BoundedContinuousFunction (TreeProduct n) ℝ) :=
  treeFunction n '' {t : TreeNode n | TreeNode.level t = n}
abbrev ComponentProduct := ∀ n : ℕ, TreeComponent n
def componentVanishes (x : ComponentProduct) : Prop :=
  Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0)
noncomputable def componentC0Sublattice : VectorSublattice ComponentProduct where
  carrier := {x | componentVanishes x}
  zero_mem' := by
    change Tendsto (fun n ↦ componentLatticeNorm n (0 : TreeComponent n)) atTop (nhds 0)
    have hzero : (fun n ↦ componentLatticeNorm n (0 : TreeComponent n)) =
        fun _ ↦ 0 := by
      funext n
      exact (componentLatticeNorm n).eq_zero_iff 0 |>.2 rfl
    rw [hzero]
    exact tendsto_const_nhds
  add_mem' := by
    intro x y hx hy
    change Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0) at hx
    change Tendsto (fun n ↦ componentLatticeNorm n (y n)) atTop (nhds 0) at hy
    change Tendsto (fun n ↦ componentLatticeNorm n (x n + y n)) atTop (nhds 0)
    apply squeeze_zero
    · exact fun n ↦ (componentLatticeNorm n).nonneg _
    · exact fun n ↦ (componentLatticeNorm n).add_le _ _
    · simpa using hx.add hy
  smul_mem' := by
    intro a x hx
    change Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0) at hx
    change Tendsto (fun n ↦ componentLatticeNorm n (a • x n)) atTop (nhds 0)
    have heq : (fun n ↦ componentLatticeNorm n (a • x n)) =
        fun n ↦ |a| * componentLatticeNorm n (x n) := by
      funext n
      exact (componentLatticeNorm n).smul a (x n)
    rw [heq]
    simpa using hx.const_mul |a|
  sup_mem' := by
    intro x y hx hy
    change Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0) at hx
    change Tendsto (fun n ↦ componentLatticeNorm n (y n)) atTop (nhds 0) at hy
    change Tendsto (fun n ↦ componentLatticeNorm n (x n ⊔ y n)) atTop (nhds 0)
    apply squeeze_zero
    · exact fun n ↦ (componentLatticeNorm n).nonneg _
    · intro n
      have habsx : componentLatticeNorm n |x n| = componentLatticeNorm n (x n) := by
        apply le_antisymm
        · exact (componentLatticeNorm n).solid (by simp)
        · exact (componentLatticeNorm n).solid (by simp)
      have habsy : componentLatticeNorm n |y n| = componentLatticeNorm n (y n) := by
        apply le_antisymm
        · exact (componentLatticeNorm n).solid (by simp)
        · exact (componentLatticeNorm n).solid (by simp)
      calc
        componentLatticeNorm n (x n ⊔ y n) ≤
            componentLatticeNorm n (|x n| + |y n|) :=
          (componentLatticeNorm n).solid (by
            have hsum0 : (0 : TreeComponent n) ≤ |x n| + |y n| :=
              add_nonneg (abs_nonneg _) (abs_nonneg _)
            rw [abs_of_nonneg hsum0]
            apply abs_le'.mpr
            constructor
            · exact sup_le ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
                ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))
            · exact (neg_le_neg (le_sup_left : x n ≤ x n ⊔ y n)).trans
                ((neg_le_abs _).trans (le_add_of_nonneg_right (abs_nonneg _))))
        _ ≤ componentLatticeNorm n |x n| + componentLatticeNorm n |y n| :=
          (componentLatticeNorm n).add_le _ _
        _ = componentLatticeNorm n (x n) + componentLatticeNorm n (y n) := by
          rw [habsx, habsy]
    · simpa using hx.add hy
abbrev FinalSpace := ↥componentC0Sublattice.toSubmodule
noncomputable def finalCoordinateEmbedding (n : ℕ) (z : TreeComponent n) : FinalSpace :=
  ⟨fun m ↦ if h : m = n then h.symm ▸ z else 0, by
    change Tendsto
      (fun m ↦ componentLatticeNorm m (if h : m = n then h.symm ▸ z else 0))
      atTop (nhds 0)
    have heq : (fun m ↦ componentLatticeNorm m
        (if h : m = n then h.symm ▸ z else 0)) =ᶠ[atTop] fun _ ↦ 0 := by
      filter_upwards [eventually_gt_atTop n] with m hm
      rw [dif_neg hm.ne']
      exact (componentLatticeNorm m).eq_zero_iff _ |>.2 rfl
    exact (tendsto_congr' heq).2 tendsto_const_nhds⟩
@[simp] theorem finalCoordinateEmbedding_same (n : ℕ) (z : TreeComponent n) :
    (finalCoordinateEmbedding n z).1 n = z := by
  simp [finalCoordinateEmbedding]
noncomputable instance finalSpaceLattice : Lattice FinalSpace where
  le := fun x y ↦ x.1 ≤ y.1
  le_refl := fun _ ↦ le_rfl
  le_trans := fun _ _ _ hxy hyz ↦ hxy.trans hyz
  le_antisymm := fun x y hxy hyx ↦ Subtype.ext (le_antisymm hxy hyx)
  sup := fun x y ↦ ⟨x.1 ⊔ y.1, componentC0Sublattice.sup_mem x.2 y.2⟩
  le_sup_left := fun _ _ ↦ le_sup_left
  le_sup_right := fun _ _ ↦ le_sup_right
  sup_le := fun _ _ _ hx hz ↦ sup_le hx hz
  inf := fun x y ↦ ⟨x.1 ⊓ y.1, componentC0Sublattice.inf_mem x.2 y.2⟩
  inf_le_left := fun _ _ ↦ inf_le_left
  inf_le_right := fun _ _ ↦ inf_le_right
  le_inf := fun _ _ _ hx hz ↦ le_inf hx hz
instance finalSpaceIsOrderedAddMonoid : IsOrderedAddMonoid FinalSpace where
  add_le_add_left a b hab c := by
    intro n
    simpa [add_comm] using add_le_add_right (hab n) (c.1 n)
noncomputable instance finalSpaceVectorLattice : VectorLattice FinalSpace where
  smul_le_smul_of_nonneg_left := by
    intro a ha x y hxy n
    exact smul_le_smul_of_nonneg_left (hxy n) ha
noncomputable def finalNormValue (x : FinalSpace) : ℝ :=
  sSup (Set.range fun n ↦ componentLatticeNorm n (x.1 n))
theorem finalNormValue_bddAbove (x : FinalSpace) :
    BddAbove (Set.range fun n ↦ componentLatticeNorm n (x.1 n)) :=
  x.2.bddAbove_range
theorem componentNorm_le_finalNormValue (x : FinalSpace) (n : ℕ) :
    componentLatticeNorm n (x.1 n) ≤ finalNormValue x := by
  exact le_csSup (finalNormValue_bddAbove x) ⟨n, rfl⟩
noncomputable def finalLatticeNorm : PaperLatticeNorm FinalSpace where
  toFun := finalNormValue
  nonneg := by
    intro x
    exact ((componentLatticeNorm 0).nonneg _).trans
      (componentNorm_le_finalNormValue x 0)
  eq_zero_iff := by
    intro x
    constructor
    · intro hx
      apply Subtype.ext
      funext n
      apply (componentLatticeNorm n).eq_zero_iff (x.1 n) |>.1
      apply le_antisymm
      · simpa [hx] using componentNorm_le_finalNormValue x n
      · exact (componentLatticeNorm n).nonneg _
    · rintro rfl
      unfold finalNormValue
      have hzero : (fun n ↦ componentLatticeNorm n ((0 : FinalSpace).1 n)) =
          fun _ ↦ 0 := by
        funext n
        apply (componentLatticeNorm n).eq_zero_iff _ |>.2
        rfl
      rw [hzero]
      simp
  add_le := by
    intro x y
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    calc
      componentLatticeNorm n ((x + y).1 n) ≤
          componentLatticeNorm n (x.1 n) + componentLatticeNorm n (y.1 n) := by
        simpa using (componentLatticeNorm n).add_le (x.1 n) (y.1 n)
      _ ≤ finalNormValue x + finalNormValue y :=
        add_le_add (componentNorm_le_finalNormValue x n)
          (componentNorm_le_finalNormValue y n)
  smul := by
    intro a x
    unfold finalNormValue
    simp_rw [show ∀ n, componentLatticeNorm n ((a • x).1 n) =
        |a| * componentLatticeNorm n (x.1 n) by
      intro n
      simpa using (componentLatticeNorm n).smul a (x.1 n)]
    exact
      (Real.smul_iSup_of_nonneg (abs_nonneg a)
        (fun n ↦ componentLatticeNorm n (x.1 n))).symm
  solid := by
    intro x y hxy
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    exact ((componentLatticeNorm n).solid (hxy n)).trans
      (componentNorm_le_finalNormValue y n)
noncomputable def finalLargeVector (n : ℕ) : FinalSpace :=
  ⟨fun m ↦ if h : m = n then h.symm ▸ ((2 : ℝ) ^ n • componentRoot n) else 0, by
    change Tendsto
      (fun m ↦ componentLatticeNorm m
        (if h : m = n then h.symm ▸ ((2 : ℝ) ^ n • componentRoot n) else 0))
      atTop (nhds 0)
    have heq : (fun m ↦ componentLatticeNorm m
        (if h : m = n then h.symm ▸ ((2 : ℝ) ^ n • componentRoot n) else 0)) =ᶠ[atTop]
        fun _ ↦ 0 := by
      filter_upwards [eventually_gt_atTop n] with m hm
      rw [dif_neg hm.ne']
      exact (componentLatticeNorm m).eq_zero_iff _ |>.2 rfl
    exact (tendsto_congr' heq).2 tendsto_const_nhds⟩
end OrderClosures


