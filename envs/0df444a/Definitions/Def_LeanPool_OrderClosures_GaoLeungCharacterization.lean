-- Prove2me | Definitions.Def_LeanPool_OrderClosures_GaoLeungCharacterization
-- name    : LeanPool_OrderClosures_GaoLeungCharacterization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:55:33.031695+00:00
-- url     : https://prove2.me/theorems/82cac025-ed07-44bb-a608-13ad5a2c401e
-- title:
--   Gao Leung Characterization
-- statement:
--   Definitions and structural lemmas for Gao Leung Characterization, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungCharacterization.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_DisjointComplement
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Theorems.Thm_ClosedOrderIdeal_inf_toSubmodule
public import Theorems.Thm_ClosedOrderIdeal_mem_sInf
public import Theorems.Thm_ClosedOrderIdeal_sup_toSubmodule
public import Theorems.Thm_IsVLArchimedean_of_sigmaConditionallyCompleteLattice
public import Theorems.Thm_IsVLDisjoint_add_left
public import Theorems.Thm_IsVLDisjoint_add_right
public import Theorems.Thm_IsVLDisjoint_smul_left
public import Theorems.Thm_IsVLDisjoint_smul_right
public import Theorems.Thm_IsVecLatHom_of_disjoint
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
public import Theorems.Thm_OrderConvergesTo_abs
public import Theorems.Thm_OrderConvergesTo_add
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_Positive_extension_nonneg
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
public import Theorems.Thm_inf_eq_zero_of_isVLDisjoint
public import Theorems.Thm_isVLDisjoint_comm
public import Theorems.Thm_isVLDisjoint_zero_left
public import Theorems.Thm_isVLDisjoint_zero_right
public import Theorems.Thm_sup_abs_eq_add_abs_of_isVLDisjoint
attribute [local simp] ClosedOrderIdeal.inf_toSubmodule
attribute [local simp] ClosedOrderIdeal.mem_sInf
attribute [local simp] ClosedOrderIdeal.sup_toSubmodule
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
open scoped BoundedContinuousFunction
universe u
section
variable {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]
end
section DisjointEmbedding
variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
variable {P : Type*}
lemma isVLDisjoint_smul_finset_sum
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    (a : P → ℝ) {p : P} {F : Finset P} (hp : p ∉ F) :
    IsVLDisjoint (a p • x p) (∑ q ∈ F, a q • x q) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using isVLDisjoint_zero_right (a p • x p)
  | @insert q F hq ih =>
      rw [Finset.sum_insert hq]
      have hp' : p ≠ q ∧ p ∉ F := by
        simpa only [Finset.mem_insert, not_or] using hp
      apply IsVLDisjoint.add_right
      · exact ((hx hp'.1).smul_left (a p)).smul_right (a q)
      · exact ih hp'.2
lemma finset_disjoint_sum_le
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {b : X} (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {a : P → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ p, 0 ≤ a p ∧ a p ≤ M) (F : Finset P) :
    ∑ p ∈ F, a p • x p ≤ M • b := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using smul_nonneg hM hb
  | @insert p F hp ih =>
      rw [Finset.sum_insert hp]
      have hterm : a p • x p ≤ M • b :=
        (smul_le_smul_of_nonneg_left (hxb p).2 (ha p).1).trans
          (smul_le_smul_of_nonneg_right (ha p).2 hb)
      have hterm0 : 0 ≤ a p • x p := smul_nonneg (ha p).1 (hxb p).1
      have hsum0 : 0 ≤ ∑ q ∈ F, a q • x q := by
        exact Finset.sum_nonneg fun q _ ↦ smul_nonneg (ha q).1 (hxb q).1
      have hdisj := isVLDisjoint_smul_finset_sum hx a hp
      have hadd : a p • x p + ∑ q ∈ F, a q • x q =
          a p • x p ⊔ ∑ q ∈ F, a q • x q := by
        simpa [abs_of_nonneg hterm0, abs_of_nonneg hsum0] using
          (sup_abs_eq_add_abs_of_isVLDisjoint hdisj).symm
      rw [hadd]
      exact sup_le hterm ih
end DisjointEmbedding
section DisjointEmbedding
variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
variable {P : Type*} [TopologicalSpace P] [DiscreteTopology P] [Countable P]
noncomputable instance boundedContinuousFunctionVectorLattice :
    VectorLattice (P →ᵇ ℝ) where
  toModule := inferInstance
  smul_le_smul_of_nonneg_left := by
    intro a ha f g h p
    exact mul_le_mul_of_nonneg_left (h p) ha
noncomputable def disjointFiniteSum (x : P → X)
    (a : P →ᵇ ℝ) (F : Finset P) : X :=
  ∑ p ∈ F, a p • x p
noncomputable def disjointSup (x : P → X) (a : P →ᵇ ℝ) : X :=
  sSup (Set.range (disjointFiniteSum x a))
omit [DiscreteTopology P] in
/-- Packages the defining finite sums as a genuine least upper bound; reused
throughout the construction of `disjointEmbedding`. -/
theorem disjointSup_isLUB
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {b : X} (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {a : P →ᵇ ℝ} (ha : 0 ≤ a) :
    IsLUB (Set.range (disjointFiniteSum x a)) (disjointSup x a) := by
  classical
  have ha' : ∀ p, 0 ≤ a p ∧ a p ≤ ‖a‖ := by
    intro p
    exact ⟨ha p, (le_abs_self (a p)).trans
      (by simpa [Real.norm_eq_abs] using a.norm_coe_le_norm p)⟩
  have hbound : BddAbove (Set.range (disjointFiniteSum x a)) := by
    refine ⟨‖a‖ • b, ?_⟩
    rintro _ ⟨F, rfl⟩
    exact finset_disjoint_sum_le hx hb hxb (norm_nonneg a) ha' F
  refine ⟨?_, ?_⟩
  · intro y hy
    exact SigmaConditionallyCompleteLattice.le_csSup _ _ (Set.countable_range _)
      hbound hy
  · intro y hy
    exact SigmaConditionallyCompleteLattice.csSup_le _ _ (Set.countable_range _)
      (Set.range_nonempty _) hy
omit [DiscreteTopology P] in
/-- Records positivity of `disjointSup`; needed by the positive linear
extension used to construct `disjointEmbedding`. -/
theorem disjointSup_nonneg
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {b : X} (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {a : P →ᵇ ℝ} (ha : 0 ≤ a) :
    0 ≤ disjointSup x a := by
  apply (disjointSup_isLUB hx hb hxb ha).1
  exact ⟨∅, by simp [disjointFiniteSum]⟩
omit [DiscreteTopology P] in
/-- Proves additivity of `disjointSup` on the positive cone, the second input
to the positive linear extension defining `disjointEmbedding`. -/
theorem disjointSup_add
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {b : X} (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {a c : P →ᵇ ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    disjointSup x (a + c) = disjointSup x a + disjointSup x c := by
  classical
  have hac : 0 ≤ a + c := add_nonneg ha hc
  have hA := disjointSup_isLUB hx hb hxb ha
  have hC := disjointSup_isLUB hx hb hxb hc
  have hAC := disjointSup_isLUB hx hb hxb hac
  apply le_antisymm
  · apply hAC.2
    rintro _ ⟨F, rfl⟩
    simp only [disjointFiniteSum, BoundedContinuousFunction.add_apply, add_smul,
      Finset.sum_add_distrib]
    exact add_le_add (hA.1 ⟨F, rfl⟩) (hC.1 ⟨F, rfl⟩)
  · rw [add_comm, ← le_sub_iff_add_le]
    apply hC.2
    rintro _ ⟨G, rfl⟩
    rw [le_sub_iff_add_le]
    rw [add_comm, ← le_sub_iff_add_le]
    apply hA.2
    rintro _ ⟨F, rfl⟩
    rw [le_sub_iff_add_le]
    let H := F ∪ G
    have hFa : disjointFiniteSum x a F ≤ disjointFiniteSum x a H := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left)
      intro p _ _
      exact smul_nonneg (ha p) (hxb p).1
    have hGc : disjointFiniteSum x c G ≤ disjointFiniteSum x c H := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_right)
      intro p _ _
      exact smul_nonneg (hc p) (hxb p).1
    calc
      disjointFiniteSum x a F + disjointFiniteSum x c G ≤
          disjointFiniteSum x a H + disjointFiniteSum x c H := add_le_add hFa hGc
      _ = disjointFiniteSum x (a + c) H := by
        simp only [disjointFiniteSum, BoundedContinuousFunction.add_apply, add_smul,
          Finset.sum_add_distrib]
      _ ≤ disjointSup x (a + c) := hAC.1 ⟨H, rfl⟩
lemma isVLDisjoint_smul_same_of_inf_eq_zero
    {x : X} {a c : ℝ} (hac : a ⊓ c = 0) :
    IsVLDisjoint (a • x) (c • x) := by
  by_cases hle : a ≤ c
  · have ha0 : a = 0 := by simpa [inf_eq_left.mpr hle] using hac
    rw [ha0, zero_smul]
    exact isVLDisjoint_zero_left _
  · have hc0 : c = 0 := by
      simpa [inf_eq_right.mpr (le_of_not_ge hle)] using hac
    rw [hc0, zero_smul]
    exact isVLDisjoint_zero_right _
omit [DiscreteTopology P] [Countable P] in
/-- Extends coefficientwise disjointness from one summand to a finite sum;
used to prove disjointness of two finite approximating sums. -/
lemma isVLDisjoint_smul_finset_sum_of_inf_eq_zero
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {a c : P →ᵇ ℝ} (hac : a ⊓ c = 0)
    (p : P) (G : Finset P) :
    IsVLDisjoint (a p • x p) (disjointFiniteSum x c G) := by
  classical
  induction G using Finset.induction_on with
  | empty => simpa [disjointFiniteSum] using isVLDisjoint_zero_right (a p • x p)
  | @insert q G hq ih =>
      rw [disjointFiniteSum, Finset.sum_insert hq]
      apply IsVLDisjoint.add_right
      · by_cases hpq : p = q
        · subst q
          apply isVLDisjoint_smul_same_of_inf_eq_zero
          have hp := congrArg (fun f : P →ᵇ ℝ ↦ f p) hac
          simpa using hp
        · exact ((hx hpq).smul_left (a p)).smul_right (c q)
      · simpa [disjointFiniteSum] using ih
omit [DiscreteTopology P] [Countable P] in
/-- Shows that finite sums with disjoint coefficient functions are disjoint;
used to pass disjointness to their order suprema. -/
lemma isVLDisjoint_finset_sums_of_inf_eq_zero
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {a c : P →ᵇ ℝ} (hac : a ⊓ c = 0)
    (F G : Finset P) :
    IsVLDisjoint (disjointFiniteSum x a F) (disjointFiniteSum x c G) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa [disjointFiniteSum] using isVLDisjoint_zero_left (disjointFiniteSum x c G)
  | @insert p F hp ih =>
      rw [disjointFiniteSum, Finset.sum_insert hp]
      exact IsVLDisjoint.add_left
        (isVLDisjoint_smul_finset_sum_of_inf_eq_zero hx hac p G)
        (by simpa [disjointFiniteSum] using ih)
omit [DiscreteTopology P] in
/-- Passes disjointness of coefficient functions to the corresponding
`disjointSup` values; this proves that the eventual embedding is a lattice map. -/
theorem disjointSup_disjoint
    {x : P → X} (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    {b : X} (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b)
    {a c : P →ᵇ ℝ} (hac : a ⊓ c = 0) :
    disjointSup x a ⊓ disjointSup x c = 0 := by
  have ha : 0 ≤ a := hac ▸ inf_le_left
  have hc : 0 ≤ c := hac ▸ inf_le_right
  have hA := disjointSup_isLUB hx hb hxb ha
  have hC := disjointSup_isLUB hx hb hxb hc
  let BC : Band X := Band.disjointComplement {disjointSup x c}
  have hfiniteA : Set.range (disjointFiniteSum x a) ⊆ (BC : Set X) := by
    rintro _ ⟨F, rfl⟩ _ hz
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    let BF : Band X := Band.disjointComplement {disjointFiniteSum x a F}
    have hfiniteC : Set.range (disjointFiniteSum x c) ⊆ (BF : Set X) := by
      rintro _ ⟨G, rfl⟩ _ hz
      simp only [Set.mem_singleton_iff] at hz
      subst hz
      exact isVLDisjoint_comm.mp
        (isVLDisjoint_finset_sums_of_inf_eq_zero hx hac F G)
    have htauC : disjointSup x c ∈ BF :=
      BF.sSup_mem hfiniteC (Set.range_nonempty _) hC
    exact isVLDisjoint_comm.mp (htauC _ rfl)
  have htauA : disjointSup x a ∈ BC :=
    BC.sSup_mem hfiniteA (Set.range_nonempty _) hA
  exact inf_eq_zero_of_isVLDisjoint
    (disjointSup_nonneg hx hb hxb ha) (disjointSup_nonneg hx hb hxb hc)
    (htauA _ rfl)
noncomputable def disjointEmbedding
    (x : P → X) (hx : Pairwise fun p q ↦ IsVLDisjoint (x p) (x q))
    (b : X) (hb : 0 ≤ b) (hxb : ∀ p, 0 ≤ x p ∧ x p ≤ b) :
    VecLatHom (P →ᵇ ℝ) X := by
  letI : IsVLArchimedean X := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  let tau : (P →ᵇ ℝ) → X := disjointSup x
  have htau_nonneg : ∀ a, 0 ≤ a → 0 ≤ tau a :=
    fun _ ha ↦ disjointSup_nonneg hx hb hxb ha
  have htau_add : ∀ a c, 0 ≤ a → 0 ≤ c → tau (a + c) = tau a + tau c :=
    fun _ _ ha hc ↦ disjointSup_add hx hb hxb ha hc
  let T : (P →ᵇ ℝ) →ₗ[ℝ] X := Positive.extension htau_nonneg htau_add
  apply IsVecLatHom.mk' T
  apply IsVecLatHom.of_disjoint T.isLinear
  intro a c hac
  have ha : 0 ≤ a := hac ▸ inf_le_left
  have hc : 0 ≤ c := hac ▸ inf_le_right
  rw [Positive.extension_nonneg htau_nonneg htau_add ha,
    Positive.extension_nonneg htau_nonneg htau_add hc]
  exact disjointSup_disjoint hx hb hxb hac
end DisjointEmbedding
section DisjointSequence
variable {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]
end DisjointSequence
section RowLimitSublattice
abbrev PairIndex := ℕ × ℕ
abbrev PairLInfinity := PairIndex →ᵇ ℝ
def rowLimitSubmodule : Submodule ℝ PairLInfinity where
  carrier := {a | ∀ m : ℕ,
    Tendsto (fun n : ℕ ↦ a (m, n + 1)) atTop
      (nhds ((m + 1 : ℕ) * a (m, 0)))}
  zero_mem' := by simp
  add_mem' := by
    intro a c ha hc m
    simpa [mul_add] using (ha m).add (hc m)
  smul_mem' := by
    intro r a ha m
    simpa [mul_assoc, mul_left_comm, mul_comm] using (ha m).const_smul r
noncomputable def rowLimitSublattice : VectorSublattice PairLInfinity :=
  VectorSublattice.ofAbsClosed rowLimitSubmodule fun a ha ↦ by
    intro m
    change Tendsto (fun k => |a (m, k + 1)|) atTop (𝓝 ((m + 1 : ℕ) * |a (m, 0)|))
    simpa only [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m + 1 : ℕ))]
      using (ha m).abs
noncomputable def rowHead : PairLInfinity :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun p : PairIndex ↦ if p.2 = 0 then 1 else 0) 1 (by
      intro p
      simp [Real.norm_eq_abs]
      split_ifs <;> norm_num)
noncomputable def rowApprox (j : ℕ) : PairLInfinity :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun p : PairIndex ↦
      if p.2 = 0 then
        if p.1 ≤ j then 1 else 0
      else if p.1 ≤ j ∧ j < p.2 then (p.1 + 1 : ℕ) else 0)
    (j + 1) (by
      intro p
      rw [Real.norm_eq_abs]
      by_cases hn : p.2 = 0
      · simp only [hn, ite_true]
        by_cases hm : p.1 ≤ j
        · rw [if_pos hm, abs_one]
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
        · rw [if_neg hm, abs_zero]
          positivity
      · simp only [hn, ite_false]
        by_cases ht : p.1 ≤ j ∧ j < p.2
        · rw [if_pos ht, abs_of_nonneg (by positivity)]
          exact_mod_cast Nat.succ_le_succ ht.1
        · rw [if_neg ht, abs_zero]
          positivity)
end RowLimitSublattice
section CoordinatewiseUO
variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
variable {P : Type*} [TopologicalSpace P] [DiscreteTopology P] [Countable P]
end CoordinatewiseUO
section SublatticeImage
variable {E : Type*} {X : Type*}
  [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]
  [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
def vectorSublatticeImage (T : VecLatHom E X) (H : VectorSublattice E) :
    VectorSublattice X where
  carrier := T '' (H : Set E)
  zero_mem' := ⟨0, H.toSubmodule.zero_mem, map_zero T⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨a + c, H.toSubmodule.add_mem ha hc, map_add T a c⟩
  smul_mem' := by
    rintro r _ ⟨a, ha, rfl⟩
    exact ⟨r • a, H.toSubmodule.smul_mem r ha, map_smul T r a⟩
  sup_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨a ⊔ c, H.sup_mem ha hc, T.map_sup' a c⟩
end SublatticeImage
section CoordinateConvergence
variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
variable {P : Type*} [TopologicalSpace P] [DiscreteTopology P] [Countable P]
end CoordinateConvergence
section RowLimitExclusion
variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
end RowLimitExclusion
section LiftConvergence
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
end LiftConvergence
section ReverseImplication
variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
end ReverseImplication
section Characterization
variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
end Characterization
end OrderClosures


