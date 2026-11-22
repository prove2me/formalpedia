-- Prove2me | Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
-- name    : LeanPool_OrderClosures_GaoLeungProblem_Iterations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:03:47.442462+00:00
-- url     : https://prove2.me/theorems/78d39fd2-26f1-442e-a17a-10afe74af732
-- title:
--   Iterations
-- statement:
--   Definitions and structural lemmas for Iterations, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Theorems.Thm_ClosedOrderIdeal_inf_toSubmodule
public import Theorems.Thm_ClosedOrderIdeal_mem_sInf
public import Theorems.Thm_ClosedOrderIdeal_sup_toSubmodule
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
public import Theorems.Thm_OrderClosures_CNFListLT_trans
public import Theorems.Thm_OrderClosures_CNFStep_trans
public import Theorems.Thm_OrderConvergesTo_le
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_Positive_le_def
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
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
open Set
universe u v
section OrdinalConstruction
noncomputable def canonicalOrderAdherenceTower
    {X : Type v} [AddCommGroup X] [Lattice X]
     (A : Set X) : OrderAdherenceTower A where
  stage η := transfiniteIterate orderAdherence η A
  stage_zero := transfiniteIterate_bot _ _
  stage_succ η := transfiniteIterate_succ _ _ _ (by
    rw [not_isMax_iff]
    exact ⟨η + 1, lt_add_one η⟩)
  stage_limit η hη := by
    rw [transfiniteIterate_limit _ _ _ hη]
    ext x
    simp
abbrev GaoSuccessorGenerator (β : Ordinal.{u}) :=
  {ζ : GaoIndex β // ζ ∈ GaoStageIndices β 1}
abbrev GaoComponentIndex (κ : Cardinal.{u}) :=
  Set.Iio (Cardinal.ord (Order.succ κ))
abbrev GaoComponent (β : Ordinal.{u}) :=
  C(GaoCompactSpace β, ℝ)
abbrev GaoIterationProduct (κ : Cardinal.{u}) :=
  (∀ β : GaoComponentIndex κ, GaoComponent β.1) ×
    (ULift.{u + 1, u} (Cardinal.ord κ).ToType → ℝ)
instance (κ : Cardinal.{u}) : IsOrderedAddMonoid (GaoIterationProduct κ) where
  add_le_add_left a b hab c := by
    constructor
    · intro β
      simpa [add_comm] using add_le_add_right (hab.1 β) (c.1 β)
    · intro i
      simpa [add_comm] using add_le_add_right (hab.2 i) (c.2 i)
instance (κ : Cardinal.{u}) : PosSMulMono ℝ (GaoIterationProduct κ) where
  smul_le_smul_of_nonneg_left a ha b₁ b₂ hbc := by
    constructor
    · intro β
      rw [ContinuousMap.le_def]
      intro y
      exact smul_le_smul_of_nonneg_left ((hbc.1 β) y) ha
    · intro i
      exact smul_le_smul_of_nonneg_left (hbc.2 i) ha
noncomputable instance (κ : Cardinal.{u}) : VectorLattice (GaoIterationProduct κ) where
theorem mk_gaoSuccessorGenerator_le
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : Ordinal.{u}) (hβ : β < Cardinal.ord (Order.succ κ)) :
    Cardinal.mk (GaoSuccessorGenerator β) ≤ Cardinal.lift.{u + 1, u} κ := by
  let bound : Ordinal.{u} := (Ordinal.omega0 ^ β + 1) + 1
  let e : GaoIndex β ↪ Set.Iio bound :=
    ⟨fun ζ ↦ ⟨ζ.1, by
        change ζ.1 < (Ordinal.omega0 ^ β + 1) + 1
        rw [← Order.succ_eq_add_one, Order.lt_succ_iff]
        exact ζ.2⟩,
      fun _ _ h ↦ Subtype.ext (congrArg (fun z : Set.Iio bound ↦ z.1) h)⟩
  have hβcard : β.card ≤ κ := Cardinal.card_le_iff.mpr hβ
  have hpowcard : (Ordinal.omega0 ^ β).card ≤ κ := by
    refine (Ordinal.card_opow_le Ordinal.omega0 β).trans ?_
    rw [Ordinal.card_omega0]
    exact max_le hκ (max_le hκ hβcard)
  have honeκ : (1 : Cardinal) ≤ κ := Cardinal.one_lt_aleph0.le.trans hκ
  have hboundcard : bound.card ≤ κ := by
    calc
      bound.card = (Ordinal.omega0 ^ β).card + 1 + 1 := by
        simp only [bound, Ordinal.card_add, Ordinal.card_one]
      _ ≤ κ + 1 + 1 := add_le_add (add_le_add hpowcard le_rfl) le_rfl
      _ = κ := by
        rw [Cardinal.add_eq_left hκ honeκ, Cardinal.add_eq_left hκ honeκ]
  calc
    Cardinal.mk (GaoSuccessorGenerator β) ≤ Cardinal.mk (GaoIndex β) :=
      Cardinal.mk_subtype_le _
    _ ≤ Cardinal.mk (Set.Iio bound) := Cardinal.mk_le_of_injective e.injective
    _ = Cardinal.lift.{u + 1, u} bound.card := Cardinal.mk_Iio_ordinal bound
    _ ≤ Cardinal.lift.{u + 1, u} κ := Cardinal.lift_le.mpr hboundcard
noncomputable def gaoGeneratorEmbedding
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : Ordinal.{u}) (hβ : β < Cardinal.ord (Order.succ κ)) :
    GaoSuccessorGenerator β ↪ ULift.{u + 1, u} (Cardinal.ord κ).ToType := by
  apply Classical.choice
  rw [← Cardinal.le_def]
  change Cardinal.mk (GaoSuccessorGenerator β) ≤
    Cardinal.lift.{u + 1, u} (Cardinal.mk (Cardinal.ord κ).ToType)
  rw [Cardinal.mk_ord_toType]
  exact mk_gaoSuccessorGenerator_le κ hκ β hβ
noncomputable def gaoComponentGenerator
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ)
    (a : ULift.{u + 1, u} (Cardinal.ord κ).ToType) : GaoComponent β.1 := by
  classical
  exact if h : ∃ ζ : GaoSuccessorGenerator β.1,
        gaoGeneratorEmbedding κ hκ β.1 β.2 ζ = a then
      ordinalProjection β.1 (Classical.choose h).1
    else 0
noncomputable def gaoGlobalGenerator
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (a : ULift.{u + 1, u} (Cardinal.ord κ).ToType) : GaoIterationProduct κ :=
  (fun β ↦ gaoComponentGenerator κ hκ β a,
    fun b ↦ if b = a then (1 : ℝ) else 0)
def gaoProductProjection (κ : Cardinal.{u}) (β : GaoComponentIndex κ) :
    GaoIterationProduct κ → GaoComponent β.1 := fun x ↦ x.1 β
noncomputable def gaoProductInclusion
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ) :
    GaoComponent β.1 → GaoIterationProduct κ := fun x ↦
  (Pi.single β x, 0)
noncomputable def gaoIterationSet
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) : Set (GaoIterationProduct κ) :=
  solidHull (Set.range (gaoGlobalGenerator κ hκ))
end OrdinalConstruction
end OrderClosures


