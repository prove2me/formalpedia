-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
-- name    : LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:29:08.426816+00:00
-- url     : https://prove2.me/theorems/ec4be854-1f1b-40e2-a444-04c169bfe9cf
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/Basic.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
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
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
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
attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_bot
attribute [local simp] VectorSublattice.mem_top


set_option autoImplicit true
@[expose] public section
@[expose] public section
section MainVariables
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
structure Band (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    extends OrderIdeal X where
  sSup_mem' :
    ∀ (S : Set X), S ⊆ carrier → S.Nonempty → ∀ x, IsLUB S x → x ∈ carrier
namespace Band
instance : SetLike (Band X) X where
  coe B := B.carrier
  coe_injective p q h := by
    cases p; cases q; congr
    exact SetLike.ext' h
variable (B : Band X)
theorem sSup_mem {S : Set X} (hS : S ⊆ (B : Set X)) (hne : S.Nonempty)
    {x : X} (hx : IsLUB S x) : x ∈ B :=
  B.sSup_mem' S hS hne x hx
theorem sup_mem {x y : X} (hx : x ∈ B) (hy : y ∈ B) :
    x ⊔ y ∈ B :=
  B.toOrderIdeal.sup_mem hx hy
def ofPosDirectedSSupMem (J : OrderIdeal X)
    (h : ∀ S, S ⊆ (J : Set X) → (∀ x ∈ S, 0 ≤ x) → DirectedOn (· ≤ ·) S
      → S.Nonempty → ∀ x, IsLUB S x → x ∈ J) : Band X where
  toOrderIdeal := J
  sSup_mem' := by
    classical
    intro S hSJ hne y hy
    obtain ⟨s₀, hs₀⟩ := hne
    have hs₀J : s₀ ∈ J := hSJ hs₀
    have finsup_mem : ∀ (F : Finset X) (hF : F.Nonempty), ↑F ⊆ S →
        F.sup' hF id ∈ J := by
      intro F hF hFS
      induction hF using Finset.Nonempty.cons_induction with
      | singleton x =>
        rw [Finset.sup'_singleton]
        exact hSJ (hFS (by simp))
      | cons x F hxF hFne ih =>
        rw [Finset.sup'_cons hFne id]
        refine J.sup_mem (hSJ (hFS ?_)) (ih ?_)
        · simp
        · intro a ha; exact hFS (by simp [ha])
    set T : Set X :=
      { z | ∃ F : Finset X, ∃ hF : F.Nonempty, ↑F ⊆ S ∧ s₀ ∈ F ∧
        z = F.sup' hF id - s₀ }
    have hT_J : T ⊆ (J : Set X) := by
      rintro z ⟨F, hF, hFS, _, rfl⟩
      exact J.toSubmodule.sub_mem (finsup_mem F hF hFS) hs₀J
    have hT_pos : ∀ z ∈ T, 0 ≤ z := by
      rintro z ⟨F, hF, hFS, hs₀F, rfl⟩
      exact sub_nonneg.mpr (Finset.le_sup' id hs₀F)
    have hT_dir : DirectedOn (· ≤ ·) T := by
      rintro a ⟨Fa, hFa, hFaS, hs₀a, rfl⟩ b ⟨Fb, hFb, hFbS, hs₀b, rfl⟩
      refine ⟨(Fa ∪ Fb).sup' (hFa.mono Finset.subset_union_left) id - s₀,
        ⟨Fa ∪ Fb, hFa.mono Finset.subset_union_left, ?_, ?_, rfl⟩, ?_, ?_⟩
      · rw [Finset.coe_union]; exact Set.union_subset hFaS hFbS
      · exact Finset.mem_union.mpr (Or.inl hs₀a)
      · exact sub_le_sub_right
          (Finset.sup'_mono id Finset.subset_union_left hFa) s₀
      · exact sub_le_sub_right
          (Finset.sup'_mono id Finset.subset_union_right hFb) s₀
    have hT_ne : T.Nonempty :=
      ⟨0, ⟨{s₀}, Finset.singleton_nonempty s₀, by
        intro a ha; rw [Finset.coe_singleton, Set.mem_singleton_iff] at ha
        rw [ha]; exact hs₀,
        Finset.mem_singleton_self _, by
        rw [Finset.sup'_singleton]; exact (sub_self s₀).symm⟩⟩
    have hT_lub : IsLUB T (y - s₀) := by
      refine ⟨?_, ?_⟩
      · rintro z ⟨F, hF, hFS, _, rfl⟩
        exact sub_le_sub_right
          (Finset.sup'_le hF id (fun a ha => hy.1 (hFS ha))) s₀
      · intro c hc
        rw [sub_le_iff_le_add]
        apply hy.2
        intro s hs
        have hF : ({s, s₀} : Finset X).Nonempty := ⟨s, by simp⟩
        have hFS : (↑({s, s₀} : Finset X) : Set X) ⊆ S := by
          intro a ha
          rw [Finset.coe_insert, Finset.coe_singleton] at ha
          rcases ha with rfl | rfl
          · exact hs
          · exact hs₀
        have hs₀mem : s₀ ∈ ({s, s₀} : Finset X) := by simp
        have hT_elt : ({s, s₀} : Finset X).sup' hF id - s₀ ∈ T :=
          ⟨_, hF, hFS, hs₀mem, rfl⟩
        have hle : ({s, s₀} : Finset X).sup' hF id - s₀ ≤ c := hc hT_elt
        have hsup_ge : s ≤ ({s, s₀} : Finset X).sup' hF id :=
          Finset.le_sup' id (by simp : s ∈ ({s, s₀} : Finset X))
        have : ({s, s₀} : Finset X).sup' hF id ≤ c + s₀ :=
          sub_le_iff_le_add.mp hle
        exact hsup_ge.trans this
    have hu : y - s₀ ∈ J := h T hT_J hT_pos hT_dir hT_ne (y - s₀) hT_lub
    have hres : y - s₀ + s₀ ∈ J := J.toSubmodule.add_mem hu hs₀J
    change y ∈ J
    rw [sub_add_cancel] at hres
    exact hres
end Band
end MainVariables
section CCLSubtype
variable {X : Type*} [AddCommGroup X] [ConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]
namespace Band
noncomputable instance instConditionallyCompleteLatticeSubtype
    (B : Band X) :
    ConditionallyCompleteLattice ↥B.toSubmodule := by
  letI : Nonempty ↥B.toSubmodule := ⟨0⟩
  refine conditionallyCompleteLatticeOfPosSet ↥B.toSubmodule ?_
  intro S _ hne hbdd
  set T : Set X := Subtype.val '' S with hT_def
  have hT_sub : T ⊆ (B : Set X) := by
    rintro _ ⟨⟨a, ha⟩, _, rfl⟩; exact ha
  have hT_ne : T.Nonempty := hne.image _
  obtain ⟨u, hu⟩ := hbdd
  have hT_bdd : BddAbove T :=
    ⟨u.1, by rintro _ ⟨v, hv, rfl⟩; exact hu hv⟩
  have hT_lub : IsLUB T (sSup T) := isLUB_csSup hT_ne hT_bdd
  refine ⟨⟨sSup T, B.sSup_mem hT_sub hT_ne hT_lub⟩, ?_, ?_⟩
  · rintro a ha
    change a.1 ≤ sSup T
    exact hT_lub.1 ⟨a, ha, rfl⟩
  · rintro a hub
    change sSup T ≤ a.1
    exact hT_lub.2 (by rintro _ ⟨b, hb, rfl⟩; exact hub hb)
end Band
end CCLSubtype


