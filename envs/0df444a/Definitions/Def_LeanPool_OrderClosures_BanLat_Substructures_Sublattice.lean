-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
-- name    : LeanPool_OrderClosures_BanLat_Substructures_Sublattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:23:35.624416+00:00
-- url     : https://prove2.me/theorems/6da537e3-2b26-4d77-8baf-3ea5cf9b016b
-- title:
--   Sublattice
-- statement:
--   Definitions and structural lemmas for Sublattice, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Order.Sublattice
public import Mathlib.Order.SupClosed
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
public import Theorems.Thm_NormedVectorLattice_continuous_sup
public import Theorems.Thm_inf_eq_sub_posPart
public import Theorems.Thm_nonneg_smul_inf
public import Theorems.Thm_nonneg_smul_sup
public import Theorems.Thm_sup_eq_add_posPart
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


set_option autoImplicit true
@[expose] public section
@[expose] public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace PointedCone
omit [VectorLattice X] in
/-- If `s` is closed under addition, so is its sup-closure. -/
theorem add_mem_supClosure_of_addClosed {s : Set X}
    (hadd : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a + b ∈ s)
    {x y : X} (hx : x ∈ _root_.supClosure s) (hy : y ∈ _root_.supClosure s) :
    x + y ∈ _root_.supClosure s := by
  have step : ∀ a ∈ s, ∀ b ∈ _root_.supClosure s, a + b ∈ _root_.supClosure s := by
    intro a ha b hb
    have h_sc : SupClosed {c : X | a + c ∈ _root_.supClosure s} := fun u hu v hv => by
      change a + (u ⊔ v) ∈ _root_.supClosure s
      rw [add_sup]; exact supClosed_supClosure hu hv
    have hsub : s ⊆ {c : X | a + c ∈ _root_.supClosure s} :=
      fun c hc => subset_supClosure (hadd ha hc)
    exact supClosure_min hsub h_sc hb
  have h_sc : SupClosed {c : X | c + y ∈ _root_.supClosure s} := fun u hu v hv => by
    change (u ⊔ v) + y ∈ _root_.supClosure s
    rw [sup_add]; exact supClosed_supClosure hu hv
  have hsub : s ⊆ {c : X | c + y ∈ _root_.supClosure s} :=
    fun c hc => step c hc y hy
  exact supClosure_min hsub h_sc hx
theorem smul_mem_supClosure_of_smulClosed {s : Set X}
    (hsmul : ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x⦄, x ∈ s → a • x ∈ s)
    {a : ℝ} (ha : 0 ≤ a) {x : X} (hx : x ∈ _root_.supClosure s) :
    a • x ∈ _root_.supClosure s := by
  have h_sc : SupClosed {c : X | a • c ∈ _root_.supClosure s} := fun u hu v hv => by
    change a • (u ⊔ v) ∈ _root_.supClosure s
    rw [nonneg_smul_sup u v a ha]; exact supClosed_supClosure hu hv
  have hsub : s ⊆ {c : X | a • c ∈ _root_.supClosure s} :=
    fun c hc => subset_supClosure (hsmul ha hc)
  exact supClosure_min hsub h_sc hx
omit [VectorLattice X] in
/-- If `s` is closed under addition, so is its inf-closure. -/
theorem add_mem_infClosure_of_addClosed {s : Set X}
    (hadd : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a + b ∈ s)
    {x y : X} (hx : x ∈ _root_.infClosure s) (hy : y ∈ _root_.infClosure s) :
    x + y ∈ _root_.infClosure s := by
  have step : ∀ a ∈ s, ∀ b ∈ _root_.infClosure s, a + b ∈ _root_.infClosure s := by
    intro a ha b hb
    have h_ic : InfClosed {c : X | a + c ∈ _root_.infClosure s} := fun u hu v hv => by
      change a + (u ⊓ v) ∈ _root_.infClosure s
      rw [add_inf]; exact infClosed_infClosure hu hv
    have hsub : s ⊆ {c : X | a + c ∈ _root_.infClosure s} :=
      fun c hc => subset_infClosure (hadd ha hc)
    exact infClosure_min hsub h_ic hb
  have h_ic : InfClosed {c : X | c + y ∈ _root_.infClosure s} := fun u hu v hv => by
    change (u ⊓ v) + y ∈ _root_.infClosure s
    rw [inf_add]; exact infClosed_infClosure hu hv
  have hsub : s ⊆ {c : X | c + y ∈ _root_.infClosure s} :=
    fun c hc => step c hc y hy
  exact infClosure_min hsub h_ic hx
theorem smul_mem_infClosure_of_smulClosed {s : Set X}
    (hsmul : ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x⦄, x ∈ s → a • x ∈ s)
    {a : ℝ} (ha : 0 ≤ a) {x : X} (hx : x ∈ _root_.infClosure s) :
    a • x ∈ _root_.infClosure s := by
  have h_ic : InfClosed {c : X | a • c ∈ _root_.infClosure s} := fun u hu v hv => by
    change a • (u ⊓ v) ∈ _root_.infClosure s
    rw [nonneg_smul_inf u v a ha]; exact infClosed_infClosure hu hv
  have hsub : s ⊆ {c : X | a • c ∈ _root_.infClosure s} :=
    fun c hc => subset_infClosure (hsmul ha hc)
  exact infClosure_min hsub h_ic hx
def supClosure (C : PointedCone ℝ X) : PointedCone ℝ X where
  carrier := _root_.supClosure (C : Set X)
  zero_mem' := subset_supClosure C.zero_mem
  add_mem' hx hy := add_mem_supClosure_of_addClosed (fun _ hx _ hy => C.add_mem hx hy) hx hy
  smul_mem' c _ hx :=
    smul_mem_supClosure_of_smulClosed (fun _ ha _ hx => C.smul_mem ha hx) c.2 hx
@[simp]
theorem coe_supClosure (C : PointedCone ℝ X) :
    (supClosure C : Set X) = _root_.supClosure (C : Set X) := rfl
def infClosure (C : PointedCone ℝ X) : PointedCone ℝ X where
  carrier := _root_.infClosure (C : Set X)
  zero_mem' := subset_infClosure C.zero_mem
  add_mem' hx hy := add_mem_infClosure_of_addClosed (fun _ hx _ hy => C.add_mem hx hy) hx hy
  smul_mem' c _ hx :=
    smul_mem_infClosure_of_smulClosed (fun _ ha _ hx => C.smul_mem ha hx) c.2 hx
@[simp]
theorem coe_infClosure (C : PointedCone ℝ X) :
    (infClosure C : Set X) = _root_.infClosure (C : Set X) := rfl
end PointedCone
structure VectorSublattice (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] extends Submodule ℝ X where
  sup_mem' : ∀ {x y : X}, x ∈ carrier → y ∈ carrier → x ⊔ y ∈ carrier
namespace VectorSublattice
instance : SetLike (VectorSublattice X) X where
  coe Y := Y.carrier
  coe_injective p q h := by
    cases p; cases q; congr
    exact SetLike.ext' h
variable (Y : VectorSublattice X)
theorem sup_mem {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) :
    x ⊔ y ∈ Y :=
  Y.sup_mem' hx hy
theorem inf_mem {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) :
    x ⊓ y ∈ Y := by
  rw [inf_eq_sub_posPart x y]
  exact Y.toSubmodule.sub_mem hx (Y.sup_mem' (Y.toSubmodule.sub_mem hx hy) (Y.toSubmodule.zero_mem))
theorem posPart_mem_of_absClosed (M : Submodule ℝ X)
    (h : ∀ x : X, x ∈ M → |x| ∈ M) {x : X} (hx : x ∈ M) : x⁺ ∈ M := by
  have key : x + |x| = 2 • x⁺ := add_abs_eq_two_nsmul_posPart x
  have h2 : (2 : ℝ)⁻¹ • (x + |x|) = x⁺ := by
    rw [key, ← Nat.cast_smul_eq_nsmul ℝ 2]; norm_num [smul_smul]
  rw [← h2]
  exact M.smul_mem _ (M.add_mem hx (h x hx))
def ofAbsClosed (M : Submodule ℝ X)
    (h : ∀ x : X, x ∈ M → |x| ∈ M) : VectorSublattice X where
  toSubmodule := M
  sup_mem' := fun {x y} hx hy => by
    rw [sup_eq_add_posPart x y]
    exact M.add_mem hx (posPart_mem_of_absClosed M h (M.sub_mem hy hx))
instance : CoeHead (VectorSublattice X) (PointedCone ℝ X) where
  coe Y :=
    { toAddSubmonoid := Y.toSubmodule.toAddSubmonoid
      smul_mem' := fun c _ hx => Y.toSubmodule.smul_mem c.1 hx }
noncomputable instance instLatticeSubtype : Lattice ↥Y.toSubmodule :=
  Subtype.lattice (P := fun x => x ∈ Y.toSubmodule)
    (fun _ _ hx hy => Y.sup_mem hx hy) (fun _ _ hx hy => Y.inf_mem hx hy)
instance instIsOrderedAddMonoidSubtype :
    IsOrderedAddMonoid ↥Y.toSubmodule where
  add_le_add_left := by
    intro a b (h : a.1 ≤ b.1) c; exact add_le_add_left h c.1
  add_le_add_right := by
    intro a b (h : a.1 ≤ b.1) c; exact add_le_add_right h c.1
instance instPosSMulMonoSubtype : PosSMulMono ℝ ↥Y.toSubmodule where
  smul_le_smul_of_nonneg_left := by
    intro a ha b₁ b₂ h
    change (a • b₁).1 ≤ (a • b₂).1
    exact smul_le_smul_of_nonneg_left h ha
instance instVectorLatticeSubtype : VectorLattice ↥Y.toSubmodule := ⟨⟩
instance : PartialOrder (VectorSublattice X) :=
  PartialOrder.lift (fun Y => (Y : Set X)) SetLike.coe_injective
instance : Top (VectorSublattice X) where
  top :=
    { toSubmodule := ⊤
      sup_mem' := fun _ _ => Submodule.mem_top }
instance : Bot (VectorSublattice X) where
  bot :=
    { toSubmodule := ⊥
      sup_mem' := fun {x y} hx hy => by
        have hx' : x = 0 := (Submodule.mem_bot ℝ).mp hx
        have hy' : y = 0 := (Submodule.mem_bot ℝ).mp hy
        rw [hx', hy', sup_idem]; exact Submodule.zero_mem _ }
instance : InfSet (VectorSublattice X) where
  sInf S :=
    { toSubmodule := sInf ((·.toSubmodule) '' S)
      sup_mem' := fun {x y} hx hy => by
        have hx' := (Submodule.mem_sInf).mp hx
        have hy' := (Submodule.mem_sInf).mp hy
        refine (Submodule.mem_sInf).mpr ?_
        rintro _ ⟨Y, hY, rfl⟩
        exact Y.sup_mem (hx' _ ⟨Y, hY, rfl⟩) (hy' _ ⟨Y, hY, rfl⟩) }
def generated (s : Set X) : VectorSublattice X :=
  sInf {Y : VectorSublattice X | s ⊆ Y}
lemma latticeClosure_add_mem_of_submodule (M : Submodule ℝ X)
    {x y : X} (hx : x ∈ latticeClosure (M : Set X))
    (hy : y ∈ latticeClosure (M : Set X)) :
    x + y ∈ latticeClosure (M : Set X) := by
  let := AddCommGroup.toDistribLattice X
  refine latticeClosure_sup_inf_induction
    (p := fun a _ => a + y ∈ latticeClosure (M : Set X)) ?_ ?_ ?_ hx
  · intro a ha
    refine latticeClosure_sup_inf_induction
      (p := fun b _ => a + b ∈ latticeClosure (M : Set X)) ?_ ?_ ?_ hy
    · intro b hb; exact subset_latticeClosure (M.add_mem ha hb)
    · intro p _ q _ h₁ h₂
      rw [add_sup]; exact isSublattice_latticeClosure.supClosed h₁ h₂
    · intro p _ q _ h₁ h₂
      rw [add_inf]; exact isSublattice_latticeClosure.infClosed h₁ h₂
  · intro p _ q _ h₁ h₂
    rw [sup_add]; exact isSublattice_latticeClosure.supClosed h₁ h₂
  · intro p _ q _ h₁ h₂
    rw [inf_add]; exact isSublattice_latticeClosure.infClosed h₁ h₂
lemma latticeClosure_smul_mem_of_submodule (M : Submodule ℝ X)
    (c : ℝ) {x : X} (hx : x ∈ latticeClosure (M : Set X)) :
    c • x ∈ latticeClosure (M : Set X) := by
  let := AddCommGroup.toDistribLattice X
  rcases le_or_gt 0 c with hc | hc
  · refine latticeClosure_sup_inf_induction
      (p := fun a _ => c • a ∈ latticeClosure (M : Set X)) ?_ ?_ ?_ hx
    · intro a ha; exact subset_latticeClosure (M.smul_mem c ha)
    · intro p _ q _ h₁ h₂
      rw [nonneg_smul_sup p q c hc]
      exact isSublattice_latticeClosure.supClosed h₁ h₂
    · intro p _ q _ h₁ h₂
      rw [nonneg_smul_inf p q c hc]
      exact isSublattice_latticeClosure.infClosed h₁ h₂
  · have hc' : 0 ≤ -c := by linarith
    refine latticeClosure_sup_inf_induction
      (p := fun a _ => c • a ∈ latticeClosure (M : Set X)) ?_ ?_ ?_ hx
    · intro a ha; exact subset_latticeClosure (M.smul_mem c ha)
    · intro p _ q _ h₁ h₂
      have eq : c • (p ⊔ q) = (c • p) ⊓ (c • q) := by
        rw [show c • (p ⊔ q) = -((-c) • (p ⊔ q)) by rw [neg_smul, neg_neg],
          nonneg_smul_sup p q (-c) hc', neg_sup, neg_smul, neg_neg, neg_smul, neg_neg]
      rw [eq]
      exact isSublattice_latticeClosure.infClosed h₁ h₂
    · intro p _ q _ h₁ h₂
      have eq : c • (p ⊓ q) = (c • p) ⊔ (c • q) := by
        rw [show c • (p ⊓ q) = -((-c) • (p ⊓ q)) by rw [neg_smul, neg_neg],
          nonneg_smul_inf p q (-c) hc', neg_inf, neg_smul, neg_neg, neg_smul, neg_neg]
      rw [eq]
      exact isSublattice_latticeClosure.supClosed h₁ h₂
def sublatticeOfSubmoduleLatticeClosure (M : Submodule ℝ X) :
    VectorSublattice X where
  toSubmodule :=
    { carrier := latticeClosure (M : Set X)
      zero_mem' := subset_latticeClosure M.zero_mem
      add_mem' := latticeClosure_add_mem_of_submodule M
      smul_mem' := latticeClosure_smul_mem_of_submodule M }
  sup_mem' := fun {_ _} hx hy => by
    let := AddCommGroup.toDistribLattice X
    exact isSublattice_latticeClosure.supClosed hx hy
open scoped Pointwise in
/-- The difference set `supClosure C - supClosure C` of a pointed cone is a
vector sublattice. -/
def sublatticeOfConeSupClosureDiff (C : PointedCone ℝ X) :
    VectorSublattice X where
  toSubmodule :=
    { carrier := _root_.supClosure (C : Set X) - _root_.supClosure (C : Set X)
      zero_mem' :=
        ⟨0, subset_supClosure C.zero_mem, 0, subset_supClosure C.zero_mem, sub_self 0⟩
      add_mem' := by
        rintro _ _ ⟨u₁, hu₁, v₁, hv₁, rfl⟩ ⟨u₂, hu₂, v₂, hv₂, rfl⟩
        refine ⟨u₁ + u₂, ?_, v₁ + v₂, ?_, ?_⟩
        · exact PointedCone.add_mem_supClosure_of_addClosed
            (fun _ h _ h' => C.add_mem h h') hu₁ hu₂
        · exact PointedCone.add_mem_supClosure_of_addClosed
            (fun _ h _ h' => C.add_mem h h') hv₁ hv₂
        · change (u₁ + u₂) - (v₁ + v₂) = (u₁ - v₁) + (u₂ - v₂); abel
      smul_mem' := by
        rintro c _ ⟨u, hu, v, hv, rfl⟩
        rcases le_or_gt 0 c with hc | hc
        · refine ⟨c • u, ?_, c • v, ?_, ?_⟩
          · exact PointedCone.smul_mem_supClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc hu
          · exact PointedCone.smul_mem_supClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc hv
          · change c • u - c • v = c • (u - v); rw [smul_sub]
        · have hc' : 0 ≤ -c := by linarith
          refine ⟨(-c) • v, ?_, (-c) • u, ?_, ?_⟩
          · exact PointedCone.smul_mem_supClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc' hv
          · exact PointedCone.smul_mem_supClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc' hu
          · change (-c) • v - (-c) • u = c • (u - v)
            rw [smul_sub, neg_smul, neg_smul]; abel }
  sup_mem' := by
    rintro _ _ ⟨u₁, hu₁, v₁, hv₁, rfl⟩ ⟨u₂, hu₂, v₂, hv₂, rfl⟩
    refine ⟨(u₁ + v₂) ⊔ (u₂ + v₁), ?_, v₁ + v₂, ?_, ?_⟩
    · exact supClosed_supClosure
        (PointedCone.add_mem_supClosure_of_addClosed
          (fun _ h _ h' => C.add_mem h h') hu₁ hv₂)
        (PointedCone.add_mem_supClosure_of_addClosed
          (fun _ h _ h' => C.add_mem h h') hu₂ hv₁)
    · exact PointedCone.add_mem_supClosure_of_addClosed
        (fun _ h _ h' => C.add_mem h h') hv₁ hv₂
    · have h : ((u₁ - v₁) ⊔ (u₂ - v₂)) + (v₁ + v₂) = (u₁ + v₂) ⊔ (u₂ + v₁) := by
        rw [sup_add]; congr 1 <;> abel
      change ((u₁ + v₂) ⊔ (u₂ + v₁)) - (v₁ + v₂) = (u₁ - v₁) ⊔ (u₂ - v₂)
      rw [← h]; abel
open scoped Pointwise in
/-- The difference set `infClosure C - infClosure C` of a pointed cone is a
vector sublattice. -/
def sublatticeOfConeInfClosureDiff (C : PointedCone ℝ X) :
    VectorSublattice X where
  toSubmodule :=
    { carrier := _root_.infClosure (C : Set X) - _root_.infClosure (C : Set X)
      zero_mem' :=
        ⟨0, subset_infClosure C.zero_mem, 0, subset_infClosure C.zero_mem, sub_self 0⟩
      add_mem' := by
        rintro _ _ ⟨u₁, hu₁, v₁, hv₁, rfl⟩ ⟨u₂, hu₂, v₂, hv₂, rfl⟩
        refine ⟨u₁ + u₂, ?_, v₁ + v₂, ?_, ?_⟩
        · exact PointedCone.add_mem_infClosure_of_addClosed
            (fun _ h _ h' => C.add_mem h h') hu₁ hu₂
        · exact PointedCone.add_mem_infClosure_of_addClosed
            (fun _ h _ h' => C.add_mem h h') hv₁ hv₂
        · change (u₁ + u₂) - (v₁ + v₂) = (u₁ - v₁) + (u₂ - v₂); abel
      smul_mem' := by
        rintro c _ ⟨u, hu, v, hv, rfl⟩
        rcases le_or_gt 0 c with hc | hc
        · refine ⟨c • u, ?_, c • v, ?_, ?_⟩
          · exact PointedCone.smul_mem_infClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc hu
          · exact PointedCone.smul_mem_infClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc hv
          · change c • u - c • v = c • (u - v); rw [smul_sub]
        · have hc' : 0 ≤ -c := by linarith
          refine ⟨(-c) • v, ?_, (-c) • u, ?_, ?_⟩
          · exact PointedCone.smul_mem_infClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc' hv
          · exact PointedCone.smul_mem_infClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc' hu
          · change (-c) • v - (-c) • u = c • (u - v)
            rw [smul_sub, neg_smul, neg_smul]; abel }
  sup_mem' := by
    rintro _ _ ⟨u₁, hu₁, v₁, hv₁, rfl⟩ ⟨u₂, hu₂, v₂, hv₂, rfl⟩
    have hadd : ∀ ⦃a⦄, a ∈ (C : Set X) → ∀ ⦃b⦄, b ∈ (C : Set X) → a + b ∈ (C : Set X) :=
      fun _ ha _ hb => C.add_mem ha hb
    have hu₁v₂ : u₁ + v₂ ∈ _root_.infClosure (C : Set X) :=
      PointedCone.add_mem_infClosure_of_addClosed hadd hu₁ hv₂
    have hu₂v₁ : u₂ + v₁ ∈ _root_.infClosure (C : Set X) :=
      PointedCone.add_mem_infClosure_of_addClosed hadd hu₂ hv₁
    have hv₁v₂ : v₁ + v₂ ∈ _root_.infClosure (C : Set X) :=
      PointedCone.add_mem_infClosure_of_addClosed hadd hv₁ hv₂
    have hinf : (u₁ + v₂) ⊓ (u₂ + v₁) ∈ _root_.infClosure (C : Set X) :=
      infClosed_infClosure hu₁v₂ hu₂v₁
    refine ⟨u₁ + u₂ + v₁ + v₂, ?_, (u₁ + v₂) ⊓ (u₂ + v₁) + (v₁ + v₂), ?_, ?_⟩
    · have heq : u₁ + u₂ + v₁ + v₂ = (u₁ + v₂) + (u₂ + v₁) := by abel
      rw [heq]
      exact PointedCone.add_mem_infClosure_of_addClosed hadd hu₁v₂ hu₂v₁
    · exact PointedCone.add_mem_infClosure_of_addClosed hadd hinf hv₁v₂
    · have step1 : (u₁ + v₂) ⊔ (u₂ + v₁) =
          (u₁ + v₂) + (u₂ + v₁) - (u₁ + v₂) ⊓ (u₂ + v₁) := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact inf_add_sup _ _
      have step2 : ((u₁ - v₁) ⊔ (u₂ - v₂)) + (v₁ + v₂) =
          (u₁ + v₂) ⊔ (u₂ + v₁) := by
        rw [sup_add]; congr 1 <;> abel
      change u₁ + u₂ + v₁ + v₂ - ((u₁ + v₂) ⊓ (u₂ + v₁) + (v₁ + v₂))
        = (u₁ - v₁) ⊔ (u₂ - v₂)
      symm
      calc (u₁ - v₁) ⊔ (u₂ - v₂)
          = ((u₁ + v₂) ⊔ (u₂ + v₁)) - (v₁ + v₂) := by rw [← step2]; abel
        _ = ((u₁ + v₂) + (u₂ + v₁) - (u₁ + v₂) ⊓ (u₂ + v₁)) - (v₁ + v₂) := by rw [← step1]
        _ = u₁ + u₂ + v₁ + v₂ - ((u₁ + v₂) ⊓ (u₂ + v₁) + (v₁ + v₂)) := by abel
end VectorSublattice
namespace LLexpr
variable {n : ℕ}
section Combinations
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
end Combinations
end LLexpr
section Normed
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]
namespace VectorSublattice
variable (Y : VectorSublattice X)
instance instNormedVectorLatticeSubtype :
    NormedVectorLattice ↥Y.toSubmodule where
  solid := by
    intro x y h
    change ‖x.1‖ ≤ ‖y.1‖
    exact HasSolidNorm.solid h
  norm_smul a x := norm_smul a x.1
noncomputable def topologicalClosure (Y : VectorSublattice X) : VectorSublattice X where
  toSubmodule := Y.toSubmodule.topologicalClosure
  sup_mem' := fun {x y} hx hy => by
    have hx' : x ∈ closure (Y.toSubmodule : Set X) := by
      rw [← Submodule.topologicalClosure_coe]; exact hx
    have hy' : y ∈ closure (Y.toSubmodule : Set X) := by
      rw [← Submodule.topologicalClosure_coe]; exact hy
    have hxy : x ⊔ y ∈ closure (Y.toSubmodule : Set X) :=
      map_mem_closure₂ (f := fun a b : X => a ⊔ b)
        NormedVectorLattice.continuous_sup hx' hy'
        (fun _ ha _ hb => Y.sup_mem ha hb)
    rw [← Submodule.topologicalClosure_coe] at hxy
    exact hxy
@[reducible]
noncomputable def banachLatticeSubtype [CompleteSpace X]
    (hclosed : IsClosed (Y : Set X)) : BanachLattice ↥Y.toSubmodule where
  toCompleteSpace := by
    have : IsClosed (Y.toSubmodule : Set X) := hclosed
    infer_instance
end VectorSublattice
end Normed


