-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_Cutoffs
-- name    : PretorsionImageClosed_LinearQuiver_Cutoffs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T03:59:57.907577+00:00
-- url     : https://prove2.me/theorems/9031b3fe-7b58-5559-a2b1-76d391295244
-- title:
--   Cutoffs
-- statement:
--   Definitions and structural lemmas for Cutoffs, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Cutoffs.lean

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalSets
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_exists_interval_of_epi
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_exists_interval_of_mono
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_ofIntervals_prop_interval
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_def

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Statement
namespace LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
attribute [local instance] Classical.propDecidable
theorem isQuotientClosed_iff (T : Subcategory (Statement.LinRep k n)) :
    T.IsQuotientClosed ↔ ∀ a d d' : Fin n, a ≤ d' → d' ≤ d →
      T.prop (interval k a d) → T.prop (interval k a d') := by
  constructor
  · intro hT a d d' _ hd'd h
    exact hT (intervalProj k a hd'd) inferInstance h
  · intro h X Y f hf hX
    haveI := hf
    apply prop_of_forall_retract T Y
    intro a d had hr
    haveI : Epi (f ≫ hr.r) := epi_comp _ _
    obtain ⟨e, hde, he⟩ := exists_interval_of_epi T had hX (f ≫ hr.r)
    exact h a e d had hde he
theorem isSubobjectClosed_iff (F : Subcategory (Statement.LinRep k n)) :
    F.IsSubobjectClosed ↔ ∀ a a' d : Fin n, a ≤ a' → a' ≤ d →
      F.prop (interval k a d) → F.prop (interval k a' d) := by
  constructor
  · intro hF a a' d haa' _ h
    exact hF (intervalIncl k d haa') inferInstance h
  · intro h X Y f hf hY
    haveI := hf
    apply prop_of_forall_retract F X
    intro a d had hr
    haveI : Mono (hr.i ≫ f) := mono_comp _ _
    obtain ⟨c, hca, hc⟩ := exists_interval_of_mono F had hY (hr.i ≫ f)
    exact h c a d hca had hc
@[ext]
structure RowCutoff (n : ℕ) where
  /-- The cutoff of row `a`: `M_{a,d}` belongs to the subcategory iff `d < β a`. -/
  β : Fin n → ℕ
  le_β : ∀ a, a.val ≤ β a
  β_le : ∀ a, β a ≤ n
@[ext]
structure ColCutoff (n : ℕ) where
  /-- The cutoff of column `d`: `M_{a,d}` belongs to the subcategory iff `α d ≤ a`. -/
  α : Fin n → ℕ
  α_le : ∀ d, α d ≤ d.val + 1
def RowCutoff.subcategory (β : RowCutoff n) : Subcategory (Statement.LinRep k n) :=
  ofIntervals (fun a d => d.val < β.β a)
theorem RowCutoff.prop_interval_iff (β : RowCutoff n) {a d : Fin n} (had : a ≤ d) :
    (β.subcategory (k := k)).prop (interval k a d) ↔ d.val < β.β a :=
  ofIntervals_prop_interval _ had
theorem RowCutoff.isQuotientClosed (β : RowCutoff n) :
    (β.subcategory (k := k)).IsQuotientClosed := by
  rw [isQuotientClosed_iff]
  intro a d d' had' hd'd h
  rw [β.prop_interval_iff (had'.trans hd'd)] at h
  rw [β.prop_interval_iff had']
  exact lt_of_le_of_lt (Fin.le_def.1 hd'd) h
def ColCutoff.subcategory (α : ColCutoff n) : Subcategory (Statement.LinRep k n) :=
  ofIntervals (fun a d => α.α d ≤ a.val)
theorem ColCutoff.prop_interval_iff (α : ColCutoff n) {a d : Fin n} (had : a ≤ d) :
    (α.subcategory (k := k)).prop (interval k a d) ↔ α.α d ≤ a.val :=
  ofIntervals_prop_interval _ had
theorem ColCutoff.isSubobjectClosed (α : ColCutoff n) :
    (α.subcategory (k := k)).IsSubobjectClosed := by
  rw [isSubobjectClosed_iff]
  intro a a' d haa' ha'd h
  rw [α.prop_interval_iff (haa'.trans ha'd)] at h
  rw [α.prop_interval_iff ha'd]
  exact h.trans (Fin.le_def.1 haa')
def rowCutoff (T : Subcategory (Statement.LinRep k n)) : RowCutoff n where
  β a := Nat.findGreatest
    (fun m => m = a.val ∨ ∃ d : Fin n, d.val + 1 = m ∧ a ≤ d ∧ T.prop (interval k a d)) n
  le_β a := Nat.le_findGreatest a.isLt.le (Or.inl rfl)
  β_le _ := Nat.findGreatest_le _
theorem prop_interval_iff_lt_rowCutoff {T : Subcategory (Statement.LinRep k n)}
    (hT : T.IsQuotientClosed) {a d : Fin n} (had : a ≤ d) :
    T.prop (interval k a d) ↔ d.val < (rowCutoff T).β a := by
  constructor
  · intro h
    exact Nat.le_findGreatest d.isLt (Or.inr ⟨d, rfl, had, h⟩)
  · intro h
    have hspec := Nat.findGreatest_spec (P := fun m => m = a.val ∨
      ∃ d : Fin n, d.val + 1 = m ∧ a ≤ d ∧ T.prop (interval k a d)) a.isLt.le (Or.inl rfl)
    change (rowCutoff T).β a = a.val ∨ ∃ d' : Fin n, d'.val + 1 = (rowCutoff T).β a ∧ a ≤ d' ∧
      T.prop (interval k a d') at hspec
    rcases hspec with h0 | ⟨d', hd', had', hd'T⟩
    · exact absurd (h.trans_eq h0) (not_lt.2 (Fin.le_def.1 had))
    · have hdd' : d ≤ d' := Fin.le_def.2 (by omega)
      exact (isQuotientClosed_iff T).1 hT a d' d had hdd' hd'T
def colCutoff (F : Subcategory (Statement.LinRep k n)) : ColCutoff n where
  α d := Nat.find (p := fun m => m = d.val + 1 ∨
    ∃ a : Fin n, a.val = m ∧ a ≤ d ∧ F.prop (interval k a d)) ⟨d.val + 1, Or.inl rfl⟩
  α_le d := Nat.find_min' _ (Or.inl rfl)
theorem prop_interval_iff_colCutoff_le {F : Subcategory (Statement.LinRep k n)}
    (hF : F.IsSubobjectClosed) {a d : Fin n} (had : a ≤ d) :
    F.prop (interval k a d) ↔ (colCutoff F).α d ≤ a.val := by
  constructor
  · intro h
    exact Nat.find_min' _ (Or.inr ⟨a, rfl, had, h⟩)
  · intro h
    have hspec := Nat.find_spec (p := fun m => m = d.val + 1 ∨
      ∃ a : Fin n, a.val = m ∧ a ≤ d ∧ F.prop (interval k a d)) ⟨d.val + 1, Or.inl rfl⟩
    change (colCutoff F).α d = d.val + 1 ∨ ∃ a' : Fin n, a'.val = (colCutoff F).α d ∧ a' ≤ d ∧
      F.prop (interval k a' d) at hspec
    rcases hspec with h0 | ⟨a', ha', ha'd, ha'F⟩
    · have := Fin.le_def.1 had
      omega
    · have haa' : a' ≤ a := Fin.le_def.2 (by omega)
      exact (isSubobjectClosed_iff F).1 hF a' a d haa' had ha'F
theorem RowCutoff.eq_of_forall_iff (β β' : RowCutoff n)
    (h : ∀ a d : Fin n, a ≤ d → (d.val < β.β a ↔ d.val < β'.β a)) : β = β' := by
  ext a
  by_contra hne
  wlog hlt : β.β a < β'.β a generalizing β β'
  · exact this β' β (fun a d had => (h a d had).symm) (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  · have hd : β.β a < n := hlt.trans_le (β'.β_le a)
    have had : a ≤ (⟨β.β a, hd⟩ : Fin n) := Fin.le_def.2 (β.le_β a)
    have := (h a ⟨β.β a, hd⟩ had).2 hlt
    exact lt_irrefl _ this
theorem ColCutoff.eq_of_forall_iff (α α' : ColCutoff n)
    (h : ∀ a d : Fin n, a ≤ d → (α.α d ≤ a.val ↔ α'.α d ≤ a.val)) : α = α' := by
  ext d
  by_contra hne
  wlog hlt : α.α d < α'.α d generalizing α α'
  · exact this α' α (fun a d had => (h a d had).symm) (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  · have ha : α.α d < n := by have := α'.α_le d; have := d.isLt; omega
    have had : (⟨α.α d, ha⟩ : Fin n) ≤ d := Fin.le_def.2 (by have := α'.α_le d; simp only; omega)
    have := (h ⟨α.α d, ha⟩ d had).1 le_rfl
    simp only at this
    omega
theorem rowCutoff_subcategory {T : Subcategory (Statement.LinRep k n)} (hT : T.IsQuotientClosed) :
    (rowCutoff T).subcategory = T := by
  symm
  apply subcategory_ext_intervals
  intro a d had
  rw [RowCutoff.prop_interval_iff _ had, prop_interval_iff_lt_rowCutoff hT had]
theorem rowCutoff_of_subcategory (β : RowCutoff n) : rowCutoff (β.subcategory (k := k)) = β := by
  apply RowCutoff.eq_of_forall_iff
  intro a d had
  rw [← prop_interval_iff_lt_rowCutoff (β.isQuotientClosed (k := k)) had, β.prop_interval_iff had]
theorem colCutoff_subcategory {F : Subcategory (Statement.LinRep k n)} (hF : F.IsSubobjectClosed) :
    (colCutoff F).subcategory = F := by
  symm
  apply subcategory_ext_intervals
  intro a d had
  rw [ColCutoff.prop_interval_iff _ had, prop_interval_iff_colCutoff_le hF had]
theorem colCutoff_of_subcategory (α : ColCutoff n) : colCutoff (α.subcategory (k := k)) = α := by
  apply ColCutoff.eq_of_forall_iff
  intro a d had
  rw [← prop_interval_iff_colCutoff_le (α.isSubobjectClosed (k := k)) had, α.prop_interval_iff had]
def quotientClosedEquiv :
    {T : Subcategory (Statement.LinRep k n) // T.IsQuotientClosed} ≃ RowCutoff n where
  toFun T := rowCutoff T.1
  invFun β := ⟨β.subcategory, β.isQuotientClosed⟩
  left_inv T := Subtype.ext (rowCutoff_subcategory T.2)
  right_inv β := rowCutoff_of_subcategory β
def subobjectClosedEquiv :
    {F : Subcategory (Statement.LinRep k n) // F.IsSubobjectClosed} ≃ ColCutoff n where
  toFun F := colCutoff F.1
  invFun α := ⟨α.subcategory, α.isSubobjectClosed⟩
  left_inv F := Subtype.ext (colCutoff_subcategory F.2)
  right_inv α := colCutoff_of_subcategory α
end LinearQuiver
end PretorsionImageClosed


