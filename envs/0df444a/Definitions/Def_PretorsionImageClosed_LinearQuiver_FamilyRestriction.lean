-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
-- name    : PretorsionImageClosed_LinearQuiver_FamilyRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T04:04:37.606214+00:00
-- url     : https://prove2.me/theorems/e2e7cc41-7fd5-4c7b-97d6-1fa4f0f306b4
-- title:
--   Family Restriction
-- statement:
--   Definitions and structural lemmas for Family Restriction, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open Statement Polynomial Finset
namespace LinearQuiver
variable {n : ℕ}
theorem castSucc_max (a c : Fin n) : (max a c).castSucc = max a.castSucc c.castSucc :=
  Monotone.map_max (fun _ _ h => Fin.castSucc_le_castSucc_iff.2 h)
theorem castSucc_min (a c : Fin n) : (min a c).castSucc = min a.castSucc c.castSucc :=
  Monotone.map_min (fun _ _ h => Fin.castSucc_le_castSucc_iff.2 h)
def IntervalFamily.restrict (D : IntervalFamily (n + 1)) : IntervalFamily n where
  D := univ.filter (fun p : Fin n × Fin n => (p.1.castSucc, p.2.castSucc) ∈ D.D)
  le_of_mem p hp := Fin.castSucc_le_castSucc_iff.1 (D.le_of_mem _ (Finset.mem_filter.1 hp).2)
theorem mem_restrict {D : IntervalFamily (n + 1)} {p : Fin n × Fin n} :
    p ∈ D.restrict.D ↔ (p.1.castSucc, p.2.castSucc) ∈ D.D := by
  simp [IntervalFamily.restrict]
theorem IntervalFamily.IsClosed.restrict {D : IntervalFamily (n + 1)} (hD : D.IsClosed) :
    D.restrict.IsClosed := by
  intro a b c d hab hcd hmin
  rw [mem_restrict] at hab hcd ⊢
  have := hD _ _ _ _ hab hcd
    (by rw [← castSucc_max, ← castSucc_min]; exact Fin.castSucc_le_castSucc_iff.2 hmin)
  rwa [← castSucc_max, ← castSucc_min] at this
def ClosedFamily.restrict (D : ClosedFamily (n + 1)) : ClosedFamily n := ⟨D.1.restrict, D.2.restrict⟩
def admFin (D : IntervalFamily n) : Finset (Fin n) :=
  univ.filter (fun a => ∀ p ∈ D.D, p.1 ≤ a → a ≤ p.2 → (a, p.2) ∈ D.D)
def adm (D : IntervalFamily n) : Finset (Fin (n + 1)) :=
  insert (Fin.last n) ((admFin D).map Fin.castSuccEmb)
theorem mem_admFin {D : IntervalFamily n} {a : Fin n} :
    a ∈ admFin D ↔ ∀ p ∈ D.D, p.1 ≤ a → a ≤ p.2 → (a, p.2) ∈ D.D := by
  simp [admFin]
theorem last_mem_adm (D : IntervalFamily n) : Fin.last n ∈ adm D := Finset.mem_insert_self _ _
theorem castSucc_mem_adm {D : IntervalFamily n} {a : Fin n} : a.castSucc ∈ adm D ↔ a ∈ admFin D := by
  simp [adm, (Fin.castSucc_lt_last a).ne]
open Classical in
/-- The extension `D_J` of `D` by the intervals `[a, n]`, `a ∈ J` (Construction 8.3). -/
def IntervalFamily.glue (D : IntervalFamily n) (J : Finset (Fin (n + 1))) : IntervalFamily (n + 1) where
  D := univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
    (∃ a d : Fin n, p = (a.castSucc, d.castSucc) ∧ (a, d) ∈ D.D) ∨ (p.2 = Fin.last n ∧ p.1 ∈ J))
  le_of_mem p hp := by
    rw [Finset.mem_filter] at hp
    rcases hp.2 with ⟨a, d, rfl, had⟩ | ⟨h2, -⟩
    · exact Fin.castSucc_le_castSucc_iff.2 (D.le_of_mem _ had)
    · rw [h2]
      exact Fin.le_last _
theorem mem_glue {D : IntervalFamily n} {J : Finset (Fin (n + 1))} {p : Fin (n + 1) × Fin (n + 1)} :
    p ∈ (D.glue J).D ↔
      (∃ a d : Fin n, p = (a.castSucc, d.castSucc) ∧ (a, d) ∈ D.D) ∨ (p.2 = Fin.last n ∧ p.1 ∈ J) := by
  show p ∈ univ.filter _ ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
theorem mem_glue_castSucc {D : IntervalFamily n} {J : Finset (Fin (n + 1))} {a d : Fin n} :
    (a.castSucc, d.castSucc) ∈ (D.glue J).D ↔ (a, d) ∈ D.D := by
  rw [mem_glue]
  constructor
  · rintro (⟨a', d', h, had⟩ | ⟨h, -⟩)
    · rw [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [Fin.castSucc_inj] at h1 h2
      rw [h1, h2]
      exact had
    · exact absurd h (Fin.castSucc_lt_last d).ne
  · intro h
    exact Or.inl ⟨a, d, rfl, h⟩
theorem mem_glue_last {D : IntervalFamily n} {J : Finset (Fin (n + 1))} {a : Fin (n + 1)} :
    (a, Fin.last n) ∈ (D.glue J).D ↔ a ∈ J := by
  rw [mem_glue]
  constructor
  · rintro (⟨a', d', h, -⟩ | ⟨-, h⟩)
    · rw [Prod.mk.injEq] at h
      exact absurd h.2.symm (Fin.castSucc_lt_last d').ne
    · exact h
  · intro h
    exact Or.inr ⟨rfl, h⟩
def JOf (D : IntervalFamily (n + 1)) : Finset (Fin (n + 1)) :=
  univ.filter (fun a => (a, Fin.last n) ∈ D.D)
theorem mem_JOf {D : IntervalFamily (n + 1)} {a : Fin (n + 1)} : a ∈ JOf D ↔ (a, Fin.last n) ∈ D.D := by
  simp [JOf]
theorem JOf_subset_adm {D : IntervalFamily (n + 1)} (hD : D.IsClosed) : JOf D ⊆ adm D.restrict := by
  intro a ha
  rw [mem_JOf] at ha
  induction a using Fin.lastCases with
  | last => exact last_mem_adm _
  | cast a =>
    rw [castSucc_mem_adm, mem_admFin]
    intro p hp h1 h2
    rw [mem_restrict] at hp ⊢
    have := hD _ _ _ _ hp ha (by
      rw [max_eq_right (Fin.castSucc_le_castSucc_iff.2 h1), min_eq_left (Fin.le_last _)]
      exact Fin.castSucc_le_castSucc_iff.2 h2)
    rwa [max_eq_right (Fin.castSucc_le_castSucc_iff.2 h1), min_eq_left (Fin.le_last _)] at this
theorem IntervalFamily.IsClosed.glue {D : IntervalFamily n} (hD : D.IsClosed) {J : Finset (Fin (n + 1))}
    (hJ : J ⊆ adm D) : (D.glue J).IsClosed := by
  -- a new interval `[c, n]` meets an old interval `[a, b]` in `[max a c, b]`
  have key : ∀ (a b : Fin n) (c : Fin (n + 1)), (a, b) ∈ D.D → c ∈ J →
      max a.castSucc c ≤ b.castSucc → (max a.castSucc c, b.castSucc) ∈ (D.glue J).D := by
    intro a b c hab hc hmin
    rcases le_total c a.castSucc with hca | hac
    · rw [max_eq_left hca]
      exact mem_glue_castSucc.2 hab
    · rw [max_eq_right hac] at hmin ⊢
      induction c using Fin.lastCases with
      | last => exact absurd hmin (not_le.2 (Fin.castSucc_lt_last b))
      | cast c =>
        have hc' : c ∈ admFin D := castSucc_mem_adm.1 (hJ hc)
        rw [mem_admFin] at hc'
        exact mem_glue_castSucc.2 (hc' (a, b) hab (Fin.castSucc_le_castSucc_iff.1 hac)
          (Fin.castSucc_le_castSucc_iff.1 hmin))
  intro a b c d hab hcd hmin
  rw [mem_glue] at hab hcd
  rcases hab with ⟨a', b', hab', hab⟩ | ⟨hb, ha⟩ <;> rcases hcd with ⟨c', d', hcd', hcd⟩ | ⟨hd, hc⟩
  · rw [Prod.mk.injEq] at hab' hcd'
    obtain ⟨rfl, rfl⟩ := hab'
    obtain ⟨rfl, rfl⟩ := hcd'
    rw [← castSucc_max, ← castSucc_min] at hmin ⊢
    exact mem_glue_castSucc.2 (hD _ _ _ _ hab hcd (Fin.castSucc_le_castSucc_iff.1 hmin))
  · rw [Prod.mk.injEq] at hab'
    obtain ⟨rfl, rfl⟩ := hab'
    have hd' : d = Fin.last n := hd
    have hc' : c ∈ J := hc
    rw [hd', min_eq_left (Fin.le_last _)] at hmin ⊢
    exact key a' b' c hab hc' hmin
  · rw [Prod.mk.injEq] at hcd'
    obtain ⟨rfl, rfl⟩ := hcd'
    have hb' : b = Fin.last n := hb
    have ha' : a ∈ J := ha
    rw [hb', min_eq_right (Fin.le_last _), max_comm] at hmin ⊢
    exact key c' d' a hcd ha' hmin
  · have hb' : b = Fin.last n := hb
    have hd' : d = Fin.last n := hd
    have ha' : a ∈ J := ha
    have hc' : c ∈ J := hc
    rw [hb', hd', min_self, mem_glue_last]
    rcases max_choice a c with h | h <;> rw [h]
    · exact ha'
    · exact hc'
def ClosedFamily.glue (D : ClosedFamily n) (J : Finset (Fin (n + 1))) (hJ : J ⊆ adm D.1) :
    ClosedFamily (n + 1) :=
  ⟨D.1.glue J, D.2.glue hJ⟩
noncomputable instance : DecidableEq (ClosedFamily n) := Classical.decEq _
def fSum (n : ℕ) : Rq[X] := ∑ D : ClosedFamily n, C (q ^ D.1.D.card) * X ^ (adm D.1).card
def xSum (n : ℕ) : Rq[X] := ∑ D : ClosedFamily n, fWeight D
def closedFamilyZero : ClosedFamily 0 :=
  ⟨⟨∅, fun p _ => p.1.elim0⟩, fun a => a.elim0⟩
instance : Subsingleton (ClosedFamily 0) :=
  ⟨fun D E => Subtype.ext (IntervalFamily.ext
    ((Finset.eq_empty_of_isEmpty D.1.D).trans (Finset.eq_empty_of_isEmpty E.1.D).symm))⟩
def gandhiSecondOf : ℕ → Rq[X]
  | 0 => 0
  | 1 => 1
  | m + 2 => (fSum m).comp U
end LinearQuiver
end PretorsionImageClosed


