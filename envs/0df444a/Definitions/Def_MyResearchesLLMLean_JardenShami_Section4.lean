-- Prove2me | Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
-- name    : MyResearchesLLMLean_JardenShami_Section4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:41:11.953948+00:00
-- url     : https://prove2.me/theorems/acb2f19e-5048-4dae-8932-918955b806c0
-- title:
--   Section4
-- statement:
--   Definitions and structural lemmas for Section4, from Adi Jarden and Ziv Shami; formalization by Adi Jarden's pinned Edge colorings, trees and inaccessible cardinals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
namespace JardenShami
class IsTree (T : Type w) [PartialOrder T] : Prop where
  wellOrder_Iio : ∀ t : T, IsWellOrder (Set.Iio t) (fun x y => (x : T) < y)
namespace Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
def ht (t : T) : Ordinal.{w} :=
  @Ordinal.type (Set.Iio t) (fun x y => (x : T) < y) (IsTree.wellOrder_Iio t)
variable (T) in
/-- **Section 4, preliminaries.** `Lev_α(T)`: the `α`-th level of `T`. -/
def Lev (α : Ordinal.{w}) : Set T := {t | ht t = α}
variable (T) in
/-- **Section 4, preliminaries.** `Lev_{<α}(T)`: the nodes of level smaller than `α` (regarded
as a subtree with the induced order). -/
def LevLt (α : Ordinal.{w}) : Set T := {t | ht t < α}
variable (T) in
/-- **Section 4, preliminaries.** `ht(T)`: the first `α` such that `Lev_α(T) = ∅`. -/
def height : Ordinal.{w} := sInf {α | Lev T α = ∅}
def IsBranch (b : Set T) : Prop := IsMaxChain (· ≤ ·) b
def IsCofinalBranch (b : Set T) : Prop :=
  IsBranch b ∧ ∃ h : IsWellOrder b (fun x y => (x : T) < y),
    @Ordinal.type b (fun x y => (x : T) < y) h = height T
def IsLeaf (t : T) : Prop := IsMax t
variable (T) in
/-- **Section 4, preliminaries.** `T` is well-pruned: `Lev_0(T)` has exactly one element, and
`∀ x ∈ T ∀ α [ht(x,T) < α < ht(T) → ∃ y ∈ Lev_α(T) (x <_T y)]`. -/
def WellPruned : Prop :=
  (∃! x : T, ht x = 0) ∧
    ∀ (x : T) (α : Ordinal.{w}), ht x < α → α < height T → ∃ y ∈ Lev T α, x < y
instance (t : T) : IsWellOrder (Set.Iio t) (fun x y => (x : T) < y) := IsTree.wellOrder_Iio t
theorem lt_trichotomy_of_lt {x y t : T} (hx : x < t) (hy : y < t) : x < y ∨ x = y ∨ y < x := by
  by_cases h1 : x < y
  · exact Or.inl h1
  by_cases h2 : y < x
  · exact Or.inr (Or.inr h2)
  exact Or.inr (Or.inl (congrArg Subtype.val
    (Std.Trichotomous.trichotomous (r := fun a b : Set.Iio t => (a : T) < b) ⟨x, hx⟩ ⟨y, hy⟩
      h1 h2)))
theorem le_total_of_lt {x y t : T} (hx : x < t) (hy : y < t) : x ≤ y ∨ y ≤ x := by
  rcases lt_trichotomy_of_lt hx hy with h | rfl | h
  · exact Or.inl h.le
  · exact Or.inl le_rfl
  · exact Or.inr h.le
theorem ht_eq_typein {s t : T} (h : s < t) :
    ht s = Ordinal.typein (fun x y : Set.Iio t => (x : T) < y) ⟨s, h⟩ := by
  rw [← Ordinal.type_subrel]
  refine RelIso.ordinalType_congr ?_
  exact
    { toFun := fun x => ⟨⟨x.1, lt_trans x.2 h⟩, x.2⟩
      invFun := fun y => ⟨y.1.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
theorem ht_lt_ht {s t : T} (h : s < t) : ht s < ht t := by
  rw [ht_eq_typein h]
  exact Ordinal.typein_lt_type _ _
theorem exists_lt_ht_eq {t : T} {α : Ordinal.{w}} (h : α < ht t) : ∃ s < t, ht s = α := by
  obtain ⟨⟨s, hs⟩, rfl⟩ := Ordinal.typein_surj (fun x y : Set.Iio t => (x : T) < y) h
  exact ⟨s, hs, ht_eq_typein hs⟩
theorem ht_le_ht_of_Iio_subset {s t : T} (h : Set.Iio s ⊆ Set.Iio t) : ht s ≤ ht t := by
  by_contra hc
  obtain ⟨u, hu, hu'⟩ := exists_lt_ht_eq (lt_of_not_ge hc)
  exact (ht_lt_ht (h hu)).ne hu'
theorem ht_lt_ht_of_Iio_ssubset {s t : T} (h : Set.Iio s ⊂ Set.Iio t) : ht s < ht t := by
  obtain ⟨u, hut, hus⟩ := Set.exists_of_ssubset h
  have hsub : Set.Iio s ⊆ Set.Iio u := by
    intro x hx
    rcases lt_trichotomy_of_lt (h.1 hx) hut with h' | rfl | h'
    · exact h'
    · exact absurd hx hus
    · exact absurd (lt_trans h' hx) hus
  exact (ht_le_ht_of_Iio_subset hsub).trans_lt (ht_lt_ht hut)
theorem Iio_subset_or_subset {s₁ s₂ t : T} (h₁ : Set.Iio s₁ ⊆ Set.Iio t)
    (h₂ : Set.Iio s₂ ⊆ Set.Iio t) : Set.Iio s₁ ⊆ Set.Iio s₂ ∨ Set.Iio s₂ ⊆ Set.Iio s₁ := by
  by_contra hc
  simp only [not_or, Set.not_subset] at hc
  obtain ⟨⟨x, hx₁, hx₂⟩, ⟨y, hy₂, hy₁⟩⟩ := hc
  rcases le_total_of_lt (h₁ hx₁) (h₂ hy₂) with h | h
  · exact hx₂ (lt_of_le_of_lt h hy₂)
  · exact hy₁ (lt_of_le_of_lt h hx₁)
instance : WellFoundedLT T := by
  refine ⟨⟨fun t => Acc.intro t fun y hy => ?_⟩⟩
  have key : ∀ z : Set.Iio t, Acc (· < ·) (z : T) := by
    intro z
    induction z using (IsWellFounded.wf (r := fun x y : Set.Iio t => (x : T) < y)).induction with
    | _ z ih =>
      exact Acc.intro _ fun x hx => ih ⟨x, lt_trans hx z.2⟩ hx
  exact key ⟨y, hy⟩
theorem isTree_of_strictMono {P : Type*} [PartialOrder P] {β : Type*} [Preorder β]
    [WellFoundedLT β] (r : P → β) (hr : StrictMono r)
    (hc : ∀ t x y : P, x < t → y < t → x ≤ y ∨ y ≤ x) : IsTree P := by
  refine ⟨fun t => ?_⟩
  have : Std.Trichotomous (fun x y : Set.Iio t => (x : P) < y) := ⟨fun a b hab hba => by
    rcases hc t a b a.2 b.2 with h | h
    · exact Subtype.ext ((h.lt_or_eq.resolve_left hab))
    · exact Subtype.ext ((h.lt_or_eq.resolve_left hba).symm)⟩
  exact @IsWellOrder.mk _ _
    ⟨Subrelation.wf (fun {a b} h => hr h) (InvImage.wf (fun x : Set.Iio t => r x) wellFounded_lt)⟩ inferInstance
end Tree
open Tree
def IsKappaTree (κ : Cardinal.{w}) (T : Type w) [PartialOrder T] [IsTree T] : Prop :=
  height T = κ.ord ∧ ∀ α : Ordinal.{w}, α < κ.ord → #(Lev T α) < κ
section History
variable {T : Type w} [PartialOrder T] [IsTree T]
def histFun (t : T) : Set (Ordinal.{w} × T) := {p | p.2 < t ∧ ht p.2 = p.1}
theorem histFun_subset_iff {s t : T} : histFun s ⊆ histFun t ↔ Set.Iio s ⊆ Set.Iio t := by
  constructor
  · intro h x hx
    exact (h (show (ht x, x) ∈ histFun s from ⟨hx, rfl⟩)).1
  · rintro h ⟨α, p⟩ ⟨hp, hα⟩
    exact ⟨h hp, hα⟩
theorem histFun_ssubset_iff {s t : T} : histFun s ⊂ histFun t ↔ Set.Iio s ⊂ Set.Iio t := by
  simp only [Set.ssubset_def, histFun_subset_iff]
variable (T) in
/-- **Definition 4.1** (Section 4). The history tree of `T`: `F_T = ({f_t : t ∈ T}, ⊆)`. -/
def HistoryTree : Set (Set (Ordinal.{w} × T)) := Set.range histFun
variable (T) in
/-- **Definition 4.1** (Section 4), implicit claim: the history tree `F_T` is a tree. -/
theorem historyTree_isTree : IsTree (HistoryTree T) := by
  classical
  refine isTree_of_strictMono (fun g : HistoryTree T => ht g.2.choose) ?_ ?_
  · intro g g' h
    have h' : histFun g.2.choose ⊂ histFun g'.2.choose := by
      rw [g.2.choose_spec, g'.2.choose_spec]
      exact h
    exact ht_lt_ht_of_Iio_ssubset (histFun_ssubset_iff.1 h')
  · rintro ⟨_, t, rfl⟩ ⟨_, x, rfl⟩ ⟨_, y, rfl⟩ hx hy
    have hx' : histFun x ⊂ histFun t := hx
    have hy' : histFun y ⊂ histFun t := hy
    rcases Iio_subset_or_subset (histFun_ssubset_iff.1 hx').1 (histFun_ssubset_iff.1 hy').1 with
      h | h
    · exact Or.inl (histFun_subset_iff.2 h)
    · exact Or.inr (histFun_subset_iff.2 h)
instance : IsTree (HistoryTree T) := historyTree_isTree T
variable (T) in
/-- **Definition 4.2** (Section 4). `T^succ`: the subtree of `T` induced by
`{t ∈ T : ht(t,T) is a successor ordinal}`. -/
def succPart : Set T := {t | ∃ β : Ordinal.{w}, ht t = Order.succ β}
def succNode {t : T} (ht' : ¬ IsLeaf t) : T :=
  WellFounded.min wellFounded_lt {x | t < x} (not_isMax_iff.1 ht')
end History
section TreeOfColoring
variable {κ : Cardinal.{w}} {D : Type v}
theorem Kappa.coe_lt_ord (x : Kappa κ) : (x : Ordinal.{w}) < κ.ord :=
  (Ordinal.ToType.mk.symm x).2
def Kappa.mk (α : Ordinal.{w}) (h : α < κ.ord) : Kappa κ := Ordinal.ToType.mk ⟨α, h⟩
def fiberRestr (C : Coloring (Kappa κ) D) (δ β : Kappa κ) (hβ : β ≤ δ) :
    Set (Kappa κ × D) :=
  {p | ∃ h : p.1 < β, p.2 = C.color p.1 δ (h.trans_le hβ)}
theorem fiberRestr_subset_iff {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ : Kappa κ} (h₁ : β₁ ≤ δ₁)
    (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ₂ β₂ h₂ ↔
      β₁ ≤ β₂ ∧ ∀ (α : Kappa κ) (hα₁ : α < β₁) (hα₂ : α < β₂),
        C.color α δ₁ (hα₁.trans_le h₁) = C.color α δ₂ (hα₂.trans_le h₂) := by
  constructor
  · intro h
    have hle : β₁ ≤ β₂ := by
      by_contra hc
      obtain ⟨hlt, -⟩ := h (show (β₂, C.color β₂ δ₁ ((lt_of_not_ge hc).trans_le h₁)) ∈
        fiberRestr C δ₁ β₁ h₁ from ⟨lt_of_not_ge hc, rfl⟩)
      exact lt_irrefl _ hlt
    refine ⟨hle, fun α hα₁ hα₂ => ?_⟩
    have hm := h (show (α, C.color α δ₁ (hα₁.trans_le h₁)) ∈ fiberRestr C δ₁ β₁ h₁ from
      ⟨hα₁, rfl⟩)
    obtain ⟨_, hm'⟩ := hm
    exact hm'
  · rintro ⟨hle, hc⟩ ⟨α, d⟩ ⟨hα, hd⟩
    exact ⟨hα.trans_le hle, hd.trans (hc α hα (hα.trans_le hle))⟩
theorem fiberRestr_subset_of_subset {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ δ β : Kappa κ}
    {h₁ : β₁ ≤ δ₁} {h₂ : β₂ ≤ δ₂} {h : β ≤ δ} (s₁ : fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ β h)
    (s₂ : fiberRestr C δ₂ β₂ h₂ ⊆ fiberRestr C δ β h) (hle : β₁ ≤ β₂) :
    fiberRestr C δ₁ β₁ h₁ ⊆ fiberRestr C δ₂ β₂ h₂ := by
  rw [fiberRestr_subset_iff] at s₁ s₂ ⊢
  exact ⟨hle, fun α hα₁ hα₂ => (s₁.2 α hα₁ (hα₁.trans_le s₁.1)).trans
    (s₂.2 α hα₂ (hα₂.trans_le s₂.1)).symm⟩
def treeOfColoring (C : Coloring (Kappa κ) D) : Set (Set (Kappa κ × D)) :=
  {g | ∃ (δ β : Kappa κ) (hβ : β ≤ δ), g = fiberRestr C δ β hβ}
theorem treeOfColoring_isTree (C : Coloring (Kappa κ) D) : IsTree (treeOfColoring C) := by
  classical
  let β : treeOfColoring C → Kappa κ := fun g => Classical.choose (Classical.choose_spec g.2)
  have hβ : ∀ g : treeOfColoring C, ∃ h, g.1 = fiberRestr C g.2.choose (β g) h :=
    fun g => Classical.choose_spec (Classical.choose_spec g.2)
  refine isTree_of_strictMono β ?_ ?_
  · intro g g' hlt
    obtain ⟨h, hg⟩ := hβ g
    obtain ⟨h', hg'⟩ := hβ g'
    have hss : g.1 ⊂ g'.1 := hlt
    rw [hg, hg'] at hss
    have hs := (fiberRestr_subset_iff _ _).1 hss.1
    refine lt_of_le_of_ne hs.1 fun heq => hss.2 ?_
    rw [fiberRestr_subset_iff]
    exact ⟨heq.ge, fun α hα₁ hα₂ => (hs.2 α hα₂ hα₁).symm⟩
  · intro g x y hx hy
    obtain ⟨h, hg⟩ := hβ g
    obtain ⟨hx', hxe⟩ := hβ x
    obtain ⟨hy', hye⟩ := hβ y
    have sx : x.1 ⊆ g.1 := (show x.1 ⊂ g.1 from hx).1
    have sy : y.1 ⊆ g.1 := (show y.1 ⊂ g.1 from hy).1
    rw [hg, hxe] at sx
    rw [hg, hye] at sy
    rcases le_total (β x) (β y) with hle | hle
    · left
      change x.1 ⊆ y.1
      rw [hxe, hye]
      exact fiberRestr_subset_of_subset sx sy hle
    · right
      change y.1 ⊆ x.1
      rw [hxe, hye]
      exact fiberRestr_subset_of_subset sy sx hle
instance (C : Coloring (Kappa κ) D) : IsTree (treeOfColoring C) := treeOfColoring_isTree C
def colorMinOf (f : Kappa κ → Fin 2) : Coloring (Kappa κ) (Fin 2) := fun p => f p.1.inf
def colorMaxOf (f : Kappa κ → Fin 2) : Coloring (Kappa κ) (Fin 2) := fun p => f p.1.sup
end TreeOfColoring
section Enumeration
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
variable (κ T) in
/-- **Definition 4.10** (Section 4, `\label{definition enumeration}`). An enumeration of a
`κ`-tree `T`: for each `α < κ` a bijective enumeration `⟨t^i_α : i < μ_α⟩` of `Lev_α(T)`.
Here `t α i` is `t^i_α` and `μ_α = |Lev_α(T)|` (as an initial ordinal). -/
structure Enumeration where
  /-- `t α i` is `t^i_α`. -/
  t : Ordinal.{w} → Ordinal.{w} → T
  bijOn : ∀ α < κ.ord, Set.BijOn (t α) (Set.Iio (#(Lev T α)).ord) (Lev T α)
variable (κ T) in
/-- **Definition 4.11** (Section 4): `μ = sup {μ_α : α < κ}`, `μ_α = |Lev_α(T)|`. -/
def levelSup : Cardinal.{w} := ⨆ α : Kappa κ, #(Lev T (α : Ordinal.{w}))
def IsTreeColoring (e : Enumeration κ T) (C : Coloring (Kappa κ) (Kappa (levelSup κ T))) :
    Prop :=
  ∀ (α δ : Kappa κ) (h : α < δ),
    ((C.color α δ h : Ordinal.{w}) < (#(Lev T (α : Ordinal.{w}))).ord) ∧
      e.t α (C.color α δ h) ≤ e.t δ 0
def Enumeration.Covers (e : Enumeration κ T) : Prop :=
  ∀ t : T, ∃ δ < κ.ord, t < e.t δ 0
def Enumeration.node (e : Enumeration κ T) (C : Coloring (Kappa κ) (Kappa (levelSup κ T)))
    (β δ : Kappa κ) (_h : β ≤ δ) : T :=
  if hβ : β < δ then e.t β (C.color β δ hβ) else e.t δ 0
end Enumeration
end JardenShami


