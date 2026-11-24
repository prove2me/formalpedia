-- Prove2me | Definitions.Def_CSL_Shared_Indexing_DependentCoordinate
-- name    : CSL_Shared_Indexing_DependentCoordinate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:10:41.409944+00:00
-- url     : https://prove2.me/theorems/57705724-3e7f-44c8-9f61-b700caf0f638
-- title:
--   Coded sorting library: Shared / Indexing / DependentCoordinate
-- statement:
--   Module `CodedSorting.Shared.Indexing.DependentCoordinate` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Expose one pair of unequal-width chunks without rearranging spectator
--   coordinates. This is the dependent-width version of SingleCoordinate.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Indexing.DependentCoordinate

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Recursion_ArbitrarySchedule
import Definitions.Def_CSL_Circuit_Framework_CodedSimulation

/-! Expose one pair of unequal-width chunks without rearranging spectator
coordinates. This is the dependent-width version of SingleCoordinate. -/

namespace CSL.DependentCoordinate

open Address ArbitrarySchedule

variable {I : Type*} [LinearOrder I] {α : I → Type*}
variable {Prefix Gap Suffix : Type*}

abbrev Before (i : I) := {j : I // j < i}
abbrev After (i : I) := {j : I // i < j}
abbrev BeforeField (i : I) := (j : Before i) → α j.val
abbrev AfterField (i : I) := (j : After i) → α j.val

def split (i : I) : (∀j,α j) ≃
    ((BeforeField (α:=α) i) × α i × (AfterField (α:=α) i)) where
  toFun x := (fun j=>x j.val,x i,fun j=>x j.val)
  invFun p j := if h : j < i then p.1 ⟨j,h⟩ else
    if he : j = i then he.symm ▸ p.2.1 else
      p.2.2 ⟨j,lt_of_le_of_ne (le_of_not_gt h) (Ne.symm he)⟩
  left_inv x := by
    funext j
    by_cases h : j < i
    · simp only [dif_pos h]
    · simp only [dif_neg h]
      by_cases he : j = i
      · subst j; simp
      · simp [he]
  right_inv p := by
    rcases p with ⟨before,x,after⟩
    apply Prod.ext
    · funext j; simp only [dif_pos j.property]
    · apply Prod.ext
      · simp
      · funext j
        have hn : ¬ j.val < i := not_lt_of_ge (le_of_lt j.property)
        have he : j.val ≠ i := ne_of_gt j.property
        simp [hn,he]

abbrev ShortPrefix (i : I) := Prefix × BeforeField (α:=α) i
abbrev ShortGap (i : I) := AfterField (α:=α) i × Gap × BeforeField (α:=α) i
abbrev ShortSuffix (i : I) := AfterField (α:=α) i × Suffix

def repack (i : I) : FullAddress Prefix (∀j,α j) Gap Suffix ≃
    FullAddress (ShortPrefix (Prefix:=Prefix) (α:=α) i) (α i)
      (ShortGap (Gap:=Gap) (α:=α) i) (ShortSuffix (Suffix:=Suffix) (α:=α) i) where
  toFun a :=
    let h := split i a.high
    let d := split i a.low
    ⟨(a.prefixCoord,h.1),h.2.1,(h.2.2,a.gap,d.1),d.2.1,(d.2.2,a.suffix)⟩
  invFun a :=
    ⟨a.prefixCoord.1,(split i).symm (a.prefixCoord.2,a.high,a.gap.1),
      a.gap.2.1,(split i).symm (a.gap.2.2,a.low,a.suffix.1),a.suffix.2⟩
  left_inv a := by
    cases a with
    | mk p h g d s =>
      change FullAddress.mk p ((split i).symm ((split i) h)) g
        ((split i).symm ((split i) d)) s = _
      simp only [Equiv.symm_apply_apply]
  right_inv a := by
    rcases a with ⟨⟨p,bh⟩,h,⟨ah,g,bd⟩,d,⟨ad,s⟩⟩
    try dsimp only
    simp only [Equiv.apply_symm_apply]

theorem repack_swap (i : I) (a : FullAddress Prefix (∀j,α j) Gap Suffix) :
    repack i (swapChunk i a) = exchange (repack i a) := by
  simp only [repack, Equiv.coe_fn_mk, split, swapChunk, exchange, ite_true]
  have hbefore : (fun j : Before i => if j.val=i then a.low j.val else a.high j.val) =
      (fun j : Before i => a.high j.val) := by
    funext j; simp [ne_of_lt j.property]
  have hbefore' : (fun j : Before i => if j.val=i then a.high j.val else a.low j.val) =
      (fun j : Before i => a.low j.val) := by
    funext j; simp [ne_of_lt j.property]
  have hafter : (fun j : After i => if j.val=i then a.low j.val else a.high j.val) =
      (fun j : After i => a.high j.val) := by
    funext j; simp [ne_of_gt j.property]
  have hafter' : (fun j : After i => if j.val=i then a.high j.val else a.low j.val) =
      (fun j : After i => a.low j.val) := by
    funext j; simp [ne_of_gt j.property]
  rw [hbefore,hbefore',hafter,hafter']

def chunkPerm (i : I) : Equiv.Perm (FullAddress Prefix (∀j,α j) Gap Suffix) :=
  (repack i).trans (exchangeEquiv.trans (repack i).symm)

theorem chunkPerm_apply (i : I) (a : FullAddress Prefix (∀j,α j) Gap Suffix) :
    chunkPerm i a = swapChunk i a := by
  apply (repack i).injective
  rw [repack_swap]
  simp only [chunkPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem chunkPerm_symm (i : I) :
    (chunkPerm (Prefix:=Prefix) (Gap:=Gap) (Suffix:=Suffix) (α:=α) i).symm = chunkPerm i := by
  rfl

theorem transported_chunk {Value : Type*} (i : I)
    (F : FullAddress Prefix (∀j,α j) Gap Suffix → Value) :
    ArbitraryShapes.move (repack i).symm
      (transport exchangeEquiv (ArbitraryShapes.move (repack i) F)) =
        fun a => F (swapChunk i a) := by
  funext a
  change F ((repack i).symm (exchange ((repack i) a))) = F (swapChunk i a)
  exact congrArg F (chunkPerm_apply i a)

end CSL.DependentCoordinate


