-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F013
-- name    : ProbabilityTheory_chapter_01_thm_1_2_F013
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:46:49.614464+00:00
-- url     : https://prove2.me/theorems/e297cf55-3c9d-4d99-b2b0-e575158a0bd6
-- title:
--   Chapter 1, thm_1_2: supporting Lean bundle F013
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2`: `carrier`, `pts_mem_carrier`, `start_mem_carrier`, `end_mem_carrier`, `carrier_subset_Icc`, and 4 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

def carrier {a b : ℝ} (P : Partition a b) : Finset ℝ :=
  Finset.univ.image P.pts
lemma pts_mem_carrier {a b : ℝ} (P : Partition a b) (i : Fin (P.n + 1)) :
    P.pts i ∈ P.carrier := by
  unfold carrier
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
lemma start_mem_carrier {a b : ℝ} (P : Partition a b) :
    a ∈ P.carrier := by
  simpa [P.pts_start] using
    (P.pts_mem_carrier (0 : Fin (P.n + 1)))
lemma end_mem_carrier {a b : ℝ} (P : Partition a b) :
    b ∈ P.carrier := by
  simpa [P.pts_end] using
    (P.pts_mem_carrier (Fin.last P.n))
lemma carrier_subset_Icc {a b : ℝ} (P : Partition a b) :
    ↑P.carrier ⊆ Set.Icc a b := by
  intro x hx
  unfold carrier at hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  exact DarbouxRS.partition_pts_mem_Icc_core P
end Partition

noncomputable def Refinement.of_exists
    {a b : ℝ} {P P' : Partition a b}
    (h : ∀ i : Fin (P.n + 1),
      ∃ j : Fin (P'.n + 1), P.pts i = P'.pts j) :
    Refinement P P' where
  index := fun i => Classical.choose (h i)
  index_spec := fun i => Classical.choose_spec (h i)
  strictMono_index := by
    intro i j hij
    by_contra hnot

    have hji :
        Classical.choose (h j) ≤ Classical.choose (h i) :=
      le_of_not_gt hnot

    have hP'le :
        P'.pts (Classical.choose (h j)) ≤
        P'.pts (Classical.choose (h i)) :=
      P'.strict_mono.monotone hji

    have hi :
        P.pts i = P'.pts (Classical.choose (h i)) :=
      Classical.choose_spec (h i)

    have hj :
        P.pts j = P'.pts (Classical.choose (h j)) :=
      Classical.choose_spec (h j)

    have hPle : P.pts j ≤ P.pts i := by
      calc
        P.pts j = P'.pts (Classical.choose (h j)) := hj
        _ ≤ P'.pts (Classical.choose (h i)) := hP'le
        _ = P.pts i := hi.symm

    exact not_le_of_gt (P.strict_mono hij) hPle

noncomputable def Partition.ofFinset
    {a b : ℝ} (hab : a < b)
    (s : Finset ℝ)
    (ha : a ∈ s) (hb : b ∈ s)
    (hsub : ↑s ⊆ Set.Icc a b) :
    Partition a b := by
  classical

  have hpair : ({a, b} : Finset ℝ) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb

  have hpair_card : ({a, b} : Finset ℝ).card = 2 := by
    simp [ne_of_lt hab]

  have hcard_ge_two : 2 ≤ s.card := by
    calc
      2 = ({a, b} : Finset ℝ).card := hpair_card.symm
      _ ≤ s.card := Finset.card_le_card hpair

  have hcard_pos : 0 < s.card := by omega

  have hcard_eq : s.card - 1 + 1 = s.card := by
    omega

  have hn : 0 < s.card - 1 := by
    omega

  let e : Fin s.card ≃o s := s.orderIsoOfFin (k := s.card) rfl

  refine
  { n := s.card - 1
    hn := hn
    pts := fun i => (e (Fin.cast hcard_eq i)).1
    pts_start := ?_
    pts_end := ?_
    strict_mono := ?_ }

  ·  
    let i0 : Fin s.card :=
      Fin.cast hcard_eq (0 : Fin (s.card - 1 + 1))

    obtain ⟨ia, hia⟩ := e.surjective ⟨a, ha⟩

    have hi0_le : i0 ≤ ia := by
      change i0.val ≤ ia.val
      simp [i0]

    have hleft : (e i0).1 ≤ a := by
      calc
        (e i0).1 ≤ (e ia).1 := e.monotone hi0_le
        _ = a := congrArg Subtype.val hia

    have hright : a ≤ (e i0).1 := by
      exact (hsub (e i0).2).1

    change (e (Fin.cast hcard_eq (0 : Fin (s.card - 1 + 1)))).1 = a
    exact le_antisymm hleft hright

  ·  
    let ilast : Fin s.card :=
      Fin.cast hcard_eq (Fin.last (s.card - 1))

    obtain ⟨ib, hib⟩ := e.surjective ⟨b, hb⟩

    have hib_le : ib ≤ ilast := by
      change ib.val ≤ ilast.val
      simp [ilast]
      exact Nat.le_pred_of_lt ib.isLt

    have hleft : b ≤ (e ilast).1 := by
      calc
        b = (e ib).1 := (congrArg Subtype.val hib).symm
        _ ≤ (e ilast).1 := e.monotone hib_le

    have hright : (e ilast).1 ≤ b := by
      exact (hsub (e ilast).2).2

    change
      (e (Fin.cast hcard_eq (Fin.last (s.card - 1)))).1 = b
    exact le_antisymm hright hleft

  ·  
    intro i j hij
    change
      (e (Fin.cast hcard_eq i)).1 <
      (e (Fin.cast hcard_eq j)).1

    have hcast :
        Fin.cast hcard_eq i < Fin.cast hcard_eq j := by
      change i.val < j.val
      exact hij

    exact e.strictMono hcast
lemma Partition.ofFinset_contains
    {a b : ℝ} (hab : a < b)
    (s : Finset ℝ)
    (ha : a ∈ s) (hb : b ∈ s)
    (hsub : ↑s ⊆ Set.Icc a b)
    {x : ℝ} (hx : x ∈ s) :
    ∃ j : Fin ((Partition.ofFinset hab s ha hb hsub).n + 1),
      (Partition.ofFinset hab s ha hb hsub).pts j = x := by
  classical

  have hpair : ({a, b} : Finset ℝ) ⊆ s := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact ha
    · exact hb

  have hpair_card : ({a, b} : Finset ℝ).card = 2 := by
    simp [ne_of_lt hab]

  have hcard_ge_two : 2 ≤ s.card := by
    calc
      2 = ({a, b} : Finset ℝ).card := hpair_card.symm
      _ ≤ s.card := Finset.card_le_card hpair

  have hcard_eq : s.card - 1 + 1 = s.card := by
    omega

  let e : Fin s.card ≃o s := s.orderIsoOfFin (k := s.card) rfl

  obtain ⟨ix, hix⟩ := e.surjective ⟨x, hx⟩

  let j : Fin (s.card - 1 + 1) :=
    Fin.cast hcard_eq.symm ix

  refine ⟨j, ?_⟩

  change (e (Fin.cast hcard_eq j)).1 = x

  have hcast : Fin.cast hcard_eq j = ix := by
    ext
    simp [j]

  rw [hcast]
  exact congrArg Subtype.val hix
lemma partition_endpoint_lt {a b : ℝ} (P : Partition a b) :
    a < b := by
  have hzero_last : (0 : Fin (P.n + 1)) < Fin.last P.n := by
    change 0 < P.n
    exact P.hn

  calc
    a = P.pts 0 := P.pts_start.symm
    _ < P.pts (Fin.last P.n) := P.strict_mono hzero_last
    _ = b := P.pts_end

end Darboux_fundamental_result


