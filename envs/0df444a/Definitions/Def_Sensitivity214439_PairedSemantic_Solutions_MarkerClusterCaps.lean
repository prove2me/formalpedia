-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkerClusterCaps
-- name    : Sensitivity214439_PairedSemantic_Solutions_MarkerClusterCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:56:34.970009+00:00
-- url     : https://prove2.me/theorems/1c6818b6-290c-4cbf-bc5a-f99288ea523b
-- title:
--   Marker-subset caps by the number of represented macros
-- statement:
--   Assign to a selected marker subset the cap $\beta_1$, $\beta_2$, or $\beta_3$ according as its macro image has at most one, exactly two, or at least three elements. For pairs and triples, this cap can be expressed using counts of monochromatic subpairs and subtriples.
--
--   The bundle gives the exact identities for the cap triples $(5,3,3)$, $(6,5,4)$, and $(9,7,6)$. Summing these identities over all marker pairs or triples reduces their total caps to baseline binomial terms plus sums of explicit scores of the macro-cluster sizes.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkerClusterCaps.lean lines 13–165; SHA256 714478ff6e45c34bcc256cd199951b6efa08c04359e947627b910717886cc186; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkerClusterCounts
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SensitivityClusterPartitionBound
end SensitivityClusterPartitionBound
namespace SensitivityMarkerClusterCaps
end SensitivityMarkerClusterCaps
namespace SensitivityMarkerClusterCounts
end SensitivityMarkerClusterCounts



/-! Aggregate one-, two-, and three-macro marker caps over all marker subsets. -/
namespace SensitivityMarkerClusterCaps

noncomputable section
open scoped Classical BigOperators
open SensitivityMarkerClusterCounts SensitivityClusterPartitionBound
set_option autoImplicit false

variable {V M : Type} [DecidableEq V] [DecidableEq M]

def markerCap (betaOne betaTwo betaThree : ℕ) (group : V → M) (selected : Finset V) : ℕ :=
  if (selected.image group).card ≤ 1 then betaOne
  else if (selected.image group).card ≤ 2 then betaTwo else betaThree

theorem monochrome_self (selected : Finset V) (group : V → M) (r : ℕ) (hr : selected.card = r) :
    (monochrome selected group r).card = if (selected.image group).card ≤ 1 then 1 else 0 := by
  unfold monochrome
  rw [← hr, Finset.powersetCard_self]
  by_cases h : (selected.image group).card ≤ 1 <;>
    simp only [Finset.filter_singleton, h, if_true, if_false, Finset.card_singleton, Finset.card_empty]

theorem markerCap_pair (selected : Finset V) (group : V → M) (hr : selected.card = 2)
    (b1 b2 b3 : ℕ) (hbeta : b2 ≤ b1) :
    markerCap b1 b2 b3 group selected = b2 + (b1 - b2) * (monochrome selected group 2).card := by
  have himage : (selected.image group).card ≤ 2 := (Finset.card_image_le).trans hr.le
  rw [monochrome_self selected group 2 hr]
  unfold markerCap
  split_ifs <;> omega

theorem triple_pair_monochrome (selected : Finset V) (group : V → M) (hr : selected.card = 3) :
    (monochrome selected group 2).card =
      if (selected.image group).card ≤ 1 then 3 else
      if (selected.image group).card ≤ 2 then 1 else 0 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hr
  have hpowers : ({a, b, c} : Finset V).powersetCard 2 = {{a,b}, {a,c}, {b,c}} := by
    ext part
    simp only [Finset.mem_powersetCard, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hcard⟩
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
      have hu : u ∈ ({a,b,c} : Finset V) := hsub (by simp)
      have hv : v ∈ ({a,b,c} : Finset V) := hsub (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        simp_all [Finset.pair_comm]
    · rintro (rfl | rfl | rfl) <;> simp [hab, hac, hbc, Finset.subset_iff]
  have habac : ({a,b} : Finset V) ≠ {a,c} := by
    intro h
    have : b ∈ ({a,c} : Finset V) := h ▸ (by simp)
    simp_all
  have habbc : ({a,b} : Finset V) ≠ {b,c} := by
    intro h
    have : a ∈ ({b,c} : Finset V) := h ▸ (by simp)
    simp_all
  have hacbc : ({a,c} : Finset V) ≠ {b,c} := by
    intro h
    have : a ∈ ({b,c} : Finset V) := h ▸ (by simp)
    simp_all
  unfold monochrome
  rw [hpowers]
  by_cases habg : group a = group b
  · by_cases hacg : group a = group c
    · have hbcg : group b = group c := habg.symm.trans hacg
      simp_all [Finset.filter_insert, Finset.filter_singleton, ne_comm]
    · have hbcg : group b ≠ group c := by intro h; exact hacg (habg.trans h)
      simp_all [Finset.filter_insert, Finset.filter_singleton, ne_comm]
  · by_cases hacg : group a = group c
    · have hbcg : group b ≠ group c := by intro h; exact habg (hacg.trans h.symm)
      simp_all [Finset.filter_insert, Finset.filter_singleton, ne_comm]
    · by_cases hbcg : group b = group c
      · simp_all [Finset.filter_insert, Finset.filter_singleton, ne_comm]
      · simp_all [Finset.filter_insert, Finset.filter_singleton, ne_comm]

theorem markerCap_triple89 (selected : Finset V) (group : V → M) (hr : selected.card = 3) :
    markerCap 5 3 3 group selected = 3 + 2 * (monochrome selected group 3).card := by
  rw [monochrome_self selected group 3 hr]
  unfold markerCap
  split_ifs <;> omega

theorem markerCap_triple137 (selected : Finset V) (group : V → M) (hr : selected.card = 3) :
    markerCap 6 5 4 group selected + (monochrome selected group 3).card =
      4 + (monochrome selected group 2).card := by
  rw [monochrome_self selected group 3 hr, triple_pair_monochrome selected group hr]
  unfold markerCap
  split_ifs <;> omega

theorem markerCap_triple421 (selected : Finset V) (group : V → M) (hr : selected.card = 3) :
    markerCap 9 7 6 group selected = 6 + (monochrome selected group 2).card := by
  rw [triple_pair_monochrome selected group hr]
  unfold markerCap
  split_ifs <;> omega

theorem markerCap_sum_pair (markers : Finset V) (group : V → M)
    (b1 b2 b3 : ℕ) (hbeta : b2 ≤ b1) :
    (∑ selected ∈ markers.powersetCard 2, markerCap b1 b2 b3 group selected) =
      b2 * markers.card.choose 2 +
        ∑ m ∈ markers.image group, (b1 - b2) * (cluster markers group m).card.choose 2 := by
  have h := Finset.sum_congr rfl (fun selected (hs : selected ∈ markers.powersetCard 2) =>
    markerCap_pair selected group (Finset.mem_powersetCard.mp hs).2 b1 b2 b3 hbeta)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [sum_monochrome_subsets markers group 2 2 (by omega)] at h
  simp only [Nat.sub_self, Nat.choose_zero_right, Nat.mul_one, Finset.sum_const,
    Finset.card_powersetCard, smul_eq_mul] at h
  rw [monochrome_card markers group 2 (by omega), Finset.mul_sum] at h
  simpa only [Nat.mul_comm] using h

theorem markerCap_sum_triple89 (markers : Finset V) (group : V → M) :
    (∑ selected ∈ markers.powersetCard 3, markerCap 5 3 3 group selected) =
      3 * markers.card.choose 3 +
        ∑ m ∈ markers.image group, 2 * (cluster markers group m).card.choose 3 := by
  have h := Finset.sum_congr rfl (fun selected (hs : selected ∈ markers.powersetCard 3) =>
    markerCap_triple89 selected group (Finset.mem_powersetCard.mp hs).2)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [sum_monochrome_subsets markers group 3 3 (by omega)] at h
  simp only [Nat.sub_self, Nat.choose_zero_right, Nat.mul_one, Finset.sum_const,
    Finset.card_powersetCard, smul_eq_mul] at h
  rw [monochrome_card markers group 3 (by omega), Finset.mul_sum] at h
  simpa only [Nat.mul_comm] using h

theorem choose_three_le_mul_choose_two (n total : ℕ) (hn : n ≤ total) :
    n.choose 3 ≤ (total - 2) * n.choose 2 := by
  have h := Nat.choose_mul (n := n) (k := 3) (s := 2) (by decide)
  norm_num at h
  have hm := Nat.mul_le_mul_left (n.choose 2) (Nat.sub_le_sub_right hn 2)
  nlinarith

theorem markerCap_sum_triple137 (markers : Finset V) (group : V → M) :
    (∑ selected ∈ markers.powersetCard 3, markerCap 6 5 4 group selected) =
      4 * markers.card.choose 3 +
        ∑ m ∈ markers.image group,
          ((markers.card - 2) * (cluster markers group m).card.choose 2 -
            (cluster markers group m).card.choose 3) := by
  have h := Finset.sum_congr rfl (fun selected (hs : selected ∈ markers.powersetCard 3) =>
    markerCap_triple137 selected group (Finset.mem_powersetCard.mp hs).2)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul] at h
  rw [sum_monochrome_subsets markers group 3 3 (by omega),
    sum_monochrome_subsets markers group 2 3 (by omega)] at h
  simp only [Nat.sub_self, Nat.choose_zero_right, Nat.mul_one, Nat.reduceSub,
    Nat.choose_one_right] at h
  rw [monochrome_card markers group 3 (by omega), monochrome_card markers group 2 (by omega)] at h
  have hle : ∀ m ∈ markers.image group,
      (cluster markers group m).card.choose 3 ≤
        (markers.card - 2) * (cluster markers group m).card.choose 2 := by
    intro m _
    exact choose_three_le_mul_choose_two _ _ (Finset.card_le_card (Finset.filter_subset _ _))
  rw [Finset.sum_tsub_distrib _ hle, ← Finset.mul_sum]
  have hs := Finset.sum_le_sum hle
  rw [← Finset.mul_sum] at hs
  have hsub := Nat.sub_add_cancel hs
  nlinarith

theorem markerCap_sum_triple421 (markers : Finset V) (group : V → M) :
    (∑ selected ∈ markers.powersetCard 3, markerCap 9 7 6 group selected) =
      6 * markers.card.choose 3 +
        ∑ m ∈ markers.image group, (markers.card - 2) * (cluster markers group m).card.choose 2 := by
  have h := Finset.sum_congr rfl (fun selected (hs : selected ∈ markers.powersetCard 3) =>
    markerCap_triple421 selected group (Finset.mem_powersetCard.mp hs).2)
  rw [Finset.sum_add_distrib, sum_monochrome_subsets markers group 2 3 (by omega)] at h
  simp only [Nat.reduceSub, Nat.choose_one_right, Finset.sum_const,
    Finset.card_powersetCard, smul_eq_mul] at h
  rw [monochrome_card markers group 2 (by omega)] at h
  rw [← Finset.mul_sum]
  nlinarith




end
end SensitivityMarkerClusterCaps


