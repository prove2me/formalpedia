-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkerClusterCounts
-- name    : Sensitivity214439_PairedSemantic_Solutions_MarkerClusterCounts
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:42.361187+00:00
-- url     : https://prove2.me/theorems/14779f2f-41e2-400d-959a-472faf956743
-- title:
--   Macro clusters and monochromatic marker subsets
-- statement:
--   A macro cluster is the fiber of a grouping map on a finite marker set. A monochromatic $r$-subset is an $r$-element subset whose macro image has cardinality at most one. Nonempty clusters partition the markers.
--
--   For $r>0$, the number of monochromatic $r$-subsets is the sum of $\binom{|C_m|}{r}$ over clusters. Restricting markers commutes with the monochromatic-subset filter. Double counting shows that the sum of monochromatic small-subset counts over all larger subsets equals the original small-subset count times the number of larger extensions.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkerClusterCounts.lean lines 12–99; SHA256 a98fe05aaee1dd657274b186fc532708243830f21132db527d4a88646a0d0175; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SensitivityMarkerClusterCounts
end SensitivityMarkerClusterCounts



/-! Exact cluster counts for single, pair, and triple marker intersections. -/
namespace SensitivityMarkerClusterCounts

noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false

variable {V M : Type} [DecidableEq V] [DecidableEq M]

def cluster (markers : Finset V) (group : V → M) (m : M) : Finset V :=
  markers.filter fun v => group v = m

def monochrome (markers : Finset V) (group : V → M) (r : ℕ) : Finset (Finset V) :=
  (markers.powersetCard r).filter fun selected => (selected.image group).card ≤ 1

theorem monochrome_eq_union (markers : Finset V) (group : V → M) (r : ℕ) (hr : 0 < r) :
    monochrome markers group r = (markers.image group).biUnion fun m =>
      (cluster markers group m).powersetCard r := by
  ext selected
  simp only [monochrome, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hmono⟩
    have hnon : selected.Nonempty := Finset.card_pos.mp (hcard ▸ hr)
    obtain ⟨v, hv⟩ := hnon
    refine ⟨group v, Finset.mem_image.mpr ⟨v, hsub hv, rfl⟩, ?_, hcard⟩
    intro w hw
    apply Finset.mem_filter.mpr
    refine ⟨hsub hw, ?_⟩
    exact Finset.card_le_one.mp hmono _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
      _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  · rintro ⟨m, _, hsub, hcard⟩
    refine ⟨⟨fun v hv => (Finset.mem_filter.mp (hsub hv)).1, hcard⟩, ?_⟩
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_filter.mp (hsub hv)).2.trans (Finset.mem_filter.mp (hsub hw)).2.symm

theorem monochrome_card (markers : Finset V) (group : V → M) (r : ℕ) (hr : 0 < r) :
    (monochrome markers group r).card =
      ∑ m ∈ markers.image group, (cluster markers group m).card.choose r := by
  rw [monochrome_eq_union markers group r hr, Finset.card_biUnion]
  · simp only [Finset.card_powersetCard]
  · intro m hm n hn hne
    apply Finset.disjoint_left.mpr
    intro selected hsm hsn
    obtain ⟨hsubm, hcard⟩ := Finset.mem_powersetCard.mp hsm
    obtain ⟨hsubn, _⟩ := Finset.mem_powersetCard.mp hsn
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (hcard ▸ hr)
    exact hne ((Finset.mem_filter.mp (hsubm hv)).2.symm.trans
      (Finset.mem_filter.mp (hsubn hv)).2)

theorem monochrome_restrict (markers selected : Finset V) (group : V → M)
    (hsub : selected ⊆ markers) (r : ℕ) :
    monochrome selected group r = (monochrome markers group r).filter (· ⊆ selected) := by
  ext part
  simp only [monochrome, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hp, hc⟩, hm⟩
    exact ⟨⟨⟨hp.trans hsub, hc⟩, hm⟩, hp⟩
  · rintro ⟨⟨⟨_, hc⟩, hm⟩, hp⟩
    exact ⟨⟨hp, hc⟩, hm⟩

theorem sum_monochrome_subsets (markers : Finset V) (group : V → M)
    (small large : ℕ) (hle : small ≤ large) :
    (∑ selected ∈ markers.powersetCard large, (monochrome selected group small).card) =
      (monochrome markers group small).card * (markers.card - small).choose (large - small) := by
  calc
    _ = ∑ selected ∈ markers.powersetCard large,
        ((monochrome markers group small).filter (· ⊆ selected)).card := by
      apply Finset.sum_congr rfl
      intro selected hs
      rw [monochrome_restrict markers selected group (Finset.mem_powersetCard.mp hs).1 small]
    _ = ∑ part ∈ monochrome markers group small,
        ((markers.powersetCard large).filter (part ⊆ ·)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ = _ := by
      have hlocal : ∀ part ∈ monochrome markers group small,
          ((markers.powersetCard large).filter (part ⊆ ·)).card =
          (markers.card - small).choose (large - small) := by
        intro part hp
        have hsub' := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).1
        have hcard' := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
        simpa only [hcard'] using Finset.card_filter_powersetCard_subset part markers large
          hsub' (hcard' ▸ hle)
      simp_rw [Finset.sum_congr rfl hlocal]
      simp

theorem cluster_nonempty (markers : Finset V) (group : V → M) (m : M)
    (hm : m ∈ markers.image group) : (cluster markers group m).Nonempty := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hm
  exact ⟨v, Finset.mem_filter.mpr ⟨hv, rfl⟩⟩

theorem sum_cluster_card (markers : Finset V) (group : V → M) :
    (∑ m ∈ markers.image group, (cluster markers group m).card) = markers.card := by
  exact (Finset.card_eq_sum_card_image group markers).symm




end
end SensitivityMarkerClusterCounts


