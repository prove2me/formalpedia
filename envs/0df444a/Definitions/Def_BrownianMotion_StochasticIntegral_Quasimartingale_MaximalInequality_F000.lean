-- Prove2me | Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F000
-- name    : BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:42:45.204183+00:00
-- url     : https://prove2.me/theorems/7d4b7962-c14d-4501-b736-7db23df9a819
-- title:
--   Source declarations: BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Filtration_F000
import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F000
import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F001
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_Basic_F000

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran, Rémy Degenne
-/

/-! # Maximal inequality for real quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section Bridge

/-- The monotone enumeration of a finite set of times, extended by the constant `t` at indices
beyond `#F`. -/
@[grind]
noncomputable def finIdx (F : Finset ι) (t : ι) : ℕ → ι := fun k ↦
  if h : k < #F then (F.orderIsoOfFin rfl ⟨k, h⟩ : ι) else t
variable {F : Finset ι} {t : ι} {k l : ℕ}

lemma finIdx_mem (h : k < #F) : finIdx F t k ∈ F := by grind
lemma finIdx_eq_of_card_le (h : #F ≤ k) : finIdx F t k = t := by grind
lemma finIdx_le (hF : ∀ s ∈ F, s ≤ t) (k : ℕ) : finIdx F t k ≤ t := by grind
lemma finIdx_lt_of_lt (hkl : k < l) (hl : l < #F) : finIdx F t k < finIdx F t l := by
  rw [finIdx, finIdx, dif_pos (hkl.trans hl), dif_pos hl]
  exact mod_cast (F.orderIsoOfFin rfl).strictMono (mod_cast hkl)
lemma finIdx_lt_finIdx_iff (hk : k < #F) (hl : l < #F) :
    finIdx F t k < finIdx F t l ↔ k < l := by
  rw [finIdx, finIdx, dif_pos hk, dif_pos hl, Subtype.coe_lt_coe, OrderIso.lt_iff_lt, Fin.mk_lt_mk]
@[gcongr]
lemma finIdx_monotone (hF : ∀ s ∈ F, s ≤ t) : Monotone (finIdx F t) := by
  intro k l hkl
  rcases eq_or_lt_of_le hkl with rfl | hkl
  · exact le_rfl
  rcases lt_or_ge l #F with h | h
  · exact (finIdx_lt_of_lt hkl h).le
  · grind
lemma exists_finIdx_eq {s : ι} (hs : s ∈ F) : ∃ k, k < #F ∧ finIdx F t k = s := by
  obtain ⟨k, hk⟩ := (F.orderIsoOfFin rfl).surjective ⟨s, hs⟩
  exact ⟨k, k.2, by rw [finIdx, dif_pos k.2, Fin.eta, hk]⟩
lemma finIdx_zero_eq_bot [OrderBot ι] (hbot : ⊥ ∈ F) : finIdx F t 0 = ⊥ := by
  have hcard : 0 < #F := card_pos.2 ⟨⊥, hbot⟩
  obtain ⟨k, hk, hkeq⟩ := exists_finIdx_eq (t := t) hbot
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact hkeq
  · exact le_bot_iff.1 (hkeq ▸ (finIdx_lt_of_lt hkpos hk).le)
/-- Construct an elementary predictable set from a sequence of times and a sequence of measurable
functions. -/
@[simps]
noncomputable
def elemPredSetOfSeq [OrderBot ι] {idx : ℕ → ι} (hidx : Monotone idx) {W : ℕ → Ω → ℝ} (n : ℕ)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) :
    ElementaryPredictableSet 𝓕 :=
  letI K : Finset ℕ := {k ∈ range n | idx k < idx (k + 1)}
  { setBot := ∅
    I := K.image fun k ↦ (idx k, idx (k + 1))
    set := fun p ↦ if h : ∃ k ∈ K, (idx k, idx (k + 1)) = p then W h.choose ⁻¹' {1} else ∅
    le_of_mem_I := by grind
    measurableSet_setBot := @MeasurableSet.empty _ (𝓕 ⊥)
    measurableSet_set p hp := by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hp
      have hex : ∃ k' ∈ K, (idx k', idx (k' + 1)) = (idx k, idx (k + 1)) := ⟨k, hk, rfl⟩
      simp only [dif_pos hex]
      obtain ⟨hcK, hceq⟩ := hex.choose_spec
      have h1 : idx hex.choose = idx k := (Prod.ext_iff.1 hceq).1
      have hKmem {k} (hk : k ∈ K) : k < n ∧ idx k < idx (k + 1) := by simpa [K] using hk
      have h2 : MeasurableSet[𝓕 (idx hex.choose)] (W hex.choose ⁻¹' {1}) :=
        hWmeas _ (hKmem hcK).1 (measurableSet_singleton 1)
      rwa [h1] at h2
    pairwiseDisjoint p hp q hq hpq := by
      simp only [coe_image, Set.mem_image, mem_coe] at hp hq
      obtain ⟨k, hk, rfl⟩ := hp
      obtain ⟨l, hl, rfl⟩ := hq
      have hkl : k ≠ l := fun h ↦ hpq (by rw [h])
      have hIoc : Disjoint (Set.Ioc (idx k) (idx (k + 1))) (Set.Ioc (idx l) (idx (l + 1))) := by
        rcases lt_or_gt_of_ne hkl with h | h
        · exact Set.Ioc_disjoint_Ioc_of_le (hidx (Nat.succ_le_of_lt h))
        · exact (Set.Ioc_disjoint_Ioc_of_le (hidx (Nat.succ_le_of_lt h))).symm
      exact Set.disjoint_left.2 fun x hx hx' ↦
        Set.disjoint_left.1 hIoc hx.1 hx'.1 }
end Bridge

/-! ### Upcrossing and alternation bounds along finite time sets -/

section UpcrossingBound

variable {a b : ℝ} {t : ι} {F : Finset ι} {m : ℕ}

end UpcrossingBound

/-! ### Selection of alternating tuples from frequent oscillation -/

section Selection

variable [TopologicalSpace ι] [OrderTopology ι]

variable {T : Set ι} {x d : ι} {a b : ℝ} {ω : Ω}

end Selection

/-! ### Maximal inequality along finite time sets -/

section Maximal

variable {t : ι} {F : Finset ι} {lam : ℝ}

-- todo name

end Maximal

/-! ## Maximal inequality for countable sets -/

section CountableEvents

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

variable [OrderBot ι]

end CountableEvents

end ProbabilityTheory


