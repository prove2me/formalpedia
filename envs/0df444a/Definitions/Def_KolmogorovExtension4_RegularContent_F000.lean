-- Prove2me | Definitions.Def_KolmogorovExtension4_RegularContent_F000
-- name    : KolmogorovExtension4_RegularContent_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:34:32.419374+00:00
-- url     : https://prove2.me/theorems/e0b66101-bd85-4e10-aadd-43683154df09
-- title:
--   Source declarations: KolmogorovExtension4.RegularContent
-- statement:
--   Source-preserving extracted declarations from KolmogorovExtension4.RegularContent. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_KolmogorovExtension4_CompactSystem_F000
import Definitions.Def_SourceProof_ac0a17507cdfc424e1005498
import Mathlib.MeasureTheory.Measure.AddContent

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {C R : Set (Set α)} {s : ℕ → Set α}

-- `innerRegular` is defined only for a measure, hence we expand the definition to use it with a
-- content

lemma addContent_iUnion_eq_sum_of_regular (hR : IsSetRing R) (m : AddContent ℝ≥0∞ R)
    (hm_ne_top : ∀ s ∈ R, m s ≠ ∞)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (h_reg : ∀ A ∈ R, ∀ ε, 0 < ε → ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε)
    ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ R) (hUf : (⋃ i, f i) ∈ R)
    (h_disj : Pairwise (Function.onFun Disjoint f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  refine addContent_iUnion_eq_sum_of_tendsto_zero hR m hm_ne_top ?_ hf hUf h_disj
  intro s hs hs_anti hs_iInter
  exact _root_.Prove2MeSourceProof.h_ac0a17507cdfc424e1005498 hR m hs hs_anti hs_iInter hC hCR h_reg
end MeasureTheory


