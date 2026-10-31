-- Prove2me | Definitions.Def_GongReusable_Myopic_Choice
-- name    : GongReusable_Myopic_Choice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:22:48.877673+00:00
-- url     : https://prove2.me/theorems/d7f02286-9655-439c-954c-e4808c257817
-- title:
--   Finite choice laws with an explicit no-purchase option
-- statement:
--   A choice law on a finite product set P assigns nonnegative probabilities to every offered subset and every outcome in P together with a no-purchase outcome. The probabilities sum to one, and products outside the offer have probability zero. No regularity or feasibility condition is built into this general object. The paper-specific regularity assumption is imposed separately.
--
--   The module also supplies inverse cumulative sampling in a fixed finite enumeration and Lebesgue probability measure on [0,1]. The sampler returns the no-purchase outcome as a fallback at the upper endpoint; this affects only a null set for normalized laws. The outcome space has the discrete sigma algebra. These are sampling constructions, not hypotheses about the revenue comparison.
-- source:
--   Gong, Goyal, Iyengar, Simchi-Levi, Udwani and Wang, Online Assortment Optimization with Reusable Resources, https://doi.org/10.1287/mnsc.2021.4134, supplied manuscript (SSRN 3334789 footers; journal pagination and revision year unverified), printed pp. 2, 4–5, 9 / PDF pp. 2, 4–5, 9

import Mathlib

open MeasureTheory
open scoped ENNReal
noncomputable section

namespace GongReusable.Myopic

instance choiceMeasurable (P : Type) : MeasurableSpace (Option P) := ⊤

/-- Finite choice probabilities, including the outside option. -/
abbrev ChoiceProb (P : Type) := Finset P → Option P → ℝ

structure IsChoiceLaw {P : Type} [Fintype P] (prob : ChoiceProb P) : Prop where
  nonneg : ∀ S j, 0 ≤ prob S j
  total : ∀ S, ∑ j, prob S j = 1
  support : ∀ S j, j ∉ S → prob S (some j) = 0

/-- Inverse cumulative sampling in a fixed enumeration, with a null-endpoint fallback. -/
def pickList {A : Type} (fallback : A) (p : A → ℝ) : List A → ℝ → A
  | [], _ => fallback
  | a :: rest, u => if u < p a then a else pickList fallback p rest (u - p a)

def choose {P : Type} [Fintype P] (p : Option P → ℝ) (u : ℝ) : Option P :=
  pickList none p Finset.univ.toList u

/-- Independent randomization is supplied by Lebesgue measure on the unit interval. -/
def uniform : Measure ℝ := volume.restrict (Set.Icc 0 1)

end GongReusable.Myopic


