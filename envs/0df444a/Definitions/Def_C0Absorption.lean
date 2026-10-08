-- Prove2me | Definitions.Def_C0Absorption
-- name    : C0Absorption
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:02.968984+00:00
-- url     : https://prove2.me/theorems/74546ff0-53b9-46ee-b1b5-4897da75fbdc
-- statement:
--   Here C0 is the real normed space c₀ of sequences indexed by the natural numbers that tend to zero, with the supremum norm. A map f between metric spaces is BiLip if there are real constants 0 < c ≤ C such that c d(x,y) ≤ d(f(x),f(y)) ≤ C d(x,y) for all x and y. For a real normed space Z, NoLinearC0 means that no continuous linear map T : c₀ → Z is bounded below by a positive multiple of the norm: there is no c > 0 with c‖x‖ ≤ ‖Tx‖ for every x. MetricUniversal means that every separable metric space admits a BiLip map into Z. MainConclusion is the defined proposition that there exists a complete separable real normed space Z satisfying NoLinearC0, together with a surjective BiLip map from Z × c₀ onto Z and a BiLip map from c₀ into Z, such that Z is also MetricUniversal and there is no continuous linear equivalence between Z × c₀ and Z. Thus the asserted absorption of the c₀ factor is expressed through a surjective map obeying two-sided metric bounds, while a continuous linear equivalence is explicitly excluded.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/C0Absorption.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/C0Absorption.lean; bytes 16..981
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace C0Absorption

open scoped ZeroAtInfty

abbrev C0 := C₀(ℕ, ℝ)

def BiLip {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ x y, c * dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ C * dist x y

def NoLinearC0 (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] : Prop :=
  ∀ T : C0 →L[ℝ] Z, ¬ ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖T x‖

def MetricUniversal (Z : Type*) [MetricSpace Z] : Prop :=
  ∀ (M : Type) [MetricSpace M] [TopologicalSpace.SeparableSpace M],
    ∃ f : M → Z, BiLip f

def MainConclusion : Prop :=
  ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℝ Z),
    CompleteSpace Z ∧ TopologicalSpace.SeparableSpace Z ∧ NoLinearC0 Z ∧
    (∃ F : Z × C0 → Z, Function.Surjective F ∧ BiLip F) ∧
    (∃ f : C0 → Z, BiLip f) ∧ MetricUniversal Z ∧
    ¬ Nonempty ((Z × C0) ≃L[ℝ] Z)



end C0Absorption
end OAI


