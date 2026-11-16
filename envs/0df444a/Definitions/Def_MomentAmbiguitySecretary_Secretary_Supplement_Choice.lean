-- Prove2me | Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Choice
-- name    : MomentAmbiguitySecretary_Secretary_Supplement_Choice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:48:51.941009+00:00
-- url     : https://prove2.me/theorems/37e7b6b7-6c70-4a77-8af3-8d57a27d43e0
-- title:
--   General causal randomized single-choice kernel
-- statement:
--   A measurable causal subprobability kernel assigns, to ex ante information and a value path, probabilities of selecting each index. Each probability depends only on its observed prefix, and their sum is at most one; residual probability means no selection. This is an equivalent representation of general randomized single-choice stopping rules, using independent private uniform randomness to realize the successive hazards.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Definitions, PDF/printed pp.4–6,17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Mathlib

open MeasureTheory
open scoped NNReal BigOperators

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- General causal subprobability selection kernel, with information I supplied before time 0.
The coefficient is the unconditional probability of selecting i, conditional on a fixed value
path. Causality makes it a function of the observed prefix; the missing mass is no selection.
Equivalently implement with independent uniform private randomness and the successive hazards
p_i/(1-Σ_{j<i}p_j), using hazard 0 if the denominator vanishes. -/
structure CausalChoice (I : Type*) [MeasurableSpace I] (m : ℕ) where
  mass : Fin m → I → (Fin m → ℝ≥0) → ℝ≥0
  measurable_mass : ∀ i, Measurable (fun z : I × (Fin m → ℝ≥0) => mass i z.1 z.2)
  causal : ∀ i s x y, (∀ j : Fin m, j ≤ i → x j = y j) → mass i s x = mass i s y
  total_mass : ∀ s x, ∑ i : Fin m, mass i s x ≤ 1

end MomentAmbiguitySecretary.Secretary.Supplement


