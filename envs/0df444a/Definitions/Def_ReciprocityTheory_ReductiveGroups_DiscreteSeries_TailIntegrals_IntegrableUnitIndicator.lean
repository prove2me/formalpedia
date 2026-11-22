-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:15:21.751745+00:00
-- url     : https://prove2.me/theorems/2f1dca1e-6d59-46d2-90dd-b8cedb4a114f
-- title:
--   Integrable Unit Indicator
-- statement:
--   Definitions and structural lemmas for Integrable Unit Indicator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IntegrableUnitIndicator.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
def one1 : ℝ → ℝ := Set.indicator (Set.Icc (-1) 1) 1
def pw1 (β : ℝ) : ℝ → ℝ := Set.indicator (Set.Icc (-1) 1) (fun t => |t| ^ (-β))
section Shell
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def tW (q : ι) (x : ι → ℂ) : ℝ := Real.sqrt (∑ i, if i = q then 0 else Complex.normSq (x i))
def Bset (q : ι) : Set (ι → ℂ) := {x | 1 / 2 ≤ tW q x ∧ tW q x ≤ 1 ∧ ‖x q‖ ≤ 1}
def PsiF (p q : ι) (s : ℝ) (x : ι → ℂ) : ℝ≥0∞ := (‖1 - star (x p) / (tW q x : ℂ)‖₊ : ℝ≥0∞) ^ (-s)
def eF (p q i : ι) (z : ℂ) : ℝ := if i = q then 1 else if i = p then |z.im| else |z.re| * |z.im|
def gF (p q : ι) (β : ℝ) (i : ι) (z : ℂ) : ℝ :=
  if i = q then one1 z.re * one1 z.im else if i = p then one1 z.re * pw1 β z.im else pw1 β z.re * pw1 β z.im
end Shell
section Shell2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Shell2
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0


