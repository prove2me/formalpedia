-- Prove2me | Definitions.Def_BayesClock_LowHighTerms
-- name    : BayesClock_LowHighTerms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:11.443625+00:00
-- url     : https://prove2.me/theorems/76b90801-3b69-455c-ac74-4065aad41c6c
-- title:
--   The core and tail terms of the benchmark
-- statement:
--   For a family of thresholds $t_S$, write $\breve v_{i,S}=\min\{t_S,v_i\}$ and $\hat v_{i,S}=v_i\cdot\mathbb I[v_i>t_S]$, and let $k=|\mathcal S|$. The terms of the core-tail decomposition are
--
--   $$\mathrm{LOW}=\mathbb E_v\Big[\max_{S\in\mathcal S}\sum_{i\in S}\min(v_i,t_S)\Big],\qquad \mathrm{HIGH}=\mathbb E_v\Big[\max_{S\in\mathcal S}\sum_{i\in S}v_i\,\mathbb I[v_i>t_S]\Big],$$
--
--   $$\mathrm{HIGH\text-CORE}=\mathbb E_v\Big[\max_{S\in\mathcal S}\sum_{i\in S}\hat v_i\,\mathbb I\big[|S(t_S,v)|\le10\log k+1\big]\Big],$$
--
--   $$\mathrm{HIGH\text-TAIL}=\sum_{S\in\mathcal S}\sum_{i\in S}\mathbb E[v_i]\cdot\Pr_v\big[|S(t_S,v)-\{i\}|>10\log k\big],$$
--
--   $$\mathrm{LOW\text-CORE}=\mathbb E_v\Big[\max_{S\in\mathcal S}\sum_{i\in S}\breve v_{i,S}\,\mathbb I\big[\forall x\in[0,t_S):|S(x,v)|\le10\,\mathbb E_v[|S(x,v)|]+1\big]\Big],$$
--
--   $$\mathrm{LOW\text-TAIL}=\sum_{S\in\mathcal S}\sum_{i\in S}\mathbb E[v_i]\cdot\Pr\big[\exists x\in[0,t_S):|S(x,v)-\{i\}|>10\,\mathbb E_v[|S(x,v)|]\big],$$
--
--   and, for a positive integer $m$,
--
--   $$\Delta=\mathbb E\Big[\max_{S\in\mathcal S}\sum_{i\in S}\hat v_i\,\mathbb I\big[|S(t_S,v)|\le m\big]\Big].$$
--
--   **Formalization Note** All terms take values in $[0,\infty]$ and accept an arbitrary thresholds family `t : Finset N → ℝ≥0`. The expectation inside the event of LOW-TAIL is that of the whole set $S$, as printed. `highPart` is the map $x\mapsto x\,\mathbb I[x>t]$. In $10\log k$ the logarithm is base 2 (`Real.logb 2`), the paper's convention.
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, equations (1)–(3), pp.8–10; Lemma 3, p.10

import Mathlib
import Definitions.Def_BayesClock_maximalSets
import Definitions.Def_BayesClock_aboveSet
import Definitions.Def_BayesClock_expectedAbove
import Definitions.Def_BayesClock_expectedValue

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-! The family of terms of the core-tail decomposition, for an arbitrary family of thresholds
`t : Finset N → ℝ≥0` (`t S` is the paper's `tS`). Feldman et al., arXiv:2202.09291v1, §3.2, pp.8–10.

**Formalization Note** All terms take values in `ℝ≥0∞`. `log k` is the base-2 logarithm
`Real.logb 2` of the number `k` of maximal feasible sets, the paper's convention (it writes `ln 2`
for the natural logarithm, §A.1, p.20), and `k ≥ 1` for a downward-closed constraint, so `log k ≥ 0`. -/

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The high-value part `v̂ᵢ = vᵢ · I[vᵢ > t]` of a value `x` for the threshold `t`, p.8. -/
noncomputable def highPart (t x : ℝ≥0) : ℝ≥0 :=
  if t < x then x else 0

/-- `LOW = E_v[max S ∈ 𝒮, ∑ i ∈ S, min(vᵢ, tS)]`, equation (1), p.8. -/
noncomputable def LOW (𝓕 : Finset (Finset N)) (ν : N → Measure ℝ≥0) (t : Finset N → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ v, ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S, ((min (v i) (t S) : ℝ≥0) : ℝ≥0∞) ∂Measure.pi ν

/-- `HIGH = E_v[max S ∈ 𝒮, ∑ i ∈ S, vᵢ · I[vᵢ > tS]]`, equation (1), p.8. -/
noncomputable def HIGH (𝓕 : Finset (Finset N)) (ν : N → Measure ℝ≥0) (t : Finset N → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ v, ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S, (highPart (t S) (v i) : ℝ≥0∞) ∂Measure.pi ν

/-- `HIGH-CORE = E_v[max S ∈ 𝒮, ∑ i ∈ S, v̂ᵢ · I[|S(tS, v)| ≤ 10 log k + 1]]`, p.8. -/
noncomputable def HIGH_CORE (𝓕 : Finset (Finset N)) (ν : N → Measure ℝ≥0)
    (t : Finset N → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ v, ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S,
    (if ((aboveSet S (t S) v).card : ℝ) ≤ 10 * Real.logb 2 (maximalSets 𝓕).card + 1
      then (highPart (t S) (v i) : ℝ≥0∞) else 0) ∂Measure.pi ν

/-- `HIGH-TAIL = ∑ S ∈ 𝒮, ∑ i ∈ S, E[vᵢ] · Pr_v[|S(tS, v) − {i}| > 10 log k]`, equation (2), p.9. -/
noncomputable def HIGH_TAIL (𝓕 : Finset (Finset N)) (ν : N → Measure ℝ≥0)
    (t : Finset N → ℝ≥0) : ℝ≥0∞ :=
  ∑ S ∈ maximalSets 𝓕, ∑ i ∈ S, expectedValue (ν i) *
    Measure.pi ν {v | 10 * Real.logb 2 (maximalSets 𝓕).card < (((aboveSet S (t S) v).erase i).card : ℝ)}

open Classical in
/-- `LOW-CORE = E_v[max S ∈ 𝒮, ∑ i ∈ S, v̆ᵢ,S · I[∀ x ∈ [0, tS) : |S(x, v)| ≤ 10 E_v[|S(x, v)|] + 1]]`,
p.9, where `v̆ᵢ,S = min{tS, vᵢ}`. -/
noncomputable def LOW_CORE (𝓕 : Finset (Finset N)) (ν : N → Measure ℝ≥0)
    (t : Finset N → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ v, ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S,
    (if ∀ x, x < t S → ((aboveSet S x v).card : ℝ≥0∞) ≤ 10 * expectedAbove ν S x + 1
      then ((min (t S) (v i) : ℝ≥0) : ℝ≥0∞) else 0) ∂Measure.pi ν

/-- `LOW-TAIL = ∑ S ∈ 𝒮, ∑ i ∈ S, E[vᵢ] · Pr[∃ x ∈ [0, tS) : |S(x, v) − {i}| > 10 E_v[|S(x, v)|]]`,
equation (3), p.10. The expectation inside the event is that of the whole set `S`, as printed. -/
noncomputable def LOW_TAIL (𝓕 : Finset (Finset N)) (ν : N → Measure ℝ≥0)
    (t : Finset N → ℝ≥0) : ℝ≥0∞ :=
  ∑ S ∈ maximalSets 𝓕, ∑ i ∈ S, expectedValue (ν i) *
    Measure.pi ν {v | ∃ x, x < t S ∧
      10 * expectedAbove ν S x < (((aboveSet S x v).erase i).card : ℝ≥0∞)}

/-- `Δ = E[max S ∈ 𝒮, ∑ i ∈ S, v̂ᵢ · I[|S(tS, v)| ≤ m]]`, Lemma 3, p.10. -/
noncomputable def Delta (𝓕 : Finset (Finset N)) (ν : N → Measure ℝ≥0) (t : Finset N → ℝ≥0)
    (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ v, ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S,
    (if (aboveSet S (t S) v).card ≤ m then (highPart (t S) (v i) : ℝ≥0∞) else 0) ∂Measure.pi ν

end BayesClock


