-- Prove2me | Definitions.Def_BayesClock_uniformPriceValue
-- name    : BayesClock_uniformPriceValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:08.050041+00:00
-- url     : https://prove2.me/theorems/163f905a-bed2-4511-a4de-aa37f770a369
-- title:
--   Conditional means and the value of a uniform price
-- statement:
--   For a price $p\ge0$, $\mathbb E[v_i\mid v_i\ge p]=\mathbb E[v_i\,\mathbb I[v_i\ge p]]/\Pr[v_i\ge p]$ is the conditional mean, and
--
--   $$W(p)=\mathbb E\Big[\max_{S\in\mathcal S}\sum_{i\in S}\mathbb E[v_i\mid v_i\ge p]\cdot\mathbb I[v_i\ge p]\Big]$$
--
--   is the expression on the right side of Lemma 3.
--
--   **Formalization Note** The conditional mean is the ratio in $[0,\infty]$. When $\Pr[v_i\ge p]=0$ the ratio is $0/0=0$, which is harmless: it is multiplied by the indicator of a null event.
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, Lemma 3, p.10; Section 3.2, p.11

import Mathlib
import Definitions.Def_BayesClock_maximalSets

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- The conditional mean `E[vᵢ | vᵢ ≥ p]` of a value with law `ν₀`, Feldman et al.,
arXiv:2202.09291v1, Lemma 3, p.10.

**Formalization Note** The ratio `(∫⁻ x in [p, ∞), x dν₀) / ν₀ [p, ∞)` in `ℝ≥0∞`. If
`ν₀ [p, ∞) = 0` it is `0 / 0 = 0`, which is harmless: it is only ever multiplied by the indicator of
`vᵢ ≥ p`, a null event in that case. -/
noncomputable def condMean (ν₀ : Measure ℝ≥0) (p : ℝ≥0) : ℝ≥0∞ :=
  (∫⁻ x in Set.Ici p, (x : ℝ≥0∞) ∂ν₀) / ν₀ (Set.Ici p)

/-- `W(p) = E[max S ∈ 𝒮, ∑ i ∈ S, E[vᵢ | vᵢ ≥ p] · I[vᵢ ≥ p]]`, the right side of Lemma 3,
Feldman et al., arXiv:2202.09291v1, p.10, and the expression in the note on p.11. -/
noncomputable def uniformPriceValue {N : Type*} [Fintype N] [DecidableEq N]
    (𝓕 : Finset (Finset N)) (ν : N → Measure ℝ≥0) (p : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ v, ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S,
    condMean (ν i) p * (if p ≤ v i then 1 else 0) ∂Measure.pi ν

end BayesClock


