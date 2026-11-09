-- Prove2me | Definitions.Def_MinCostMaj_thresholdLaw
-- name    : MinCostMaj_thresholdLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:06:39.568732+00:00
-- url     : https://prove2.me/theorems/d2ee9d91-7191-4bed-b764-3cffcacc51bb
-- title:
--   The law of the global threshold sequence $t_i\sim\mathrm{Unif}[2^{-i},2^{-(i-1)}]$
-- statement:
--   The algorithm samples one global threshold sequence $(t_i)_{i\ge1}$, independently for each $i$, with
--   $$t_i\sim\mathrm{Unif}\big[2^{-i},\,2^{-(i-1)}\big],$$
--   and uses the same $t_i$ for every variable. This item is the joint law of the sequence: the product of the uniform laws on these intervals.
--
--   All probabilities and expectations of the rounding analysis are taken with respect to this law.
--
--   **Formalization Note** A sequence is a function $t:\mathbb N\to\mathbb R$; coordinate $0$ is unused and gets the uniform law on $[1,2]$. Each factor is a probability measure, so the product is Mathlib's independent product `Measure.infinitePi`.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), §5, pp.10–11 (PDF pp.11–12)

import Mathlib

namespace MinCostMaj

open MeasureTheory

/-- The law of one threshold: uniform on `[2^{−i}, 2^{−(i−1)}] = [2^{−i}, 2 · 2^{−i}]`. -/
noncomputable def thrLaw (i : ℕ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc (((1 : ℝ) / 2) ^ i) (2 * ((1 : ℝ) / 2) ^ i))

/-- **The law of the global threshold sequence** (§5, pp.10–11).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, §5, pp.10–11: "we choose one global threshold sequence (ti)i≥1
for the whole instance by sampling independently for each i ≥ 1: ti ∼ Unif[2^{−i}, 2^{−(i−1)}].
The same threshold ti is used for every variable."

The product (Mathlib's `Measure.infinitePi`) of the uniform laws on `[2^{−i}, 2^{−(i−1)}]`.

**Formalization Note.** A sequence is `t : ℕ → ℝ`; coordinate `0` is unused by every definition
and gets the uniform law on `[1, 2]` (any probability law would do). Each factor is a probability
measure (the interval has length `2^{−i} > 0`), so the product is the independent product. -/
noncomputable def thresholdMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi thrLaw

end MinCostMaj


