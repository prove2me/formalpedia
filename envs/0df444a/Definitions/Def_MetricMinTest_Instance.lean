-- Prove2me | Definitions.Def_MetricMinTest_Instance
-- name    : MetricMinTest_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:42.221746+00:00
-- url     : https://prove2.me/theorems/3b6b47e5-966b-4f28-b7c3-94a08bac71f9
-- title:
--   Instance $P=(P_1,\dots,P_k)$ of laws on $[-1,1]$
-- statement:
--   An **instance** assigns to every index $i$ a probability law $P_i$ on $\mathbb R$ that puts no mass outside $[-1,1]$. A query to index $i$ returns an observation drawn from $P_i$. No parametric restriction is imposed: the laws are arbitrary probability measures on $[-1,1]$.
--
--   **Formalization Note** Indices form an arbitrary type $\iota$ (finite in every use).
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6

import Mathlib

namespace MetricMinTest

/-- **Instance.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027
submission (manuscript sha256 dcece193…ad32bb), §2 p.6: "An instance is `P = (P₁, …, P_k)`,
laws on `[−1, 1]`".

**Formalization Note.** Indices form a type `ι`; each `law i` is an arbitrary probability measure
on `ℝ` giving no mass outside `[−1, 1]`. No parametric (e.g. Bernoulli) restriction. -/
structure Instance (ι : Type) where
  /-- The observation law `P_i` at index `i`. -/
  law : ι → MeasureTheory.Measure ℝ
  isProb : ∀ i, MeasureTheory.IsProbabilityMeasure (law i)
  support : ∀ i, law i (Set.Icc (-1 : ℝ) 1)ᶜ = 0

instance Instance.instIsProbabilityMeasure {ι : Type} (P : Instance ι) (i : ι) :
    MeasureTheory.IsProbabilityMeasure (P.law i) := P.isProb i

end MetricMinTest


