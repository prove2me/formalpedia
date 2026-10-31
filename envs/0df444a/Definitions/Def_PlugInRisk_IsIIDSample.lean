-- Prove2me | Definitions.Def_PlugInRisk_IsIIDSample
-- name    : PlugInRisk_IsIIDSample
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:40.381168+00:00
-- url     : https://prove2.me/theorems/6f4b525d-f27e-4c10-9ad8-a544252ee431
-- title:
--   i.i.d. sample with law $\mu$
-- statement:
--   A sequence $(S_n)_{n\ge0}$ of random variables on a probability space $(\Omega,\mathcal F,P)$ with values in $\mathcal X$ is an **i.i.d. sample with law $\mu$** if every $S_n$ is measurable, the $S_n$ are mutually independent under $P$, and each $S_n$ has distribution $\mu$.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, §2, p.6 and App. A.2, p.34

import Mathlib

open MeasureTheory

namespace PlugInRisk

/-- **i.i.d. sample with law `μ`** (Bartl & Tangpi, arXiv:2003.10479v2, §2, p.6: "μ_N denotes the
empirical measure of μ build from an i.i.d. sample (S_n)_{n≤N} defined on some abstract
probability space (Ω, F, P)"; App. A.2, p.34: "S, (S_n)_{n≥1} are i.i.d. random variables taking
their values in a Polish space 𝒳 distributed according to μ").

**Formalization Note** The whole sequence `S : ℕ → Ω → 𝒳` is measurable, mutually independent
under `P` (`iIndepFun`), and each `S n` has law `μ`. -/
def IsIIDSample {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] (P : Measure Ω)
    (S : ℕ → Ω → 𝒳) (μ : Measure 𝒳) : Prop :=
  (∀ n, Measurable (S n)) ∧ ProbabilityTheory.iIndepFun S P ∧ ∀ n, P.map (S n) = μ

end PlugInRisk


