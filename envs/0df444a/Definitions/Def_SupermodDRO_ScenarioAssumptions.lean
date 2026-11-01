-- Prove2me | Definitions.Def_SupermodDRO_ScenarioAssumptions
-- name    : SupermodDRO_ScenarioAssumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:56.003422+00:00
-- url     : https://prove2.me/theorems/af244b54-96e2-42d0-bc2e-8facdd7b9e96
-- title:
--   Assumptions on the data of one scenario (p.7)
-- statement:
--   The data $(\mu,\delta,\underline z,\overline z)$ of one scenario satisfy, for every coordinate $i$:
--
--   1. if $\delta_i=0$ then $\overline z_i=\mu_i=\underline z_i$;
--   2. if $\mu_i\in\{\overline z_i,\underline z_i\}$ then $\overline z_i=\mu_i=\underline z_i$ and $\delta_i=0$;
--   3. $\underline z_i\le\mu_i\le\overline z_i$ and $\delta_i\ge0$.
--
--   Items 1 and 2 are the paper's "without loss of generality" assumptions; they guarantee that every coordinate with $\underline z_i<\overline z_i$ has $\underline z_i<\mu_i<\overline z_i$ and $\delta_i>0$, so the formulas (5) are well defined.
--
--   **Formalization Note** Item 3 is not written in the paper but used throughout (the support contains the mean, (5) is a probability vector); it is stated as a reading of the paper's implicit assumptions.
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), §2.1, p.7 (WLOG assumptions); item 3 implicit

import Mathlib

namespace SupermodDRO

/-- **The assumptions on the data of one scenario.** Long, Qi & Zhang, *Supermodularity in Two-Stage
Distributionally Robust Optimization*, author manuscript (June 2022), §2.1, p.7: "If there are i, k
such that δᵢᵏ = 0, by the constraint on MAD, z̃ᵢ realizes at µᵢᵏ almost surely when the random
scenario k̃ takes value at k, and hence we can let z̄ᵢᵏ = µᵢᵏ = z̲ᵢᵏ for notational simplification.
Similarly, for any i, k with µᵢᵏ ∈ {z̄ᵢᵏ, z̲ᵢᵏ}, by the constraint on mean and MAD, we can also let
z̄ᵢᵏ = µᵢᵏ = z̲ᵢᵏ and δᵢᵏ = 0 for notational simplification."

For the data `μ, δ, zl, zu ∈ ℝⁿ` of one scenario:
1. (`wlog_delta`) `δ i = 0` implies `zu i = μ i = zl i`;
2. (`wlog_mean`) `μ i ∈ {zu i, zl i}` implies `zu i = μ i = zl i` and `δ i = 0`;
3. (`ordered`, `delta_nonneg`) `zl ≤ μ ≤ zu` and `δ ≥ 0`.

**Formalization Note** Items 1 and 2 are the paper's WLOG assumptions. Item 3 is never written in
the paper but is used throughout it (the support `[z̲ᵏ, z̄ᵏ]` contains the mean `µᵏ`, (5) is a
probability vector, the case `µᵢᵏ ∈ {z̄ᵢᵏ, z̲ᵢᵏ}` is the boundary case); it is a reading of the
paper's implicit assumptions. -/
structure ScenarioAssumptions {n : ℕ} (μ δ zl zu : Fin n → ℝ) : Prop where
  wlog_delta : ∀ i, δ i = 0 → zu i = μ i ∧ μ i = zl i
  wlog_mean : ∀ i, (μ i = zu i ∨ μ i = zl i) → (zu i = μ i ∧ μ i = zl i) ∧ δ i = 0
  ordered : zl ≤ μ ∧ μ ≤ zu
  delta_nonneg : 0 ≤ δ

end SupermodDRO


