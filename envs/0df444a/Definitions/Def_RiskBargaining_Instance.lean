-- Prove2me | Definitions.Def_RiskBargaining_Instance
-- name    : RiskBargaining_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:25:00.187669+00:00
-- url     : https://prove2.me/theorems/d577db65-9fdb-4feb-9e85-daea09f06421
-- title:
--   Instance $(R,M,\mathcal A)$ of the bargaining problem, with Assumption 1
-- statement:
--   An **instance** of the bargaining problem, for a player set $N$, consists of endowments $R_i\in L^p$ ($i\in N$), a random profit $M_x\in L^p$ for each decision $x\in\mathcal X$, and coherent acceptability functionals $\mathcal A_i$ ($i\in N$). The decision space $\mathcal X$ is a compact topological space and
--   $$
--   x\mapsto M_x
--   $$
--   is continuous from $\mathcal X$ to $L^p$ equipped with the weak topology (Assumption 1, which the paper imposes for the rest of the paper).
--
--   Every result of the mission is stated about these data.
--
--   **Formalization Note** The probability space, $p$ and $\mathcal X$ are fixed parameters, and the paper's $M:\mathcal X\times\Omega\to\mathbb R$ is a map `M : X → Lp ℝ p μ`, the form that Assumption 1 gives it. The weak topology is that of `WeakSpace ℝ (Lp ℝ p μ)`. The value $p=\infty$ is admitted.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Definition 2, p.8; Assumption 1, p.9

import Mathlib
import Definitions.Def_RiskBargaining_IsCoherentAcceptability

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Instance of the bargaining problem** `(R, M, 𝒜)`.
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Definition 2, p.8, and Assumption 1, p.9.

Endowments (opportunity losses) `R i ∈ L^p`, the joint profit `M x ∈ L^p` of each decision `x`, and a
coherent acceptability functional `A i` for each player. Assumption 1, which the paper imposes "for
the rest of the paper", is part of the structure: the decision space `X` is compact and `x ↦ M x` is
continuous into `L^p` with the weak topology.

**Formalization Note.** The probability space, the exponent `p ≥ 1` (`p = ∞` admitted) and `X` are fixed
parameters; the page's `M : 𝒳 × Ω → ℝ` becomes `M : X → Lp ℝ p μ`, the form Assumption 1 gives it.
`WeakSpace ℝ (Lp ℝ p μ)` carries the weak topology, so `cont_M` is continuity into `σ(L^p, (L^p)*)`.
The player type `ι` is arbitrary here; every statement takes it finite and nonempty. -/
structure Instance (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (X : Type*) [TopologicalSpace X] [CompactSpace X] (ι : Type*) where
  /-- The endowment `R i` of player `i`. -/
  R : ι → Lp ℝ p μ
  /-- The joint random profit `M x` of decision `x`. -/
  M : X → Lp ℝ p μ
  /-- The acceptability functional of player `i`. -/
  A : ι → Lp ℝ p μ → ℝ
  /-- Each `A i` is coherent (Definition 1). -/
  coherent : ∀ i, IsCoherentAcceptability (A i)
  /-- Assumption 1: `x ↦ M x` is continuous into `L^p` with the weak topology. -/
  cont_M : Continuous fun x => toWeakSpace ℝ (Lp ℝ p μ) (M x)

end RiskBargaining


