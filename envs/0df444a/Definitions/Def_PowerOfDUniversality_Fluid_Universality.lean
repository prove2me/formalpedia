-- Prove2me | Definitions.Def_PowerOfDUniversality_Fluid_Universality
-- name    : PowerOfDUniversality_Fluid_Universality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:44.911568+00:00
-- url     : https://prove2.me/theorems/5be7cda9-f7dd-4576-9f08-96faf6e52f81
-- title:
--   The two fluid-limit statements compared by Proposition 4.9 (JSQ for every server-count sequence; JSQ(d(N)) with d(N) → ∞)
-- statement:
--   Proposition 4.9 asserts that JSQ($d(N)$) with $d(N)\to\infty$ and the ordinary JSQ policy "have the same fluid limit". This file names the two statements involved, for a fixed buffer $b$ and normalized arrival rate $\lambda$.
--
--   **The JSQ fluid limit for every server-count sequence.** For every sequence of server counts $N_j\ge 1$ with $N_j\to\infty$, arrival rates $\lambda_j\ge 0$ with $\lambda_j/N_j\to\lambda$, and deterministic initial occupancy vectors with
--   $$\Big\|\frac{\mathbf Q^{N_j}(0)}{N_j}-\mathbf q^\infty\Big\|_1\to 0,\qquad \mathbf q^\infty\in\mathcal S,$$
--   any subsequence of the fluid-scaled JSQ processes $\{\mathbf q^{N_j}(t)\}_{t\ge 0}$ has a further subsequence that converges weakly (Skorohod $J_1$, $\ell_1$ topology) to a limit satisfying (2.1)/(4.5).
--
--   **The JSQ($d(N)$) fluid limit.** For systems with $N=1,2,\dots$ servers, arrival rates $\lambda(N)\ge 0$ with $\lambda(N)/N\to\lambda$, JSQ($d(N)$) with $1\le d(N)\le N$ and $d(N)\to\infty$, and deterministic initial states with $\mathbf q^{d(N)}(0)\to\mathbf q^\infty\in\mathcal S$ in $\ell_1$, the same subsequential convergence to a solution of (2.1) holds. This is the conclusion of Theorem 2.1.
--
--   The first statement quantifies over all server-count sequences because the proof of Proposition 4.9 applies the JSQ fluid limit to $\bar N=N-n(N)$ servers.
--
--   **Formalization Note** In both statements the systems live on a common probability space with `Ω : Type`; only the laws of the processes enter the conclusion.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, p. 27, §4.2, Proposition 4.9 and its proof (N̄ = N − n(N)); Theorem 2.1, p. 5; Theorem 4.1, p. 17

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-!
Mukherjee, Borst, van Leeuwaarden & Whiting, arXiv:1612.00723v2, §4.2 (p. 27): the two fluid
limit statements that Proposition 4.9 relates ("the JSQ(d(N)) scheme and the ordinary JSQ policy
have the same fluid limit"), for a fixed buffer `b` and normalized arrival rate `λ`.
-/

/-- **The fluid limit (4.5) of the ordinary JSQ policy, for every sequence of server counts.**
For every sequence of server counts `N_j ≥ 1` with `N_j → ∞`, arrival rates `λ_j ≥ 0` with
`λ_j / N_j → λ`, deterministic initial occupancy vectors `Q0 j` whose scaled versions converge to
`q^∞ ∈ 𝕊` in `ℓ¹`, and systems `sys j` (`N_j` servers, buffer `b`, rate `λ_j`) started from
`Q0 j` on a common probability space: any subsequence of the fluid-scaled JSQ processes
`q^{N_j}` has a further subsequence converging weakly (Skorohod `J₁`, `ℓ¹`) to a limit
satisfying (2.1)/(4.5). -/
def JSQFluidLimit (b : ℕ∞) (lam : ℝ) : Prop :=
  ∀ (Ns : ℕ → ℕ) (lamN : ℕ → ℝ) (Q0 : ℕ → ℕ →₀ ℕ) (qinf : ℕ → ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (sys : ∀ j, System P (Ns j) b (lamN j)),
    (∀ j, 1 ≤ Ns j) → Tendsto Ns atTop atTop →
    (∀ j, 0 ≤ lamN j) → Tendsto (fun j => lamN j / (Ns j : ℝ)) atTop (𝓝 lam) →
    qinf ∈ FluidSpace b → (∀ j ω, (sys j).Q0 ω = Q0 j) →
    Tendsto (fun j => l1dist (scaledOcc (Ns j) (Q0 j)) qinf) atTop (𝓝 0) →
    SubseqFluidLimit P b lam qinf (fun j ω t => (sys j).fluid jsq ω t)

/-- **The fluid limit (2.1) of the JSQ(d(N)) scheme with `d(N) → ∞`** (the conclusion of
Theorem 2.1). The `j`-th system has `N = j + 1` servers, arrival rate `λ_j ≥ 0` with
`λ_j / (j + 1) → λ`, and uses JSQ(`d_j`) with `1 ≤ d_j ≤ j + 1` and `d_j → ∞`; its initial
occupancy vector `Q0 j` is deterministic with `Q0 j / (j + 1) → q^∞ ∈ 𝕊` in `ℓ¹`. Then any
subsequence of the fluid-scaled processes has a further subsequence converging weakly (Skorohod
`J₁`, `ℓ¹`) to a limit satisfying (2.1). -/
def JSQdFluidLimit (b : ℕ∞) (lam : ℝ) : Prop :=
  ∀ (lamN : ℕ → ℝ) (d : ℕ → ℕ) (Q0 : ℕ → ℕ →₀ ℕ) (qinf : ℕ → ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (sys : ∀ j, System P (j + 1) b (lamN j)),
    (∀ j, 0 ≤ lamN j) → Tendsto (fun j => lamN j / ((j : ℝ) + 1)) atTop (𝓝 lam) →
    (∀ j, 1 ≤ d j ∧ d j ≤ j + 1) → Tendsto d atTop atTop →
    qinf ∈ FluidSpace b → (∀ j ω, (sys j).Q0 ω = Q0 j) →
    Tendsto (fun j => l1dist (scaledOcc (j + 1) (Q0 j)) qinf) atTop (𝓝 0) →
    SubseqFluidLimit P b lam qinf (fun j ω t => (sys j).fluid (jsqd (j + 1) (d j)) ω t)

end PowerOfDUniversality.Fluid


