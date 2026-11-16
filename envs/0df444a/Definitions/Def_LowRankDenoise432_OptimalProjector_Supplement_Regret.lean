-- Prove2me | Definitions.Def_LowRankDenoise432_OptimalProjector_Supplement_Regret
-- name    : LowRankDenoise432_OptimalProjector_Supplement_Regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:39:55.265984+00:00
-- url     : https://prove2.me/theorems/c5db133f-ea1f-42a9-b3d3-50e4c45c5ae8
-- title:
--   §§1.1, 2, 3.1, 3.3 — feasible paths, path gap Δ(c), leverage ρ, conditional independence and the regret event
-- statement:
--   These are the objects that Lemma 3.1 and Theorem 3.6 add to the model of Section 2.
--
--   **Feasible paths.** The feasible set $\mathcal Z$ is a nonempty finite family of vectors $z\in\{0,1\}^d$ (edge-incidence vectors of source-to-sink paths), each with at most $L$ ones, $\sum_e z_e\le L$. A vector $z$ is an *optimal path* for a cost $c\in\mathbb R^d$ if $z\in\mathcal Z$ and $c^\top z\le c^\top w$ for all $w\in\mathcal Z$. The optimal cost is $\min_{z\in\mathcal Z}c^\top z$.
--
--   **Path gap.** If some path is not optimal for $c$, the path gap is
--   $$\Delta(c)=\min\Big\{c^\top z-\min_{w\in\mathcal Z}c^\top w\;:\;z\in\mathcal Z,\ c^\top z>\min_{w\in\mathcal Z}c^\top w\Big\},$$
--   the smallest cost difference between the optimum and a path that is not optimal. Several optimal paths may tie.
--
--   **Decisions and regret.** With the projection estimate $\hat c_\Pi=\bar c+\Pi(\bar y_m-\bar c)$ of equation (1), a decision is a measurable random path $\hat z$ with $\hat z(\omega)\in\arg\min_{z\in\mathcal Z}\hat c_\Pi(\omega)^\top z$ at every outcome (ties broken in any measurable way, possibly at random; a deterministic tie-breaking rule $z(\hat c_\Pi)$ is a special case), and the event $\{\text{regret}>0\}$ is $\{c^\top\hat z>\min_{w\in\mathcal Z}c^\top w\}$.
--
--   **Leverage, bias and tails.** For a $d\times d$ matrix $\Pi$, $\rho=\max_e\Pi_{ee}$. The bias is $\beta=\|(I-\Pi)(c-\bar c)\|_2$ (Euclidean norm). The bound $2d\exp(-a/s)$ is taken to be $0$ when $s=0$.
--
--   **Conditional independence.** In Section 2, given $c$ the replications $\varepsilon^{(1)},\dots,\varepsilon^{(m)}$ are independent, with independent coordinates. This is stated as conditional joint independence of the scalar noises $\varepsilon^{(r)}_e$, $(r,e)\in[m]\times[d]$, given $\sigma(c)$: for every finite set $S$ of indices and bounded measurable $f_i$,
--   $$\mathbb E\Big[\prod_{i\in S}f_i(\varepsilon_i)\,\Big|\,c\Big]=\prod_{i\in S}\mathbb E\big[f_i(\varepsilon_i)\mid c\big]\quad\text{a.s.}$$
--   The conditional probability of an event $A$ given $c$ is $\mathbb P(A\mid c)=\mathbb E[\mathbf 1_A\mid\sigma(c)]$.
--
--   These objects let the error-to-regret lemma and the suboptimality bound be stated on top of the published noisy-cost model.
--
--   **Formalization Note.** Vectors are `Fin d → ℝ`; $\mathcal Z$ is a `Finset`. The optimal cost and $\Delta(c)$ are infima over finite sets, so they are minima when the sets are nonempty. When every path is optimal, $\Delta(c)$ takes the junk value $0$, and every statement that uses it is guarded by "some path is not optimal". `expTail d a s` is $2d\exp(-a/s)$ for $s\ne0$ and $0$ for $s=0$, so the zero-noise and zero-projector endpoint is a separate case rather than Lean's $a/0=0$. Conditional independence is stated by product factorization for bounded measurable test functions (equivalent to the kernel-based `iCondIndepFun` of Mathlib, which would add a standard Borel assumption on $\Omega$). The published `NoisyCostModel` is not changed.
-- source:
--   Henry Aldridge-Krawciw, Irene Aldridge, Low-Rank Denoising for Predict-then-Optimize, STOC 2027 submission #432 (October 2026), source.pdf SHA-256 8d92579f841e1b4853ee9eecd477b739374858db635a23defcc3fb767b137889, PDF p.1 Section 1.1 (paths with at most L edges), PDF p.2 Section 2 (independent replications with independent coordinates given c; path gap Δ(c); estimator (1)), PDF p.3 Theorem 3.6 (ρ, β)

import Mathlib
import Definitions.Def_LowRankDenoise432_OptimalProjector_Model
open MeasureTheory ProbabilityTheory Matrix

namespace LowRankDenoise432.OptimalProjector.Supplement

/-! Objects of Sections 1.1, 2, 3.1 and 3.3 (PDF pp.1–3) of Aldridge-Krawciw–Aldridge,
*Low-Rank Denoising for Predict-then-Optimize*, used by Lemma 3.1 and Theorem 3.6: the feasible
path family, optimizing paths, the path gap `Δ(c)`, the leverage `ρ = maxₑ Πₑₑ`, conditional joint
independence of the noise given `c`, conditional probabilities given `c`, and the regret event.
The published model `NoisyCostModel` is reused unchanged. -/

/-- The feasible set `𝒵`: a nonempty finite family of `0/1` vectors of `ℝ^d` (edge-incidence
vectors of paths), each with at most `L` ones. -/
def IsPathFamily {d : ℕ} (Z : Finset (Fin d → ℝ)) (L : ℕ) : Prop :=
  Z.Nonempty ∧ (∀ z ∈ Z, ∀ e, z e = 0 ∨ z e = 1) ∧ ∀ z ∈ Z, ∑ e, z e ≤ L

/-- `z ∈ argmin_{w ∈ 𝒵} cᵀw`. -/
def IsOptimalPath {d : ℕ} (Z : Finset (Fin d → ℝ)) (c z : Fin d → ℝ) : Prop :=
  z ∈ Z ∧ ∀ w ∈ Z, c ⬝ᵥ z ≤ c ⬝ᵥ w

/-- The optimal cost `min_{z ∈ 𝒵} cᵀz` (a minimum over a finite set; `0` if `𝒵 = ∅`). -/
noncomputable def optCost {d : ℕ} (Z : Finset (Fin d → ℝ)) (c : Fin d → ℝ) : ℝ :=
  ⨅ z : Z, c ⬝ᵥ (z : Fin d → ℝ)

/-- Some path of `𝒵` is not optimal for `c`. -/
def HasNonoptimal {d : ℕ} (Z : Finset (Fin d → ℝ)) (c : Fin d → ℝ) : Prop :=
  ∃ z ∈ Z, optCost Z c < c ⬝ᵥ z

/-- The path gap `Δ(c)`: the smallest cost difference `cᵀz − min_w cᵀw` over the paths `z` that
are not optimal (ties among optimal paths allowed). Meaningful only under `HasNonoptimal Z c`;
otherwise it is the junk value `0` and every statement guards it by `HasNonoptimal`. -/
noncomputable def pathGap {d : ℕ} (Z : Finset (Fin d → ℝ)) (c : Fin d → ℝ) : ℝ :=
  ⨅ z : {z : Fin d → ℝ // z ∈ Z ∧ optCost Z c < c ⬝ᵥ z}, (c ⬝ᵥ z.1 - optCost Z c)

/-- `ρ = maxₑ Πₑₑ`, the largest diagonal entry of `Π` (`0` when `d = 0`). -/
noncomputable def maxDiag {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ e, Q e e

/-- The bound `2d·exp(−a/s)`, read as its limit `0` when the denominator `s` is `0` (used only
with `a > 0` or with a guarded junk value): this is the explicit case split for the zero-noise /
zero-projector endpoint instead of Lean's `a / 0 = 0`. -/
noncomputable def expTail (d : ℕ) (a s : ℝ) : ℝ :=
  if s = 0 then 0 else 2 * (d : ℝ) * Real.exp (-(a / s))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d m : ℕ}

/-- Section 2's "given `c`, the replications `ε⁽¹⁾, …, ε⁽ᵐ⁾` are independent, with independent
coordinates": the scalar noises `ε⁽ʳ⁾ₑ`, indexed by `(r, e)`, are conditionally jointly
independent given `σ(c)`, in the product form: for every finite set `S` of indices and bounded
measurable test functions `fᵢ`,
`𝔼[∏_{i∈S} fᵢ(εᵢ) | c] = ∏_{i∈S} 𝔼[fᵢ(εᵢ) | c]` almost surely. -/
def CondJointIndep (M : NoisyCostModel P d m) : Prop :=
  ∀ (S : Finset (Fin m × Fin d)) (f : Fin m × Fin d → ℝ → ℝ),
    (∀ i, Measurable (f i)) → (∀ i, ∃ C : ℝ, ∀ x, |f i x| ≤ C) →
    P[fun ω => ∏ i ∈ S, f i (M.ε i.1 ω i.2) | MeasurableSpace.comap M.c inferInstance] =ᵐ[P]
      fun ω => ∏ i ∈ S,
        P[fun ω' => f i (M.ε i.1 ω' i.2) | MeasurableSpace.comap M.c inferInstance] ω

/-- `P(A | c)`: the conditional expectation of the indicator of `A` given `σ(c)`. -/
noncomputable def condProbGivenCost (M : NoisyCostModel P d m) (A : Set Ω) : Ω → ℝ :=
  P[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap M.c inferInstance]

/-- The projection estimate `ĉ_Π = c̄ + Π(ȳ_m − c̄)` at the outcome `ω` (equation (1)). -/
noncomputable def costEstimate (M : NoisyCostModel P d m) (Q : Matrix (Fin d) (Fin d) ℝ)
    (ω : Ω) : Fin d → ℝ :=
  projEstimate Q M.costMean (M.obsAvg ω)

/-- The decision: a measurable random path `ẑ : Ω → ℝ^d` with `ẑ(ω) ∈ argmin_{z ∈ 𝒵} ĉ_Π(ω)ᵀz` at
every outcome (any choice among tied minimizers, possibly randomized; a deterministic tie-breaking
rule `z(ĉ_Π)` is a special case). -/
def IsDecision (M : NoisyCostModel P d m) (Z : Finset (Fin d → ℝ))
    (Q : Matrix (Fin d) (Fin d) ℝ) (zhat : Ω → Fin d → ℝ) : Prop :=
  Measurable zhat ∧ ∀ ω, IsOptimalPath Z (costEstimate M Q ω) (zhat ω)

/-- The event `{regret > 0}`: the chosen path `ẑ(ω)` has true cost `cᵀẑ` above the optimal cost
`min_z cᵀz`. -/
def regretEvent (M : NoisyCostModel P d m) (Z : Finset (Fin d → ℝ))
    (zhat : Ω → Fin d → ℝ) : Set Ω :=
  {ω | optCost Z (M.c ω) < M.c ω ⬝ᵥ zhat ω}

/-- The bias `β = ‖(I − Π)(c − c̄)‖₂` at the outcome `ω` (Euclidean norm). -/
noncomputable def biasNorm (M : NoisyCostModel P d m) (Q : Matrix (Fin d) (Fin d) ℝ)
    (ω : Ω) : ℝ :=
  Real.sqrt (sqNorm ((1 - Q) *ᵥ (M.c ω - M.costMean)))

end LowRankDenoise432.OptimalProjector.Supplement


