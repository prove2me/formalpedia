-- Prove2me | Definitions.Def_MussaRosen_Mono_Setting
-- name    : MussaRosen_Mono_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:56:32.210497+00:00
-- url     : https://prove2.me/theorems/3209b8d2-7804-4395-b9c0-22324c44c776
-- title:
--   §2, §4, pp. 303–309 — admissible assignments, consumer surplus z, profit Π, optimality, the first variation Λ(h; q) of (9), and μ(t) of (10)
-- statement:
--   This module fixes the objects of Mussa and Rosen's monopoly quality problem.
--
--   **Types and costs.** Consumers differ by a taste parameter $\theta\in[\underline\theta,\bar\theta]$ with density $f$ (the published `TypeDistribution`: $f>0$ on $[\underline\theta,\bar\theta]$, $\int_{\underline\theta}^{\bar\theta} f=1$, and $F(\theta)=\int_{\underline\theta}^{\theta}f(s)\,ds$). A consumer of type $\theta$ who buys one unit of quality $q$ at price $p$ has utility $x+\theta q$; producing a unit of quality $q$ costs $C(q)$. An **assignment** is a function $q(\theta)$ giving the quality bought by type $\theta$; quality $0$ means not buying.
--
--   **Admissible assignments.** $q$ is *piecewise differentiable* if it is differentiable at every point of $(\underline\theta,\bar\theta)$ outside a finite set. $q$ is *admissible* if it is nondecreasing on $[\underline\theta,\bar\theta]$, satisfies $q(\theta)\ge 0$ there, and is piecewise differentiable.
--
--   **Surplus and profit.** The consumer surplus of type $\theta$ is
--   $$z(\theta)=\int_{\underline\theta}^{\theta}q(s)\,ds,$$
--   which is equation (7) with the boundary condition $z(\theta^*)=0$. The monopolist's profit is
--   $$\Pi(q)=\int_{\underline\theta}^{\bar\theta}\bigl[\theta\,q(\theta)-z(\theta)-C(q(\theta))\bigr]f(\theta)\,d\theta .$$
--   An assignment is **optimal** if it is admissible and no admissible assignment gives a larger profit.
--
--   **First variation and $\mu$.** For a deformation $h$, equation (9) defines
--   $$\Lambda(h;q)=\int_{\underline\theta}^{\bar\theta}\Bigl[\theta\,h(\theta)-\int_{\underline\theta}^{\theta}h(s)\,ds-C'(q(\theta))\,h(\theta)\Bigr]f(\theta)\,d\theta ,$$
--   and the first line of equation (10) defines the marginal profit of raising quality by one unit for all types $\theta\ge t$:
--   $$\mu(t)=\int_{t}^{\bar\theta}\Bigl[\theta-\int_t^{\theta}ds-C'(q(\theta))\Bigr]f(\theta)\,d\theta .$$
--   Finally, footnote 4's two-type profit is
--   $$n^1\bigl(\theta^1q^a-C(q^a)\bigr)+n^2\bigl(\theta^2q^b-(\theta^2-\theta^1)q^a-C(q^b)\bigr).$$
--
--   These objects are shared by every statement of the mission. The marginal revenue $MR(\theta)=\theta-(1-F(\theta))/f(\theta)$ of (8) is the published `virtualValuation`.
--
--   **Formalization Note** Assignments are total functions $\mathbb R\to\mathbb R$; only their values on $[\underline\theta,\bar\theta]$ enter. The cost hypotheses ($C'>0$, $C''>0$ on $q\ge 0$) are not part of these definitions; every theorem states them. $F$ is integrated from $\underline\theta$, while the paper writes $\int_0^\theta f$ on p. 307; the two agree because $f$ is a density on $[\underline\theta,\bar\theta]$. The inner integral $\int_t^\theta ds$ of (10) is kept literally.
-- source:
--   Mussa and Rosen, Monopoly and product quality, J. Econ. Theory 18 (1978), pp. 303–309, §2, §4, (7), (9), (10); footnote 4, pp. 305–306

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model
import Definitions.Def_MechanismDesign_Screening_NonlinearPricing

namespace MussaRosen.Mono

open MechanismDesign.Screening intervalIntegral

/-!
# Mussa and Rosen (1978), the monopolist's quality-assignment problem (§2, §4, pp. 303–309)

Consumer types `θ ∈ [θ̲, θ̄]` (`θlo`, `θhi`) are distributed with the density `D.f` of a
`TypeDistribution`; the cost of one unit of quality `q` is `C q`. An assignment `q : ℝ → ℝ`
gives the quality bought by type `θ`; only its values on `[θ̲, θ̄]` matter. None of the
definitions below carries the cost hypotheses: those are hypotheses of the theorems.
-/

variable {θlo θhi : ℝ}

/-- **Piecewise differentiable** (p. 308): `q` is differentiable at every point of `(θ̲, θ̄)`
outside some finite set. -/
def IsPiecewiseDiff (θlo θhi : ℝ) (q : ℝ → ℝ) : Prop :=
  ∃ s : Finset ℝ, ∀ θ ∈ Set.Ioo θlo θhi, θ ∉ s → DifferentiableAt ℝ q θ

/-- An **admissible assignment** (pp. 303, 308): nondecreasing on `[θ̲, θ̄]`, of feasible
quality `q(θ) ≥ 0` on `[θ̲, θ̄]`, and piecewise differentiable. -/
def IsAdmissible (θlo θhi : ℝ) (q : ℝ → ℝ) : Prop :=
  MonotoneOn q (Set.Icc θlo θhi) ∧ (∀ θ ∈ Set.Icc θlo θhi, 0 ≤ q θ) ∧ IsPiecewiseDiff θlo θhi q

/-- **Consumer surplus** `z(θ) = ∫_{θ̲}^{θ} q(s) ds`: equation (7) with the boundary condition
`z(θ*) = 0` (p. 307), in the form written on p. 315. -/
noncomputable def surplus (θlo : ℝ) (q : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ s in θlo..θ, q s

/-- The monopolist's **profit** (p. 308):
`Π(q) = ∫_{θ̲}^{θ̄} [θ q(θ) − z(θ) − C(q(θ))] f(θ) dθ`. -/
noncomputable def profit (D : TypeDistribution θlo θhi) (C : ℝ → ℝ) (q : ℝ → ℝ) : ℝ :=
  ∫ θ in θlo..θhi, (θ * q θ - surplus θlo q θ - C (q θ)) * D.f θ

/-- `q` is an **optimal** assignment (p. 308): it is admissible and no admissible assignment
yields a larger profit. -/
def IsOptimal (D : TypeDistribution θlo θhi) (C : ℝ → ℝ) (q : ℝ → ℝ) : Prop :=
  IsAdmissible θlo θhi q ∧ ∀ q' : ℝ → ℝ, IsAdmissible θlo θhi q' → profit D C q' ≤ profit D C q

/-- The **first variation** `Λ(h; q)` of the profit in the direction of a deformation `h`
(equation (9), p. 308):
`Λ(h; q) = ∫_{θ̲}^{θ̄} [θ h(θ) − ∫_{θ̲}^{θ} h(s) ds − C′(q(θ)) h(θ)] f(θ) dθ`. -/
noncomputable def firstVariation (D : TypeDistribution θlo θhi) (C q h : ℝ → ℝ) : ℝ :=
  ∫ θ in θlo..θhi, (θ * h θ - (∫ s in θlo..θ, h s) - deriv C (q θ) * h θ) * D.f θ

/-- The marginal profit `μ(t)` of a unit increase in quality for all types `θ ≥ t`, the first
line of equation (10), p. 309:
`μ(t) = ∫_t^{θ̄} [θ − ∫_t^{θ} ds − C′(q(θ))] f(θ) dθ`. -/
noncomputable def mu (D : TypeDistribution θlo θhi) (C q : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ θ in t..θhi, (θ - (∫ _s in t..θ, (1 : ℝ)) - deriv C (q θ)) * D.f θ

/-- The monopolist's profit with two consumer types (footnote 4, pp. 305–306): `n¹` consumers of
type `θ¹` buy quality `q^a`, `n²` consumers of type `θ²` buy quality `q^b`:
`n¹ (θ¹ q^a − C(q^a)) + n² (θ² q^b − (θ² − θ¹) q^a − C(q^b))`. -/
def twoTypeProfit (C : ℝ → ℝ) (θ1 θ2 n1 n2 qa qb : ℝ) : ℝ :=
  n1 * (θ1 * qa - C qa) + n2 * (θ2 * qb - (θ2 - θ1) * qa - C qb)

end MussaRosen.Mono


