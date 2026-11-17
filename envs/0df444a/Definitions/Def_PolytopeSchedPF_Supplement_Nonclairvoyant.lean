-- Prove2me | Definitions.Def_PolytopeSchedPF_Supplement_Nonclairvoyant
-- name    : PolytopeSchedPF_Supplement_Nonclairvoyant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:20:56.476423+00:00
-- url     : https://prove2.me/theorems/e5f2f0db-c877-48d9-8588-cb59810e47a5
-- title:
--   Deterministic and randomized nonclairvoyant scheduling policies and their competitiveness (§3.1, Definition 3.1)
-- statement:
--   Fix a rate polytope $P$ with all jobs released at time $0$. A **deterministic nonclairvoyant policy** maps every vector of processing requirements $p$ to a schedule $\mathrm{ALG}(p)$ such that
--
--   1. for every $p\in\mathbb R^n_{\ge0}$, $\mathrm{ALG}(p)$ is a feasible schedule for $p$;
--   2. (nonclairvoyance) the algorithm does not learn $p_j$ until job $j$ completes: if $p,p'\ge0$, $t\ge0$, and every job $j$ either has $p_j=p'_j$ or has received less processing $\int_0^t\mathrm{ALG}(p)_j$ by time $t$ than both $p_j$ and $p'_j$, then $\mathrm{ALG}(p)$ and $\mathrm{ALG}(p')$ coincide on $[0,t)$.
--
--   A **randomized nonclairvoyant algorithm** on $P$ is a probability space $(\Omega,\mu)$ of random bits, independent of the input, and for every $\omega\in\Omega$ a deterministic nonclairvoyant policy $A_\omega$, such that the total completion time $(\omega,p)\mapsto\sum_jC_j$ of $A_\omega$ on $p$ is jointly measurable. It is **$c$-competitive for total completion time** if for every $p\in\mathbb R^n_{\ge0}$
--
--   $$\mathbb E_\omega\Big[\sum_{j}C_j\Big]\le c\cdot\mathrm{OPT}(p),$$
--
--   where $\mathrm{OPT}(p)$ is the optimal total completion time (unit weights, release dates $0$).
--
--   These are the objects of the lower bound of Theorem 1.5.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0,\infty]$, so a non-integrable cost counts as $\infty$. Joint measurability is the standing convention that makes the expectation over $(p,\omega)$ in Yao's principle (p.43) meaningful. The random bits may live in a type of any universe.
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, §3.1 "Online algorithms for PSP", pp.13–14 (PDF pp.15–16); Definition 3.1, p.14 (PDF p.16); proof of Theorem 1.5 (nonanticipative policy, random bits R independent of p), pp.40, 43 (PDF pp.42, 45)

import Mathlib
import Definitions.Def_PolytopeSchedPF_Orders

namespace PolytopeSchedPF

namespace Supplement

open MeasureTheory

/-- **Deterministic nonclairvoyant policy, all jobs released at time `0`**
(Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §3.1 "Online algorithms for PSP", pp.13–14;
"deterministic nonanticipative policy" in the proof of Theorem 1.5, p.40).
A policy maps processing requirements `p` to a schedule `ALG p`. It is required that
(a) for every `p ∈ ℝⁿ_{≥0}`, `ALG p` is a feasible (speed-1) schedule for `p` with release dates `0`;
(b) nonclairvoyance: the algorithm "does not learn `p_j` until job `j` completes". If `p, p' ≥ 0`,
`t ≥ 0`, and every job `j` either has `p_j = p'_j`, or has received strictly less processing
`∫₀ᵗ (ALG p)_j` by time `t` than both `p_j` and `p'_j` (so it is unfinished at `t` under both
inputs), then `ALG p` and `ALG p'` coincide on `[0, t)`.

**Formalization Note** The policy may depend on the instance `P` (the matrix `B` and the weights are
known to an online algorithm once the jobs are released, here at time `0`). Condition (b) only lets
the schedule before `t` depend on the sizes of jobs that have completed by `t`. The sequential
schedule and PF satisfy (a) and (b), so the class is nonempty. -/
def IsNonclairvoyantPolicy {n D : ℕ} (P : RatePolytope n D)
    (ALG : (Fin n → ℝ) → ℝ → Fin n → ℝ) : Prop :=
  (∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j) → IsFeasible P p 0 (ALG p)) ∧
  ∀ p p' : Fin n → ℝ, (∀ j, 0 ≤ p j) → (∀ j, 0 ≤ p' j) → ∀ t : ℝ, 0 ≤ t →
    (∀ j, p j = p' j ∨
      ((∫ u in (0 : ℝ)..t, ALG p u j) < p j ∧ (∫ u in (0 : ℝ)..t, ALG p u j) < p' j)) →
    ∀ s : ℝ, 0 ≤ s → s < t → ALG p s = ALG p' s

/-- The total completion time `∑_j C_j` of the schedule a policy produces on input `p`, all release
dates `0` (§3.1, p.13; unit weights). -/
noncomputable def totalCompletion {n : ℕ} (ALG : (Fin n → ℝ) → ℝ → Fin n → ℝ)
    (p : Fin n → ℝ) : ℝ :=
  ∑ j, completionTime p 0 (ALG p) j

/-- **Randomized nonclairvoyant algorithm** on an instance `P` (Definition 3.1, p.14; proof of
Theorem 1.5, p.43): a probability space `(Ω, μ)` of internal random bits and, for every `ω ∈ Ω`, a
deterministic nonclairvoyant policy `A ω`. The random bits are independent of the input `p`, and
the cost `(ω, p) ↦ ∑_j C_j` is jointly measurable, so that expectations over `(p, ω)` (used in Yao's
principle, p.43) are defined.

**Formalization Note** The randomness lives in an arbitrary type `Ω : Type u` (universe
polymorphic). Joint measurability uses the Borel σ-algebra on `ℝⁿ` and the product σ-algebra. -/
structure RandomizedPolicy {n D : ℕ} (P : RatePolytope n D) where
  /-- The space of random bits. -/
  Ω : Type*
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- The distribution of the random bits. -/
  μ : Measure Ω
  /-- `μ` is a probability measure. -/
  [isProb : IsProbabilityMeasure μ]
  /-- The deterministic policy run for the random bits `ω`. -/
  A : Ω → (Fin n → ℝ) → ℝ → Fin n → ℝ
  /-- Every realization is a deterministic nonclairvoyant policy. -/
  nonclairvoyant : ∀ ω, IsNonclairvoyantPolicy P (A ω)
  /-- The cost is jointly measurable in the random bits and the input. -/
  measurable_cost : Measurable (fun x : Ω × (Fin n → ℝ) => totalCompletion (A x.1) x.2)

attribute [instance] RandomizedPolicy.mΩ RandomizedPolicy.isProb

/-- The expected total completion time `E_ω[∑_j C_j]` of a randomized policy on input `p`, as a
lower Lebesgue integral in `ℝ≥0∞` (so a non-integrable cost is `∞`, never `0`). -/
noncomputable def RandomizedPolicy.expectedCost {n D : ℕ} {P : RatePolytope n D}
    (R : RandomizedPolicy P) (p : Fin n → ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (totalCompletion (R.A ω) p) ∂(R.μ)

/-- A randomized policy is **`c`-competitive for total completion time** on `P` with all release
dates `0` (Definition 3.1, p.14) if for every input `p ∈ ℝⁿ_{≥0}` its expected cost is at most
`c · OPT(p)`, where `OPT(p)` is the base `opt0 P 1 p` (unit weights, release dates `0`). -/
def RandomizedPolicy.IsCompetitive {n D : ℕ} {P : RatePolytope n D}
    (R : RandomizedPolicy P) (c : ℝ) : Prop :=
  ∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j) →
    R.expectedCost p ≤ ENNReal.ofReal (c * opt0 P (fun _ => 1) p)

end Supplement

end PolytopeSchedPF


