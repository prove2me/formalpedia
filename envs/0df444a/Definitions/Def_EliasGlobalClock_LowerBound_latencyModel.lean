-- Prove2me | Definitions.Def_EliasGlobalClock_LowerBound_latencyModel
-- name    : EliasGlobalClock_LowerBound_latencyModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:01.669213+00:00
-- url     : https://prove2.me/theorems/b5ad35a9-ee12-4c78-9b9e-3fbcf90d1271
-- title:
--   Uniform operational latency, admissible errors and dyadic summands
-- statement:
--   Fix a shared probability law $\nu$, an anonymous protocol, and an error profile $\epsilon:\mathbb Z_+\to(0,1)$ that is nonincreasing. A latency profile $L:\mathbb Z_+\to\mathbb N$ is valid when every deterministic finite spontaneous wake-up assignment with population at most $n$ and first wake-up time $t_0$ satisfies
--
--   $$\Pr(t^*-t_0>L(n))<\epsilon(n).$$
--
--   The probability integrates the conditional product law over the actual shared-input law. The constructed first-success time $t^*$ is infinite for executions that never succeed. The definition includes every starting time and does not assume termination. The profile $\epsilon$ is fixed, so $L(n)$ denotes the paper's $L(n,\epsilon)$.
--
--   The error-growth predicate means that there are one constant $C>0$ and one cutoff $n_0$ such that, for every positive integer $n\ge n_0$, $\ln(1/\epsilon(n))\le C n^{1-\eta}$. The integer tail-minimum envelope is $\widehat L(n)=\min_{k\ge n}L(k)$; its defining set is nonempty. Finally the dyadic summand is
--
--   $$a_i=\frac{\ln(1/\epsilon(2^{i+1}))}{L(2^{i+1})},\qquad i=0,1,\ldots.$$
--
--   These definitions keep the operational guarantee separate from the lower-bound lemmas. No monotonicity condition is built into $L$.
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), printed pp.1, 7–8, 11–12, PDF pp.2, 8–9, 12–13, latency definition and Theorem 4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_streamProtocol

open MeasureTheory ProbabilityTheory

namespace EliasGlobalClock.LowerBound

/-- A fixed whole error profile, defined at every positive population size. -/
def ErrorProfile (ε : ℕ+ → ℝ) : Prop :=
  Antitone ε ∧ ∀ n, 0 < ε n ∧ ε n < 1

/-- One finite bound at each population scale, uniformly over all deterministic
spontaneous patterns and all starting slots. The rule receives none of this data.
L is the latency at the fixed whole profile ε, not a separate per-scalar protocol. -/
noncomputable def IsLatency {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : StreamProtocol Ω) (ε : ℕ+ → ℝ) (L : ℕ+ → ℕ) : Prop :=
  ∀ (n : ℕ+) (r t₀ : ℕ) (wake : Fin r → ℕ),
    0 < r → r ≤ (n : ℕ) → (∀ u, t₀ ≤ wake u) → (∃ u, wake u = t₀) →
      (∫⁻ y, privateLaw P wake y (actualFail wake (t₀ + L n)) ∂ν) <
        ENNReal.ofReal (ε n)

/-- The source's big-O hypothesis has one fixed constant and cutoff, before n. -/
def ErrorGrowth (ε : ℕ+ → ℝ) (η : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ+, n₀ ≤ (n : ℕ) →
    Real.log (1 / ε n) ≤ C * (n : ℝ) ^ (1 - η)

/-- An attained tail minimum of integer latency bounds. The defining set is
nonempty (take k=n). It supplies the internal monotone-envelope bridge, rather
than imposing a monotonicity hypothesis on a source latency profile. -/
noncomputable def latencyEnvelope (L : ℕ+ → ℕ) (n : ℕ+) : ℕ :=
  sInf {b : ℕ | ∃ k : ℕ+, n ≤ k ∧ L k = b}

/-- Population sizes 2,4,8,...; the natural argument is shifted to start at i=1. -/
def dyadicPopulation (i : ℕ) : ℕ+ := ⟨2 ^ (i + 1), by positivity⟩

noncomputable def latencyTerm (ε : ℕ+ → ℝ) (L : ℕ+ → ℕ) (i : ℕ) : ℝ :=
  Real.log (1 / ε (dyadicPopulation i)) / (L (dyadicPopulation i) : ℝ)

end EliasGlobalClock.LowerBound


