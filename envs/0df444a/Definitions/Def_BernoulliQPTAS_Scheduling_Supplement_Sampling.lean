-- Prove2me | Definitions.Def_BernoulliQPTAS_Scheduling_Supplement_Sampling
-- name    : BernoulliQPTAS_Scheduling_Supplement_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:34:21.905766+00:00
-- url     : https://prove2.me/theorems/e5cac921-f729-4421-9434-cf539f8a6349
-- title:
--   The reweighted distribution $Q$, the estimator $\hat C$, list policies and the instance of Theorem 7.1
-- statement:
--   This file defines the objects of Sections 6.3 and 7, on top of the published Section 2 model.
--
--   **Reweighted distribution.** Let $\mu_i=q_ip_i$ and $P=\sum_i\mu_i$. Under $Q$ one chooses a job $i$ with probability $\mu_i/P$, sets $X_i=p_i$, and draws every other outcome independently from its own distribution. Thus
--
--   $$
--   Q(\omega)=\sum_i \frac{\mu_i}{P}\,\mathbf 1[\omega_i=1]\prod_{j\ne i}\Pr[\omega_j].
--   $$
--
--   **Estimator.** For a deterministic policy tree $t$ (a value of the policy's coins) and a realization $\omega$, let $V(\omega)=\sum_jX_j(\omega)$ and $C(t,\omega)$ be the realized sum of completion times. One simulation gives $Z=P\,C/V$. With $n=\lceil 3N\rho^{-2}\ln(2/\delta)\rceil$, the estimate is $\hat C=\frac1n\sum_{k=1}^nZ_k$, where the $n$ simulations are independent, each with fresh coins of the policy and a realization drawn from $Q$.
--
--   **List policies.** A randomized policy is a list policy if, for almost every value of its coins, the order in which it starts the jobs is one fixed list, the same on every outcome realization. Start times are unrestricted, so the policy may idle.
--
--   **Instance of Theorem 7.1.** For an integer $b$ let $M=2^b$. There are two machines and $N=bM$ jobs, $M$ of each type $i=0,\dots,b-1$, and a job of type $i$ has
--
--   $$
--   p_i=\frac{M^2}{4^i},\qquad q_i=\frac{2^i}{M^2}.
--   $$
--
--   **Formalization Note** Job $j\in\{0,\dots,bM-1\}$ has type $\lfloor j/M\rfloor$. Values of $Z$ and $\hat C$ are extended nonnegative reals, with $0/0=0$. $V=0$ has $Q$-probability zero.
-- source:
--   Junho Hwang, A QPTAS for Stochastic Scheduling of Bernoulli Jobs, STOC 2027 submission #427 (October 2026), PDF SHA-256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9, Section 6.3, pp. 19–20 (Theorem 6.4 and its proof: Q, V, C, Z, n); Section 7, p. 20 (list policies, instance of Theorem 7.1)

import Definitions.Def_BernoulliQPTAS_Scheduling_Objective

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling.Supplement

open BernoulliQPTAS.Scheduling MeasureTheory

/-! ### Section 6.3, pp. 19–20: the reweighted distribution and the estimator -/

/-- `P = Σ_j μ_j` as a nonnegative real. -/
noncomputable def meanNN {N m : ℕ} (I : Instance N m) : ℝ≥0 :=
  ∑ j, chance I j * processing I j true

/-- The probability of the realization `ω` under the reweighted distribution `Q` of p. 20:
    choose a job `i` with probability `μ_i / P`, set `X_i = p_i`, and draw every other
    outcome from its own distribution. -/
noncomputable def reweightedWeight {N m : ℕ} (I : Instance N m) (ω : Outcome N) : ℝ≥0 :=
  ∑ i, (chance I i * processing I i true / meanNN I) *
    (if ω i then ∏ j ∈ Finset.univ.erase i, (if ω j then chance I j else 1 - chance I j)
      else 0)

/-- The reweighted distribution `Q` as a measure on realizations. -/
noncomputable def reweightedLaw {N m : ℕ} (I : Instance N m) : Measure (Outcome N) :=
  ∑ ω, (reweightedWeight I ω : ℝ≥0∞) • Measure.dirac ω

instance reweightedLaw_finite {N m : ℕ} (I : Instance N m) :
    IsFiniteMeasure (reweightedLaw I) := by
  constructor
  simp only [reweightedLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun _ _ => ENNReal.coe_lt_top

/-- `V(ω) = Σ_j X_j(ω)`, the realized total processing time. -/
noncomputable def realizedVolume {N m : ℕ} (I : Instance N m) (ω : Outcome N) : ℝ≥0∞ :=
  ∑ j, (processing I j (ω j) : ℝ≥0∞)

/-- The estimator `Z = P · C / V` for one simulation: a deterministic tree `t` (the policy's
    coins) run on the realization `ω`; `C` is the realized sum of completion times. -/
noncomputable def estimatorSample {N m : ℕ} (I : Instance N m)
    (x : PolicyTree N m × Outcome N) : ℝ≥0∞ :=
  totalMean I Finset.univ * realizedCost I x.1 x.2 / realizedVolume I x.2

/-- The number of simulations `⌈3 N ρ^{-2} ln(2/δ)⌉`. -/
noncomputable def sampleCount (N : ℕ) (ρ δ : ℝ) : ℕ :=
  ⌈3 * (N : ℝ) * ρ ^ (-2 : ℤ) * Real.log (2 / δ)⌉₊

/-- The estimate `Ĉ`: the average of the `n` simulated values of `Z`. -/
noncomputable def estimate {N m : ℕ} (I : Instance N m) (n : ℕ)
    (xs : Fin n → PolicyTree N m × Outcome N) : ℝ≥0∞ :=
  (∑ k, estimatorSample I (xs k)) / (n : ℝ≥0∞)

/-- The joint law of `n` independent simulations: in each, fresh coins of the policy `π`
    (a tree drawn from `π.law`) and an independent realization drawn from `Q`. -/
noncomputable def samplingLaw {N m : ℕ} (I : Instance N m) (π : RandomPolicy N m) (n : ℕ) :
    Measure (Fin n → PolicyTree N m × Outcome N) :=
  haveI := π.probability
  Measure.pi fun _ : Fin n => π.law.prod (reweightedLaw I)

/-! ### Section 7, p. 20: list policies and the lower-bound instance -/

/-- A list policy: for every value of its coins (almost surely), the order in which the
    jobs are started is one fixed list, the same on every outcome realization. Start times
    are unrestricted, so idling is allowed. -/
def IsListPolicy {N m : ℕ} (π : RandomPolicy N m) : Prop :=
  ∀ᵐ t ∂π.law, ∃ l : List (Fin N), ∀ ω : Outcome N, (trace t ω).map Action.job = l

/-- The type `i = ⌊j / M⌋` of job `j` in the instance of Theorem 7.1, `M = 2^b`. -/
def jobType (b : ℕ) (j : Fin (b * 2 ^ b)) : ℕ := j.val / 2 ^ b

lemma jobType_lt (b : ℕ) (j : Fin (b * 2 ^ b)) : jobType b j < b := by
  unfold jobType
  exact Nat.div_lt_of_lt_mul (by simp [Nat.mul_comm])

/-- The instance of Theorem 7.1: two machines, `M = 2^b` jobs of each type
    `i = 0, …, b-1`, a job of type `i` having `p_i = M² / 4^i` and `q_i = 2^i / M²`. -/
def listInstance (b : ℕ) : Instance (b * 2 ^ b) 2 where
  size j := ((2 : ℚ) ^ b) ^ 2 / 4 ^ jobType b j
  probability j := 2 ^ jobType b j / ((2 : ℚ) ^ b) ^ 2
  size_pos _ := by positivity
  probability_pos _ := by positivity
  probability_le_one j := by
    rw [div_le_one (by positivity), ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by have := jobType_lt b j; omega)

end BernoulliQPTAS.Scheduling.Supplement


