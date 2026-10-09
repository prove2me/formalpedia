-- Prove2me | Definitions.Def_ModernOnlineLearning_Bandits_Tsallis
-- name    : ModernOnlineLearning_Bandits_Tsallis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:37:29.691113+00:00
-- url     : https://prove2.me/theorems/39a387a3-c3b0-4892-8e56-272436ccb1d5
-- title:
--   Algorithm 9.6, p. 166 — Tsallis-INF with importance-weighted losses and FTRL updates
-- statement:
--   **Tsallis-INF**, in the FTRL version of Algorithm 9.6, maintains a probability vector $x_t$ over $d$ arms. After drawing $A_t\sim x_t$, it estimates the loss of arm $i$ as $\widetilde g_{t,i}=g_{t,i}/x_{t,i}$ when $i=A_t$, and zero otherwise. Its next prediction minimizes
--
--   $$x\longmapsto\left\langle\sum_{s=1}^{t-1}\widetilde g_s,x\right\rangle-4L_\infty\sqrt t\sum_{i=1}^{d}\sqrt{x_i}$$
--
--   over the probability simplex. The run predicate states this minimization in every history; it is the algorithm referred to by Theorem 9.17.
--
--   **Formalization Note** All coordinates of the chosen minimizer are positive, so the importance-weighted estimator never divides by zero. Predictability across histories is stated explicitly; both properties follow from the strictly convex FTRL objective. The draws themselves are represented by the finite path law in the protocol definition.
-- source:
--   Orabona, arXiv:1912.13213v10, Algorithm 9.6 and proof of Theorem 9.17, p. 166

import Definitions.Def_ModernOnlineLearning_Bandits_Protocol
set_option autoImplicit false
noncomputable section

namespace ModernOnlineLearning.Bandits

/-- Importance-weighted estimate from Algorithm 9.6. -/
def lossEstimate {T d : ℕ} (g : ℕ → Fin d → ℝ)
    (x : ArmPath T d → ℕ → Fin d → ℝ) (A : ArmPath T d)
    (t : ℕ) (i : Fin d) : ℝ :=
  if armAt A t = i then g t i / x A t i else 0

/-- The exact FTRL objective in line 2 of Algorithm 9.6. -/
def tsallisObjective {T d : ℕ} (L : ℝ) (g : ℕ → Fin d → ℝ)
    (x : ArmPath T d → ℕ → Fin d → ℝ) (A : ArmPath T d)
    (t : ℕ) (p : Fin d → ℝ) : ℝ :=
  (∑ i, (∑ s ∈ Finset.Ico 1 t, lossEstimate g x A s i) * p i) -
    4 * L * Real.sqrt (t : ℝ) * ∑ i, Real.sqrt (p i)

/-- All possible histories satisfy Algorithm 9.6. The interior and predictability
    clauses spell out properties of its FTRL minimizer needed for the finite law. -/
def IsTsallisRun {T d : ℕ} (L : ℝ) (g : ℕ → Fin d → ℝ)
    (x : ArmPath T d → ℕ → Fin d → ℝ) : Prop :=
  (∀ A t, t ∈ Finset.Icc 1 T →
    IsSimplex (x A t) ∧
    (∀ i, 0 < x A t i) ∧
    (∀ p, IsSimplex p →
      tsallisObjective L g x A t (x A t) ≤ tsallisObjective L g x A t p)) ∧
  (∀ A B t, t ∈ Finset.Icc 1 T →
    (∀ s, s ∈ Finset.Ico 1 t → armAt A s = armAt B s) →
    x A t = x B t)

/-- The expected mix-loss expression on the left of (9.8). -/
def expectedMixRegret {T d : ℕ} (anchor : Fin d)
    (g : ℕ → Fin d → ℝ)
    (x : ArmPath T d → ℕ → Fin d → ℝ) (k : Fin d) : ℝ :=
  ∑ A : ArmPath T d, pathWeight anchor x A *
    ∑ t ∈ Finset.Icc 1 T,
      ((∑ i, g t i * x A t i) - g t k)

/-- Expected square root of the probability of arm `i` in round `t`. -/
def expectedSqrtProbability {T d : ℕ} (anchor : Fin d)
    (x : ArmPath T d → ℕ → Fin d → ℝ) (t : ℕ) (i : Fin d) : ℝ :=
  ∑ A : ArmPath T d, pathWeight anchor x A * Real.sqrt (x A t i)


end ModernOnlineLearning.Bandits


