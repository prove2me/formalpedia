-- Prove2me | Definitions.Def_ModernOnlineLearning_OnlineToBatch_Defs
-- name    : ModernOnlineLearning_OnlineToBatch_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:30.194161+00:00
-- url     : https://prove2.me/theorems/6e12faa8-1c3a-4f47-9fec-4a1e9f478e1e
-- title:
--   Chapter 3 setting: true risk, fixed-competitor regret, and history-dependent online predictions
-- statement:
--   Let $V\subseteq\mathbb R^d$ be a decision set, let $\rho$ be a distribution of data points $z\in D$, and let $f(x,z)$ be a real loss. The **true risk** is
--
--   $$F(x)=\mathbb E_{z\sim\rho}[f(x,z)].$$
--
--   For a deterministic online rule $A$, a sample path $(\xi_t)_{t\ge1}$ and a fixed comparator $u$, the **regret** through round $T$ is
--
--   $$\operatorname{Regret}_T(u)=\sum_{t=1}^T f(A_t(\xi),\xi_t)-\sum_{t=1}^T f(u,\xi_t).$$
--
--   The rule is **non-anticipating** when $A_t$ lies in $V$ and has the same output on any two sample paths agreeing at rounds $1,\ldots,t-1$. The empirical risk of $x$ is $T^{-1}\sum_{t=1}^T f(x,\xi_t)$; the best true risk of a finite set $S$ is $\inf_{x\in S}F(x)$.
--
--   These are the common objects in the conversion and finite-set validation statements.
--
--   **Formalization Note** Rounds start at one; index zero is unused. The real integral and the infimum are used only with measurable bounded losses and a nonempty finite $S$, respectively, in the theorems below.
-- source:
--   Orabona, arXiv:1912.13213v10, §1, p. 2; Theorem 3.10, p. 27; §3.2 and Theorem 3.17, pp. 31–32

import Mathlib

namespace ModernOnlineLearning.OnlineToBatch

/-- The book's decision space `ℝ^d` with its Euclidean structure. -/
abbrev Decision (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Expected loss under the data distribution. Used only when the section of `f` is measurable
and bounded, so the integral is genuine. -/
noncomputable def risk {E D : Type*} [MeasurableSpace D]
    (ρ : MeasureTheory.Measure D) (f : E → D → ℝ) (x : E) : ℝ :=
  ∫ z, f x z ∂ρ

/-- Regret against a fixed competitor for rounds `1,...,T`; index zero is unused. -/
def regret {E D : Type*} (f : E → D → ℝ)
    (A : ℕ → (ℕ → D) → E) (ω : ℕ → D) (u : E) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.Icc 1 T, f (A t ω) (ω t)) -
    (∑ t ∈ Finset.Icc 1 T, f u (ω t))

/-- A deterministic online algorithm sees only samples from earlier rounds and always
predicts in `V`. Its value at round zero is unused. -/
def IsOnlineAlgorithm {E D : Type*} (V : Set E)
    (A : ℕ → (ℕ → D) → E) : Prop :=
  (∀ t ω, 1 ≤ t → A t ω ∈ V) ∧
    (∀ t ω ω', 1 ≤ t →
      (∀ s, 1 ≤ s → s < t → ω s = ω' s) → A t ω = A t ω')

/-- The average loss of a fixed decision on the first `T` samples. -/
noncomputable def empiricalRisk {E D : Type*} (f : E → D → ℝ)
    (ω : ℕ → D) (x : E) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.Icc 1 T, f x (ω t)) / (T : ℝ)

/-- The lowest true risk among a finite validation set. Used only when the set is nonempty
and losses are measurable and bounded, so the real infimum is a minimum. -/
noncomputable def bestRisk {E D : Type*} [MeasurableSpace D]
    (ρ : MeasureTheory.Measure D) (f : E → D → ℝ) (S : Finset E) : ℝ :=
  sInf (risk ρ f '' (S : Set E))

end ModernOnlineLearning.OnlineToBatch


