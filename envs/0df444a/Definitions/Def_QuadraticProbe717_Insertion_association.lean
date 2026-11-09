-- Prove2me | Definitions.Def_QuadraticProbe717_Insertion_association
-- name    : QuadraticProbe717_Insertion_association
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:20:23.204585+00:00
-- url     : https://prove2.me/theorems/10bdb16c-d9bf-44df-8305-b461ea79a949
-- title:
--   Positive association and independent marginal comparison laws
-- statement:
--   Let $P$ be a probability law, and let $X=(X_i)_{i\in I}$ be a finite real random vector. Write $\operatorname{Cov}_P$ for covariance. Covariance is said to exist when both arguments and their product are integrable. The vector is positively associated if
--   $$
--   \operatorname{Cov}_P(f(X),g(X))\ge0
--   $$
--   for every pair of coordinatewise nondecreasing real functions $f,g$ for which the covariance exists. Neither identical coordinate laws nor independence is part of this definition.
--
--   For indicator coordinates, define $S=\sum_iX_i$ and $d=\sum_{i<j}\operatorname{Cov}_P(X_i,X_j)$. The independent comparison law is the product of the actual marginal laws, $\bigotimes_i\mathcal L_P(X_i)$; it is a construction, not a certificate supplied by a hypothesis.
--
--   These definitions support Harris's inequality with unbounded inputs and the general concentration statements in Section 5. The marginal maps are used only with measurable coordinates in those statements.
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Section 2, positive association; Section 5, p. 9, p. 5 (PDF p. 5)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace QuadraticProbe717.Insertion

/-- Covariance exists when both tests and their product are integrable; no L² restriction. -/
def CovarianceExists {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ) : Prop :=
  Integrable f P ∧ Integrable g P ∧ Integrable (fun ω => f ω * g ω) P

/-- Full association, testing every increasing pair, rather than just individual coordinates. -/
def PositivelyAssociated {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → ℝ) : Prop :=
  ∀ f g : (ι → ℝ) → ℝ, Monotone f → Monotone g →
    CovarianceExists P (fun ω => f (fun i => X i ω)) (fun ω => g (fun i => X i ω)) →
    0 ≤ covariance (fun ω => f (fun i => X i ω)) (fun ω => g (fun i => X i ω)) P

def indicatorSum {Ω : Type*} (s : ℕ) (X : Fin s → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, X i ω

noncomputable def pairCovarianceSum {Ω : Type*} [MeasurableSpace Ω]
    (s : ℕ) (P : Measure Ω) (X : Fin s → Ω → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then covariance (X i) (X j) P else 0

/-- Product of the actual marginal laws: independent copies, without extra marginal hypotheses. -/
noncomputable def independentMarginals {Ω : Type*} [MeasurableSpace Ω]
    (s : ℕ) (P : Measure Ω) (X : Fin s → Ω → ℝ) : Measure (Fin s → ℝ) :=
  Measure.pi (fun i => Measure.map (X i) P)

end QuadraticProbe717.Insertion


