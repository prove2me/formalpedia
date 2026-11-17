-- Prove2me | Definitions.Def_IntervalToDynamic_Supplement_Geometry
-- name    : IntervalToDynamic_Supplement_Geometry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:35:43.250943+00:00
-- url     : https://prove2.me/theorems/091ad397-14d7-4a0b-8eed-9a83dacf759c
-- title:
--   Homogeneous interval aggregations, attained interval costs, and the cap profile $\Gamma_{\mathcal X}$
-- statement:
--   Rounds are numbered $1,\ldots,T$, and an interval is a nonempty integer interval $I=[a,b]\subseteq[T]$. A **homogeneous aggregation** is a family of weights $\lambda_I\ge0$ satisfying
--   $$
--   \sum_{I:t\in I}\lambda_I=1\qquad(t\in[T]).
--   $$
--   For continuous losses on a nonempty compact domain, the singleton-corrected interval cost is
--   $$
--   c_I=\begin{cases}
--   \min_{z\in\mathcal X}\sum_{t\in I}f_t(z)+A_T\rho(|I|),&|I|>1,\\
--   \min\{\min_{z\in\mathcal X}f_t(z)+A_T\rho(1),\ \max_{z\in\mathcal X}f_t(z)\},&I=\{t\}.
--   \end{cases}
--   $$
--   The associated dual value is $\sum_I\lambda_Ic_I-\sum_tf_t(u_t)$.
--
--   For compact convex $\mathcal X\subseteq\mathbb R^d$, let $s_{\mathcal X}(n)=\max_{x\in\mathcal X}n^\top x$ and $F_{\mathcal X}(n)=\arg\max_{x\in\mathcal X}n^\top x$. The **cap profile** $\Gamma_{\mathcal X}(r)$ is the supremum, over every positive finite family of unit normals $n_i$ and contacts $u_i\in F_{\mathcal X}(n_i)$ of diameter at most $r$, of
--   $$
--   \min_{z\in\mathcal X}\max_i\bigl(s_{\mathcal X}(n_i)-n_i^\top z\bigr).
--   $$
--
--   These objects make the exact duality of Theorem 2 and the geometry in Theorem 3 reusable without replacing fractional covers by partitions or restricting the number of contacts.
--
--   **Formalization Note** Finite minima and maxima are represented by real `sInf` and `sSup`; every theorem using them assumes nonemptiness, compactness and continuity, and Theorem 2 states attainment by explicit primal and dual witnesses.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Eqs. (4)–(8), pp.5–6 (PDF pp.7–8)

import Mathlib
import Definitions.Def_IntervalToDynamic_intervalRegret
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs

open ModernOnlineLearning.Dynamic (dynamicRegret pathLength)

namespace IntervalToDynamic.Supplement

/-- A nonempty integer interval contained in the paper's rounds `[T] = {1, ..., T}`. -/
abbrev RoundInterval (T : ℕ) :=
  {p : Fin (T + 1) × Fin (T + 1) // 1 ≤ p.1.1 ∧ p.1.1 ≤ p.2.1}

def RoundInterval.start {T : ℕ} (I : RoundInterval T) : ℕ := I.1.1.1
def RoundInterval.stop {T : ℕ} (I : RoundInterval T) : ℕ := I.1.2.1
def RoundInterval.rounds {T : ℕ} (I : RoundInterval T) : Finset ℕ :=
  Finset.Icc I.start I.stop

/-- A homogeneous aggregation (exact fractional interval cover), Eq. (7), p.5. -/
def IsHomogeneous {T : ℕ} (lam : RoundInterval T → ℝ) : Prop :=
  (∀ I, 0 ≤ lam I) ∧
  ∀ t ∈ Finset.Icc 1 T,
    (∑ I : RoundInterval T, (if t ∈ I.rounds then lam I else (0 : ℝ))) = 1

/-- The minimum value notation used in Theorem 2. Its hypotheses ensure the image is nonempty,
compact, and hence that this `sInf` is attained. -/
noncomputable def minOn {E : Type*} (X : Set E) (f : E → ℝ) : ℝ := sInf (f '' X)

/-- The maximum value notation used in Theorem 2. -/
noncomputable def maxOn {E : Type*} (X : Set E) (f : E → ℝ) : ℝ := sSup (f '' X)

/-- The singleton-corrected interval cost `c_I` in Theorem 2, p.5. -/
noncomputable def intervalCost {E : Type*} {T : ℕ} (X : Set E)
    (f : ℕ → E → ℝ) (A : ℝ) (rho : ℕ → ℝ) (I : RoundInterval T) : ℝ :=
  if I.rounds.card = 1 then
    min (minOn X (f I.start) + A * rho 1) (maxOn X (f I.start))
  else
    minOn X (fun z => ∑ t ∈ I.rounds, f t z) + A * rho I.rounds.card

/-- The dual objective `Σ_I λ_I c_I - Σ_t f_t(u_t)` in Theorem 2. -/
noncomputable def aggregationValue {E : Type*} {T : ℕ} (X : Set E)
    (f : ℕ → E → ℝ) (u : ℕ → E) (A : ℝ) (rho : ℕ → ℝ)
    (lam : RoundInterval T → ℝ) : ℝ :=
  (∑ I : RoundInterval T, lam I * intervalCost X f A rho I) -
    ∑ t ∈ Finset.Icc 1 T, f t (u t)

/-- All simultaneous OIR constraints (4) for an actual decision sequence. -/
def SatisfiesOIR {E : Type*} {T : ℕ} (X : Set E) (f : ℕ → E → ℝ)
    (x : ℕ → E) (A : ℝ) (rho : ℕ → ℝ) : Prop :=
  ∀ I : RoundInterval T, ∀ z ∈ X,
    IntervalToDynamic.intervalRegret f x I.start I.stop z ≤ A * rho I.rounds.card

/-- The unit `ℓ_p` ball in `ℝ²`, used in the two clauses of Theorem 1. -/
noncomputable def unitLpBall (p : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∑ i, |x i| ^ p ≤ 1}

/-- The support function `s_X(n)` in Definition 1, p.6. -/
noncomputable def support {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (n : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun x => inner ℝ n x) '' X)

/-- The exposed face `F_X(n)` in Definition 1. -/
noncomputable def exposedFace {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (n : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ X ∧ inner ℝ n x = support X n}

/-- The cap profile `Γ_X(r)` of Definition 1, Eq. (8), p.6.

The outer supremum ranges over arbitrary positive finite contact families. The theorem hypotheses
make every support and inner infimum attained and make the outer set nonempty and bounded. -/
noncomputable def capProfile {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (r : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (N : ℕ) (hN : 0 < N)
      (n u : Fin N → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖n i‖ = 1) ∧ (∀ i, u i ∈ exposedFace X (n i)) ∧
      (∀ i j, ‖u i - u j‖ ≤ r) ∧
      v = sInf ((fun z => sSup ((fun i => support X (n i) - inner ℝ (n i) z) '' Set.univ)) '' X)}

end IntervalToDynamic.Supplement


