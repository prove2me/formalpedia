-- Prove2me | Definitions.Def_TightReleaseSchedules_Stationary_gaussian_experiment
-- name    : TightReleaseSchedules_Stationary_gaussian_experiment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:43:17.665205+00:00
-- url     : https://prove2.me/theorems/2024d08f-209e-48de-a9b6-b815db345d24
-- title:
--   Passive Gaussian observations, anchored moments and convex projection
-- statement:
--   Let $T$ be a horizon and $d$ a Euclidean dimension. A deterministic path $\theta_1,\ldots,\theta_T$ generates independent standard Gaussian designs $X_i\in\mathbb R^d$ and independent standard Gaussian noises $\xi_i\in\mathbb R$. The observed row and its anchored cross-moment, relative to a known vector $\theta_0$, are
--
--   $$
--   Y_i=X_i^\top\theta_i+\xi_i,\qquad Z_i=X_i(Y_i-X_i^\top\theta_0).
--   $$
--   For a deterministic finite set $I$ of rounds, the anchored average is $|I|^{-1}\sum_{i\in I}Z_i$ and the average shift is $|I|^{-1}\sum_{i\in I}(\theta_i-\theta_0)$. The covariance entries are the actual scalar covariances of the coordinates of $Z_i$. The projection $\Pi_K(x)$ is the Euclidean nearest point in a nonempty closed convex set $K$. These definitions supply the experiment and estimators shared by the goal and Lemma 3.3.
--
--   **Formalization Note** Vectors use Euclidean space, rows are indexed by `Fin T` with index $i$ denoting round $i+1$, and the row law is a product of Mathlib standard Gaussian measures. Projection is selected using Mathlib's Hilbert projection existence theorem. Outside its nonempty closed convex domain its value is set to zero; no theorem here uses that branch. Empty-window averages are also assigned Lean's default value zero; the lemma and all effective algorithm releases use nonempty windows.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), §§3.1, 3.4, printed pp.6–7, PDF pp.7–8; notation, printed pp.5–6, PDF pp.6–7

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace TightReleaseSchedules.Stationary

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Data (T d : ℕ) := Fin T → Vector d × ℝ
abbrev GaussianRows (T d : ℕ) := Fin T → Vector d × ℝ

/-- Independent standard Gaussian designs and unit Gaussian label noises. -/
def gaussianRows (T d : ℕ) : Measure (GaussianRows T d) :=
  Measure.pi (fun _ => (stdGaussian (Vector d)).prod (gaussianReal 0 1))

/-- The target is data-generating input, never a policy argument. Index `i` is round `i+1`. -/
def observations {T d : ℕ} (θ : Fin T → Vector d) (z : GaussianRows T d) : Data T d :=
  fun i => ((z i).1, inner ℝ (z i).1 (θ i) + (z i).2)

def crossMoment {d : ℕ} (θ₀ : Vector d) (row : Vector d × ℝ) : Vector d :=
  (row.2 - inner ℝ row.1 θ₀) • row.1

def anchoredAverage {T d : ℕ} (θ₀ : Vector d) (I : Finset (Fin T))
    (h : Data T d) : Vector d :=
  (I.card : ℝ)⁻¹ • ∑ i ∈ I, crossMoment θ₀ (h i)

def pathAverage {T d : ℕ} (β : Fin T → Vector d) (I : Finset (Fin T)) : Vector d :=
  (I.card : ℝ)⁻¹ • ∑ i ∈ I, β i

/-- The actual Hilbert-space projection, selected from the standard existence theorem.
Outside the nonempty closed convex domain the value is irrelevant and set to zero. -/
def convexProjection {d : ℕ} (K : Set (Vector d)) (x : Vector d) : Vector d := by
  classical
  exact if h : K.Nonempty ∧ IsClosed K ∧ Convex ℝ K then
    Classical.choose (exists_norm_eq_iInf_of_complete_convex h.1 h.2.1.isComplete h.2.2 x)
  else 0

def crossCovariance {T d : ℕ} (θ₀ : Vector d) (θ : Fin T → Vector d)
    (i : Fin T) (k l : Fin d) : ℝ :=
  covariance (fun z => crossMoment θ₀ (observations θ z i) k)
    (fun z => crossMoment θ₀ (observations θ z i) l) (gaussianRows T d)

end TightReleaseSchedules.Stationary


