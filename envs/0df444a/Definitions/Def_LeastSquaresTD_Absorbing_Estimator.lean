-- Prove2me | Definitions.Def_LeastSquaresTD_Absorbing_Estimator
-- name    : LeastSquaresTD_Absorbing_Estimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:37:36.992625+00:00
-- url     : https://prove2.me/theorems/0ba48149-aede-46f1-9d85-d8fa9bf2c4e0
-- title:
--   Trial-based LS TD estimate and restart-process law
-- statement:
--   Let $Z_0,Z_1,\ldots$ be the states of the **restart process**: from $x\in\mathcal N$ it moves according to $P(x,\cdot)$; from $x\in\mathcal T$ it draws a new start state according to $S$. Its finite path probabilities are the Markov cylinder probabilities with initial law $S$ and this restart kernel. Let $\phi_x\in\mathbb R^m$ be the feature vector of $x$.
--
--   Equation (11) applied to the transitions within trials gives
--
--   $$
--   A_n=\sum_{\substack{k<n\\ Z_k\in\mathcal N}}\phi_{Z_k}(\phi_{Z_k}-\gamma\phi_{Z_{k+1}})^\top,\quad
--   b_n=\sum_{\substack{k<n\\ Z_k\in\mathcal N}}R(Z_k,Z_{k+1})\phi_{Z_k},\quad
--   \theta_n=A_n^{-1}b_n.
--   $$
--
--   This is the estimator studied by the mission. The definition also names the matrix $M=\Phi^\top\Pi(I-\gamma P)\Phi$ and vector $c=\Phi^\top\Pi\bar r$ appearing in Lemma 5, where the rows of $\Phi$ are the features and $\Pi=\operatorname{diag}(\pi)$.
--
--   **Formalization Note** Figure 2 resets its time index between trials. Here $n$ counts restart-process steps, so an estimate repeats during a restart draw; only transitions departing non-absorbing states enter $A_n,b_n$. The common factors $1/t$ in (11) cancel. A singular matrix has Lean's total-inverse default until the estimate becomes well defined; the convergence theorem concerns its asymptotic value.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), https://doi.org/10.1023/A:1018056104778, p. 42, Figure 2 and Eq. (11); p. 43, Lemma 5

import Definitions.Def_LeastSquaresTD_Absorbing_Chain

namespace LeastSquaresTD.Absorbing

open MeasureTheory Filter Topology

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ}

/-- Equation (11) on every transition of an ordinary Markov chain, as in
Lemma 5. -/
noncomputable def chainLstdA (φ : X → Fin m → ℝ) (γ : ℝ)
    (z : ℕ → X) (n : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ k ∈ Finset.range n,
    Matrix.vecMulVec (φ (z k)) (φ (z k) - γ • φ (z (k + 1)))

/-- The reward sum in (11) on every ordinary-chain transition. -/
noncomputable def chainLstdB (R : X → X → ℝ) (φ : X → Fin m → ℝ)
    (z : ℕ → X) (n : ℕ) : Fin m → ℝ :=
  ∑ k ∈ Finset.range n, R (z k) (z (k + 1)) • φ (z k)

/-- The ordinary-chain LS TD estimate of Lemma 5. The common `1/t` factors
in (11) cancel for positive `t`. -/
noncomputable def chainLstdTheta (R : X → X → ℝ) (φ : X → Fin m → ℝ)
    (γ : ℝ) (z : ℕ → X) (n : ℕ) : Fin m → ℝ :=
  Matrix.mulVec (chainLstdA φ γ z n)⁻¹ (chainLstdB R φ z n)

/-- Equation (11), p. 42, on the transitions performed inside trials in Figure 2.
The paper's factors `1/t` cancel when the matrix is invertible. Restart draws
are excluded, and `n` counts restart-process steps rather than only transitions. -/
noncomputable def lstdA (C : Chain X) (φ : X → Fin m → ℝ) (γ : ℝ)
    (z : ℕ → X) (n : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ k ∈ (Finset.range n).filter (fun k => C.P (z k) (z k) ≠ 1),
    Matrix.vecMulVec (φ (z k)) (φ (z k) - γ • φ (z (k + 1)))

/-- The reward-weighted feature sum in (11), restricted to in-trial transitions. -/
noncomputable def lstdB (C : Chain X) (R : X → X → ℝ) (φ : X → Fin m → ℝ)
    (z : ℕ → X) (n : ℕ) : Fin m → ℝ :=
  ∑ k ∈ (Finset.range n).filter (fun k => C.P (z k) (z k) ≠ 1),
    R (z k) (z (k + 1)) • φ (z k)

/-- The trial-based LS TD estimate (11). Lean's inverse is total and gives a
default on singular matrices; the convergence result entails eventual nonsingularity. -/
noncomputable def lstdTheta (C : Chain X) (R : X → X → ℝ)
    (φ : X → Fin m → ℝ) (γ : ℝ) (z : ℕ → X) (n : ℕ) : Fin m → ℝ :=
  Matrix.mulVec (lstdA C φ γ z n)⁻¹ (lstdB C R φ z n)

/-- The matrix in Lemma 5, with `Φ` the matrix whose row is `φ x`. -/
noncomputable def limitMatrix (C : Chain X) (φ : X → Fin m → ℝ)
    (γ : ℝ) (π : X → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.transpose (Matrix.of φ) * Matrix.diagonal π * (1 - γ • C.P) * Matrix.of φ

/-- The right-hand vector in Lemma 5. -/
noncomputable def limitVector (C : Chain X) (R : X → X → ℝ)
    (φ : X → Fin m → ℝ) (π : X → ℝ) : Fin m → ℝ :=
  Matrix.mulVec (Matrix.transpose (Matrix.of φ))
    (Matrix.mulVec (Matrix.diagonal π) (C.rbar R))

/-- The cylinder-distribution description of the restart process of Figure 2.
`X` has a discrete measurable space in the theorems. -/
def HasRestartLaw {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (C : Chain X) (S : X → ℝ) (μ : Measure Ω) (Z : ℕ → Ω → X) : Prop :=
  (∀ n, Measurable (Z n)) ∧
  ∀ (n : ℕ) (xs : Fin (n + 1) → X),
    μ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} =
      ENNReal.ofReal (S (xs 0) * ∏ i : Fin n,
        C.restartKernel S (xs i.castSucc) (xs i.succ))

/-- Finite-dimensional distributions of the ordinary Markov chain in
Lemma 5, with arbitrary initial distribution `S`. -/
def HasChainLaw {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (C : Chain X) (S : X → ℝ) (μ : Measure Ω) (Z : ℕ → Ω → X) : Prop :=
  (∀ n, Measurable (Z n)) ∧
  ∀ (n : ℕ) (xs : Fin (n + 1) → X),
    μ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} =
      ENNReal.ofReal (S (xs 0) * ∏ i : Fin n,
        C.P (xs i.castSucc) (xs i.succ))

/-- Empirical proportion of all transitions leaving a state, for Lemma 5. -/
noncomputable def chainOutFrequency (z : ℕ → X) (x : X) (n : ℕ) : ℝ :=
  ((Finset.range n).filter (fun k => z k = x)).card / n

/-- Empirical proportion of in-trial transitions leaving `x`. -/
noncomputable def outFrequency (C : Chain X) (z : ℕ → X) (x : X) (n : ℕ) : ℝ :=
  ((Finset.range n).filter (fun k => C.P (z k) (z k) ≠ 1 ∧ z k = x)).card / n

/-- Empirical proportion of in-trial transitions from `x` to `y`. -/
noncomputable def pairFrequency (C : Chain X) (z : ℕ → X) (x y : X) (n : ℕ) : ℝ :=
  ((Finset.range n).filter (fun k => C.P (z k) (z k) ≠ 1 ∧ z k = x ∧ z (k + 1) = y)).card / n

end LeastSquaresTD.Absorbing


