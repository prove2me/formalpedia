-- Prove2me | Definitions.Def_StochQuasiNewton_SQN_FiniteSum
-- name    : StochQuasiNewton_SQN_FiniteSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:50:14.283254+00:00
-- url     : https://prove2.me/theorems/9e0a8563-e69b-4032-ac0d-820e064694da
-- title:
--   Finite-sum objective, minibatch gradient and subsampled Hessian (1.3), (1.4), (2.3)
-- statement:
--   Let $f_1,\dots,f_N:\mathbb R^n\to\mathbb R$ be the losses of the $N$ training examples, $f_i(w)=f(w;x_i,z_i)$. This file defines the objects of the finite-sum model.
--
--   1. The **objective** (1.3):
--   $$F(w)=\frac1N\sum_{i=1}^N f_i(w).$$
--   2. The **minibatch stochastic gradient** (1.4) for a sample $\mathcal S\subseteq\{1,\dots,N\}$ with $b=|\mathcal S|$:
--   $$\nabla F_{\mathcal S}(w)=\frac1b\sum_{i\in\mathcal S}\nabla f_i(w).$$
--   3. The **subsampled Hessian** (2.3) for a sample $\mathcal S_H$ with $b_H=|\mathcal S_H|$:
--   $$\nabla^2F_{\mathcal S_H}(w)=\frac1{b_H}\sum_{i\in\mathcal S_H}\nabla^2 f_i(w).$$
--   4. **Strict Loewner bounds** $\lambda I\prec A\prec\Lambda I$ for a linear operator $A$ on $\mathbb R^n$: $\lambda\|v\|^2<\langle Av,v\rangle<\Lambda\|v\|^2$ for every $v\neq0$.
--
--   These are the objects in which Assumption 1 of the paper is stated and on which Algorithm 1 operates.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin n)` (Euclidean norm). The Hessian $\nabla^2 f_i(w)$ is the derivative of the gradient map, `fderiv ℝ (gradient (f i)) w`, a continuous linear operator. The strict Loewner order is written through the quadratic form; for the symmetric Hessians of $C^2$ functions this is the usual order. The data $(x_i,z_i)$ and the loss/prediction pair $\ell,h$ of (1.2) do not appear: the analysis only uses the $f_i$.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), p. 1009, Eqs. (1.3)–(1.4); p. 1011, Eq. (2.3); p. 1015, Assumption 1 (3.3)

import Mathlib

open scoped RealInnerProductSpace

namespace StochQuasiNewton.SQN

/-- The finite-sum objective (1.3): `F(w) = (1/N) ∑_{i=1}^N f_i(w)`, where `f i` is the loss
`f(w; x_i, z_i)` of the `i`-th training example. -/
noncomputable def objective {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, f i w

/-- The minibatch stochastic gradient (1.4): `∇F_S(w) = (1/b) ∑_{i ∈ S} ∇f_i(w)` with `b = |S|`. -/
noncomputable def miniBatchGrad {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Finset (Fin N)) (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (1 / (S.card : ℝ)) • ∑ i ∈ S, gradient (f i) w

/-- The subsampled Hessian (2.3): `∇²F_{S_H}(w) = (1/b_H) ∑_{i ∈ S_H} ∇²f_i(w)` with
`b_H = |S_H|`, as a linear operator on `ℝⁿ` (the Hessian of `f i` at `w` is the derivative of
its gradient map). -/
noncomputable def subsampledHessian {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (SH : Finset (Fin N)) (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (1 / (SH.card : ℝ)) • ∑ i ∈ SH, fderiv ℝ (gradient (f i)) w

/-- Strict Loewner bounds `lam • I ≺ A ≺ Lam • I` for a linear operator `A` on `ℝⁿ`, in
quadratic-form language: `lam ‖v‖² < ⟪A v, v⟫ < Lam ‖v‖²` for every nonzero `v`. -/
def StrictLoewnerBounds {n : ℕ} (lam Lam : ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
    lam * ‖v‖ ^ 2 < ⟪A v, v⟫ ∧ ⟪A v, v⟫ < Lam * ‖v‖ ^ 2

end StochQuasiNewton.SQN


