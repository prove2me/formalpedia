-- Prove2me | Definitions.Def_TensorAHPE_Algorithm2
-- name    : TensorAHPE_Algorithm2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:26:46.321488+00:00
-- url     : https://prove2.me/theorems/48560f07-118b-4dd1-8235-888eea1699ac
-- title:
--   The optimal tensor method (Algorithm 2): parameters, condition (3.7) and runs
-- statement:
--   **Algorithm 2** of the paper, for problem (1.1) with $\nabla^d f$ $L_d$-Lipschitz:
--
--   1. (STEP 1) $x_0=y_0\in\mathbb R^n$, $\epsilon_0=0$, $A_0=0$; parameters $0<\bar\epsilon<1$, $0<\bar\rho<1$, $M\ge L_d$ with $M>0$, $\hat\sigma\ge0$, $0<\sigma_l<\sigma_u<1$ with $\hat\sigma+\sigma_u<1$ and $\sigma_l(1+\hat\sigma)^{d-1}<\sigma_u(1-\hat\sigma)^{d-1}$.
--   2. (STEP 2) If $\|v_k\|\le\bar\rho$ and $\epsilon_k\le\bar\epsilon$, stop.
--   3. (STEP 3) Find $\lambda_{k+1}$ and a $\hat\sigma$-approximate solution $(y_{k+1},u_{k+1},\epsilon_{k+1})$ of (2.5) at $(\lambda_{k+1},\tilde x_k)$ such that either
--   $$\frac{d!\,\sigma_l}{L_d+M}\le\lambda_{k+1}\|y_{k+1}-\tilde x_k\|^{d-1}\le\frac{d!\,\sigma_u}{L_d+M}\qquad(3.7)$$
--   or $\|\nabla f(y_{k+1})+u_{k+1}-\nabla f_{\tilde x_k}(y_{k+1})\|\le\bar\rho$ and $\epsilon_{k+1}\le\bar\epsilon$, with $\tilde x_k$ and $a_{k+1}$ given by (3.8)–(3.9) (the formulas of Algorithm 1).
--   4. (STEP 4) $v_{k+1}=\nabla f(y_{k+1})+u_{k+1}-\nabla f_{\tilde x_k}(y_{k+1})$ (3.10), $A_{k+1}=A_k+a_{k+1}$, $x_{k+1}=x_k-a_{k+1}v_{k+1}$.
--
--   A **run through iteration $k$** satisfies STEP 1, does not stop at iterations $0,\dots,k-1$, and satisfies STEPS 3–4 at each of them. Such a run, read with $\tilde y_j=y_j$, is the object of Theorems 3.3 and 3.4.
--
--   **Formalization Note** $v_0$ is left unconstrained (STEP 1 prints $v_0\in\partial f(x_0)$; it only enters the first stopping test). The sequences are data related by the steps; $A_k$, $a_{k+1}$, $\tilde x_k$ are those of the A-HPE definitions. $\nabla f$ and $\nabla f_{\tilde x}$ are Mathlib's `gradient`. $M>0$ comes from (2.4).
-- source:
--   Jiang, Wang & Zhang, An Optimal High-Order Tensor Method for Convex Optimization, arXiv:1812.06557v3, Algorithm 2, p.8 (with Eq. (2.4), p.5, for M > 0, and A₀ = 0 from Algorithm 1, p.7)

import Mathlib
import Definitions.Def_TensorAHPE_Problem
import Definitions.Def_TensorAHPE_IsApproxSol
import Definitions.Def_TensorAHPE_AHPE

namespace TensorAHPE

/-! The optimal tensor method (Algorithm 2) of Jiang, Wang & Zhang, arXiv:1812.06557v3, p.8. -/

/-- The input parameters of Algorithm 2, STEP 1, p.8: `M`, `σ̂`, `σ_l`, `σ_u`, `ε̄`, `ρ̄`. -/
structure Params where
  M : ℝ
  σhat : ℝ
  σl : ℝ
  σu : ℝ
  εbar : ℝ
  ρbar : ℝ

/-- **Admissible parameters (Algorithm 2, STEP 1).** arXiv:1812.06557v3, Algorithm 2, STEP 1, p.8:
"set 0 < ε̄, ρ̄ < 1, M ≥ L_d. Let σ̂ ≥ 0, 0 < σ_l < σ_u < 1 such that σ := σ̂ + σ_u < 1 and
σ_l(1 + σ̂)^{d−1} < σ_u(1 − σ̂)^{d−1}", together with `M > 0` from Eq. (2.4), p.5 ("where M > 0
is the parameter of the high-order regularization term").

**Formalization Note.** `d − 1` is natural-number subtraction; every statement using it assumes
`d ≥ 1`. -/
def Params.Admissible (prm : Params) (d : ℕ) (L : ℝ) : Prop :=
  0 < prm.εbar ∧ prm.εbar < 1 ∧ 0 < prm.ρbar ∧ prm.ρbar < 1 ∧ L ≤ prm.M ∧ 0 < prm.M ∧
    0 ≤ prm.σhat ∧ 0 < prm.σl ∧ prm.σl < prm.σu ∧ prm.σu < 1 ∧ prm.σhat + prm.σu < 1 ∧
    prm.σl * (1 + prm.σhat) ^ (d - 1) < prm.σu * (1 - prm.σhat) ^ (d - 1)

/-- **Condition (3.7).** arXiv:1812.06557v3, Eq. (3.7), p.8:
"d!σ_l/(L_d + M) ≤ λ_{k+1}‖y_{k+1} − x̃_k‖^{d−1} ≤ d!σ_u/(L_d + M)", for a step size `lam`, a
point `y` and a centre `xt` (read with `λ, y, x̃` in Proposition 3.2, p.9).

**Formalization Note.** `‖·‖^{d−1}` is a natural power with `d − 1` natural subtraction; at
`d = 1` it is `1`. -/
def Cond37 (d : ℕ) (L : ℝ) (prm : Params) (lam : ℝ) {n : ℕ} (y xt : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  (d.factorial : ℝ) * prm.σl / (L + prm.M) ≤ lam * ‖y - xt‖ ^ (d - 1) ∧
    lam * ‖y - xt‖ ^ (d - 1) ≤ (d.factorial : ℝ) * prm.σu / (L + prm.M)

/-- The sequences of a run of Algorithm 2: `x_k`, `y_k`, `u_k`, `v_k`, `λ_k`, `ε_k`. The values at
index `0` of `u` and `λ` are not part of the algorithm and are never read. -/
structure Alg2Seq (n : ℕ) where
  x : ℕ → EuclideanSpace ℝ (Fin n)
  y : ℕ → EuclideanSpace ℝ (Fin n)
  u : ℕ → EuclideanSpace ℝ (Fin n)
  v : ℕ → EuclideanSpace ℝ (Fin n)
  lam : ℕ → ℝ
  eps : ℕ → ℝ

/-- `A_k` of a run of Algorithm 2 (`A₀ = 0`, `A_{k+1} = A_k + a_{k+1}`). -/
noncomputable def Alg2Seq.A {n : ℕ} (s : Alg2Seq n) (k : ℕ) : ℝ := accA s.lam k
/-- `a_k` of a run of Algorithm 2, Eq. (3.9) (meaningful for `k ≥ 1`). -/
noncomputable def Alg2Seq.a {n : ℕ} (s : Alg2Seq n) (k : ℕ) : ℝ := aSeq s.lam k
/-- `x̃_k` of a run of Algorithm 2, Eq. (3.8). -/
noncomputable def Alg2Seq.xt {n : ℕ} (s : Alg2Seq n) (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  xtilde s.lam s.x s.y k

/-- **A run of Algorithm 2 (the optimal tensor method) through iteration `k`.**
Jiang, Wang & Zhang, arXiv:1812.06557v3, Algorithm 2, p.8:
"STEP 1. Let x₀ = y₀ ∈ ℝⁿ, v₀ ∈ ∂f(x₀), ε₀ = 0, k = 0 and set 0 < ε̄, ρ̄ < 1, M ≥ L_d. Let σ̂ ≥ 0,
0 < σ_l < σ_u < 1 such that σ := σ̂ + σ_u < 1 and σ_l(1 + σ̂)^{d−1} < σ_u(1 − σ̂)^{d−1}.
STEP 2. If ‖v_k‖ ≤ ρ̄ and ε_k ≤ ε̄, then STOP. Else, go to STEP 3.
STEP 3. Find λ_{k+1} and a σ̂-approximate solution (y_{k+1}, u_{k+1}, ε_{k+1}) ∈ ℝⁿ × ℝⁿ × ℝ₊ of
(2.5) at (λ_{k+1}, x̃_k) such that either (3.7) or ‖∇f(y_{k+1}) + u_{k+1} − ∇f_{x̃_k}(y_{k+1})‖ ≤ ρ̄
and ε_{k+1} ≤ ε̄ hold, where x̃_k = … (3.8) and a_{k+1} = … (3.9).
STEP 4. Let v_{k+1} = ∇f(y_{k+1}) + u_{k+1} − ∇f_{x̃_k}(y_{k+1}) (3.10), A_{k+1} = A_k + a_{k+1},
x_{k+1} = x_k − a_{k+1}v_{k+1}. Set k ← k + 1 and go to STEP 2."

`IsAlg2Run P prm s k`: the parameters satisfy STEP 1, `x₀ = y₀`, `ε₀ = 0`, and for every
iteration `j < k`: STEP 2 did not stop at `j`, and STEP 3 and STEP 4 hold, with `A₀ = 0` (from
Algorithm 1, STEP 1, p.7; used on p.26) built into `accA`.

**Formalization Note.** (1) `v₀` is unconstrained: STEP 1 prints `v₀ ∈ ∂f(x₀)` (possibly meaning
`∂F`); `v₀` only enters STEP 2 at `k = 0`, and leaving it free covers both readings. (2) The
sequences are data related by STEP 3–4, because `x̃_k` depends on `λ_{k+1}`. (3) `∇f` and `∇f_x̃`
are Mathlib's `gradient`; `f_x̃ = model P.f d prm.M x̃` is (2.4). (4) The stopping test is part of
the run: a run through `k` did not stop at `0, …, k − 1`; whether it stops at `k` is not
constrained. -/
def IsAlg2Run {n d : ℕ} (P : Problem n d) (prm : Params) (s : Alg2Seq n) (k : ℕ) : Prop :=
  prm.Admissible d P.L ∧ s.x 0 = s.y 0 ∧ s.eps 0 = 0 ∧
    ∀ j < k,
      ¬ (‖s.v j‖ ≤ prm.ρbar ∧ s.eps j ≤ prm.εbar) ∧
      IsApproxSol P.f P.h d prm.M prm.σhat (s.lam (j + 1)) (s.xt j) (s.y (j + 1)) (s.u (j + 1))
        (s.eps (j + 1)) ∧
      (Cond37 d P.L prm (s.lam (j + 1)) (s.y (j + 1)) (s.xt j) ∨
        (‖gradient P.f (s.y (j + 1)) + s.u (j + 1)
            - gradient (model P.f d prm.M (s.xt j)) (s.y (j + 1))‖ ≤ prm.ρbar ∧
          s.eps (j + 1) ≤ prm.εbar)) ∧
      s.v (j + 1) = gradient P.f (s.y (j + 1)) + s.u (j + 1)
        - gradient (model P.f d prm.M (s.xt j)) (s.y (j + 1)) ∧
      s.x (j + 1) = s.x j - s.a (j + 1) • s.v (j + 1)

/-- The sequences of a run of Algorithm 2 read as a run of Algorithm 1 with `ỹ_k = y_k`
(arXiv:1812.06557v3, p.8–9: "we let y_{k+1} = ỹ_{k+1} in STEP 4 of Algorithm 1"). -/
def Alg2Seq.toAlg1 {n : ℕ} (s : Alg2Seq n) : Alg1Seq n where
  x := s.x
  y := s.y
  yt := s.y
  v := s.v
  lam := s.lam
  eps := s.eps

end TensorAHPE


