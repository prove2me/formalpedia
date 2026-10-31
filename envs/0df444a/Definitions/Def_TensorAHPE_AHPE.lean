-- Prove2me | Definitions.Def_TensorAHPE_AHPE
-- name    : TensorAHPE_AHPE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:59.59465+00:00
-- url     : https://prove2.me/theorems/ae3b31a0-8707-4c5a-88ad-308510f99667
-- title:
--   The A-HPE framework (Algorithm 1): $a_{k+1}$, $A_k$, $\tilde x_k$ and its runs
-- statement:
--   The **accelerated hybrid proximal extragradient (A-HPE) framework** of Monteiro and Svaiter, Algorithm 1 of the paper, for $F=f+h$:
--
--   1. Let $x_0,y_0\in\mathbb R^n$ and $0<\sigma<1$; set $A_0=0$.
--   2. At iteration $k$, find $\lambda_{k+1}>0$ and $(\tilde y_{k+1},v_{k+1},\epsilon_{k+1})$ with
--   $$v_{k+1}\in\partial_{\epsilon_{k+1}}F(\tilde y_{k+1}),\qquad \|\lambda_{k+1}v_{k+1}+\tilde y_{k+1}-\tilde x_k\|^2+2\lambda_{k+1}\epsilon_{k+1}\le\sigma^2\|\tilde y_{k+1}-\tilde x_k\|^2,$$
--   where
--   $$a_{k+1}=\frac{\lambda_{k+1}+\sqrt{\lambda_{k+1}^2+4\lambda_{k+1}A_k}}2,\qquad \tilde x_k=\frac{A_k}{A_k+a_{k+1}}y_k+\frac{a_{k+1}}{A_k+a_{k+1}}x_k.$$
--   3. Choose $y_{k+1}$ with $F(y_{k+1})\le F(\tilde y_{k+1})$, and set $A_{k+1}=A_k+a_{k+1}$, $x_{k+1}=x_k-a_{k+1}v_{k+1}$.
--
--   A **run through iteration $k$** is a family of sequences satisfying these conditions for the iterations $0,\dots,k-1$. The quantities $a_{k+1}$, $A_k$ and $\tilde x_k$ are shared with Algorithm 2.
--
--   **Formalization Note** The printed STEP 2 ("if $0\in\partial F(y_k)$, STOP") is omitted: a run may continue past an exact minimizer, which only enlarges the set of runs; the paper notes (p.7) that in Algorithm 2 this test is replaced by an approximate one. The sequences are data related by the steps, because $\tilde x_k$ depends on $\lambda_{k+1}$; $A_k$, $a_{k+1}$ and $\tilde x_k$ are computed from them, with $A_0=0$. The condition $\epsilon_{k+1}\ge0$ is not written: for a proper $F$ the inclusion forces it.
-- source:
--   Jiang, Wang & Zhang, An Optimal High-Order Tensor Method for Convex Optimization, arXiv:1812.06557v3, Algorithm 1, p.7

import Mathlib
import Definitions.Def_TensorAHPE_epsSubdiff

namespace TensorAHPE

/-! The A-HPE framework (Algorithm 1) of Jiang, Wang & Zhang, arXiv:1812.06557v3, p.7, and the
step sizes `a_{k+1}`, `A_k` and the extrapolated point `x̃_k` it shares with Algorithm 2 (p.8). -/

/-- **The step `a_{k+1}`.** arXiv:1812.06557v3, Algorithm 1, STEP 3, p.7, and Eq. (3.9), p.8:
"a_{k+1} = (λ_{k+1} + √(λ_{k+1}² + 4λ_{k+1}A_k))/2", as a function of `λ_{k+1}` and `A_k`. -/
noncomputable def aNext (lam A : ℝ) : ℝ :=
  (lam + Real.sqrt (lam ^ 2 + 4 * lam * A)) / 2

/-- **The accumulated weights `A_k`.** arXiv:1812.06557v3, Algorithm 1, STEP 1 and STEP 4, p.7:
"set A₀ = 0", "A_{k+1} = A_k + a_{k+1}" (Algorithm 2, STEP 4, p.8, is the same). `accA lam k`
is `A_k` for the step sizes `lam 1, lam 2, …`; `lam 0` is never read. -/
noncomputable def accA (lam : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => accA lam k + aNext (lam (k + 1)) (accA lam k)

/-- **The steps `a_k`.** `aSeq lam (k + 1) = a_{k+1} = aNext λ_{k+1} A_k`; the value at index `0`
is a placeholder `0` that no statement reads. -/
noncomputable def aSeq (lam : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => aNext (lam (k + 1)) (accA lam k)

/-- **The extrapolated point `x̃_k`.** arXiv:1812.06557v3, Algorithm 1, STEP 3, p.7, and
Eq. (3.8), p.8: "x̃_k = (A_k/(A_k + a_{k+1})) y_k + (a_{k+1}/(A_k + a_{k+1})) x_k". It depends on
`λ_{k+1}` through `a_{k+1}`. -/
noncomputable def xtilde {n : ℕ} (lam : ℕ → ℝ) (x y : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  (accA lam k / (accA lam k + aSeq lam (k + 1))) • y k +
    (aSeq lam (k + 1) / (accA lam k + aSeq lam (k + 1))) • x k

/-- The sequences of a run of Algorithm 1: `x_k`, `y_k`, `ỹ_k`, `v_k`, `λ_k`, `ε_k`. The values
at index `0` of `ỹ`, `v`, `λ`, `ε` are not part of the algorithm and are never read. -/
structure Alg1Seq (n : ℕ) where
  x : ℕ → EuclideanSpace ℝ (Fin n)
  y : ℕ → EuclideanSpace ℝ (Fin n)
  yt : ℕ → EuclideanSpace ℝ (Fin n)
  v : ℕ → EuclideanSpace ℝ (Fin n)
  lam : ℕ → ℝ
  eps : ℕ → ℝ

/-- `A_k` of a run of Algorithm 1. -/
noncomputable def Alg1Seq.A {n : ℕ} (s : Alg1Seq n) (k : ℕ) : ℝ := accA s.lam k
/-- `a_k` of a run of Algorithm 1 (meaningful for `k ≥ 1`). -/
noncomputable def Alg1Seq.a {n : ℕ} (s : Alg1Seq n) (k : ℕ) : ℝ := aSeq s.lam k
/-- `x̃_k` of a run of Algorithm 1. -/
noncomputable def Alg1Seq.xt {n : ℕ} (s : Alg1Seq n) (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  xtilde s.lam s.x s.y k

/-- **A run of Algorithm 1 (the A-HPE framework) through iteration `k`.**
Jiang, Wang & Zhang, arXiv:1812.06557v3, Algorithm 1, p.7:
"STEP 1. Let x₀, y₀ ∈ ℝⁿ, 0 < σ < 1 be given, and set A₀ = 0 and k = 0.
STEP 2. If 0 ∈ ∂F(y_k), then STOP.
STEP 3. Otherwise, find λ_{k+1} > 0 and a triplet (ỹ_{k+1}, v_{k+1}, ε_{k+1}) such that
v_{k+1} ∈ ∂_{ε_{k+1}}F(ỹ_{k+1}), (3.1)
‖λ_{k+1}v_{k+1} + ỹ_{k+1} − x̃_k‖² + 2λ_{k+1}ε_{k+1} ≤ σ²‖ỹ_{k+1} − x̃_k‖² (3.2)
where x̃_k = …, a_{k+1} = ….
STEP 4. Choose y_{k+1} such that F(y_{k+1}) ≤ F(ỹ_{k+1}) and let A_{k+1} = A_k + a_{k+1},
x_{k+1} = x_k − a_{k+1}v_{k+1}.
STEP 5. Set k ← k + 1, and go to STEP 2."

`IsAlg1Run F σ s k`: `0 < σ < 1`, and for every iteration `j < k`, STEP 3 and STEP 4 hold with
`A_j`, `a_{j+1}`, `x̃_j` computed by `accA`, `aSeq`, `xtilde` (so `A₀ = 0`).

**Formalization Note.** (1) STEP 2's test `0 ∈ ∂F(y_k)` is omitted: a run may continue past an
exact minimizer. This only enlarges the set of runs (every run of the printed algorithm is one),
and it lets Algorithm 2, which has no such test, be an instance. (2) The sequences are data related
by STEP 3–4, not built by recursion: `x̃_k` depends on `λ_{k+1}`. (3) `ε_{k+1} ≥ 0` is not
written: for a proper `F`, (3.1) already forces it (take `y = ỹ_{k+1}`). (4) `x₀`, `y₀` are
`s.x 0`, `s.y 0`, arbitrary. -/
def IsAlg1Run {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EReal) (σ : ℝ) (s : Alg1Seq n) (k : ℕ) :
    Prop :=
  0 < σ ∧ σ < 1 ∧
    ∀ j < k,
      0 < s.lam (j + 1) ∧
      s.v (j + 1) ∈ epsSubdiff F (s.eps (j + 1)) (s.yt (j + 1)) ∧
      ‖s.lam (j + 1) • s.v (j + 1) + s.yt (j + 1) - s.xt j‖ ^ 2 + 2 * s.lam (j + 1) * s.eps (j + 1)
        ≤ σ ^ 2 * ‖s.yt (j + 1) - s.xt j‖ ^ 2 ∧
      F (s.y (j + 1)) ≤ F (s.yt (j + 1)) ∧
      s.x (j + 1) = s.x j - s.a (j + 1) • s.v (j + 1)

end TensorAHPE


