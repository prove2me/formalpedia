-- Prove2me | Definitions.Def_TruncNewton_NegCurv_Setting
-- name    : TruncNewton_NegCurv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:53:47.324983+00:00
-- url     : https://prove2.me/theorems/b095b67d-e9b4-421a-8f3b-d7f989f8784d
-- title:
--   §2, p. 194 — the TNCG minor iteration (Steps 1–4) and its exits (2.1)–(2.2)
-- statement:
--   Let $H$ be a linear operator on $\mathbb{R}^n$ (with the Euclidean inner product $u^{\mathsf T}v$ and norm $\|\cdot\|$) and let $g\in\mathbb{R}^n$. In the Truncated-Newton method of Dembo and Steihaug, $H$ and $g$ are the Hessian and the gradient of the objective at the current major iterate, and the search direction is computed by the **TNCG minor iteration**, a conjugate gradient (CG) method applied to $Hp=-g$ and started at $p_0=0$.
--
--   The CG state at minor iteration $i$ is a quadruple $(p_i, r_i, d_i, \delta_i)$, defined by
--
--   $$
--   p_0=0,\quad r_0=-g,\quad d_0=r_0,\quad \delta_0=r_0^{\mathsf T}r_0
--   $$
--
--   (Step 1), and, with $q_i=Hd_i$ (Step 2),
--
--   $$
--   \alpha_i=\frac{r_i^{\mathsf T}r_i}{d_i^{\mathsf T}q_i},\qquad p_{i+1}=p_i+\alpha_i d_i,\qquad r_{i+1}=r_i-\alpha_i q_i,
--   $$
--
--   $$
--   \beta_i=\frac{r_{i+1}^{\mathsf T}r_{i+1}}{r_i^{\mathsf T}r_i},\qquad d_{i+1}=r_{i+1}+\beta_i d_i,\qquad \delta_{i+1}=r_{i+1}^{\mathsf T}r_{i+1}+\beta_i^2\delta_i
--   $$
--
--   (Steps 3 and 4). The minor iteration stops at the first of two tests:
--
--   1. **(2.1), insufficient curvature** (Step 2, at iteration $i$): $d_i^{\mathsf T}Hd_i\le \varepsilon\,\delta_i$;
--   2. **(2.2), Truncated-Newton termination** (Step 3, at iteration $i$, reached only if (2.1) failed at $i$): $\|r_{i+1}\|\le \eta\,\|g\|$.
--
--   The method *exits through (2.1) at $i$* if neither test fired at any earlier iteration $j<i$ and (2.1) holds at $i$; it *exits through (2.2) at $i$* if neither test fired at any $j<i$, (2.1) fails at $i$ and (2.2) holds at $i$.
--
--   These objects are the input to Theorem 2.4 of the paper, which takes $\varepsilon=\eta=0$.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)` and $H$ a continuous linear map on it. The recursion `cg H g` is total and has no stopping test; Lean's convention $x/0=0$ makes the states after a would-be stop meaningless, and every statement reads them only through the first-exit predicates `ExitsVia21`/`ExitsVia22`. The page's test $\|r_{i+1}\|/\|g\|\le\eta$ is written in the equivalent product form $\|r_{i+1}\|\le\eta\|g\|$ (Step 3 is only reached when $g\ne0$). The CG step lengths $\alpha_i,\beta_i$ are called `a`, `b` in Lean. The exit output $p$ is not needed by this mission and is not defined.
-- source:
--   Dembo and Steihaug, Truncated-Newton algorithms for large-scale unconstrained optimization, Math. Programming 26 (1983), p. 194, Minor iteration Steps 1–4, (2.1)–(2.2)

import Mathlib

namespace TruncNewton.NegCurv

/-- The state `(p_i, r_i, d_i, δ_i)` of the TNCG minor iteration (Steps 1–4, p. 194). -/
structure CGState (n : ℕ) where
  p : EuclideanSpace ℝ (Fin n)
  r : EuclideanSpace ℝ (Fin n)
  d : EuclideanSpace ℝ (Fin n)
  δ : ℝ

/-- The conjugate gradient recursion of the minor iteration, without stopping tests.
Step 1 gives the state at `i = 0`; Steps 2–4 give the state at `i + 1`. The CG step lengths
`αᵢ, βᵢ` of the page are called `a, b` here. -/
noncomputable def cg {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) : ℕ → CGState n
  | 0 => ⟨0, -g, -g, inner ℝ (-g) (-g)⟩
  | i + 1 =>
    let s := cg H g i
    let q := H s.d
    let a := inner ℝ s.r s.r / inner ℝ s.d q
    let p' := s.p + a • s.d
    let r' := s.r - a • q
    let b := inner ℝ r' r' / inner ℝ s.r s.r
    ⟨p', r', r' + b • s.d, inner ℝ r' r' + b ^ 2 * s.δ⟩

/-- The curvature test (2.1) of Step 2 at minor iteration `i`: `dᵢᵀ H dᵢ ≤ ε δᵢ`. -/
def test21 {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (i : ℕ) : Prop :=
  inner ℝ ((cg H g i).d) (H (cg H g i).d) ≤ ε * (cg H g i).δ

/-- The truncation test (2.2) of Step 3 at minor iteration `i`: `‖r_{i+1}‖ ≤ η ‖g‖`
(the page's `‖r_{i+1}‖/‖g‖ ≤ η`, in product form). -/
def test22 {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (η : ℝ) (i : ℕ) : Prop :=
  ‖(cg H g (i + 1)).r‖ ≤ η * ‖g‖

/-- The minor iteration reaches iteration `i` (no test fired before) and exits there through
the curvature test (2.1). -/
def ExitsVia21 {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (ε η : ℝ) (i : ℕ) : Prop :=
  (∀ j < i, ¬ test21 H g ε j ∧ ¬ test22 H g η j) ∧ test21 H g ε i

/-- The minor iteration reaches iteration `i`, passes the curvature test (2.1) there, and exits
through the truncation test (2.2). -/
def ExitsVia22 {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (ε η : ℝ) (i : ℕ) : Prop :=
  (∀ j < i, ¬ test21 H g ε j ∧ ¬ test22 H g η j) ∧ ¬ test21 H g ε i ∧ test22 H g η i

end TruncNewton.NegCurv


