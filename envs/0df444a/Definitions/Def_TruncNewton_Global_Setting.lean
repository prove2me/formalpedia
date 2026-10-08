-- Prove2me | Definitions.Def_TruncNewton_Global_Setting
-- name    : TruncNewton_Global_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:54:11.655553+00:00
-- url     : https://prove2.me/theorems/49f8beaa-013d-43b8-9da5-6ffe707ce4c1
-- title:
--   TNCG minor iteration and Wolfe line search, §§1–2
-- statement:
--   The **TNCG minor iteration** begins with $p_0=0$, $r_0=d_0=-g$, and $\delta_0=\langle r_0,r_0\rangle$. For a Hessian operator $H$, it generates conjugate-gradient states using the coefficients and updates in Steps 2–4 on p. 194. The quadratic model is $\phi(p)=\langle g,p\rangle+\tfrac12\langle p,Hp\rangle$.
--
--   At index $i$, the iteration tests $\langle d_i,Hd_i\rangle\le\varepsilon\delta_i$ first. If that test succeeds, it returns $-g$ for $i=0$ and $p_i$ otherwise. Only if it fails does it test $\|r_{i+1}\|\le\eta\|g\|$ and return $p_{i+1}$ when that test succeeds. Earlier indices must have passed neither exit test. A **TNCG direction** is exactly an output of this first-exit rule.
--
--   A **TNCG run** takes positive step lengths $\lambda_k$ and directions obtained from the Hessian and gradient at $x_k$, satisfying the decrease condition (1.9), the gradient curvature condition (1.10), and $x_{k+1}=x_k+\lambda_kp_k$. The alternative function-value condition (1.11) is defined separately.
--
--   **Formalization Note** The vector norm is Euclidean and $H(x)$ is the derivative of the gradient. The residual test uses a product, equivalent to the printed quotient whenever Step 3 is reached. The recursion is total in Lean; the first-exit predicate prevents its zero-denominator states from being returned. A stationary run is extended constantly after convergence.
-- source:
--   Dembo and Steihaug, Truncated-Newton algorithms for large-scale unconstrained optimization, Math. Programming 26 (1983), pp. 190–194, (1.2), (1.9)–(1.11), Steps 1–4, (2.1)–(2.2), https://doi.org/10.1007/BF02592055

import Mathlib

namespace TruncNewton.Global

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def hess {n : ℕ} (f : E n → ℝ) (x : E n) : E n →L[ℝ] E n :=
  fderiv ℝ (gradient f) x

structure CGState (n : ℕ) where
  p : E n
  r : E n
  d : E n
  δ : ℝ

noncomputable def cg {n : ℕ} (H : E n →L[ℝ] E n) (g : E n) : ℕ → CGState n :=
  Nat.rec ⟨0, -g, -g, inner ℝ (-g) (-g)⟩ (fun _ s =>
      let q := H s.d
      let a := inner ℝ s.r s.r / inner ℝ s.d q
      let p' := s.p + a • s.d
      let r' := s.r - a • q
      let b := inner ℝ r' r' / inner ℝ s.r s.r
      ⟨p', r', r' + b • s.d, inner ℝ r' r' + b ^ 2 * s.δ⟩)

def test21 {n : ℕ} (H : E n →L[ℝ] E n) (g : E n) (ε : ℝ) (i : ℕ) : Prop :=
  inner ℝ (cg H g i).d (H (cg H g i).d) ≤ ε * (cg H g i).δ

def test22 {n : ℕ} (H : E n →L[ℝ] E n) (g : E n) (η : ℝ) (i : ℕ) : Prop :=
  ‖(cg H g (i + 1)).r‖ ≤ η * ‖g‖

def ExitsVia21 {n : ℕ} (H : E n →L[ℝ] E n) (g : E n)
    (ε η : ℝ) (i : ℕ) : Prop :=
  (∀ j < i, ¬ test21 H g ε j ∧ ¬ test22 H g η j) ∧ test21 H g ε i

def ExitsVia22 {n : ℕ} (H : E n →L[ℝ] E n) (g : E n)
    (ε η : ℝ) (i : ℕ) : Prop :=
  (∀ j < i, ¬ test21 H g ε j ∧ ¬ test22 H g η j) ∧
    ¬ test21 H g ε i ∧ test22 H g η i

def IsTNCGDirection {n : ℕ} (H : E n →L[ℝ] E n) (g : E n)
    (ε η : ℝ) (p : E n) : Prop :=
  (∃ i, ExitsVia21 H g ε η i ∧ p = if i = 0 then (cg H g 0).d else (cg H g i).p) ∨
  (∃ i, ExitsVia22 H g ε η i ∧ p = (cg H g (i + 1)).p)

noncomputable def phi {n : ℕ} (H : E n →L[ℝ] E n) (g p : E n) : ℝ :=
  inner ℝ g p + (1 / 2 : ℝ) * inner ℝ p (H p)

def cond19 {n : ℕ} (f : E n → ℝ) (α : ℝ) (x p : E n) (t : ℝ) : Prop :=
  f (x + t • p) ≤ f x + α * t * inner ℝ (gradient f x) p

def cond110 {n : ℕ} (f : E n → ℝ) (β : ℝ) (x p : E n) (t : ℝ) : Prop :=
  β * inner ℝ (gradient f x) p ≤ inner ℝ (gradient f (x + t • p)) p

def cond111 {n : ℕ} (f : E n → ℝ) (β : ℝ) (x p : E n) (t : ℝ) : Prop :=
  f x + β * t * inner ℝ (gradient f x) p ≤ f (x + t • p)

def IsTNCGRun {n : ℕ} (f : E n → ℝ) (ε : ℝ) (η : ℕ → ℝ)
    (α β : ℝ) (x0 : E n) (x : ℕ → E n) (lam : ℕ → ℝ)
    (p : ℕ → E n) : Prop :=
  x 0 = x0 ∧ ∀ k,
    IsTNCGDirection (hess f (x k)) (gradient f (x k)) ε (η k) (p k) ∧
    0 < lam k ∧ cond19 f α (x k) (p k) (lam k) ∧
    cond110 f β (x k) (p k) (lam k) ∧
    x (k + 1) = x k + lam k • p k

end TruncNewton.Global


