-- Prove2me | Definitions.Def_HessianDamping_IGAHD_Setting
-- name    : HessianDamping_IGAHD_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:14.704174+00:00
-- url     : https://prove2.me/theorems/3673170b-652d-4c4e-8387-697ba8489975
-- title:
--   (IGAHD), (14)–(15), and B_k: algorithm and Lyapunov quantities
-- statement:
--   Let $H$ be a real Hilbert space and $f:H\to\mathbb R$. This definition fixes the inertial gradient algorithm with Hessian damping for parameters $\alpha,\beta,s$ and sequences $(x_k),(y_k)$. Its recurrence starts at $k=1$:
--
--   $$y_k=x_k+(1-\alpha/k)(x_k-x_{k-1})-\beta\sqrt{s}(\nabla f(x_k)-\nabla f(x_{k-1}))-(\beta\sqrt{s}/k)\nabla f(x_{k-1}),\qquad x_{k+1}=y_k-s\nabla f(y_k).$$
--
--   It also defines $t_k=(k-1)/(\alpha-1)$, the vector $v_k$ of (15), the energy $E_k=t_k^2(f(x_k)-f(x^*))+(2s)^{-1}\|v_k\|^2$ of (14), and the quadratic expression $B_k$ of the proof on p. 17. These objects provide the fixed notation for Theorem 6 and its supporting estimates.
--
--   **Formalization Note** The predicate imposes no condition at $k=0$, where the paper's coefficients divide by $k$. The quantities $v_k$ and $E_k$ are used only from $k=1$. Their definitions are total Lean functions, but their intended domain is that indexed tail.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 15, (IGAHD), (14)–(15); p. 17, B_k

import Mathlib

namespace HessianDamping.IGAHD

/-- The two steps of (IGAHD), starting at k = 1. -/
def IsIGAHDRun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (α β s : ℝ) (x y : ℕ → H) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    y k = x k + (1 - α / (k : ℝ)) • (x k - x (k - 1))
      - (β * Real.sqrt s) • (gradient f (x k) - gradient f (x (k - 1)))
      - (β * Real.sqrt s / (k : ℝ)) • gradient f (x (k - 1)) ∧
    x (k + 1) = y k - s • gradient f (y k)

/-- The coefficient t_k specified by t_{k+1} = k/(α-1). -/
noncomputable def tK (α : ℝ) (k : ℕ) : ℝ := ((k : ℝ) - 1) / (α - 1)

/-- The auxiliary vector v_k of (15), used from k = 1. -/
noncomputable def vK {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (α β s : ℝ) (x : ℕ → H)
    (xstar : H) (k : ℕ) : H :=
  (x (k - 1) - xstar) + tK α k •
    (x k - x (k - 1) + (β * Real.sqrt s) • gradient f (x (k - 1)))

/-- The Lyapunov quantity E_k of (14), used from k = 1. -/
noncomputable def EK {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (α β s : ℝ) (x : ℕ → H)
    (xstar : H) (k : ℕ) : ℝ :=
  tK α k ^ 2 * (f (x k) - f xstar)
    + 1 / (2 * s) * ‖vK f α β s x xstar k‖ ^ 2

/-- The quadratic quantity B_k defined in the proof of Theorem 6, p. 17. -/
noncomputable def BK {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (α β s : ℝ) (x y : ℕ → H)
    (k : ℕ) : ℝ :=
  tK α (k + 1) * β * Real.sqrt s *
      inner ℝ (gradient f (y k)) (gradient f (x k))
    + s / 2 * (tK α (k + 1) - 1) *
      ‖gradient f (x k) - gradient f (y k)‖ ^ 2
    + s / 2 * ‖gradient f (y k)‖ ^ 2

end HessianDamping.IGAHD


