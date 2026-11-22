-- Prove2me | Definitions.Def_KarimiPL_ProxCD_Setting
-- name    : KarimiPL_ProxCD_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:15.166991+00:00
-- url     : https://prove2.me/theorems/7a5cda52-66fb-472c-8f05-17cc34256d28
-- title:
--   §4 (12)–(13), §4.3 (16)–(17), p. 8, 10 — separable g, D_g, proximal-PL, the coordinate step (16) and its uniform-random run
-- statement:
--   This file fixes the objects of randomized proximal coordinate descent (Karimi, Nutini, Schmidt, §4 and §4.3). Throughout, $E_d = \mathbb R^d$ with the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$; for $x\in\mathbb R^d$, $x_i$ is its $i$-th coordinate, $e_i$ the $i$-th standard basis vector, and $\nabla_i f(x)$ the $i$-th coordinate of the gradient $\nabla f(x)$.
--
--   1. **Separable function.** Given univariate functions $g_1,\dots,g_d:\mathbb R\to\mathbb R$,
--   $$g(x)=\sum_{i=1}^d g_i(x_i).$$
--   2. **Proximal model and $\mathcal D_g$ (13).** For $f,g:\mathbb R^d\to\mathbb R$, a point $x$ and $\alpha>0$,
--   $$\mathcal D_g(x,\alpha) = -2\alpha\,\min_y\Big[\langle\nabla f(x),y-x\rangle+\frac{\alpha}{2}\|y-x\|^2+g(y)-g(x)\Big].$$
--   3. **Proximal-PL inequality (12)** with constant $\mu$ and optimal value $F^*$, for $F=f+g$:
--   $$\frac12\,\mathcal D_g(x,L)\ \ge\ \mu\,\big(F(x)-F^*\big)\quad\text{for all }x.$$
--   4. **Coordinate model (the bracket of (16)).** For a coordinate $i$ and a step $t\in\mathbb R$,
--   $$m_i(x,t)=t\,\nabla_i f(x)+\frac L2 t^2+g_i(x_i+t)-g_i(x_i).$$
--   5. **Coordinate proximal-gradient step (16).** A point $y$ is a step from $x$ along coordinate $i$ if $y=x+t^\star e_i$ where $t^\star$ minimizes $t\mapsto m_i(x,t)$.
--   6. **Run along an index word.** Given a step selection $\mathrm{sel}(x,i)$ (a choice of step from $x$ along $i$) and a start $x_0$, the iterate after $k$ steps with chosen coordinates $i_0,\dots,i_{k-1}$ is $x_{j+1}=\mathrm{sel}(x_j,i_j)$.
--   7. **Expected gap.** When $i_0,\dots,i_{k-1}$ are independent and uniform on $\{1,\dots,d\}$, every index word has probability $d^{-k}$, so
--   $$\mathbb E[F(x_k)-F^*]=\frac1{d^k}\sum_{(i_0,\dots,i_{k-1})}\big(F(x_k)-F^*\big).$$
--
--   These are the objects in which Theorem 6 and its proof in Appendix H are stated.
--
--   **Formalization Note** The minimum in (13) is written as a real infimum `⨅`. For convex real-valued $g$ and $\alpha>0$ the bracket is coercive, so the infimum is attained and equals the paper's minimum; outside that class the real infimum of an unbounded-below family is the junk value $0$, which is why every theorem using $\mathcal D_g$ assumes convex $g_i$ and $L>0$. Proximal-PL is stated in the multiplied-out form $\mu(F(x)-F^*)\le\frac12\mathcal D_g(x,L)$. Equation (16) as printed sets $x_{k+1}$ equal to the minimizing step $\alpha$; Appendix H shows the iterate is $x_k+\alpha^\star e_{i_k}$, which is what is encoded. Only real-valued $g_i$ are covered (indicator functions of boxes, used in §4.4, are outside this scope).
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, §4 (11)–(13), p. 8; §4.3 (16)–(17), p. 10; Appendix H, p. 23

import Mathlib
import Definitions.Def_KarimiPL_Rel_Conditions

namespace KarimiPL.ProxCD

open InnerProductSpace

/-- A separable function g(x) = Σ_i g_i(x_i), built from univariate functions `gs i`. -/
noncomputable def sepSum {d : ℕ} (gs : Fin d → ℝ → ℝ) (x : KarimiPL.Rel.E d) : ℝ :=
  ∑ i, gs i (x i)

/-- The bracket of (13): ⟨∇f(x), y − x⟩ + (α/2)‖y − x‖² + g(y) − g(x). -/
noncomputable def proxModel {d : ℕ} (f g : KarimiPL.Rel.E d → ℝ) (x : KarimiPL.Rel.E d) (α : ℝ) (y : KarimiPL.Rel.E d) : ℝ :=
  ⟪gradient f x, y - x⟫_ℝ + α / 2 * ‖y - x‖ ^ 2 + g y - g x

/-- (13): D_g(x, α) = −2α min_y [⟨∇f(x), y − x⟩ + (α/2)‖y − x‖² + g(y) − g(x)].
The minimum is written as a real infimum; it is attained (hence faithful) for convex
real-valued `g` and `α > 0`. -/
noncomputable def Dg {d : ℕ} (f g : KarimiPL.Rel.E d → ℝ) (x : KarimiPL.Rel.E d) (α : ℝ) : ℝ :=
  -2 * α * ⨅ y, proxModel f g x α y

/-- The proximal-PL inequality (12): (1/2) D_g(x, L) ≥ μ (F(x) − F*) for all x, with F = f + g. -/
def ProxPL {d : ℕ} (f g : KarimiPL.Rel.E d → ℝ) (L μ Fstar : ℝ) : Prop :=
  ∀ x, μ * (f x + g x - Fstar) ≤ 1 / 2 * Dg f g x L

/-- The bracket of (16) at coordinate `i`:
t ∇_i f(x) + (L/2) t² + g_i(x_i + t) − g_i(x_i). -/
noncomputable def coordModel {d : ℕ} (f : KarimiPL.Rel.E d → ℝ) (gs : Fin d → ℝ → ℝ) (L : ℝ) (x : KarimiPL.Rel.E d)
    (i : Fin d) (t : ℝ) : ℝ :=
  t * gradient f x i + L / 2 * t ^ 2 + gs i (x i + t) - gs i (x i)

/-- `y` is a coordinate-wise proximal-gradient step (16) from `x` along coordinate `i`:
y = x + t e_i with t a minimizer of the bracket of (16). -/
def IsProxCoordStep {d : ℕ} (f : KarimiPL.Rel.E d → ℝ) (gs : Fin d → ℝ → ℝ) (L : ℝ) (x : KarimiPL.Rel.E d) (i : Fin d)
    (y : KarimiPL.Rel.E d) : Prop :=
  ∃ t : ℝ, y = x + t • EuclideanSpace.single i (1 : ℝ) ∧
    ∀ s : ℝ, coordModel f gs L x i t ≤ coordModel f gs L x i s

/-- The iterate after `k` steps of the method driven by the step selection `sel`, along the
index word `is : Fin k → Fin d` (`is j` is the coordinate chosen at step `j`). -/
noncomputable def pcdRun {d : ℕ} (sel : KarimiPL.Rel.E d → Fin d → KarimiPL.Rel.E d) (x0 : KarimiPL.Rel.E d) :
    (k : ℕ) → (Fin k → Fin d) → KarimiPL.Rel.E d
  | 0, _ => x0
  | k + 1, is => sel (pcdRun sel x0 k (Fin.init is)) (is (Fin.last k))

/-- KarimiPL.Rel.E[F(x_k) − F*] when i_0, …, i_{k−1} are i.i.d. uniform on the d coordinates:
every index word has probability d^{−k}. -/
noncomputable def expectedGap {d : ℕ} (F : KarimiPL.Rel.E d → ℝ) (sel : KarimiPL.Rel.E d → Fin d → KarimiPL.Rel.E d) (x0 : KarimiPL.Rel.E d)
    (Fstar : ℝ) (k : ℕ) : ℝ :=
  (1 / (d : ℝ) ^ k) * ∑ is : Fin k → Fin d, (F (pcdRun sel x0 k is) - Fstar)

end KarimiPL.ProxCD


