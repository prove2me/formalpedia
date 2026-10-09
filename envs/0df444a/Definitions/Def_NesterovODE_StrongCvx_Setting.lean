-- Prove2me | Definitions.Def_NesterovODE_StrongCvx_Setting
-- name    : NesterovODE_StrongCvx_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:20.755459+00:00
-- url     : https://prove2.me/theorems/93519b47-6e02-4052-9f85-2efcd975f2b4
-- title:
--   §1.3 and §4 — smooth and strongly convex classes, ODE (17), and the two energies
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$. The class $\mathcal F_L$ consists of convex continuously differentiable functions with $L$-Lipschitz gradient, where $L>0$. The class $\mathcal S_\mu$ consists of continuously differentiable functions for which $x\mapsto f(x)-\mu\|x\|^2/2$ is convex. Their intersection is $\mathcal S_{\mu,L}$.
--
--   For a position and velocity pair $(X,V)$, equation (17) is
--   $$
--   \dot X(t)=V(t),\qquad \dot V(t)+\frac r t V(t)+\nabla f(X(t))=0\quad(t>0),
--   $$
--   with $X(0)=x_0$ and $V(0)=0$. The energy used for Theorem 5 is
--   $$
--   E_5(t)=\frac{2t^2}{r-1}(f(X(t))-f(x^*))
--    +(r-1)\left\|X(t)+\frac{t}{r-1}V(t)-x^*\right\|^2.
--   $$
--   Section 4.3 uses
--   $$
--   E_8(t;\alpha)=t^\alpha(f(X(t))-f(x^*))
--    +\frac{(2r-\alpha)^2t^{\alpha-2}}8
--    \left\|X(t)+\frac{2t}{2r-\alpha}V(t)-x^*\right\|^2,
--   $$
--   and $t_\alpha=\sqrt{(\alpha-2)(2r-\alpha)/(2\mu)}$. These energies are the quantities bounded in the paper's rate argument.
--
--   **Formalization Note** The space and solution predicate are imported from the shared well-posedness definitions. The class $\mathcal S_\mu$ records the paper's convexity formula; the rate theorems impose $\mu>0$. The formula for $E_5$ is used with $r>3$; those for $E_8$ and $t_\alpha$ are used with $2\le\alpha\le 2r/3$, $\mu>0$, and $t>0$ as applicable. These conditions give the real divisions, square root, and real powers their intended values. The source first introduces $E_8$ for $\alpha>2$; Theorem 8 includes the endpoint $\alpha=2$.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, pp. 5, 12–13, 17, §1.3, (17), energies for Theorems 5 and 8

import Mathlib
import Definitions.Def_NesterovODE_WellPosed_Setting

namespace NesterovODE.StrongCvx

/-- The paper's class F_L, with the required positive Lipschitz constant. -/
def InFL {n : ℕ} (L : NNReal) (f : NesterovODE.WellPosed.E n → ℝ) : Prop :=
  NesterovODE.WellPosed.IsFL f L

/-- The paper's literal definition of S_mu. -/
def InSMu {n : ℕ} (mu : ℝ) (f : NesterovODE.WellPosed.E n → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ ConvexOn ℝ Set.univ (fun x => f x - mu / 2 * ‖x‖ ^ 2)

/-- The intersection S_{mu,L} = F_L ∩ S_mu. -/
def InSMuL {n : ℕ} (mu : ℝ) (L : NNReal) (f : NesterovODE.WellPosed.E n → ℝ) : Prop :=
  InFL L f ∧ InSMu mu f

/-- A solution to (17) on nonnegative time; `V` is its velocity. -/
def IsSolution {n : ℕ} (f : NesterovODE.WellPosed.E n → ℝ) (r : ℝ) (x₀ : NesterovODE.WellPosed.E n)
    (X V : ℝ → NesterovODE.WellPosed.E n) : Prop :=
  NesterovODE.WellPosed.IsSolution f r x₀ X V

/-- The energy used in the proof of Theorem 5. -/
noncomputable def energy5 {n : ℕ} (f : NesterovODE.WellPosed.E n → ℝ) (r : ℝ) (xstar : NesterovODE.WellPosed.E n)
    (X V : ℝ → NesterovODE.WellPosed.E n) (t : ℝ) : ℝ :=
  2 * t ^ 2 / (r - 1) * (f (X t) - f xstar) +
    (r - 1) * ‖X t + (t / (r - 1)) • V t - xstar‖ ^ 2

/-- The energy NesterovODE.WellPosed.E(t; α) in §4.3. -/
noncomputable def energy8 {n : ℕ} (f : NesterovODE.WellPosed.E n → ℝ) (r α : ℝ) (xstar : NesterovODE.WellPosed.E n)
    (X V : ℝ → NesterovODE.WellPosed.E n) (t : ℝ) : ℝ :=
  t ^ α * (f (X t) - f xstar) +
    ((2 * r - α) ^ 2 * t ^ (α - 2) / 8) *
      ‖X t + (2 * t / (2 * r - α)) • V t - xstar‖ ^ 2

/-- The threshold t_α in the proof of Theorem 8. -/
noncomputable def tAlpha (r α mu : ℝ) : ℝ :=
  Real.sqrt ((α - 2) * (2 * r - α) / (2 * mu))

end NesterovODE.StrongCvx


