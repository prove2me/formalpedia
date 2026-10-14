-- Prove2me | Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov
-- name    : GPhNGIDiffusion_EMError_Lyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:39.24103+00:00
-- url     : https://prove2.me/theorems/08b511b0-c949-4178-9351-93b92f337fcd
-- title:
--   Lyapunov function of (A.4) and the properties (A.5)–(A.7)
-- statement:
--   Let $\phi\in C^2(\mathbb R,\mathbb R)$ be the cutoff
--   $$
--   \phi(z)=\begin{cases} z, & z\ge 0,\\ -\tfrac12, & z\le -1,\\ -\tfrac12 z^4-z^3+z, & -1<z<0.\end{cases}
--   $$
--   For a matrix $\tilde Q$ and constants $\kappa,\hat c_2$, the function of (A.4) is
--   $$
--   V(y)=(e'y)^2+\kappa\,[y-p\phi(e'y)]'\tilde Q\,[y-p\phi(e'y)]+\hat c_2,\qquad y\in\mathbb R^d.
--   $$
--   A function $V$ is a **Lyapunov function of the model with constants $c_1,\breve c_1$** if
--
--   1. $V\in C^2(\mathbb R^d,\mathbb R_+)$;
--   2. (A.5) there are $\hat c_1,\hat C,\hat C'>0$ with $\hat c_1|y|^2\le V(y)\le \hat C|y|^2+\hat C'$ for all $y$;
--   3. (A.6) there is $C>0$ with $|\nabla V(y)|\le C(1+|y|)$ for all $y$;
--   4. (A.7) $c_1,\breve c_1>0$ and $\mathcal AV(y)\le -c_1V(y)+\breve c_1$ for all $y$, where $\mathcal A$ is the generator (1.4) of the model.
--
--   These are exactly the properties of the paper's $V$ used in Lemmas A.1, A.3 and A.4 and in the proof of Proposition 2.1; the milestone (A.4)–(A.7) asserts that the function of (A.4) has them.
--
--   **Formalization Note** The paper's $V$ depends on a matrix $\tilde Q$ and a constant $\kappa$ taken from Dieker and Gao, which the paper does not pin down. Lemmas A.1, A.3 and A.4 are therefore stated for every $V$ with these properties, and the existence of such a $V$ of the form (A.4) is a separate statement.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, pp. 23-24, the cutoff φ, (A.4), (A.5), (A.6), (A.7)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GPhNGIDiffusion_EMError_Model
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion

open Matrix
open scoped RealInnerProductSpace

namespace GPhNGIDiffusion.EMError

variable {d : ℕ}

/-- The `C²` cutoff `φ` of Appendix A (p. 23):
`φ(z) = z` for `z ≥ 0`, `φ(z) = −1/2` for `z ≤ −1`, `φ(z) = −z⁴/2 − z³ + z` for `−1 < z < 0`. -/
noncomputable def cutoff (z : ℝ) : ℝ :=
  if 0 ≤ z then z else if z ≤ -1 then -1 / 2 else -(1 / 2) * z ^ 4 - z ^ 3 + z

/-- The function of (A.4), p. 23, built from a matrix `Q̃`, a constant `κ` and a shift `ĉ₂`:
`V(y) = (e′y)² + κ [y − pφ(e′y)]′ Q̃ [y − pφ(e′y)] + ĉ₂`, with `e = (1, …, 1)′`. -/
noncomputable def lyapunovA4 (M : Model d) (Q : Matrix (Fin d) (Fin d) ℝ) (κ c2 : ℝ)
    (y : EthierKurtz.SDEState d) : ℝ :=
  (∑ i, y i) ^ 2 +
    κ * ((WithLp.ofLp y - cutoff (∑ i, y i) • M.p) ⬝ᵥ
      (Q *ᵥ (WithLp.ofLp y - cutoff (∑ i, y i) • M.p))) + c2

/-- `V` is a Lyapunov function of the model with constants `c₁, c̆₁`: the properties (A.5)–(A.7)
(pp. 23–24) that the paper uses of the function `V` of (A.4):
* `V ∈ C²(ℝ^d, ℝ₊)`;
* (A.5) `ĉ₁|y|² ≤ V(y) ≤ Ĉ|y|² + Ĉ′` for some positive constants `ĉ₁, Ĉ, Ĉ′`;
* (A.6) `|∇V(y)| ≤ C(1 + |y|)` for some constant `C > 0`;
* (A.7) `AV(y) ≤ −c₁V(y) + c̆₁` with `c₁, c̆₁ > 0`, `A` the generator (1.4) of the model. -/
def IsLyapunovFn (M : Model d) (V : EthierKurtz.SDEState d → ℝ) (c₁ c₁' : ℝ) : Prop :=
  ContDiff ℝ 2 V ∧ (∀ y, 0 ≤ V y) ∧
    (∃ a A B : ℝ, 0 < a ∧ 0 < A ∧ 0 < B ∧ ∀ y, a * ‖y‖ ^ 2 ≤ V y ∧ V y ≤ A * ‖y‖ ^ 2 + B) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ y, ‖gradient V y‖ ≤ C * (1 + ‖y‖)) ∧
    0 < c₁ ∧ 0 < c₁' ∧
    ∀ y, generator M.drift M.σ V y ≤ -c₁ * V y + c₁'

end GPhNGIDiffusion.EMError


