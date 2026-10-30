-- Prove2me | Definitions.Def_LogRegretOCO_ONS_IsONSRun
-- name    : LogRegretOCO_ONS_IsONSRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:59:50.232404+00:00
-- url     : https://prove2.me/theorems/27ae95d0-37d9-4565-9065-85c737dc8b3e
-- title:
--   A run of Online Newton Step (Fig. 2)
-- statement:
--   Let $\mathcal P \subseteq \mathbb R^n$, let $G, D, \alpha$ be reals, $f_1, f_2, \dots : \mathbb R^n \to \mathbb R$ losses and $x_1, x_2, \dots \in \mathbb R^n$ points. Put $\beta = \tfrac12\min\{\tfrac{1}{4GD}, \alpha\}$, $\varepsilon = \tfrac{1}{\beta^2 D^2}$, $\nabla_t = \nabla f_t(x_t)$ and $A_t = \sum_{i=1}^t \nabla_i\nabla_i^\top + \varepsilon I_n$. The sequence $(x_t)$ is a **run of Online Newton Step** if
--
--   1. the first point is arbitrary in $\mathcal P$: $x_1 \in \mathcal P$;
--   2. for every $t \ge 1$,
--   $$
--   x_{t+1} = \Pi_{\mathcal P}^{A_t}\Bigl(x_t - \tfrac{1}{\beta} A_t^{-1} \nabla_t\Bigr), \qquad \Pi_{\mathcal P}^{A_t}(y) = \operatorname{argmin}_{x \in \mathcal P} (y - x)^\top A_t (y - x).
--   $$
--
--   Each round adds a Newton-type step, with $A_t$ in place of the Hessian, to the previous point and projects back onto $\mathcal P$ in the norm of $A_t$. This is the object whose regret Theorem 2 bounds.
--
--   **Formalization Note** Rounds are indexed from $1$; the paper's update for iteration $t > 1$ (using $A_{t-1}$, $\nabla_{t-1}$, $x_{t-1}$) is written at index $t + 1$, as in the proof of Theorem 2. $A_t^{-1}$ is Mathlib's matrix inverse, which is the true inverse since $A_t$ is positive definite for $\varepsilon > 0$. The projection is the minimizer predicate `IsGenProj`. The losses are an arbitrary sequence, so losses chosen by an adaptive adversary are covered. The hypotheses on $\mathcal P$, $G$, $D$, $\alpha$ and the losses belong to the theorems.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, Fig. 2 (the ONLINE NEWTON STEP algorithm), p. 176 (PDF p. 8)

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_onsBeta
import Definitions.Def_LogRegretOCO_ONS_onsEps
import Definitions.Def_LogRegretOCO_ONS_onsGrad
import Definitions.Def_LogRegretOCO_ONS_onsA
import Definitions.Def_LogRegretOCO_ONS_IsGenProj
open Matrix

namespace LogRegretOCO.ONS

/-- **A run of ONLINE NEWTON STEP (Fig. 2).**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, Fig. 2, p. 176:
"• In iteration 1, use an arbitrary point x_1 ∈ P.
 • Let β = 1/2 min{1/(4GD), α}. In iteration t > 1, use point:
   x_t = Π_P^{A_{t−1}}(x_{t−1} − (1/β) A_{t−1}^{−1} ∇_{t−1})
 where ∇_τ = ∇f_τ(x_τ), A_t = Σ_{i=1}^t ∇_i∇_iᵀ + εI_n, ε = 1/(β²D²), and Π_P^{A_{t−1}} is the
 projection in the norm induced by A_{t−1}, viz., Π_P^{A_{t−1}}(y) = argmin_{x∈P} (y − x)ᵀA_{t−1}(y − x)".

`IsONSRun P G D α f x` says: `x 1 ∈ P`, and for every `t ≥ 1`, `x (t+1)` is a generalized
projection, in the norm of `A_t`, of `x_t − β⁻¹ A_t⁻¹ ∇_t` onto `P`, with
`β = onsBeta G D α`, `ε = onsEps G D α`, `A_t = onsA ε f x t`, `∇_t = ∇f_t(x_t)`.

**Formalization Note.** Rounds are indexed from `1`, as in the paper; the paper's update of
iteration `t > 1` (which uses `A_{t−1}`, `∇_{t−1}`, `x_{t−1}`) is written at index `t + 1`
for `t ≥ 1`, as the proof of Theorem 2 writes it (`x_{t+1} = Π^{A_t}(y_{t+1})`, p. 177). `x 0`
and `f 0` are unused. The inverse is Mathlib's `Matrix.inv`; for `ε > 0` the matrix `A_t` is
positive definite, so this is the true inverse. The losses are an arbitrary sequence, so an
adaptive adversary is covered. Hypotheses on `P`, `G`, `D`, `α` and the losses are hypotheses
of the theorems about runs, not part of this predicate. -/
def IsONSRun {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (G D α : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  x 1 ∈ P ∧ ∀ t : ℕ, 1 ≤ t →
    IsGenProj (onsA (onsEps G D α) f x t) P
      (x t - (onsBeta G D α)⁻¹ •
        WithLp.toLp 2 ((onsA (onsEps G D α) f x t)⁻¹ *ᵥ WithLp.ofLp (onsGrad f x t)))
      (x (t + 1))

end LogRegretOCO.ONS


