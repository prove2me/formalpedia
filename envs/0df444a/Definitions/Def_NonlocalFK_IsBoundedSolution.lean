-- Prove2me | Definitions.Def_NonlocalFK_IsBoundedSolution
-- name    : NonlocalFK_IsBoundedSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:34.53641+00:00
-- url     : https://prove2.me/theorems/45431cef-a22d-44a8-8b2e-4146ea01324e
-- title:
--   Bounded solution in $C^{1,2}(Q)\cap C(\bar Q\setminus D)$ with boundary data $g$
-- statement:
--   Let $\mathcal LW=\tfrac12\sum_{i,j}a_{ij}\,\partial^2W/\partial x_i\partial x_j+\sum_ib_i\,\partial W/\partial x_i-rW$. A function $W$ is a **bounded solution with boundary data $g$** if $W$ is bounded on $\bar Q$, continuous on $\bar Q\setminus D$, in $C^{1,2}(Q)$, and
--
--   $$
--   -\frac{\partial W}{\partial t}(t,x)-\mathcal LW(t,x)=f(t,x)\ \text{ in }Q,\qquad W(t,x)=g(t,x)\ \text{ on }\partial_pQ.
--   $$
--
--   With $g=h+\mathcal BW$ this is the nonlocal problem (1.1)–(1.2); with $g=h+\mathcal BW_i$ it is (3.1)–(3.2); with $g=h$ it is the local problem of Proposition A.1.
--
--   **Formalization Note** The boundary equation holds on all of $\partial_pQ$, including $D$; only continuity excludes $D$. The derivatives are witnesses continuous on $Q$. The time derivative is taken within $[0,T)$, because $Q$ contains $t=0$, and is one-sided there.
-- source:
--   Dai, Kou, Yang, A Stochastic Representation for Nonlocal Parabolic PDEs with Applications, SSRN 3541591, eq. (1.1), p.1; eq. (3.1)-(3.2), p.11; Proposition A.1, p.23

import Definitions.Def_NonlocalFK_Diffusion

open Set

noncomputable section

namespace NonlocalFK

namespace Diffusion

variable {d : ℕ}

/-- `W` is a bounded solution in `C^{1,2}(Q) ∩ C(Q̄ ∖ D)` of the terminal-boundary value problem
`−∂W/∂t − 𝓛W = f` in `Q`, `W = g` on `∂ₚQ` (Dai, Kou, Yang, SSRN 3541591, (1.1), p.1; (3.1)–(3.2),
p.11; Proposition A.1, p.23), with `𝓛W = ½ ∑ a_ij ∂²W/∂x_i∂x_j + ∑ b_i ∂W/∂x_i − rW` and
`a = σσᵀ` (p.2).

**Formalization Note.** The boundary data is the argument `g`: `g = h + 𝓑W` gives (1.2),
`g = h + 𝓑Wᵢ` gives (3.2), and `g = h` gives Proposition A.1. The boundary equation holds on all of
`∂ₚQ`, including `D`; only continuity excludes `D`. The class `C^{1,2}(Q)` is given by witnesses
`Wt`, `Wx`, `Wxx` continuous on `Q`. The time derivative is taken within `[0, T)`, because `Q`
contains `t = 0`, so it is one-sided there. The partial derivatives in `x` are derivatives along
the coordinate lines. -/
def IsBoundedSolution (c : Diffusion d) (D : Set (ℝ × E d)) (g W : ℝ × E d → ℝ) : Prop :=
  (∃ C : ℝ, ∀ p ∈ c.Qbar, |W p| ≤ C) ∧
  ContinuousOn W (c.Qbar \ D) ∧
  (∃ (Wt : ℝ × E d → ℝ) (Wx : Fin d → ℝ × E d → ℝ) (Wxx : Fin d → Fin d → ℝ × E d → ℝ),
    ContinuousOn Wt c.Q ∧ (∀ i, ContinuousOn (Wx i) c.Q) ∧
    (∀ i j, ContinuousOn (Wxx i j) c.Q) ∧
    (∀ p ∈ c.Q, HasDerivWithinAt (fun s => W (s, p.2)) (Wt p) (Ico 0 c.T) p.1) ∧
    (∀ p ∈ c.Q, ∀ i, HasDerivAt
      (fun y : ℝ => W (p.1, p.2 + y • EuclideanSpace.single i (1 : ℝ))) (Wx i p) 0) ∧
    (∀ p ∈ c.Q, ∀ i j, HasDerivAt
      (fun y : ℝ => Wx j (p.1, p.2 + y • EuclideanSpace.single i (1 : ℝ))) (Wxx i j p) 0) ∧
    ∀ p ∈ c.Q,
      -Wt p - ((1 / 2 : ℝ) * ∑ i, ∑ j, (c.σ p * (c.σ p).transpose) i j * Wxx i j p
        + ∑ i, c.b p i * Wx i p - c.r * W p) = c.f p) ∧
  ∀ p ∈ c.bdry, W p = g p

end Diffusion

end NonlocalFK


