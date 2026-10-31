-- Prove2me | Definitions.Def_InfHorizonVP_Admissible
-- name    : InfHorizonVP_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:10.848395+00:00
-- url     : https://prove2.me/theorems/cb0cfefc-2002-499a-b02a-34aabfe7bbf2
-- title:
--   Admissible trajectories $\mathcal A_{(t,\xi)}$
-- statement:
--   Let $\Gamma:\mathbb R_+\times E\rightsquigarrow E$ be a multifunction, $t\ge0$ and $\xi\in E$. The set of **admissible trajectories** starting at time $t$ from $\xi$ is
--   $$
--   \mathcal A_{(t,\xi)}=\bigl\{x\in W^{1,1}_{\mathrm{loc}}([t,\infty),E)\ \bigm|\ \dot x(s)\in\Gamma(s,x(s))\ \text{a.e. } s\in[t,\infty),\ x(t)=\xi\bigr\},
--   $$
--   where $x\in W^{1,1}_{\mathrm{loc}}([t,\infty),E)$ means that $x$ is an arc on every interval $[t,T]$, $T\ge t$.
--
--   It is the feasible set of the infinite horizon problem $(P_t)$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.1, p.8

import Mathlib
import Definitions.Def_InfHorizonVP_IsArcOn
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Admissible trajectories `𝒜_(t,ξ)`.**
Frankowska, Sagara, arXiv:1801.00400v3, §3.1, p.8: "An arc satisfying the above differential
inclusion is called an admissible trajectory. Define the set of admissible trajectories starting
at time t ∈ R+ from a given initial condition ξ ∈ E by
𝒜_(t,ξ) := {x(·) ∈ W^{1,1}_loc([t,∞), E) | ẋ(s) ∈ Γ(s, x(s)) a.e. s ∈ [t,∞), x(t) = ξ}."

An arc on `[t, ∞)` is a function that is an arc (`IsArcOn`) on every compact interval `[t, T]`.

**Formalization Note.** `W^{1,1}_loc([t,∞), E)` is encoded as `∀ T ≥ t, IsArcOn x t T`. The
multifunction `Γ : ℝ₊ × E ⇝ E` is `Γ : ℝ → E → Set E`; values at negative times are never used.
"a.e. s ∈ [t, ∞)" is Lebesgue-a.e. on `(t, ∞)` (the endpoint is a null set). -/
def Admissible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : ℝ → E → Set E) (t : ℝ) (ξ : E) : Set (ℝ → E) :=
  {x | (∀ T, t ≤ T → IsArcOn x t T) ∧
    (∀ᵐ s ∂(volume.restrict (Ioi t)), deriv x s ∈ Γ s (x s)) ∧ x t = ξ}

end InfHorizonVP


