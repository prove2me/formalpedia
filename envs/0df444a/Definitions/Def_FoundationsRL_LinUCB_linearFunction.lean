-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_linearFunction
-- name    : FoundationsRL_LinUCB_linearFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:17.076557+00:00
-- url     : https://prove2.me/theorems/02a5e4a5-c700-4419-80aa-6152bf6fb178
-- title:
--   The linear function $(x,\pi)\mapsto\langle\theta,\phi(x,\pi)\rangle$
-- statement:
--   Given a feature map $\phi:\mathcal X\times\Pi\to\mathbb R^d$ and a parameter $\theta\in\mathbb R^d$, this is the function
--
--   $$
--   f_\theta(x,\pi)=\langle\theta,\phi(x,\pi)\rangle.
--   $$
--
--   It is the building block of the linear class of Eq. (3.21).
--
--   **Formalization Note** Vectors of $\mathbb R^d$ are functions `Fin d → ℝ` and the inner product is the dot product.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eq. (3.21), p. 43

import Mathlib

open Matrix

namespace FoundationsRL.LinUCB

/-- The linear function `(x, π) ↦ ⟨θ, ϕ(x, π)⟩` with parameter `θ ∈ ℝ^d` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Eq. (3.21), p. 43).
Vectors of `ℝ^d` are `Fin d → ℝ`, with the inner product `⬝ᵥ`. -/
def linearFunction {X Act : Type*} {d : ℕ} (ϕ : X → Act → Fin d → ℝ) (θ : Fin d → ℝ) :
    X → Act → ℝ :=
  fun x a => θ ⬝ᵥ ϕ x a

end FoundationsRL.LinUCB


