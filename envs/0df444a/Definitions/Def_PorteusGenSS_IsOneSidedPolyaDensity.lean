-- Prove2me | Definitions.Def_PorteusGenSS_IsOneSidedPolyaDensity
-- name    : PorteusGenSS_IsOneSidedPolyaDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:10:36.714143+00:00
-- url     : https://prove2.me/theorems/55a69460-e2e2-4c27-b335-ed9705c24d0f
-- title:
--   One-sided Pólya density
-- statement:
--   A **one-sided Pólya density** is a Pólya density $\varphi$ that vanishes on $\mathbb R^-=(-\infty,0)$. Examples are the exponential densities $\lambda e^{-\lambda t}\,(t>0)$ and all their finite convolutions (Erlang densities). In the paper, demands in each period have a one-sided Pólya density.
--
--   **Formalization Note** $\mathbb R^-$ is open, so $\varphi(0)$ is unconstrained.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 8, p. 421

import Mathlib
import Definitions.Def_PorteusGenSS_IsPolyaDensity

namespace PorteusGenSS

/-- **One-sided Pólya density (Definition 8).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 8, p. 421: "If φ is a PFₙ (Pólya) density and φ vanishes on R⁻, then φ is a
one-sided PFₙ (Pólya) density."

`IsOneSidedPolyaDensity φ` says `φ` is a Pólya density and `φ x = 0` for every `x < 0`.

**Formalization Note.** `R⁻` is the open half-line `(−∞, 0)` (§X, p. 425), so the value
`φ 0` is not constrained. -/
def IsOneSidedPolyaDensity (φ : ℝ → ℝ) : Prop :=
  IsPolyaDensity φ ∧ ∀ x : ℝ, x < 0 → φ x = 0

end PorteusGenSS


