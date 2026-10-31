-- Prove2me | Definitions.Def_CombOpt_Circulation_IsIntegralBound
-- name    : CombOpt_Circulation_IsIntegralBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:23.116715+00:00
-- url     : https://prove2.me/theorems/a472e09e-514b-417e-8f5a-d41b87358928
-- title:
--   Integral extended bounds
-- statement:
--   A vector of bounds with values in $\mathbb R\cup\{\pm\infty\}$ is **integral** if its finite components are integers; the book writes "We use '$u$ is integral' to mean that the finite components of $u$ are integers."
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.2, p. 39 (PDF p. 48)

import Mathlib

namespace CombOpt.Circulation

/-- An integral vector of extended bounds: "`u` is integral" means "that the finite components of
`u` are integers", Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.2, p. 39 (PDF p. 48). -/
def IsIntegralBound {I : Type*} (w : I → EReal) : Prop :=
  ∀ i, w i ≠ ⊤ → w i ≠ ⊥ → ∃ n : ℤ, w i = ((n : ℝ) : EReal)

end CombOpt.Circulation


