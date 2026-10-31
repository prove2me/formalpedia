-- Prove2me | Definitions.Def_AubinLipschitz_secondDeriv
-- name    : AubinLipschitz_secondDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:10.3388+00:00
-- url     : https://prove2.me/theorems/e58a7e87-42c0-4e8b-ae5f-3402e3c56a32
-- title:
--   §2, Definition 3 — the second derivative $\partial^2U(x_0,p_0)$
-- statement:
--   Let $U:X\to\mathbb R\cup\{+\infty\}$ be a proper convex function and $p_0\in\partial U(x_0)$. The **second derivative** of $U$ at $(x_0,p_0)$ is the Clarke derivative of the set-valued map $x\mapsto\partial U(x)$:
--
--   $$
--   \partial^2U(x_0,p_0):=C\partial U(x_0,p_0).
--   $$
--
--   It is a set-valued map from $X$ to $X^*$, and it plays the role of the Hessian for a nonsmooth convex function.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §2, Definition 3, (20), p.19

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_AubinLipschitz_clarkeDeriv
open RockafellarMaxMono.Shared

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §2, Definition 3, (20), p.19: the *second derivative* `∂²U(x₀, p₀) := C∂U(x₀, p₀)`,
the Clarke derivative of the map `x ↦ ∂U(x)` at `(x₀, p₀)`, where `p₀ ∈ ∂U(x₀)`. -/
def secondDeriv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (U : X → EReal) (x₀ : X)
    (p₀ : StrongDual ℝ X) : X → Set (StrongDual ℝ X) :=
  clarkeDeriv (subdiff U) x₀ p₀

end AubinLipschitz


