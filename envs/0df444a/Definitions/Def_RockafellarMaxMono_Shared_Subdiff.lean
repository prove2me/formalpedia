-- Prove2me | Definitions.Def_RockafellarMaxMono_Shared_Subdiff
-- name    : RockafellarMaxMono_Shared_Subdiff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:00:11.3752+00:00
-- url     : https://prove2.me/theorems/896491dc-a746-4f84-adbd-28e252301292
-- title:
--   Subdifferential $\partial f : V \rightrightarrows V^*$
-- statement:
--   Let $V$ be a real normed space with (continuous) dual $V^*$, and write $\langle y, x^* \rangle = x^*(y)$ for the canonical pairing. The **subdifferential** of a function $f : V \to [-\infty, +\infty]$ is the multivalued mapping $\partial f : V \to V^*$ defined by
--
--   $$
--   \partial f(x) = \{\, x^* \in V^* \mid f(y) \ge f(x) + \langle y - x, x^* \rangle \ \ \forall y \in V \,\}.
--   $$
--
--   Its elements are the **subgradients** of $f$ at $x$. When $f$ is a proper convex function and $f(x) = +\infty$, the set $\partial f(x)$ is empty. Taking $V = E^*$, the subdifferential of the conjugate $f^*$ is the mapping $\partial f^* : E^* \to E^{**}$ of the paper.
--
--   It serves chunk 01-maximal-monotone (p. 209; Theorem A, p. 209, the Fenchel–Young characterization (2.2), p. 210, and the lemmas of §§2–3, pp. 211–213, including $\partial f^*$ on $E^*$) and chunk 02-cyclic-characterization (p. 209; Theorem B, p. 209, and the lemmas of §§2–4, pp. 210–215).
--
--   **Formalization Note** $V^*$ is Mathlib's `StrongDual ℝ V` (continuous linear functionals); the Lean name of the set-valued map is `subdiff f x`. The inequality is computed in `EReal`.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 209, definition of the subdifferential

import Mathlib

namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), p. 209: the *subdifferential* of `f : V → (−∞, +∞]` at `x` is
`∂f(x) = {x* ∈ V* | f(y) ≥ f(x) + ⟨y − x, x*⟩ for all y ∈ V}`, a subset of the
(strong) dual `V* = StrongDual ℝ V`; the pairing `⟨y − x, x*⟩` is `x' (y - x)`. -/
def subdiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → EReal) (x : V) :
    Set (StrongDual ℝ V) :=
  {x' | ∀ y : V, f x + ((x' (y - x) : ℝ) : EReal) ≤ f y}

end RockafellarMaxMono.Shared


