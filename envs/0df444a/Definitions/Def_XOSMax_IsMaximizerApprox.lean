-- Prove2me | Definitions.Def_XOSMax_IsMaximizerApprox
-- name    : XOSMax_IsMaximizerApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:42.068606+00:00
-- url     : https://prove2.me/theorems/f04b696d-220a-454a-837e-f0eb660b8056
-- title:
--   $\alpha$-maximizers
-- statement:
--   For a ground set $V$ and $\alpha\ge 1$, a set $\tilde X\subseteq V$ is an **$\alpha$-maximizer** of $f$ if
--   $$
--   f(\tilde X)\ \ge\ \frac1\alpha\cdot\max_{X\subseteq V}f(X).
--   $$
--   A $1$-maximizer is an exact maximizer.
--
--   This is the approximation notion of the mission's goal theorem.
--
--   **Formalization Note** The maximum over the finitely many subsets of $V$ is unfolded: the definition says $\tilde X\subseteq V$ and $\frac1\alpha f(X)\le f(\tilde X)$ for every $X\subseteq V$. The parameter $\alpha$ is a real number and every use has $\alpha\ge1$.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, §1, p.2, "called an α-maximizer"

import Mathlib

namespace XOSMax

/-- `IsMaximizerApprox V α f Y`: `Y` is an **`α`-maximizer** of `f` on the ground set `V`, that is,
`Y ⊆ V` and `f(Y) ≥ (1/α) · max_{X⊆V} f(X)` (Filmus, Kawase, Kobayashi & Yamaguchi,
arXiv:1811.09045v3, §1, p.2, "called an α-maximizer").

**Formalization Note** The maximum over the finitely many subsets of `V` is unfolded into
"`(1/α) · f(X) ≤ f(Y)` for every `X ⊆ V`", which is equivalent for `α > 0` and has no junk value
of a real supremum. The paper defines the notion for `α ≥ 1`; `α` is a real parameter here and every
use has `α ≥ 1`. -/
def IsMaximizerApprox {E : Type} (V : Finset E) (α : ℝ) (f : Finset E → ℝ) (Y : Finset E) : Prop :=
  Y ⊆ V ∧ ∀ X, X ⊆ V → (1 / α) * f X ≤ f Y

end XOSMax


