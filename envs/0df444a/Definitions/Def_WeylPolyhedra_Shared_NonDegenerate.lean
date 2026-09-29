-- Prove2me | Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
-- name    : WeylPolyhedra_Shared_NonDegenerate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:14:29.602987+00:00
-- url     : https://prove2.me/theorems/3cc5fd64-9720-44df-af32-79d570ef403e
-- title:
--   Non-degenerate (nicht-ausgeartet) finite point system (§1, (2))
-- statement:
--   A finite set $S$ of points of $\mathbb{R}^n$ is **non-degenerate** (Weyl: *nicht-ausgeartet*) when its points do not all lie on one hyperplane through the origin, that is, they do not all satisfy one linear equation
--
--   $$\alpha_1 x_1 + \cdots + \alpha_n x_n = 0, \qquad (\alpha_1, \ldots, \alpha_n) \neq (0, \ldots, 0).$$
--
--   Equivalently, the only vector $\alpha$ with $\langle \alpha, s\rangle = 0$ for every $s \in S$ is $\alpha = 0$; equivalently again, $S$ spans $\mathbb{R}^n$. This is the standing hypothesis of Weyl's Hauptsatz; without it the theorem fails.
--
--   Used by two missions of this paper: 01-hauptsatz (the standing hypothesis of Satz 1, p. 291, of §2, pp. 292–294, and of Satz 2, p. 295) and 02-polyeder (Satz 1, p. 291; the Zusatz, pp. 294–295; Satz 6, p. 297; §3 II, p. 298; Satz 9, p. 299; the same condition for inequality systems, p. 296).
--
--   **Formalization Note** The condition is stated literally in the form of the paper ("no nonzero $\alpha$ is orthogonal to all of $S$"), not as a spanning condition. For $n = 0$ every $S$ is non-degenerate.
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 291, §1, (2)

import Mathlib

namespace WeylPolyhedra.Shared

/-- Weyl (1935), §1, p. 291, (2): the finite point system `S ⊆ ℝⁿ` is *nicht-ausgeartet*
(non-degenerate) when its points do not all satisfy one linear equation
`a₁x₁ + ⋯ + aₙxₙ = 0` with `(a₁, ⋯, aₙ) ≠ (0, ⋯, 0)`: the only `α` with `α ⬝ᵥ s = 0` for every
`s ∈ S` is `α = 0`. -/
def NonDegenerate {n : ℕ} (S : Finset (Fin n → ℝ)) : Prop :=
  ∀ α : Fin n → ℝ, (∀ s ∈ S, α ⬝ᵥ s = 0) → α = 0

end WeylPolyhedra.Shared


