-- Prove2me | Definitions.Def_CEPolytopeHard_IsConvexEFP
-- name    : CEPolytopeHard_IsConvexEFP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:10.192768+00:00
-- url     : https://prove2.me/theorems/ee61f0ad-9b9b-4a3e-a121-b1803e065b4e
-- title:
--   $\varepsilon$-convex expected fixed point (Definition 3.1)
-- statement:
--   Let $X \subseteq \mathbb R^d$ and $f : X \to X$. A finitely supported distribution $\mu$ on $X$ is an **$\varepsilon$-convex expected fixed point** (convex EFP) of $f$ if
--   $$
--   \mathbb E_{x \sim \mu}\big[Q(x) - Q(f(x))\big] \le \varepsilon
--   $$
--   for every function $Q$ that is convex on $X$ and $1$-Lipschitz on $X$ in the normalized norm, $|Q(x) - Q(y)| \le \|x - y\|_2$.
--
--   This is Definition 3.1. By Theorem 3.3 it is equivalent to the notion of an $\varepsilon$-fixed set; Claim 4.4 produces convex EFPs from correlated equilibria and Claim 4.2 extracts fixed points from them.
--
--   **Formalization Note** The section's standing assumptions ($X$ convex and compact, $f$ continuous) are hypotheses of the theorems that use this notion.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Definition 3.1, p.13

import Mathlib
import Definitions.Def_CEPolytopeHard_nnorm

set_option autoImplicit false

namespace CEPolytopeHard

/-- An **ε-convex expected fixed point** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang,
*The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version
of November 2, 2026, sha256 6aec500a…7820, Definition 3.1, p.13: "An ϵ-convex expected fixed point
(hereafter convex EFP) of f is a distribution µ ∈ ∆(X) such that E_{x∼µ}[Q(x) − Q(f(x))] ≤ ϵ for
every convex Q : X → R that is 1-Lipschitz under ∥·∥₂"). Here `μ` is a finitely supported
distribution on `X` (nonnegative weights, total mass 1, support inside `X`), and the inequality is
required for every `Q` that is convex on `X` and satisfies `|Q x − Q y| ≤ ‖x − y‖₂` on `X`.

**Formalization Note** `‖·‖₂` is the normalized norm `nnorm` (p.9). `Q` is a function on all of
`ℝ^ι`; only its values on `X` are constrained. The section's standing assumptions (X convex and
compact, f : X → X continuous, p.13) are hypotheses of the theorems that use this notion. -/
def IsConvexEFP {ι : Type*} [Fintype ι] (X : Set (ι → ℝ)) (f : (ι → ℝ) → ι → ℝ) (ε : ℝ)
    (μ : (ι → ℝ) →₀ ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ (μ.sum fun _ w => w) = 1 ∧ (↑μ.support : Set (ι → ℝ)) ⊆ X ∧
  ∀ Q : (ι → ℝ) → ℝ, ConvexOn ℝ X Q → (∀ x ∈ X, ∀ y ∈ X, |Q x - Q y| ≤ nnorm (x - y)) →
    ∑ x ∈ μ.support, μ x * (Q x - Q (f x)) ≤ ε

end CEPolytopeHard


