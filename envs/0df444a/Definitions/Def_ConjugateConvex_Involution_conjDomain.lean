-- Prove2me | Definitions.Def_ConjugateConvex_Involution_conjDomain
-- name    : ConjugateConvex_Involution_conjDomain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:24:54.584798+00:00
-- url     : https://prove2.me/theorems/856f68bc-e88b-4f50-b3b4-9daccc025bc9
-- title:
--   §3, p. 75 — the conjugate set Γ: all ξ for which Σxξ − f(x) is bounded above in G
-- statement:
--   Let $G \subseteq \mathbb R^n$ and let $f$ be a real function defined in $G$. Write $\Sigma x\xi = x_1\xi_1 + \dots + x_n\xi_n$. The **conjugate set** of $(G, f)$ is
--
--   $$
--   \Gamma = \Bigl\{\xi \in \mathbb R^n : \text{the function } x \mapsto \Sigma x\xi - f(x) \text{ is bounded from above on } G\Bigr\}.
--   $$
--
--   $\Gamma$ is the domain on which the conjugate function $\varphi$ is finite. Applied to the pair $(\Gamma, \varphi)$ instead of $(G, f)$, the same definition gives Fenchel's set $G^*$ of §4, the set of points $x$ for which $\Sigma\xi x - \varphi(\xi)$ is bounded from above in $\Gamma$.
--
--   **Formalization Note** $\Sigma x\xi$ is Mathlib's `dotProduct` `x ⬝ᵥ ξ`. When the definition is applied to $(\Gamma, \varphi)$ the summand is written `ξ ⬝ᵥ x`, the paper's $\Sigma\xi x$; the two agree by commutativity of the dot product. If $G$ is empty every $\xi$ belongs to $\Gamma$; the theorems of the mission assume $G$ nonempty.
-- source:
--   Fenchel, On conjugate convex functions, Canad. J. Math. 1 (1949), p. 75, §3 (definition of Γ); p. 76, §4 (definition of G*)

import Mathlib

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §3, p. 75: `Γ` is the set of all points `ξ` such that `Σxξ − f(x)` is
bounded from above in `G`. -/
def conjDomain {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Set (Fin n → ℝ) :=
  {ξ | BddAbove ((fun x => x ⬝ᵥ ξ - f x) '' G)}

end ConjugateConvex.Involution


