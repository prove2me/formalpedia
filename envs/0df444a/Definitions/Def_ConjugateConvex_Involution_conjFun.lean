-- Prove2me | Definitions.Def_ConjugateConvex_Involution_conjFun
-- name    : ConjugateConvex_Involution_conjFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:24:59.131996+00:00
-- url     : https://prove2.me/theorems/2ca0b94d-4a35-4a90-8c39-87474363c0a5
-- title:
--   §3, p. 75 — the conjugate function φ(ξ) = l.u.b. over x in G of (Σxξ − f(x))
-- statement:
--   Let $G \subseteq \mathbb R^n$ and let $f$ be a real function defined in $G$. For $\xi$ in the conjugate set $\Gamma$ of $(G, f)$, the **conjugate function** is the least upper bound
--
--   $$
--   \varphi(\xi) = \sup_{x \in G}\bigl(\Sigma x\xi - f(x)\bigr).
--   $$
--
--   Together with $\Gamma$ it forms the conjugate pair $(\Gamma, \varphi)$ of Fenchel's theorem. Applied to $(\Gamma, \varphi)$, the same definition gives Fenchel's function $f^*(x) = \sup_{\xi \in \Gamma}(\Sigma\xi x - \varphi(\xi))$ on $G^*$ (§4).
--
--   **Formalization Note** The supremum is Mathlib's real `sSup` of the image $\{\Sigma x\xi - f(x) : x \in G\}$. Real `sSup` returns $0$ on a set that is unbounded above or empty, so the value is meaningful only for $\xi \in \Gamma$ (and $G \neq \emptyset$). Every theorem of the mission evaluates $\varphi$ only at points of $\Gamma$.
-- source:
--   Fenchel, On conjugate convex functions, Canad. J. Math. 1 (1949), p. 75, §3 (definition of φ); p. 76, §4 (definition of f*)

import Mathlib

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §3, p. 75: `φ(ξ) = l.u.b._{x ∈ G} (Σxξ − f(x))`. Meaningful only for `ξ`
in `conjDomain G f`; the real `sSup` returns `0` on an unbounded (or empty) set, so every
statement evaluates `conjFun G f` only on `conjDomain G f`. -/
noncomputable def conjFun {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (ξ : Fin n → ℝ) : ℝ :=
  sSup ((fun x => x ⬝ᵥ ξ - f x) '' G)

end ConjugateConvex.Involution


