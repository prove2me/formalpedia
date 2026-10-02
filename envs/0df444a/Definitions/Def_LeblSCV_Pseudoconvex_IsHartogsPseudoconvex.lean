-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_IsHartogsPseudoconvex
-- name    : LeblSCV_Pseudoconvex_IsHartogsPseudoconvex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:20:01.429784+00:00
-- url     : https://prove2.me/theorems/c4ec56e1-5767-40b5-b40e-c38befb8dd3b
-- title:
--   Definition 2.5.3 — Hartogs pseudoconvex domain
-- statement:
--   A **domain** is a connected open set. A domain $U \subset \mathbb{C}^n$ is **Hartogs pseudoconvex** if there exists a continuous plurisubharmonic exhaustion function $f : U \to \mathbb{R}$, that is, a continuous plurisubharmonic $f$ with
--   $$\{ z \in U : f(z) < r \} \subset\subset U \quad \text{for every } r \in \mathbb{R}.$$
--
--   For example, $\mathbb{C}^n$ (with $\|z\|^2$) and the unit ball (with $-\log(1 - \|z\|^2)$) are Hartogs pseudoconvex.
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. Being a domain (`IsOpen U ∧ IsConnected U`) is part of the definition, as in the book; `IsConnected` includes nonemptiness.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 92, Definition 2.5.3

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsPlurisubharmonicOn
import Definitions.Def_LeblSCV_Pseudoconvex_IsExhaustion

namespace LeblSCV.Pseudoconvex

/-- Definition 2.5.3, second part (Lebl, p. 92): a domain (connected open set) `U ⊂ ℂⁿ` is
*Hartogs pseudoconvex* if there exists a continuous plurisubharmonic exhaustion function
`f : U → ℝ`. -/
def IsHartogsPseudoconvex {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  IsOpen U ∧ IsConnected U ∧
    ∃ f : EuclideanSpace ℂ (Fin n) → ℝ, ContinuousOn f U ∧
      IsPlurisubharmonicOn (fun z => (f z : EReal)) U ∧ IsExhaustion f U

end LeblSCV.Pseudoconvex


