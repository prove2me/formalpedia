-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexity_ConvexClosure
-- name    : DiscreteConvex_IntegralConvexity_ConvexClosure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:48:34.790793+00:00
-- url     : https://prove2.me/theorems/61aa5b8f-70f7-4389-ac18-9fe33d6e4716
-- title:
--   Convex closure of a lattice function (Eq. 3.56)
-- statement:
--   The **convex closure** $\bar f : \mathbb R^n \to \mathbb R \cup \{\pm\infty\}$ of $f : \mathbb Z^n \to \mathbb R \cup \{+\infty\}$ (Eq. (3.56)):
--
--   $$\bar f(x) = \sup_{p \in \mathbb R^n,\, \alpha \in \mathbb R} \{\langle p,x\rangle + \alpha : \langle p,y\rangle + \alpha \le f(y)\ \forall y \in \mathbb Z^n\}.$$
--
--   **Formalization Note.** Represented in `EReal` (`= WithBot (WithTop ℝ)`, a complete lattice, so the supremum is total), into which `f`'s codomain `WithTop ℝ` embeds via `WithBot.some`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.56).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.56)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.56): the convex closure of a
function on the integer lattice, in `DiscreteConvex.IntegralConvexity`.
-/

namespace DiscreteConvex.IntegralConvexity

/-- The convex closure `f̄ : Rⁿ → R ∪ {±∞}` of `f : Zⁿ → R ∪ {+∞}` (Eq. (3.56)):
`f̄(x) = sup_{p ∈ Rⁿ, α ∈ R} \{⟨p,x⟩ + α : ⟨p,y⟩ + α ≤ f(y) for all y ∈ Zⁿ\}`. Represented in
`EReal` (`= WithBot (WithTop ℝ)`), into which `WithTop ℝ` embeds via `WithBot.some`. -/
noncomputable def ConvexClosure {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (x : Fin n → ℝ) : EReal :=
  sSup {v : EReal | ∃ (p : Fin n → ℝ) (α : ℝ),
    (∀ y : Fin n → ℤ, ((α + ∑ i, p i * (y i : ℝ) : ℝ) : EReal) ≤ WithBot.some (f y)) ∧
    v = ((α + ∑ i, p i * x i : ℝ) : EReal)}

end DiscreteConvex.IntegralConvexity


