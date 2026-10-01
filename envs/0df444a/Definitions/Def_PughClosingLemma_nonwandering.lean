-- Prove2me | Definitions.Def_PughClosingLemma_nonwandering
-- name    : PughClosingLemma_nonwandering
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T20:55:40.132234+00:00
-- url     : https://prove2.me/theorems/b36bd921-e528-44e4-a847-0ccf02171b24
-- title:
--   Nonwandering points and the nonwandering set $\Omega(f)$
-- statement:
--   Let $X$ be a topological space and $f\colon X\to X$ a map. A point $x\in X$ is **nonwandering** for $f$ if for every neighbourhood $U$ of $x$ there exists an integer $n\ge 1$ such that
--
--   $$f^n(U)\cap U\neq\emptyset ,$$
--
--   where $f^n=f\circ\cdots\circ f$ ($n$ times). The **nonwandering set** of $f$ is
--
--   $$\Omega(f)=\{x\in X : x \text{ is nonwandering for } f\}.$$
--
--   This is the notion of nonwandering point used in the hypothesis of Pugh's closing lemma; it is shared by every statement of the mission.
--
--   **Formalization Note** Neighbourhoods are arbitrary members of the neighbourhood filter $\mathcal N(x)$; since the condition is monotone in $U$ this is equivalent to quantifying over open neighbourhoods. No continuity of $f$ is required by the definition itself.
-- source:
--   Wikipedia, "Pugh's closing lemma", section "Formal statement" (revision oldid=1304222873, https://en.wikipedia.org/w/index.php?title=Pugh%27s_closing_lemma&oldid=1304222873), citing C. C. Pugh, "An Improved Closing Lemma and a General Density Theorem", Amer. J. Math. 89 (4) (1967), 1010-1021, https://doi.org/10.2307/2373414 (hypothesis "nonwandering point x of f"; standard definition of a nonwandering point).

import Mathlib

open scoped Topology

namespace PughClosingLemma

/-- A point `x` is *nonwandering* for a map `f : X → X` if for every neighbourhood `U` of `x`
there is an iterate `n ≥ 1` with `f^[n] '' U ∩ U ≠ ∅`. -/
def IsNonwandering {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ n : ℕ, 1 ≤ n ∧ (f^[n] '' U ∩ U).Nonempty

/-- The nonwandering set `Ω(f)` of a map `f : X → X`. -/
def nonwanderingSet {X : Type*} [TopologicalSpace X] (f : X → X) : Set X :=
  {x | IsNonwandering f x}

end PughClosingLemma


