-- Prove2me | Definitions.Def_HellmanLevy_CBER_IsSmooth
-- name    : HellmanLevy_CBER_IsSmooth
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:53:34.205148+00:00
-- url     : https://prove2.me/theorems/ca7eb2b1-36a5-4e15-82c1-6fb439931ef8
-- title:
--   Smooth equivalence relation
-- statement:
--   An equivalence relation $E$ on $X$ is **smooth** if there is a Borel map $\psi : X\to\mathbb R$ whose level sets are exactly the classes of $E$:
--   $$x\,E\,y \iff \psi(x)=\psi(y)\qquad (x,y\in X).$$
--
--   Smoothness is the lowest rung of the hierarchy of CBERs: the classes can be told apart by a Borel invariant. For common knowledge relations it corresponds to the existence of measurable Bayesian equilibria.
--
--   **Formalization Note** Definition 2.1 asks for a Borel map into some Polish space $Z$; since every Polish space is Borel isomorphic to a Borel subset of $\mathbb R$, taking $Z=\mathbb R$ (the paper's own reformulation $E\le_B \mathrm{id}_{\mathbb R}$ in §6.1) defines the same relations.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), Definition 2.1, eq. (2.1), p.7; §6.1, p.28

import Mathlib

namespace HellmanLevy.CBER

/-- An equivalence relation `E` on `X` is **smooth** if there is a Borel map `ψ : X → ℝ` whose
level sets are exactly the classes of `E`: `x E y ↔ ψ x = ψ y`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), Definition 2.1, p.7, eq. (2.1); restated in §6.1, p.28 as `E ≤_B id_ℝ`.

**Formalization Note** Definition 2.1 asks for a Borel map into some Polish space `Z`. Every
Polish space is Borel isomorphic to a Borel subset of `ℝ`, so taking `Z = ℝ` (the paper's own
§6.1 form) gives the same relations. A "Borel function" (p.7: a function with Borel graph) is
a measurable map; for maps into `ℝ` from a standard Borel space the two notions agree. -/
def IsSmooth {X : Type*} [MeasurableSpace X] (E : X → X → Prop) : Prop :=
  ∃ ψ : X → ℝ, Measurable ψ ∧ ∀ x y, E x y ↔ ψ x = ψ y

end HellmanLevy.CBER


