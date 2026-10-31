-- Prove2me | Definitions.Def_HellmanLevy_CBER_IsBorelRel
-- name    : HellmanLevy_CBER_IsBorelRel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:53:34.622548+00:00
-- url     : https://prove2.me/theorems/81fbfb77-7149-4047-aa2f-508dc576ca57
-- title:
--   Borel relation
-- statement:
--   A relation $E$ on a measurable space $X$ is **Borel** if its graph
--   $$\{(x,y)\in X\times X : x\,E\,y\}$$
--   is a measurable subset of $X\times X$.
--
--   This is the measurability notion behind countable Borel equivalence relations and Borel graphs.
--
--   **Formalization Note** The paper works on Polish spaces with their Borel σ-algebras; the theorems of this mission assume a standard Borel space.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §2.1, p.6

import Mathlib

namespace HellmanLevy.CBER

/-- A relation `E` on a measurable space `X` is **Borel** if its graph
`{(x, y) | x E y}` is a measurable subset of `X × X`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §2.1, p.6.

**Formalization Note** The paper's Polish space with its Borel σ-algebra is replaced by any
measurable space; the theorems of the mission assume `StandardBorelSpace`. -/
def IsBorelRel {X : Type*} [MeasurableSpace X] (E : X → X → Prop) : Prop :=
  MeasurableSet {p : X × X | E p.1 p.2}

end HellmanLevy.CBER


