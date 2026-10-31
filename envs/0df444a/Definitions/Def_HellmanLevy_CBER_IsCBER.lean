-- Prove2me | Definitions.Def_HellmanLevy_CBER_IsCBER
-- name    : HellmanLevy_CBER_IsCBER
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:21.864567+00:00
-- url     : https://prove2.me/theorems/0cfe8e14-32e2-4112-9a93-6cebe3cfa051
-- title:
--   Countable Borel equivalence relation (CBER)
-- statement:
--   An equivalence relation $E$ on a measurable space $X$ is a **countable Borel equivalence relation** (CBER) if it is Borel (its graph is a measurable subset of $X\times X$) and every equivalence class $\{y : x\,E\,y\}$ is countable (finite or countably infinite).
--
--   CBERs are the setting of the paper: common knowledge relations of purely atomic Bayesian games, and connected-component relations of Borel graphs of countable degree, are CBERs.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §2.1, p.6

import Mathlib
import Definitions.Def_HellmanLevy_CBER_IsBorelRel

namespace HellmanLevy.CBER

/-- A **countable Borel equivalence relation** (CBER): an equivalence relation that is Borel and
whose equivalence classes are all countable.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §2.1, p.6 ("An equivalence relation is said to be countable if each equivalence class …
is countable. We will abbreviate countable Borel equivalence relation as CBER"). -/
def IsCBER {X : Type*} [MeasurableSpace X] (E : X → X → Prop) : Prop :=
  Equivalence E ∧ IsBorelRel E ∧ ∀ x, {y | E x y}.Countable

end HellmanLevy.CBER


