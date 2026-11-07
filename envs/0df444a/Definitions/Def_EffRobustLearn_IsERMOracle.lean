-- Prove2me | Definitions.Def_EffRobustLearn_IsERMOracle
-- name    : EffRobustLearn_IsERMOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:52.210072+00:00
-- url     : https://prove2.me/theorems/f29504e9-4539-4a0e-bd8d-4259721adfbe
-- title:
--   ERM oracle for $C$ (Definition 3.1)
-- statement:
--   An ERM oracle for a class $C$ takes a dataset $\bar S=\{(x_1,y_1),\dots,(x_n,y_n)\}$ and returns any concept $c\in C$ maximizing $\sum_{(x,y)\in\bar S}c(x)y$.
--
--   **Formalization Note** "Any" is read universally: the theorems quantify over every function satisfying this predicate, with no measurability. A maximizer exists when $C\ne\emptyset$, since the sum takes finitely many values on $C$. Datasets are lists, so repeated examples stay distinct instances.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Definition 3.1, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM

namespace EffRobustLearn

/-- The agreement `∑_{(x,y)∈S̄} c(x) y` of a concept with a dataset, Definition 3.1, Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.11. -/
noncomputable def agreement {X : Type*} (S : List (X × Bool)) (c : X → Bool) : ℝ :=
  (S.map fun p => pm (c p.1) * pm p.2).sum

/-- An ERM oracle for `C`, Definition 3.1, p.11: it takes a dataset and returns any concept of `C` that maximizes
`∑_{(x,y)∈S̄} c(x) y`.

**Formalization Note.** "Any" is read universally: the theorems of the mission quantify over every function `O` satisfying
this predicate, with no measurability, so ties may be broken arbitrarily. A maximizer exists whenever `C ≠ ∅`: the sum takes finitely many
values on `C`. A dataset is a `List`, so repeated examples stay distinct instances. -/
def IsERMOracle {X : Type*} (C : Set (X → Bool)) (O : List (X × Bool) → X → Bool) : Prop :=
  ∀ S, O S ∈ C ∧ ∀ c ∈ C, agreement S c ≤ agreement S (O S)

end EffRobustLearn


