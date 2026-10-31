-- Prove2me | Definitions.Def_ResistantSets_IsHypercube
-- name    : ResistantSets_IsHypercube
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:41.674599+00:00
-- url     : https://prove2.me/theorems/a2bc6310-e9b6-4b5c-9555-50dfab281aed
-- title:
--   Hypercube (face of the cube, possibly empty)
-- statement:
--   A **hypercube** in $\{0,1\}^n$ is a set of the form
--   $$
--   \{x\in\{0,1\}^n : x_i=a_i \text{ for all } i\in I\}
--   $$
--   for a set $I$ of coordinates and a point $a$, or the empty set.
--
--   The propagation lemmas conclude that certain feasible sets are hypercubes, which is how the structure of a resistant set spreads through the cube.
--
--   **Formalization Note** The empty set counts, following p.29 ("(possibly empty) hypercube") and Lemma 4.6, whose hypothesis allows $S=\emptyset$.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, pp.15–16 (hypercube in Proposition 4.4, Lemma 4.6) and p.29 ("(possibly empty) hypercube")

import Mathlib

namespace ResistantSets

/-- **Hypercube** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §§2, 4, 5; e.g. Lemma 4.6, p.16, and "S′ is a (possibly empty)
hypercube", p.29): a face of the cube `{0,1}ⁿ`, i.e. a set `{x : xᵢ = aᵢ for all i ∈ I}` for a
set `I` of coordinates and a point `a`, or the empty set.

**Formalization Note** The empty set counts as a hypercube, following p.29 ("(possibly empty)
hypercube") and the hypothesis of Lemma 4.6, which allows `S = ∅`. -/
def IsHypercube {n : ℕ} (T : Finset (Fin n → Bool)) : Prop :=
  T = ∅ ∨ ∃ (I : Finset (Fin n)) (a : Fin n → Bool), ∀ x, x ∈ T ↔ ∀ i ∈ I, x i = a i

end ResistantSets


