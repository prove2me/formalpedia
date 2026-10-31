-- Prove2me | Definitions.Def_ResistantSets_HasRestriction
-- name    : ResistantSets_HasRestriction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:06.898534+00:00
-- url     : https://prove2.me/theorems/87030a50-cff2-45da-9e3e-f374df2eeceb
-- title:
--   "$S$ has a $T$ restriction" (isomorphic restriction)
-- statement:
--   Let $S\subseteq\{0,1\}^n$ and $T\subseteq\{0,1\}^m$ with $m\ge 1$. Following the paper's convention that "isomorphic" is omitted from "isomorphic restriction", **$S$ has a $T$ restriction** if some restriction of $S$ is isomorphic to $T$.
--
--   This is how the results of the mission name substructures: "$S$ has an $R_{1,1}$ restriction", "$S$ has a fragile restriction".
--
--   **Formalization Note** The restriction may fix no coordinate, in which case it is $S$ itself up to relabeling (as in "every restriction of it, including $S$ itself", p.5). Restrictions have dimension $m\ge1$, since every statement of the paper concerns sets in $\{0,1\}^n$ with $n\ge1$.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.5, footnote 3 ("Hereinafter, the adjective "isomorphic" will be omitted from "isomorphic restriction" and "isomorphic minor"."), with p.4

import Mathlib
import Definitions.Def_ResistantSets_restrict
import Definitions.Def_ResistantSets_IsIso

namespace ResistantSets

/-- **"S has a T restriction"** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.5, footnote 3: "Hereinafter, the adjective 'isomorphic'
will be omitted from 'isomorphic restriction' and 'isomorphic minor'."): some restriction of `S`
is isomorphic to `T ⊆ {0,1}ᵐ`, where `m ≥ 1`.

**Formalization Note** The restriction may fix no coordinate (then it is `S` itself, up to
relabeling), as in "every restriction of it, including S itself" (p.5). Restrictions have
dimension `m ≥ 1`: every statement of the paper takes "an integer n ≥ 1 and a set S ⊆ {0,1}ⁿ",
and the 0-dimensional cube is never meant. -/
def HasRestriction {n m : ℕ} (S : Finset (Fin n → Bool)) (T : Finset (Fin m → Bool)) : Prop :=
  1 ≤ m ∧ ∃ (ι : Fin m ↪ Fin n) (a : Fin n → Bool), IsIso (restrict S ι a) T

end ResistantSets


