-- Prove2me | Definitions.Def_ResistantSets_IsPolar
-- name    : ResistantSets_IsPolar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:19.019782+00:00
-- url     : https://prove2.me/theorems/c67d44bf-8074-44f7-ba34-3b080fb9bfda
-- title:
--   Antipodal points, polar and non-polar sets
-- statement:
--   Two points $a,b\in\{0,1\}^n$ are **antipodal** if $a+b=\mathbf 1$, that is, $a_i\neq b_i$ for every $i$. A set $S\subseteq\{0,1\}^n$ is **polar** if either there are antipodal feasible points or the feasible points all agree on a coordinate; otherwise it is **non-polar**. "$S$ without antipodal points" means that no two points of $S$ are antipodal.
--
--   Polarity governs the packing property of cuboids of resistant sets (Corollary 1.12), and the main theorem is about the sets that fail it minimally.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.5, §1.2 (antipodal points; polar, non-polar)

import Mathlib

namespace ResistantSets

/-- **Antipodal feasible points** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.2, p.5): "Two points a, b ∈ {0,1}ⁿ are antipodal if
a + b = 1." `HasAntipodal S` says that `S` contains two antipodal points; "S without antipodal
points" is its negation.

**Formalization Note** `a + b = 1` coordinate-wise means `aᵢ ≠ bᵢ` for every `i`. -/
def HasAntipodal {n : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∀ i, a i ≠ b i

/-- **Polar set** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.2, p.5): "We say that S ⊆ {0,1}ⁿ is polar if either there are antipodal
feasible points or the feasible points all agree on a coordinate; otherwise it is non-polar." -/
def IsPolar {n : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  HasAntipodal S ∨ ∃ i : Fin n, ∀ a ∈ S, ∀ b ∈ S, a i = b i

end ResistantSets


