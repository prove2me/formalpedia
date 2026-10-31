-- Prove2me | Definitions.Def_ResistantSets_restrict
-- name    : ResistantSets_restrict
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:21.819072+00:00
-- url     : https://prove2.me/theorems/a33dc718-1316-4763-962d-96c4be324f41
-- title:
--   Restriction of $S\subseteq\{0,1\}^n$ to a face
-- statement:
--   Let $S\subseteq\{0,1\}^n$. The **0-restriction** (**1-restriction**) of $S$ at coordinate $i$ is the set obtained from $S\cap\{x : x_i=0\}$ (from $S\cap\{x : x_i=1\}$) by dropping coordinate $i$. A **restriction** of $S$ is a set obtained after a series of 0- and 1-restrictions.
--
--   Here a restriction is given in one step: an injection $\iota:\{1,\dots,m\}\to\{1,\dots,n\}$ lists the kept coordinates and a point $a$ gives the values of the other coordinates. The restriction is
--   $$
--   \{\,y\in\{0,1\}^m : \text{the point equal to } y_k \text{ at } \iota(k) \text{ and to } a_j \text{ at every } j\notin\iota([m]) \text{ lies in } S\,\}.
--   $$
--
--   Restrictions are the excluded-substructure operation of the paper: resistance, polarity and the sets $R_{k,1}$, $R_5$ are all detected through them.
--
--   **Formalization Note** A series of 0/1-restrictions fixes a set of coordinates to values, so it is one `restrict S ι a` with `ι` increasing; an arbitrary injection `ι` also relabels the kept coordinates.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.4, §1.1 (0-restriction, 1-restriction, restriction)

import Mathlib

namespace ResistantSets

/-- **Restriction** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.1, p.4): the 0-restriction (1-restriction) of `S` at coordinate
`i` is `S ∩ {x : xᵢ = 0}` (`S ∩ {x : xᵢ = 1}`) with coordinate `i` dropped, and a
restriction of `S` is a set obtained after a series of 0- and 1-restrictions.

`restrict S ι a ⊆ {0,1}ᵐ` fixes every coordinate `j` outside the range of the injection
`ι : Fin m ↪ Fin n` to the value `a j` and keeps the coordinates `ι 0, …, ι (m−1)`, in this
order: `y ∈ restrict S ι a` iff the point that agrees with `y` on the kept coordinates
(`x (ι k) = y k`) and with `a` elsewhere lies in `S`.

**Formalization Note** A series of 0/1-restrictions fixes a set of coordinates to values, in any
order, so it is one `restrict` with `ι` increasing. An arbitrary injection `ι` also relabels
the kept coordinates. When this matters (polarity, resistance and the fragile sets are invariant
under relabeling), the statements say so. Values of `a` on the kept coordinates are ignored. -/
def restrict {n m : ℕ} (S : Finset (Fin n → Bool)) (ι : Fin m ↪ Fin n) (a : Fin n → Bool) :
    Finset (Fin m → Bool) :=
  Finset.univ.filter fun y =>
    ∃ x ∈ S, (∀ k, x (ι k) = y k) ∧ ∀ j, (∀ k, ι k ≠ j) → x j = a j

end ResistantSets


