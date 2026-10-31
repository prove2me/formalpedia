-- Prove2me | Definitions.Def_ResistantSets_minor
-- name    : ResistantSets_minor
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:17.736584+00:00
-- url     : https://prove2.me/theorems/5eaf936a-8fd6-49af-acf5-d7ad6339b4a6
-- title:
--   Minor of $S\subseteq\{0,1\}^n$ (restrictions and projections)
-- statement:
--   Let $S\subseteq\{0,1\}^n$. The **projection** of $S$ at coordinate $i$ is the set obtained from $S$ by dropping coordinate $i$, and a **minor** of $S$ is what is obtained after a series of restrictions and projections.
--
--   Here a minor is given in one step by an injection $\iota:[m]\to[n]$ of kept coordinates, a set $J$ of projected coordinates and a point $a$ giving the values of the remaining (restricted) coordinates: $y\in\{0,1\}^m$ belongs to the minor when some $x\in S$ agrees with $y$ on the kept coordinates ($x_{\iota(k)}=y_k$) and with $a$ on every coordinate that is neither kept nor in $J$.
--
--   Minors appear in the excluded-minor characterization of resistance (Theorem 1.8) and in Remark 3.2.
--
--   **Formalization Note** Restrictions and projections at distinct coordinates commute, so a series of them is determined by the restricted coordinates with their values and the projected coordinates. With $J=\emptyset$ the minor is the restriction `restrict S ι a`.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.4, §1.1 (projection, minor)

import Mathlib

namespace ResistantSets

/-- **Minor** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.1, p.4): "The projection of S at coordinate i is the set obtained from S
after dropping coordinate i. A projection of S is a set obtained after a series of single
projections. A minor of S is what is obtained after a series of restrictions and projections."

`minor S ι a J ⊆ {0,1}ᵐ` keeps the coordinates `ι 0, …, ι (m−1)`, projects away (drops) the
coordinates in `J` that are not kept, and fixes every other coordinate `j` to `a j`:
`y ∈ minor S ι a J` iff some `x ∈ S` agrees with `y` on the kept coordinates and with `a`
on the coordinates that are neither kept nor in `J`.

**Formalization Note** Restrictions and projections at distinct coordinates commute, so a series
of them is determined by the set of restricted coordinates (with their values) and the set `J`
of projected ones. An arbitrary injection `ι` also relabels the kept coordinates. `J = ∅` gives
the restriction `restrict S ι a`. -/
def minor {n m : ℕ} (S : Finset (Fin n → Bool)) (ι : Fin m ↪ Fin n) (a : Fin n → Bool)
    (J : Finset (Fin n)) : Finset (Fin m → Bool) :=
  Finset.univ.filter fun y =>
    ∃ x ∈ S, (∀ k, x (ι k) = y k) ∧ ∀ j, (∀ k, ι k ≠ j) → j ∉ J → x j = a j

end ResistantSets


