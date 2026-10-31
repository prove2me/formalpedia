-- Prove2me | Definitions.Def_FirstChoiceDesign_Setting
-- name    : FirstChoiceDesign_Setting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:39.561596+00:00
-- url     : https://prove2.me/theorems/43d06725-7827-49af-8799-03d557734436
-- title:
--   Students, schools, preferences and capacities $(I,S,\succ_I,(c_s)_{s\in S})$
-- statement:
--   There are a finite set $I$ of students and a finite set $S$ of schools. Each student $i$ has a strict preference $\succ_i$ over $S\cup\{\emptyset\}$, where $\emptyset$ is the outside option, and each school $s$ has a capacity $c_s\ge 1$. School $s$ is acceptable for $i$ if $s\succ_i\emptyset$. The preference rank $\mathrm{rank}_{is}$ of $s$ in $\succ_i$ is one plus the number of alternatives in $S\cup\{\emptyset\}$ that $i$ strictly prefers to $s$; thus $\mathrm{rank}_{is}=2$ if $s$ is $i$'s second choice.
--
--   This is the part of an assignment problem that a school's report does not touch, so strategy-proofness (Definition 3) quantifies over it, and it is also the input the deferred acceptance procedure reads the student lists from.
--
--   **Formalization Note** Students are `Fin n`, schools are `Fin m`, and `none` is $\emptyset$. A preference is an injective map `u i : Option (Fin m) → ℕ`, smaller meaning better, so the whole order over $S\cup\{\emptyset\}$ is kept, including that of unacceptable schools, whose rank enters the modified priority. Since $\emptyset$ is counted in the rank, rank $1$ means that a school is acceptable and first. `applicantList` lists the acceptable schools, best first.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), §2, p.6; rank_is, Definition 1, p.7

import Mathlib

namespace FirstChoiceDesign

/-- The part `(I, S, ≻_I, (c_s)_{s ∈ S})` of an assignment problem: `n` students, `m` schools,
strict student preferences over `S ∪ {∅}` and school capacities.
Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles
Foundation Discussion Paper No. 2056R (rev. Aug. 2017), §2, p.6.

**Formalization Note** Students are `Fin n`, schools are `Fin m`, and `none` is the outside option
`∅`. A preference is an injective `u i : Option (Fin m) → ℕ`, smaller is better, so it is the whole
strict order over `S ∪ {∅}`, including the order of unacceptable schools: their rank enters the
modified priority of Definition 1. Capacities are positive (`ℕ` on p.6 is the positive integers). -/
structure Setting (n m : ℕ) where
  /-- `u i x < u i y` means `x ≻_i y`. -/
  u : Fin n → Option (Fin m) → ℕ
  u_injective : ∀ i, Function.Injective (u i)
  /-- The capacity `c_s`. -/
  c : Fin m → ℕ
  c_pos : ∀ s, 0 < c s

/-- `rank_is`, the preference rank of school `s` in `≻_i`: `1` plus the number of alternatives of
`S ∪ {∅}` that `i` strictly prefers to `s`. Definition 1, p.7. Since `∅` is counted, rank `1` means
that `s` is first over everything, so a first choice is acceptable. -/
def Setting.rank {n m : ℕ} (B : Setting n m) (i : Fin n) (s : Fin m) : ℕ :=
  1 + (Finset.univ.filter fun x : Option (Fin m) => B.u i x < B.u i (some s)).card

/-- Student `i`'s acceptable schools (`s ≻_i ∅`, p.6), best first: the list DA walks through. -/
def Setting.applicantList {n m : ℕ} (B : Setting n m) (i : Fin n) : List (Fin m) :=
  ((List.finRange m).filter fun s => B.u i (some s) < B.u i none).insertionSort
    fun a b => B.u i (some a) ≤ B.u i (some b)

end FirstChoiceDesign


