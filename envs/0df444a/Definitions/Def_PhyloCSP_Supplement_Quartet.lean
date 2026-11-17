-- Prove2me | Definitions.Def_PhyloCSP_Supplement_Quartet
-- name    : PhyloCSP_Supplement_Quartet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:24:50.84847+00:00
-- url     : https://prove2.me/theorems/5846971d-96de-4b5e-a056-0bfe3aa0f6a6
-- title:
--   The quartet patterns $C_{12},C_{13},C_{14},C_{21},C_{23},C_{24}$ and $P_2$
-- statement:
--   On the four labeled leaves $\{1,2,3,4\}$ the caterpillars are
--   $$
--   C_{ij}=i\mid\big(j\mid(k,\ell)\big),\qquad i\neq j,\ \{k,\ell\}=\{1,2,3,4\}\setminus\{i,j\},
--   $$
--   and $P_i=((1,i),(j,k))$ is the balanced pattern with cherries $\{1,i\}$ and $\{j,k\}$. For example $C_{12}$ has the rooted triplets $1\mid 23$, $1\mid 24$, $1\mid 34$, $2\mid 34$, and $P_2$ has $3\mid 12$, $4\mid 12$, $1\mid 34$, $2\mid 34$.
--
--   This item defines the seven patterns $C_{12},C_{13},C_{14},C_{21},C_{23},C_{24},P_2$, which are all the patterns occurring in the satisfying sets of Table 1 (Theorem 6.2).
--
--   **Formalization Note** The labels $1,2,3,4$ are the elements $0,1,2,3$ of `Fin 4`. Each pattern is given by its rooted-triplet relation; that it satisfies the tree axioms is checked by `decide`.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Section 6 and Figure 3, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_PhyloCSP_Pattern

set_option autoImplicit false

namespace PhyloCSP

namespace Supplement

/-- The rooted-triplet relation of the caterpillar `a | (b | (c, d))` on `Fin 4`, given by the
list `[a, b, c, d]`: `x | yz` iff `x` comes before `y` and `z` in the list and `y ≠ z`. -/
def cat4Rel (l : List (Fin 4)) (x y z : Fin 4) : Bool :=
  decide (l.idxOf x < l.idxOf y ∧ l.idxOf x < l.idxOf z ∧ y ≠ z)

/-- The rooted-triplet relation of the balanced quartet with cherries `s` and its complement:
`x | yz` iff `y ≠ z` lie in the same cherry and `x` lies in the other one. -/
def bal4Rel (s : Finset (Fin 4)) (x y z : Fin 4) : Bool :=
  decide (y ≠ z ∧ (y ∈ s ↔ z ∈ s) ∧ (x ∈ s ↔ y ∉ s))

/-- **The quartet patterns `C_ij` and `P_i` used in Table 1 (Figure 3).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Section 6, p.14 (PDF p.16): "We denote the caterpillars by
Cij = i | (j | (k, ℓ)), where i ≠ j and k, ℓ are the two elements of {1, 2, 3, 4} other than i and
j. For i ∈ {2, 3, 4}, let Pi = ((1, i), (j, k)), where j, k are the two remaining labels."

`C₁₂` has rooted triplets `1|23, 1|24, 1|34, 2|34`.

**Formalization Note.** The labels `1, 2, 3, 4` of the paper are the elements `0, 1, 2, 3` of
`Fin 4`. Only the seven patterns that occur in Table 1 are named: `C₁₂, C₁₃, C₁₄, C₂₁, C₂₃, C₂₄`
and `P₂`. -/
def C12 : Pattern (Fin 4) := ⟨cat4Rel [0, 1, 2, 3], by decide⟩

/-- `C₁₃ = 1 | (3 | (2, 4))` (p.14, PDF p.16); labels shifted to `Fin 4`. -/
def C13 : Pattern (Fin 4) := ⟨cat4Rel [0, 2, 1, 3], by decide⟩

/-- `C₁₄ = 1 | (4 | (2, 3))` (p.14, PDF p.16); labels shifted to `Fin 4`. -/
def C14 : Pattern (Fin 4) := ⟨cat4Rel [0, 3, 1, 2], by decide⟩

/-- `C₂₁ = 2 | (1 | (3, 4))` (p.14, PDF p.16); labels shifted to `Fin 4`. -/
def C21 : Pattern (Fin 4) := ⟨cat4Rel [1, 0, 2, 3], by decide⟩

/-- `C₂₃ = 2 | (3 | (1, 4))` (p.14, PDF p.16); labels shifted to `Fin 4`. -/
def C23 : Pattern (Fin 4) := ⟨cat4Rel [1, 2, 0, 3], by decide⟩

/-- `C₂₄ = 2 | (4 | (1, 3))` (p.14, PDF p.16); labels shifted to `Fin 4`. -/
def C24 : Pattern (Fin 4) := ⟨cat4Rel [1, 3, 0, 2], by decide⟩

/-- `P₂ = ((1, 2), (3, 4))`, the balanced pattern with cherries `{1, 2}` and `{3, 4}` (p.14,
PDF p.16); labels shifted to `Fin 4`. -/
def P2 : Pattern (Fin 4) := ⟨bal4Rel {0, 1}, by decide⟩

end Supplement

end PhyloCSP


