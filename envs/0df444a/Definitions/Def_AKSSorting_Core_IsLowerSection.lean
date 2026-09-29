-- Prove2me | Definitions.Def_AKSSorting_Core_IsLowerSection
-- name    : AKSSorting_Core_IsLowerSection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:45:28.403028+00:00
-- url     : https://prove2.me/theorems/179317c2-cb95-4d8e-8342-bbfe8610db77
-- title:
--   Lower and upper sections of a finite ordered set (Definition 3.3)
-- statement:
--   Let $J$ be a finite subset of a linearly ordered set and $S\subseteq J$. Then $S$ is a **lower section** of $J$ if for all $x,y\in J$,
--   $$ y\in S,\ x\le y \implies x\in S, $$
--   and an **upper section** of $J$ if for all $x,y\in J$, $y\in S$ and $x\ge y$ imply $x\in S$.
--
--   A lower section is a set of smallest elements of $J$, and an upper section a set of largest elements. The halver property (Lemma 4) is stated in terms of sections of the set of contents of $A\cup B$.
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), p. 6, Definition 3.3

import Mathlib

namespace AKSSorting.Core

/-- `S` is a lower section of the ordered set `J` (Ajtai–Komlós–Szemerédi 1983, Definition 3.3,
p. 6): `S ⊆ J` and whenever `x, y ∈ J`, `y ∈ S` and `x ≤ y`, then `x ∈ S`. -/
def IsLowerSection {α : Type} [LinearOrder α] (J S : Finset α) : Prop :=
  S ⊆ J ∧ ∀ x ∈ J, ∀ y ∈ S, x ≤ y → x ∈ S

/-- `S` is an upper section of the ordered set `J` (Definition 3.3, p. 6): `S ⊆ J` and whenever
`x, y ∈ J`, `y ∈ S` and `x ≥ y`, then `x ∈ S`. -/
def IsUpperSection {α : Type} [LinearOrder α] (J S : Finset α) : Prop :=
  S ⊆ J ∧ ∀ x ∈ J, ∀ y ∈ S, y ≤ x → x ∈ S

end AKSSorting.Core


