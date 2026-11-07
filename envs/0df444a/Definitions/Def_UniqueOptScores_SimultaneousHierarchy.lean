-- Prove2me | Definitions.Def_UniqueOptScores_SimultaneousHierarchy
-- name    : UniqueOptScores_SimultaneousHierarchy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:30:59.561207+00:00
-- url     : https://prove2.me/theorems/11452e7e-f669-4c3d-9a23-94f8ad222327
-- title:
--   The package of Theorem 1.2
-- statement:
--   For an oracle $A$, the **simultaneous hierarchy** of Theorem 1.2 is
--   $$
--   \mathrm{US}^A = \mathrm{UO}[1]^A \subsetneq \mathrm{UO}[2]^A \subsetneq \mathrm{UO}[3]^A \subsetneq \cdots,\qquad \bigcup_{k\ge1}\mathrm{UO}[k]^A \subsetneq \mathrm{UO}^A_{\mathrm P} \subsetneq D^A \subsetneq \Theta^{\mathrm P,A}_2 ,
--   $$
--   with a witness of the gap above $\mathrm{UO}^A_{\mathrm P}$ in $\mathrm{OR}_2(\mathrm{US}^A)$ and a witness of the gap above $D^A$ in $\mathrm{NP}^A$; that is, $\mathrm{US}^A = \mathrm{UO}[1]^A$ together with the strict hierarchy package of Lemma 7.1.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Theorem 1.2, p.3

import Mathlib
import Definitions.Def_UniqueOptScores_US
import Definitions.Def_UniqueOptScores_UO
import Definitions.Def_UniqueOptScores_HierarchyPackage

namespace UniqueOptScores

/-- **The package of Theorem 1.2.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Theorem 1.2, p.3: "US^A = UO[1]^A ⊊ UO[2]^A ⊊ UO[3]^A ⊊ · · · , and ⋃_{k≥1} UO[k]^A ⊊ UO^A_P
⊊ D^A ⊊ Θ^{P,A}_2. The gap above UO^A_P has a witness in OR_2(US^A), and the gap above D^A has a
witness in NP^A."

`SimultaneousHierarchy A` is `US^A = UO[1]^A` together with `HierarchyPackage A`. -/
def SimultaneousHierarchy (A : Set (List Bool)) : Prop :=
  US A = UO A 1 ∧ HierarchyPackage A

end UniqueOptScores


