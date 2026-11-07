-- Prove2me | Definitions.Def_UniqueOptScores_HierarchyPackage
-- name    : UniqueOptScores_HierarchyPackage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:29:31.419715+00:00
-- url     : https://prove2.me/theorems/b5e6ae5a-2e94-4fd1-9fb7-7049a0ffe4eb
-- title:
--   The strict hierarchy of Lemma 7.1
-- statement:
--   For an oracle $A$, the **strict hierarchy package** is the conjunction of:
--
--   1. $\mathrm{UO}[k]^A \subsetneq \mathrm{UO}[k+1]^A$ for every $k \ge 1$;
--   2. $\bigcup_{k \ge 1} \mathrm{UO}[k]^A \subsetneq \mathrm{UO}^A_{\mathrm P}$;
--   3. $\mathrm{UO}^A_{\mathrm P} \subsetneq D^A$;
--   4. $D^A \subsetneq \Theta^{\mathrm P,A}_2$;
--   5. some language of $\mathrm{OR}_2(\mathrm{US}^A)$ lies in $D^A \setminus \mathrm{UO}^A_{\mathrm P}$ (the gap above $\mathrm{UO}^A_{\mathrm P}$ has a witness in $\mathrm{OR}_2(\mathrm{US}^A)$);
--   6. some language of $\mathrm{NP}^A$ lies in $\Theta^{\mathrm P,A}_2 \setminus D^A$ (the gap above $D^A$ has a witness in $\mathrm{NP}^A$).
--
--   This is the conclusion of Lemma 7.1 for one oracle, and what Lemma 8.1 asserts for every oracle of a comeager set.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Lemma 7.1, p.26

import Mathlib
import Definitions.Def_UniqueOptScores_NP
import Definitions.Def_UniqueOptScores_US
import Definitions.Def_UniqueOptScores_UO
import Definitions.Def_UniqueOptScores_UOP
import Definitions.Def_UniqueOptScores_Dtt
import Definitions.Def_UniqueOptScores_OR2
import Definitions.Def_UniqueOptScores_Theta2

namespace UniqueOptScores

/-- **The strict hierarchy of Lemma 7.1, with its witness clauses.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Lemma 7.1, p.26: "every fixed-level inclusion UO[k]^A ⊆ UO[k + 1]^A is strict, and
⋃_{k≥1} UO[k]^A ⊊ UO^A_P ⊊ D^A ⊊ Θ^{P,A}_2 . The middle upper gap has a witness in OR_2(US^A), and
the last gap has a witness in NP^A."

`HierarchyPackage A` is the conjunction of:
1. `UO[k]^A ⊊ UO[k+1]^A` for every `k ≥ 1`;
2. `⋃_{k ≥ 1} UO[k]^A ⊊ UO^A_P`;
3. `UO^A_P ⊊ D^A`;
4. `D^A ⊊ Θ^{P,A}_2`;
5. some language of `OR₂(US^A)` lies in `D^A ∖ UO^A_P`;
6. some language of `NP^A` lies in `Θ^{P,A}_2 ∖ D^A`. -/
def HierarchyPackage (A : Set (List Bool)) : Prop :=
  (∀ k : ℕ, 1 ≤ k → UO A k ⊂ UO A (k + 1)) ∧
  (⋃ k : ℕ, ⋃ (_ : 1 ≤ k), UO A k) ⊂ UOP A ∧
  UOP A ⊂ Dtt A ∧
  Dtt A ⊂ Theta2 A ∧
  (∃ L ∈ OR2 (US A), L ∈ Dtt A ∧ L ∉ UOP A) ∧
  (∃ L ∈ NP A, L ∈ Theta2 A ∧ L ∉ Dtt A)

end UniqueOptScores


