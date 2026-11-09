-- Prove2me | Definitions.Def_ManipPotential_Ranking
-- name    : ManipPotential_Ranking
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:37.492752+00:00
-- url     : https://prove2.me/theorems/b9650976-2d54-40d3-ae38-645da9c796ae
-- title:
--   Rankings $\mathcal L(C)$ of $m$ candidates as permutations to positions
-- statement:
--   Let $C = \{c_1, \dots, c_m\}$ be a set of $m$ candidates. A **ranking** (strict preference order) is a transitive, antisymmetric and complete relation $\succ$ on $C$; the set of all rankings is $\mathcal L(C)$, which has $m!$ elements.
--
--   A ranking is identified with the bijection that sends each candidate to its position: position $0$ is the top, position $m-1$ the bottom. Every later object of the mission (profiles, rules on rational profiles, cyclic rankings) is built on this type.
--
--   **Formalization Note** Candidates are `Fin m`, 0-based ($c_1 \mapsto 0$, …, $c_m \mapsto m-1$), and a ranking is `Equiv.Perm (Fin m)` read as candidate $\mapsto$ position. A strict total order on a finite set is exactly such a bijection, so this is a faithful encoding of $\mathcal L(C)$, and it is a finite type of cardinality $m!$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 2, "Election Instances", pp.7–8

import Mathlib

namespace ManipPotential

/-- A strict preference order (ranking) over the candidates `c₁, …, c_m` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 2,
"Election Instances", pp.7–8): `L(C)`.

**Formalization Note** Candidates are `Fin m`, 0-based (`c₁ ↦ 0`, …, `c_m ↦ m − 1`). A ranking is a
permutation sending each candidate to its position, `0` being the top. A transitive,
antisymmetric and complete relation on a finite set is exactly such a bijection to positions. -/
abbrev Ranking (m : ℕ) : Type := Equiv.Perm (Fin m)

end ManipPotential


