-- Prove2me | Definitions.Def_AvoidPlast_Supplement_IsSearchNPGen
-- name    : AvoidPlast_Supplement_IsSearchNPGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:13:19.137049+00:00
-- url     : https://prove2.me/theorems/5ad4f3ca-f010-4b2e-a896-7ffba1660e18
-- title:
--   SearchNP-computable generators
-- statement:
--   A SearchNP-computable generator with $L(n)$ outputs of length $m(n)$ is a non-deterministic polynomial-time machine $H$ that has an accepting witness on every input and outputs, on every accepting witness, a list of $L(n)$ strings of $m(n)$ bits. Seed length $j$ means $L=2^j$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 7.1, p.39; Theorem 7.2, p.40

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Supplement_IsPolyNTime

namespace AvoidPlast.Supplement

open AvoidPlast

/-- A SearchNP-computable generator with `L(n)` outputs of length `m(n)` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition
7.1, p.39, and Theorem 7.2, p.40): a non-deterministic polynomial-time machine that has an
accepting witness on every input, and whose output on every accepting witness is a list of `L(n)`
strings of `m(n)` bits (written as one string of length `L(n)·m(n)`). "Seed length `j`" is
`L = 2^j`. -/
def IsSearchNPGen (H : Machine 2) (a : ℕ) (L m : ℕ → ℕ) : Prop :=
  IsPolyNTime H a ∧
  (∀ x : List Bool, ∃ w : List Bool, w.length ≤ a * (x.length ^ a + 1) ∧ Accepts H ![x, w]) ∧
  ∀ x w : List Bool, w.length ≤ a * (x.length ^ a + 1) → Accepts H ![x, w] →
    (output H ![x, w]).length = L x.length * m x.length

end AvoidPlast.Supplement


