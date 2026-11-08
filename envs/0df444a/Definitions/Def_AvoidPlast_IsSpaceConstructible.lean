-- Prove2me | Definitions.Def_AvoidPlast_IsSpaceConstructible
-- name    : AvoidPlast_IsSpaceConstructible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:33.722431+00:00
-- url     : https://prove2.me/theorems/c6f155a4-a648-4e01-9b38-8288fdb6f1b5
-- title:
--   Space-constructible bounds
-- statement:
--   A bound $s:\mathbb N\to\mathbb N$ is computable within its own space if a machine on an $n$-bit input writes $s(n)$ in binary within work space $O(s(n))$. This is the form of the paper's "nice" convention needed for padding.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Proof of Theorem 5.8, p.25; Section 3, p.14

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_Halts
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_workSpace

namespace AvoidPlast

/-- A space bound computable within its own space (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), proof of Theorem 5.8, p.25, reading R7, the
paper's "nice" convention of p.14 for space bounds): a machine on an `n`-bit input writes `s(n)` in
binary within work space `O(s(n))`. -/
def IsSpaceConstructible (s : ℕ → ℕ) : Prop :=
  ∃ (M : Machine 1) (C : ℝ), ∀ x : List Bool,
    Halts M ![x] ∧ output M ![x] = Nat.bits (s x.length) ∧
      (workSpace M ![x] : ℝ) ≤ C * ((s x.length : ℝ) + 1)

end AvoidPlast


