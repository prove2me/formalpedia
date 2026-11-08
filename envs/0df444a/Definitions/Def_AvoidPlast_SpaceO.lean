-- Prove2me | Definitions.Def_AvoidPlast_SpaceO
-- name    : AvoidPlast_SpaceO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:46:37.152531+00:00
-- url     : https://prove2.me/theorems/38f2e584-e42c-4da0-a132-260b77f5c9c7
-- title:
--   Deterministic space $O(s(n))$
-- statement:
--   A machine $M$ with one read-only tape has **deterministic space $O(s(n))$** if it halts on every input and its work space on $x$ is at most $C(s(|x|)+1)$, for a constant $C$. A deterministic space-$n^\gamma$ machine is the case $s(n)=n^\gamma$.
--
--   **Formalization Note** The $+1$ covers $n=0$ (reading R2), and read-only input and write-only output do not count.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.14, p.29

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_Halts
import Definitions.Def_AvoidPlast_workSpace

namespace AvoidPlast

/-- A deterministic machine of space `O(s(n))` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 5.14, p.29, "deterministic
space-`n^γ` machine"): it halts on every input and its work space is at most `C · (s(|x|) + 1)`.

**Formalization Note** Reading R2: the `+ 1` covers `n = 0`, since `0^γ = 0` and every machine
scans at least one cell. The input and the output are not work space. -/
def SpaceO (M : Machine 1) (s : ℕ → ℝ) : Prop :=
  (∀ x : List Bool, Halts M ![x]) ∧
    ∃ C : ℝ, ∀ x : List Bool, (workSpace M ![x] : ℝ) ≤ C * (s x.length + 1)

end AvoidPlast


