-- Prove2me | Definitions.Def_AvoidPlast_Supplement_ComputableInSpaceIdx
-- name    : AvoidPlast_Supplement_ComputableInSpaceIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:09:17.607113+00:00
-- url     : https://prove2.me/theorems/8db600ad-b649-41d1-9241-3f0016a29c74
-- title:
--   Generators computable in space $s(n)$
-- statement:
--   $g=\{g_n\}$ is computable in space $O(s(n))$ if a machine given $n$ in binary and a seed $x$ of length $\ell(n)$ prints $g_n(x)$ using work space $K(s(n)+1)$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 1.8, p.5

import Mathlib
import Definitions.Def_AvoidPlast_Halts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_workSpace

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The generator `g = {g_n}` is computable in space `O(s(n))` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 1.8, p.5): a
machine on `(n` in binary`, x)` with `|x| = ℓ(n)` prints `g_n(x)` within work space `K(s(n) + 1)`. -/
def ComputableInSpaceIdx (g : ℕ → List Bool → List Bool) (ℓ : ℕ → ℕ) (s : ℕ → ℝ) : Prop :=
  ∃ (M : Machine 2) (K : ℝ), ∀ (n : ℕ) (x : List Bool), x.length = ℓ n →
    Halts M ![Nat.bits n, x] ∧ output M ![Nat.bits n, x] = g n x ∧
    (workSpace M ![Nat.bits n, x] : ℝ) ≤ K * (s n + 1)

end AvoidPlast.Supplement


