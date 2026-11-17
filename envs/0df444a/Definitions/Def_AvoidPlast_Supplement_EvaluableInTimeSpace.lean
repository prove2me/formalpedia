-- Prove2me | Definitions.Def_AvoidPlast_Supplement_EvaluableInTimeSpace
-- name    : AvoidPlast_Supplement_EvaluableInTimeSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:02:08.760417+00:00
-- url     : https://prove2.me/theorems/f5edf9a2-bb8e-488b-bd40-814a80b435ce
-- title:
--   Families evaluable in simultaneous time $\mathrm{poly}(n)$ and space $S(n)$
-- statement:
--   An indexed family is evaluable in simultaneous time $\mathrm{poly}(n)$ and space $O(S(n))$ if one machine given $(x,y,i)$ prints the $i$-th output bit of $C_x(y)$ within $a(|x|^a+1)$ steps and work space $K(S(|x|)+1)$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 1.3, 5.6, 5.9, pp.4, 24–25

import Mathlib
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_workSpace

namespace AvoidPlast.Supplement

open AvoidPlast

/-- An indexed family evaluable in simultaneous time `poly(n)` and space `O(S(n))` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728),
Theorems 1.3, 5.6, 5.9, pp.4, 24–25): one machine on `(x, y, i)` prints the `i`-th output bit of
`C_x(y)` within `a(|x|^a + 1)` steps and work space `K(S(|x|) + 1)`. -/
def EvaluableInTimeSpace (C : List Bool → List Bool → List Bool) (ℓin ℓout : ℕ → ℕ) (S : ℕ → ℝ) :
    Prop :=
  (∀ x y : List Bool, y.length = ℓin x.length → (C x y).length = ℓout x.length) ∧
    ∃ (M : Machine 3) (a : ℕ) (K : ℝ), ∀ (x y : List Bool) (i : ℕ),
      y.length = ℓin x.length → i < ℓout x.length →
        HaltsWithin M ![x, y, Nat.bits i] (a * (x.length ^ a + 1)) ∧
        output M ![x, y, Nat.bits i] = [(C x y).getD i false] ∧
        (workSpace M ![x, y, Nat.bits i] : ℝ) ≤ K * (S x.length + 1)

end AvoidPlast.Supplement


