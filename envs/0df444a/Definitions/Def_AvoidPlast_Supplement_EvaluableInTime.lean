-- Prove2me | Definitions.Def_AvoidPlast_Supplement_EvaluableInTime
-- name    : AvoidPlast_Supplement_EvaluableInTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:01:43.775297+00:00
-- url     : https://prove2.me/theorems/d41f577b-e9ac-40e3-919e-1cc74f378378
-- title:
--   Families evaluable in time $T(n)$
-- statement:
--   An indexed family $C=\{C_x\}$, $C_x:\{0,1\}^{\ell_{in}(|x|)}\to\{0,1\}^{\ell_{out}(|x|)}$, is evaluable in time $O(T(n))$ if a machine given $(x,y,i)$ prints the $i$-th output bit of $C_x(y)$ within $K(T(|x|)+1)$ steps.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 1.6, 6.9, 6.11, pp.4, 37–38

import Mathlib
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output

namespace AvoidPlast.Supplement

open AvoidPlast

/-- An indexed family `C = {C_x}`, `C_x : {0,1}^{ℓin(|x|)} → {0,1}^{ℓout(|x|)}`, evaluable in time
`O(T(n))` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 1.6, 6.9, 6.11, pp.4, 37–38; the shape of Definitions 3.2, 3.3,
p.14): a machine on `(x, y, i)` prints the `i`-th output bit of `C_x(y)` within `K(T(|x|) + 1)`
steps. -/
def EvaluableInTime (C : List Bool → List Bool → List Bool) (ℓin ℓout T : ℕ → ℕ) : Prop :=
  (∀ x y : List Bool, y.length = ℓin x.length → (C x y).length = ℓout x.length) ∧
    ∃ (M : Machine 3) (K : ℕ), ∀ (x y : List Bool) (i : ℕ),
      y.length = ℓin x.length → i < ℓout x.length →
        HaltsWithin M ![x, y, Nat.bits i] (K * (T x.length + 1)) ∧
        output M ![x, y, Nat.bits i] = [(C x y).getD i false]

end AvoidPlast.Supplement


