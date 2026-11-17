-- Prove2me | Definitions.Def_AvoidPlast_Supplement_IsSigmaMachine
-- name    : AvoidPlast_Supplement_IsSigmaMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:50:03.063982+00:00
-- url     : https://prove2.me/theorems/d7afee1d-62bf-4bc7-9758-9905684c04fd
-- title:
--   A $\Sigma_k$ machine of time $O(t(n))$
-- statement:
--   A $\Sigma_k$ machine is a deterministic machine $V$ with read-only tapes for the input $x$ and $k$ quantified strings; it runs in time $O(t(n))$ if it halts within $C\cdot(t(|x|)+1)$ steps whatever the quantified strings are. A *linear-time* $\Sigma_k$ machine has $t(n)=n$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 5.9, 5.11, pp.25–27

import Mathlib
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine

namespace AvoidPlast.Supplement

open AvoidPlast

/-- A `Σ_k` machine of time `O(t(n))` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 5.9, 5.11, pp.25–27): a deterministic
machine `V` with read-only tapes for the input `x` and the `k` quantified strings, halting within
`C · (t(|x|) + 1)` steps whatever the quantified strings are. "Linear time" is `t(n) = n`. -/
def IsSigmaMachine (k : ℕ) (V : Machine (k + 1)) (t : ℕ → ℕ) (C : ℕ) : Prop :=
  ∀ (x : List Bool) (ws : Fin k → List Bool),
    HaltsWithin V (Fin.cons x ws : Fin (k + 1) → List Bool) (C * (t x.length + 1))

end AvoidPlast.Supplement


