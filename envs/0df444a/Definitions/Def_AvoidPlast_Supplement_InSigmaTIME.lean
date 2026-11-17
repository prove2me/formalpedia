-- Prove2me | Definitions.Def_AvoidPlast_Supplement_InSigmaTIME
-- name    : AvoidPlast_Supplement_InSigmaTIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:51:18.766642+00:00
-- url     : https://prove2.me/theorems/f8d96051-47cc-427f-b2d1-13295a7bffe8
-- title:
--   The class $\Sigma_k\mathrm{TIME}[t(n)]$
-- statement:
--   $L\in\Sigma_k\mathrm{TIME}[t(n)]$ if some $\Sigma_k$ machine of time $O(t(n))$ accepts exactly the strings of $L$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 1.4, 5.11, pp.4, 27

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_Supplement_IsSigmaMachine
import Definitions.Def_AvoidPlast_Supplement_sigmaAccepts

namespace AvoidPlast.Supplement

open AvoidPlast

/-- `L ∈ Σ_kTIME[t(n)]` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 1.4, 5.11, pp.4, 27): a `Σ_k` machine of time
`O(t(n))` whose `Σ_k` predicate is membership in `L`. -/
def InSigmaTIME (k : ℕ) (t : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  ∃ (V : Machine (k + 1)) (C : ℕ), IsSigmaMachine k V t C ∧ ∀ x, sigmaAccepts k V t C x ↔ x ∈ L

end AvoidPlast.Supplement


