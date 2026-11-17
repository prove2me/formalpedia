-- Prove2me | Definitions.Def_AvoidPlast_Supplement_sigmaAccepts
-- name    : AvoidPlast_Supplement_sigmaAccepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:50:37.712624+00:00
-- url     : https://prove2.me/theorems/3d5c3aca-0f85-4d0d-8c92-61604fec7f03
-- title:
--   The $\Sigma_k$ predicate of a machine
-- statement:
--   A $\Sigma_k$ machine $V$ of time $O(t(n))$ accepts $x$ if
--   $$\exists w_1\,\forall w_2\cdots Q_k w_k:\ V(x,w_1,\dots,w_k)\text{ accepts},$$
--   with $|w_i|\le C(t(|x|)+1)$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 5.9, 5.11, pp.25–27

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_Supplement_altQ

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The `Σ_k` predicate of `V` on `x` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 5.9, 5.11, pp.25–27):
`∃ w₁ ∀ w₂ … Q_k w_k, V(x, w₁, …, w_k)` accepts, with `|w_i| ≤ C · (t(|x|) + 1)`. -/
def sigmaAccepts (k : ℕ) (V : Machine (k + 1)) (t : ℕ → ℕ) (C : ℕ) (x : List Bool) : Prop :=
  altQ k true (C * (t x.length + 1)) fun ws => Accepts V (Fin.cons x ws : Fin (k + 1) → List Bool)

end AvoidPlast.Supplement


