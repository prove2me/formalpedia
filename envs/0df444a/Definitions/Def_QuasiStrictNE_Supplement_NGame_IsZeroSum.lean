-- Prove2me | Definitions.Def_QuasiStrictNE_Supplement_NGame_IsZeroSum
-- name    : QuasiStrictNE_Supplement_NGame_IsZeroSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:41:03.356361+00:00
-- url     : https://prove2.me/theorems/ea4e6d32-8a64-4ed4-af9f-4a6252b4cd51
-- title:
--   Zero-sum $n$-player game
-- statement:
--   An $n$-player game is **zero-sum** if at every pure strategy profile $s$ the payoffs sum to zero:
--
--   $$
--   \sum_{i} u_i(s) = 0 .
--   $$
--
--   This is the class in the clause "even for zero-sum games" of Theorem 2.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 2, p.19; proof, p.20 ("Every payoff vector sums to zero")

import Mathlib
import Definitions.Def_QuasiStrictNE_Supplement_NGame

set_option autoImplicit false

namespace QuasiStrictNE.Supplement

/-- **Zero-sum `n`-player game** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, Theorem 2, p.19 ("even for zero-sum games") and proof,
p.20: "Every payoff vector sums to zero").

`G.IsZeroSum` holds iff at every pure strategy profile `s` the players' payoffs sum to zero:
`∑ᵢ u i s = 0`. -/
def NGame.IsZeroSum {n : ℕ} (G : NGame n) : Prop :=
  ∀ s : (i : Fin n) → Fin (G.k i), ∑ i, G.u i s = 0

end QuasiStrictNE.Supplement


