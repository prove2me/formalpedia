-- Prove2me | Definitions.Def_QuasiStrictNE_Qregion
-- name    : QuasiStrictNE_Qregion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:08.818718+00:00
-- url     : https://prove2.me/theorems/8e4aebe3-32ca-408e-b4a5-47b86c3bcf2a
-- title:
--   Best-response region $Q_i$
-- statement:
--   For player 1's payoff matrix $A$ and a pure strategy $i\in M$,
--   $$
--   Q_i=\{y\in\Delta_n : i\in BR_1(y)\}=\{y\in\Delta_n : (Ay)_i\ge (Ay)_h \text{ for all } h\in M\}
--   $$
--   is the closed region of player 2's mixed strategies against which $i$ is a best response of player 1.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §3, p.10

import Mathlib
import Definitions.Def_QuasiStrictNE_BR1

namespace QuasiStrictNE

/-- **Best-response region `Qi` of player 1's pure strategy `i`** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, §3, p.10:
"Qi = {y ∈ ∆n : i ∈ BR1(y)} = {y ∈ ∆n : (Ay)i ≥ (Ay)h for all h ∈ M}").

`Qregion A i` is the set of mixed strategies `y ∈ Δn` of player 2 to which `i` is a best response of
player 1.

**Formalization Note** `Δn` is `stdSimplex ℝ (Fin n)`; indices are 0-based. -/
def Qregion {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) : Set (Fin n → ℝ) :=
  {y | y ∈ stdSimplex ℝ (Fin n) ∧ i ∈ BR1 A y}

end QuasiStrictNE


