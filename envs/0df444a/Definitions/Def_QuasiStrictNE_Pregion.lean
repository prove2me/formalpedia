-- Prove2me | Definitions.Def_QuasiStrictNE_Pregion
-- name    : QuasiStrictNE_Pregion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:07.581041+00:00
-- url     : https://prove2.me/theorems/027e4afb-e9c5-4151-ab6e-67f68f79f996
-- title:
--   Best-response region $P_j$
-- statement:
--   For player 2's payoff matrix $B$ and a pure strategy $j\in N$,
--   $$
--   P_j=\{x\in\Delta_m : j\in BR_2(x)\}=\{x\in\Delta_m : (B^\top x)_j\ge (B^\top x)_\ell \text{ for all } \ell\in N\}
--   $$
--   is the closed region of player 1's mixed strategies against which $j$ is a best response of player 2.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §3, p.10

import Mathlib
import Definitions.Def_QuasiStrictNE_BR2

namespace QuasiStrictNE

/-- **Best-response region `Pj` of player 2's pure strategy `j`** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, §3, p.10:
"Pj = {x ∈ ∆m : j ∈ BR2(x)} = {x ∈ ∆m : (B^⊤x)j ≥ (B^⊤x)ℓ for all ℓ ∈ N}").

`Pregion B j` is the set of mixed strategies `x ∈ Δm` of player 1 to which `j` is a best response of
player 2.

**Formalization Note** `Δm` is `stdSimplex ℝ (Fin m)`; indices are 0-based. -/
def Pregion {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : Set (Fin m → ℝ) :=
  {x | x ∈ stdSimplex ℝ (Fin m) ∧ j ∈ BR2 B x}

end QuasiStrictNE


