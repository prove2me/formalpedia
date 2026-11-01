-- Prove2me | Definitions.Def_ParetoIneff_Mech_IsEq
-- name    : ParetoIneff_Mech_IsEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:59.247109+00:00
-- url     : https://prove2.me/theorems/bc3af17a-c00f-4456-b908-c1fd69d88382
-- title:
--   Pure Nash equilibrium of a mechanism
-- statement:
--   A reported profile $s$ is a **(pure Nash) equilibrium** of $\mathcal M$ with respect to the true profile $t$ if, for every machine $i$ and every deviation $s_i'\in\mathbb R_{\ge0}^m$,
--   $$
--   u_i^{\mathcal M}(s\mid t)\ge u_i^{\mathcal M}(s_i',s_{-i}\mid t).
--   $$
--   Deviations are arbitrary, so a machine may change all of its reports at once.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5

import Mathlib
import Definitions.Def_ParetoIneff_Mech_utility

open NNReal

namespace ParetoIneff

/-- `s` is a **(pure Nash) equilibrium** of `ℳ` with respect to the true profile `t`,
arXiv:1809.03454v7, p.5: for every machine `i` and every deviation `s'ᵢ ∈ ℝ≥0^m`,
`u_i(s | t) ≥ u_i(s'ᵢ, s₋ᵢ | t)`. -/
def Mech.IsEq {n : ℕ} (M : Mech n) (m : ℕ) (t s : Fin n → Fin m → ℝ≥0) : Prop :=
  ∀ (i : Fin n) (s' : Fin m → ℝ≥0), M.utility m t (Function.update s i s') i ≤ M.utility m t s i

end ParetoIneff


