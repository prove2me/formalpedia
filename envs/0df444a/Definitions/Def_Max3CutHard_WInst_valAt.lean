-- Prove2me | Definitions.Def_Max3CutHard_WInst_valAt
-- name    : Max3CutHard_WInst_valAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:54.138264+00:00
-- url     : https://prove2.me/theorems/0b7b3911-8579-4684-b320-d1ab1d645471
-- title:
--   The satisfied weight $\mathrm{val}_\Phi(\sigma)$
-- statement:
--   For an assignment $\sigma:U\cup W\to\mathbb Z_3$,
--
--   $$\mathrm{val}_\Phi(\sigma)=\sum_{e\ \text{satisfied by}\ \sigma}\lambda_e,$$
--
--   the total weight of the equations that $\sigma$ satisfies.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Håstad's equations, p.4

import Mathlib
import Definitions.Def_Max3CutHard_WInst
import Definitions.Def_Max3CutHard_Eqn_Sat

namespace Max3CutHard

/-- **`val_Φ(σ)`, the weight satisfied by an assignment.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Håstad's
equations, p.4: "For an assignment `σ : U ∪ W → ℤ₃`, `val_Φ(σ)` is the total weight of the
equations it satisfies". -/
noncomputable def WInst.valAt {U W : Type} (Φ : WInst U W) (σU : U → ZMod 3) (σW : W → ZMod 3) : ℝ :=
  (Φ.eqs.map fun p => if p.1.Sat σU σW then p.2 else 0).sum

end Max3CutHard


