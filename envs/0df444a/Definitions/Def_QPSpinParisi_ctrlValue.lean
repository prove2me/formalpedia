-- Prove2me | Definitions.Def_QPSpinParisi_ctrlValue
-- name    : QPSpinParisi_ctrlValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:09:57.596896+00:00
-- url     : https://prove2.me/theorems/f4a2bf8e-5ac1-46ec-9c6b-434982bad881
-- title:
--   The value of the control problem
-- statement:
--   The value $\sup_{u\in D[s,1]}$ of the control objective. The class is nonempty, and for integrable $\kappa$ and $1$-Lipschitz $f$ the objective is bounded above uniformly in $u$, so this is a genuine supremum.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.3), p.4 (PDF p.4); (3.23), p.19 (PDF p.19)

import Mathlib
import Definitions.Def_QPSpinParisi_ctrlJ
import Definitions.Def_QPSpinParisi_Dctrl

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The value `sup_{u ∈ D[s,1]}` of the control objective (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.3), p.4, PDF p.4; (3.23), p.19, PDF p.19).

**Formalization Note** The real `sSup` is honest when `κ` is integrable on `[s,1]`: `u = 0` lies in `Dctrl`, and the
objective is at most `‖x‖ + E‖W.noise 1 - W.noise s‖ + ∫|κ|` for every `u` when `f` is 1-Lipschitz with `f 0 = 0`. -/
noncomputable def ctrlValue {c : ℕ → ℝ} (W : BrownianNoise c) (f : E3 → ℝ) (κ : ℝ → ℝ) (s : ℝ) (x : E3) : ℝ :=
  sSup (ctrlJ W f κ s x '' Dctrl W s)

end QPSpinParisi


