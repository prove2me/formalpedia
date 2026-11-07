-- Prove2me | Definitions.Def_QPSpinParisi_Psi
-- name    : QPSpinParisi_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:35.183422+00:00
-- url     : https://prove2.me/theorems/6b456ec7-3ba2-4eb9-b90a-8e34f9b7a640
-- title:
--   The value function $\Psi_{\xi,\gamma}$, (2.3)
-- statement:
--   For $\gamma\in\mathcal U$,
--   $$\Psi_{\xi,\gamma}(s,x)=\sup_{u\in D[s,1]}\mathbb E\Big[\Big\|x+\int_s^1\sqrt{\zeta(r)}\,dB_r+\int_s^1\zeta(r)\gamma(r)u_r\,dr\Big\|-\frac12\int_s^1\zeta(r)\gamma(r)\|u_r\|^2\,dr\Big].$$
--   This is the stochastic control problem that defines the Parisi functional.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.3), p.4 (PDF p.4)

import Mathlib
import Definitions.Def_QPSpinParisi_ctrlValue
import Definitions.Def_QPSpinParisi_gamHat
import Definitions.Def_QPSpinParisi_zeta

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The value function `Ψ_{ξ,γ}(s, x)` of (2.3) (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.3), p.4, PDF p.4): terminal function `‖·‖`, drift weight `ζγ`.
-/
noncomputable def Psi {c : ℕ → ℝ} (W : BrownianNoise c) (γ : Ico (0 : ℝ) 1 → ℝ) (s : ℝ) (x : E3) : ℝ :=
  ctrlValue W (fun y => ‖y‖) (fun r => zeta c r * gamHat γ r) s x

end QPSpinParisi


