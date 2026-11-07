-- Prove2me | Definitions.Def_QPSpinParisi_Pf
-- name    : QPSpinParisi_Pf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:51.141068+00:00
-- url     : https://prove2.me/theorems/adfadeb7-098c-484f-9a0b-6b42ef5e3408
-- title:
--   The Parisi functional $P_\xi$, (2.4)
-- statement:
--   The Parisi functional on $\mathcal U$:
--   $$P_\xi(\gamma)=\Psi_{\xi,\gamma}(0,0)-\frac12\int_0^1q\zeta(q)\gamma(q)\,dq.$$
--   Theorem 1 identifies its infimum with the limiting maximal product-state energy.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.4), p.4 (PDF p.4)

import Mathlib
import Definitions.Def_QPSpinParisi_Psi

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The Parisi functional `P_ξ(γ) = Ψ_{ξ,γ}(0, 0) - (1/2) ∫₀¹ q ζ(q) γ(q) dq` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.4), p.4, PDF p.4). -/
noncomputable def Pf {c : ℕ → ℝ} (W : BrownianNoise c) (γ : Ico (0 : ℝ) 1 → ℝ) : ℝ :=
  Psi W γ 0 0 - (1 / 2) * ∫ q in (0 : ℝ)..1, q * zeta c q * gamHat γ q

end QPSpinParisi


