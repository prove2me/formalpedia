-- Prove2me | Definitions.Def_QPSpinParisi_PfB
-- name    : QPSpinParisi_PfB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:46.9536+00:00
-- url     : https://prove2.me/theorems/a73e4e68-4077-4ee2-ada0-0cfc0271f53c
-- title:
--   The functional $P_{\xi,\beta}$ on $\mathcal M$
-- statement:
--   For $\alpha\in\mathcal M$,
--   $$P_{\xi,\beta}(\alpha)=\Psi_{\xi,\beta,\alpha}(0,0)-\frac\beta2\int_0^1q\zeta(q)\alpha(q)\,dq.$$
--   This is the scalar Parisi functional at inverse temperature $\beta$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.17 (PDF p.17)

import Mathlib
import Definitions.Def_QPSpinParisi_PsiB

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The functional `P_{ξ,β}(α) = Ψ_{ξ,β,α}(0, 0) - (β/2) ∫₀¹ q ζ(q) α(q) dq` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.17, PDF p.17). -/
noncomputable def PfB {c : ℕ → ℝ} (W : BrownianNoise c) (β : ℝ) (α : Icc (0 : ℝ) 1 → ℝ) : ℝ :=
  PsiB W β α 0 0 - (β / 2) * ∫ q in (0 : ℝ)..1, q * zeta c q * alHat α q

end QPSpinParisi


