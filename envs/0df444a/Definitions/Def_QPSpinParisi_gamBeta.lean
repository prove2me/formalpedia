-- Prove2me | Definitions.Def_QPSpinParisi_gamBeta
-- name    : QPSpinParisi_gamBeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:46.32019+00:00
-- url     : https://prove2.me/theorems/ec211423-c73e-4587-b7c7-0ecfe9672e13
-- title:
--   $\gamma_{\xi,\beta}=\beta\alpha_{\xi,\beta}$ on $[0,1)$
-- statement:
--   For $\alpha$ on $[0,1]$, the function $q\mapsto\beta\alpha(q)$ on $[0,1)$. At the minimizer it is the function $\gamma_{\xi,\beta}$ of the zero-temperature limit.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.19 (PDF p.19)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The function `γ_{ξ,β}(q) := β α_{ξ,β}(q)` for `q < 1` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.19, PDF p.19), for a general `α`. -/
noncomputable def gamBeta (β : ℝ) (α : Icc (0 : ℝ) 1 → ℝ) : Ico (0 : ℝ) 1 → ℝ :=
  fun q => β * α ⟨q.1, q.2.1, q.2.2.le⟩

end QPSpinParisi


