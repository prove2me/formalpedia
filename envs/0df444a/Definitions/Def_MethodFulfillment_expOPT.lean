-- Prove2me | Definitions.Def_MethodFulfillment_expOPT
-- name    : MethodFulfillment_expOPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:12:05.401614+00:00
-- url     : https://prove2.me/theorems/8d4ca917-34fd-4d80-b58a-54c37150df3b
-- title:
--   Benchmark $\mathbb E[\mathrm{OPT}(D)]$
-- statement:
--   The **benchmark** of the competitive ratio is the expected offline optimum
--   $$\mathbb E[\mathrm{OPT}(D)]=\sum_{\omega}\Big(\prod_{t}\Pr(\omega_t)\Big)\,\mathrm{OPT}(\omega),$$
--   the expectation over the independent arrivals of the optimum of the integer program (1)–(4). A competitive ratio is measured against this quantity (Definition 2).
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Definition 2, p.10

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_arrProb
import Definitions.Def_MethodFulfillment_OPT

namespace MethodFulfillment

/-- The benchmark `E[OPT(D)]` (Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…,
Definition 2, p.10): the expectation of the offline optimum (1) over the independent arrivals,
`∑_ω (∏_t arrProb P t (ω t)) · OPT(ω)`. -/
noncomputable def expOPT {I K Q : Type} [DecidableEq I] [DecidableEq K] [Fintype Q] {T : ℕ}
    (P : Instance I K Q T) : ℝ :=
  ∑ ω : Fin T → Option Q, (∏ t, arrProb P t (ω t)) * OPT P ω

end MethodFulfillment


