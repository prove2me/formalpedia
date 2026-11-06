-- Prove2me | Definitions.Def_MethodFulfillment_expALG
-- name    : MethodFulfillment_expALG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:39.279199+00:00
-- url     : https://prove2.me/theorems/69f250f5-cfb3-43b5-a15f-2bab41f4ab7a
-- title:
--   Expected cost $\mathbb E[\mathrm{ALG}(D)]$ of Algorithm 1
-- statement:
--   The expected cost of Algorithm 1 with LP solution $y$ and method-acceptance strategy $\sigma$ is
--   $$\mathbb E[\mathrm{ALG}(D)]=\sum_{r}\Pr(r)\,\mathrm{cost}(r),$$
--   the expectation over the arrival process and the randomization of the algorithm, as in Definition 2.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Definition 2, p.10

import Mathlib
import Definitions.Def_MethodFulfillment_runProb
import Definitions.Def_MethodFulfillment_runCost

namespace MethodFulfillment

/-- The expected cost `E[ALG(D)]` of Algorithm 1 with LP solution `y` and method-acceptance
strategy `σ` (Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…, Definition 2, p.10): the
expectation of `runCost` under `runProb`, over the arrivals and the algorithm's randomization. -/
noncomputable def expALG {I K Q : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    [Fintype Q] {T : ℕ} (P : Instance I K Q T) (y : Q → Finset (I × K) → ℝ)
    (σ : Fin T → Run I K Q T → Option Q → Finset (I × K) → Finset (I × K) → ℝ) : ℝ :=
  ∑ r, runProb P y σ r * runCost P r

end MethodFulfillment


