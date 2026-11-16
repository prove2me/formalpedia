-- Prove2me | Definitions.Def_GeomDRSub_Supplement_OracleStrategy_call
-- name    : GeomDRSub_Supplement_OracleStrategy_call
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:39:20.861207+00:00
-- url     : https://prove2.me/theorems/7662253b-847d-4e9c-afd8-f7f50762977a
-- title:
--   The $k$-th call of an execution
-- statement:
--   The $k$-th call ($k=0,1,\dots$) of the execution of an oracle algorithm with seed $\omega$ and answering rule $\mathrm{ans}$ is $c_k=\mathrm{step}(d,x,k,\omega,r_0,\dots,r_{k-1})$, where the $r_i$ are the responses produced by that execution.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Definition 6.1, p.33

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_OracleStrategy_state

namespace GeomDRSub.Supplement

/-- **The `k`-th call of an execution** (0-based). Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Definition 6.1 (p.33): the call
made by `A` after receiving the responses to its first `k` calls, in the execution with seed `ω`
and answering rule `ans` (see `OracleStrategy.state`). -/
noncomputable def OracleStrategy.call {Ω : Type} [MeasurableSpace Ω] {m : ℕ}
    (A : OracleStrategy Ω m) (d : ℕ) (x : Fin m → ℝ) (ans : ℕ → OCall d → OResp d) (ω : Ω)
    (k : ℕ) : OCall d :=
  A.step d x k ω (A.state d x ans ω k).1

end GeomDRSub.Supplement


