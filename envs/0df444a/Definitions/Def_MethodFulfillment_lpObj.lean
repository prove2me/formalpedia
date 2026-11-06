-- Prove2me | Definitions.Def_MethodFulfillment_lpObj
-- name    : MethodFulfillment_lpObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:48.493246+00:00
-- url     : https://prove2.me/theorems/3a6e2320-8974-4aee-b6c0-c77e5491ca95
-- title:
--   Objective (6) of the expected LP
-- statement:
--   The objective of the expected LP (6) at $x$ is
--   $$\sum_{q\in Q}\langle c,x[q]\rangle=\sum_{q\in Q}\sum_{m\in M(q)}c_m\,x_m .$$
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), (6), p.11

import Mathlib
import Definitions.Def_MethodFulfillment_Instance

namespace MethodFulfillment

/-- The objective (6) of the expected LP, `∑_q ⟨c, x[q]⟩ = ∑_q ∑_{m ∼ q} c_m x_m` (Amil, Makhdoumi &
Wei, manuscript, PDF sha256 197c13b9…, (6), p.11). -/
def lpObj {I K Q : Type} [Fintype Q] {T : ℕ} (P : Instance I K Q T)
    (x : Q → Finset (I × K) → ℝ) : ℝ :=
  ∑ q, ∑ m ∈ P.methods q, P.c q m * x q m

end MethodFulfillment


