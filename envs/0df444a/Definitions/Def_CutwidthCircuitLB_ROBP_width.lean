-- Prove2me | Definitions.Def_CutwidthCircuitLB_ROBP_width
-- name    : CutwidthCircuitLB_ROBP_width
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:23.064481+00:00
-- url     : https://prove2.me/theorems/4a1bdf6f-b835-4b11-ac5b-9cc509f16f64
-- title:
--   Width $\max_i |V_i|$ of a read-once program
-- statement:
--   The **width** of a read-once program with layers $V_0, \dots, V_\ell$ is $\max_i |V_i|$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.2, p.7

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP

namespace CutwidthCircuitLB

/-- The **width** `max_i |V_i|` of a read-once program (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.2, p.7). -/
def ROBP.width {n : ℕ} (R : ROBP n) : ℕ :=
  Finset.univ.sup R.layerSize

end CutwidthCircuitLB


