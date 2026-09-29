-- Prove2me | solution 1 for AlgebraicCurve.mem_repartitionsOf_iff_coe_mem_adeleBdd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/94ef0ed9-35d3-568a-9480-dcfcbe26edc2

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor repartitions repartitionsOf adeleBdd"
p2m_open "AlgebraicCurve"

open WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd.AlgebraicCurve WithZero in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {D : Divisor K F} {α : ↥(repartitions K F)} :
    α ∈ repartitionsOf D ↔ (α : Place K F → F) ∈ adeleBdd D := Iff.rfl

end S_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd
end P2MW
export P2MW.S_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd (solution)
