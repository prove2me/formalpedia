-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T16:12:09.436441+00:00
-- url     : https://prove2.me/theorems/96cdeeaf-35ad-481c-983c-ad339ee55b4f
-- title:
--   Global Norm One Bridge
-- statement:
--   Definitions and structural lemmas for Global Norm One Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/GlobalNormOneBridge.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraBuildingNormOneGeneratorRatio_mem_splitNormOne

set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def cyclicAlgebraSplitNormOneGeneratorRatio
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    CyclicAlgebraSplitNormOne P r :=
  ⟨cyclicAlgebraBuildingNormOneGeneratorRatio P r u v,
    cyclicAlgebraBuildingNormOneGeneratorRatio_mem_splitNormOne P r u v⟩
noncomputable def orderNormOneInnerFormToCyclicAlgebraSplitNormOne
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      CyclicAlgebraSplitNormOne P r :=
  (orderNormOneToCyclicAlgebraNormOne P r).comp
    (orderNormOneInnerFormToActualNormOne P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


