-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
-- name    : QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:41:15.738756+00:00
-- url     : https://prove2.me/theorems/0f526679-43b8-4d42-bd8e-d5d0c73a5076
-- title:
--   LPSHecke Correspondence
-- statement:
--   Definitions and structural lemmas for LPSHecke Correspondence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCorrespondence.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction
set_option autoImplicit false
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
noncomputable def lpsQuaternionShellAwayLabel
    (a : LPSResiduePrime p) :
    LPSGeneratorIndex p → lpsQuaternionAwaySubmonoid a.q :=
  fun t => lpsQuaternionAwayElement a t.1
    (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.2)
noncomputable def lpsPGLHeckeLabel
    (a : LPSResiduePrime p) :
    LPSGeneratorIndex p → PGL(2, ZMod a.q) :=
  fun t => lpsQuaternionAwayPGL a.q (lpsQuaternionShellAwayLabel a t)
end QEC.Coding.TannerLiftedProduct


