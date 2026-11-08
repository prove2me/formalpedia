-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
-- name    : QEC_Coding_ExpanderCodes_LPSQuaternionWord
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:44:03.238347+00:00
-- url     : https://prove2.me/theorems/14bb83bb-92bf-426b-9c4e-bf14b89ee4ac
-- title:
--   LPSQuaternion Word
-- statement:
--   Definitions and structural lemmas for LPSQuaternion Word, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
set_option autoImplicit false
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
def LPSQuaternion.HasLPSParity (t : LPSQuaternion) : Prop :=
  Odd t.a ∧ Even t.b ∧ Even t.c ∧ Even t.d
noncomputable def lpsQuaternionWordProduct
    (word : List (LPSGeneratorIndex p)) : LPSQuaternion :=
  (word.map fun t => t.1).prod
noncomputable def lpsQuaternionAwayWordProduct
    (a : LPSResiduePrime p) (word : List (LPSGeneratorIndex p)) :
    lpsQuaternionAwaySubmonoid a.q :=
  (word.map (lpsQuaternionShellAwayLabel a)).prod
noncomputable def lpsPSLWordProduct
    (a : LPSResiduePrime p) (word : List (LPSGeneratorIndex p)) :
    PSL(2, ZMod a.q) :=
  (word.map (lpsQuaternionLabel a)).prod
end QEC.Coding.TannerLiftedProduct


