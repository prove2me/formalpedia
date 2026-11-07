-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_SyndromeInjectivity
-- name    : QEC_Coding_Stabilizer_SyndromeInjectivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:11:19.50556+00:00
-- url     : https://prove2.me/theorems/1f7524bc-d44f-49ce-a1dc-247a7faa62b0
-- title:
--   Syndrome Injectivity
-- statement:
--   Definitions and structural lemmas for Syndrome Injectivity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SyndromeInjectivity.lean

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Degeneracy
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace StabilizerCode
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
end StabilizerCode
end Coding
end QEC


