-- Prove2me | Definitions.Def_QEC_Coding_CSS_Syndrome
-- name    : QEC_Coding_CSS_Syndrome
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:17:03.898977+00:00
-- url     : https://prove2.me/theorems/ba0dc02b-852a-46a3-ad96-894cb19e8af1
-- title:
--   Syndrome
-- statement:
--   Definitions and structural lemmas for Syndrome, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean

import Definitions.Def_QEC_Coding_CSS_ParityChecks
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace PauliSymplectic
universe v
variable {ι κP κQ : Type v} [Fintype ι] [Fintype κP] [Fintype κQ]
end PauliSymplectic
end Coding
end QEC


