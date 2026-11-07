-- Prove2me | Definitions.Def_QEC_Coding_CSS_Correctability
-- name    : QEC_Coding_CSS_Correctability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:18:16.769927+00:00
-- url     : https://prove2.me/theorems/6687f697-a02f-4cf5-900d-629e60eff73a
-- title:
--   Correctability
-- statement:
--   Definitions and structural lemmas for Correctability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Correctability.lean

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_Correctability
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace PauliSymplectic
universe u v
variable {iota kappaP kappaQ : Type u} [Fintype iota] [DecidableEq iota]
  [Fintype kappaP] [Fintype kappaQ]
end PauliSymplectic
end Coding
end QEC


