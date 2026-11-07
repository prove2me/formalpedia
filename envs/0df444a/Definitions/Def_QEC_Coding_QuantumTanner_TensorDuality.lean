-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
-- name    : QEC_Coding_QuantumTanner_TensorDuality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:08:21.239876+00:00
-- url     : https://prove2.me/theorems/3c85fc57-f3ab-4b2f-b94f-250771944e0a
-- title:
--   Tensor Duality
-- statement:
--   Definitions and structural lemmas for Tensor Duality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_Core_Duality
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
def columnExtension (b : B) (c : Word F A) : Word F (A × B) :=
  fun ab => if ab.2 = b then c ab.1 else 0
def rowExtension (a : A) (r : Word F B) : Word F (A × B) :=
  fun ab => if ab.1 = a then r ab.2 else 0
end QEC.Coding.QuantumTanner


