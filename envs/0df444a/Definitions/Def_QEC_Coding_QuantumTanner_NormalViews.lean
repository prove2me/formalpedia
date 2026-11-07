-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
-- name    : QEC_Coding_QuantumTanner_NormalViews
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:23:42.135137+00:00
-- url     : https://prove2.me/theorems/1f93e4fc-6273-41af-af1f-256f0663d3b4
-- title:
--   Normal Views
-- statement:
--   Definitions and structural lemmas for Normal Views, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NormalViews.lean

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]
end QEC.Coding.QuantumTanner


