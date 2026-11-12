-- Prove2me | Definitions.Def_QEC_Results_Distillation_TriorthogonalDistillation
-- name    : QEC_Results_Distillation_TriorthogonalDistillation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T22:34:16.508134+00:00
-- url     : https://prove2.me/theorems/e08f17c7-5812-4c93-b234-7526c6ff2e51
-- title:
--   Triorthogonal Distillation
-- statement:
--   Definitions and structural lemmas for Triorthogonal Distillation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/TriorthogonalDistillation.lean

import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily BH12NoisyInjection BH12Protocol
open Filter Topology
end QEC.Distillation.Triorthogonal.BH12Concatenation


