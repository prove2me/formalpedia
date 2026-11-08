-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:09:35.223377+00:00
-- url     : https://prove2.me/theorems/f5bc7f46-e7c2-4971-ab23-62ff30dc2d5e
-- title:
--   Coset Detectability
-- statement:
--   Definitions and structural lemmas for Coset Detectability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CosetDetectability.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
open Coding Semantics
open scoped BigOperators
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]
local instance _p2m_local_instance_b70f205f2b_23 : DecidableEq Logical := Classical.decEq _
local instance _p2m_local_instance_b70f205f2b_24 : DecidableEq (Word F Logical) := Classical.decEq _
local instance _p2m_local_instance_b70f205f2b_25 : Fintype (Word F Logical) := Fintype.ofFinite _
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput


