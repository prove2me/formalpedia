-- Prove2me | Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
-- name    : QEC_Coding_CSS_GibbsSyndrome_Selection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:26:47.599091+00:00
-- url     : https://prove2.me/theorems/ec8c5311-2e70-4a0a-8f6f-b244ea75bfa4
-- title:
--   Selection
-- statement:
--   Definitions and structural lemmas for Selection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Selection.lean

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.CSSGibbs
open Classical Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
local instance _p2m_local_instance_807a85e857_19 : Fintype (LinearMap.range P) := Fintype.ofFinite _
local instance _p2m_local_instance_807a85e857_20 : Fintype (LinearMap.range Q) := Fintype.ofFinite _
def selectedProjector (A : Finset (Realizable P Q)) : Operator (Qubit.QubitRegister ι) :=
  ∑ a ∈ A, projector P Q horth (realizableEmbedding P Q a)
end QEC.Coding.CSSGibbs


