-- Prove2me | Definitions.Def_QEC_Results_QLDPC_ConditionalLiftedProductFamily
-- name    : QEC_Results_QLDPC_ConditionalLiftedProductFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:56:14.955181+00:00
-- url     : https://prove2.me/theorems/23e7df8f-f4c7-4ea3-b972-0af8194eebf3
-- title:
--   Conditional Lifted Product Family
-- statement:
--   Definitions and structural lemmas for Conditional Lifted Product Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/ConditionalLiftedProductFamily.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing
noncomputable local instance _p2m_local_instance_608e2928fd_22 {F : Type} : DecidableEq F := Classical.decEq _
noncomputable local instance pk22ConditionalQubitDecidableEq
    {p : ℕ} {R R' : Type} (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    DecidableEq
      (FamilyQubitIndex (W := Fin (p + 1)) (R := R) (R' := R')
        (G := LPSVertexGroup hp hp4) B) :=
  Classical.decEq _
end QEC.Coding.TannerLiftedProduct


