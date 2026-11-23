-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:17.818752+00:00
-- url     : https://prove2.me/theorems/d0dbd27c-1f0b-448e-86f7-d8df35fa5a11
-- title:
--   Jacquet Rallis Transfer Factor Krylov Det
-- statement:
--   Definitions and structural lemmas for Jacquet Rallis Transfer Factor Krylov Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisTransferFactorKrylovDet.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.TransferFactor
variable {k : Type} [CommRing k] {r : ℕ}
def vrow (Y : Gl r k) (i : ℕ) : Fin (r + 1) → k := Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ i)
end GlobalTheory.JR.TransferFactor


