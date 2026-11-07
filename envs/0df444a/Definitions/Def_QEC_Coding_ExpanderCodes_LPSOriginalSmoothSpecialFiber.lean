-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSmoothSpecialFiber
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalSmoothSpecialFiber
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T04:33:16.704616+00:00
-- url     : https://prove2.me/theorems/f6ace374-f732-461a-ae84-151ec565e9d9
-- title:
--   LPSOriginal Smooth Special Fiber
-- statement:
--   Definitions and structural lemmas for LPSOriginal Smooth Special Fiber, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSmoothSpecialFiber.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory
def lpsOriginalSpecialFibreSmoothLocus
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalSpecialFibre p N hN).Opens :=
  letI := lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation p N hN
  (lpsOriginalSpecialFibreToPrimeField p N hN).smoothLocus
def lpsOriginalSpecialFibreSmoothOpenToPrimeField
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalSpecialFibreSmoothLocus p N hN).toScheme ⟶ Spec (.of (ZMod p)) :=
  (lpsOriginalSpecialFibreSmoothLocus p N hN).ι ≫
    lpsOriginalSpecialFibreToPrimeField p N hN
end
end QEC.Coding.TannerLiftedProduct


