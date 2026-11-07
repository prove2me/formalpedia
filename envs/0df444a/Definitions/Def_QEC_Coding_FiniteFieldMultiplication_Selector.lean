-- Prove2me | Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
-- name    : QEC_Coding_FiniteFieldMultiplication_Selector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:10:34.759556+00:00
-- url     : https://prove2.me/theorems/e78d6bab-6e0f-4d5f-bedf-73a4cc44a3dc
-- title:
--   Selector
-- statement:
--   Definitions and structural lemmas for Selector, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/Selector.lean

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
set_option autoImplicit false
namespace QEC.Coding
noncomputable def f256SelectorFunctional : (Fin 512 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  f256RMFEpsi.comp f256MFEPsi
noncomputable def f256SelectorCoefficient (q : Fin 512) : ZMod 2 :=
  f256SelectorFunctional (Pi.single q 1)
noncomputable def f256SelectedCoordinates : Finset (Fin 512) :=
  Finset.univ.filter fun q => f256SelectorCoefficient q = 1
noncomputable def f256SelectorQ0 : Fin 512 := f256MFEIndex 0 0 0
noncomputable def f256SelectedCoordinateFraction : ℚ :=
  (f256SelectedCoordinates.card : ℚ) / 512
end QEC.Coding


