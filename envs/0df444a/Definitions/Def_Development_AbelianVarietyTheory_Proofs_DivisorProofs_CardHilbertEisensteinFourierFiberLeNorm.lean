-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardHilbertEisensteinFourierFiberLeNorm
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardHilbertEisensteinFourierFiberLeNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:02.570655+00:00
-- url     : https://prove2.me/theorems/c7f83b29-be92-4fc2-ac92-1bc071092c81
-- title:
--   Card Hilbert Eisenstein Fourier Fiber Le Norm
-- statement:
--   Definitions and structural lemmas for Card Hilbert Eisenstein Fourier Fiber Le Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardHilbertEisensteinFourierFiberLeNorm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDivisorsLeAbsNormNumberFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
noncomputable section
namespace GlobalTheory.QFiber
open FractionalIdeal
variable {F : Type} [Field F] [NumberField F]
def toIdeal (K : FractionalIdeal (𝓞 F)⁰ F) : Ideal (𝓞 F) :=
  open Classical in if h : K ≤ 1 then (le_one_iff_exists_coeIdeal.mp h).choose else ⊥
end GlobalTheory.QFiber


