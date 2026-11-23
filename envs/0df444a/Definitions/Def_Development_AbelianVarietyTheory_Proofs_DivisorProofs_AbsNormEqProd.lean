-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:25.37236+00:00
-- url     : https://prove2.me/theorems/787f7dfa-9ed5-4936-88da-49208b69c8d2
-- title:
--   Abs Norm Eq Prod
-- statement:
--   Definitions and structural lemmas for Abs Norm Eq Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormEqProd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
namespace GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.HeckeTwoExp
namespace GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
def toQ (𝔞 𝔟 : Frac F) : (Σ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
    {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}) → Quotient (qRel 𝔞 𝔟) :=
  fun s => Quotient.mk _ ⟨(s.2.1.1, s.1.out.1), s.2.1.2.1, s.1.out.2.1, s.2.2⟩
end GlobalTheory.HeckeTwoExp
namespace GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.HeckeTwoExp


