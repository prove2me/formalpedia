-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumLatticePairUnitQuotientRegroup
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumLatticePairUnitQuotientRegroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:34.165428+00:00
-- url     : https://prove2.me/theorems/bb69f37e-4eb2-418e-b9cc-023572a023fd
-- title:
--   Tsum Lattice Pair Unit Quotient Regroup
-- statement:
--   Definitions and structural lemmas for Tsum Lattice Pair Unit Quotient Regroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TsumLatticePairUnitQuotientRegroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
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
namespace GlobalTheory.HeckeTwo.Regroup
variable {F : Type} [Field F] [NumberField F]
variable (𝔞 𝔟 : Frac F)
def leftPt (c : Quotient (unitRel (latM 𝔞))) : LatPair 𝔞 𝔟 :=
  ⟨(c.out.1, 0), c.out.2.1, ((𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F).zero_mem, fun h => c.out.2.2 (congrArg Prod.fst h)⟩
def rightPt (c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) (a : {a : F // a ∈ latM 𝔞}) : LatPair 𝔞 𝔟 :=
  ⟨(a.1, c.out.1), a.2, c.out.2.1, fun h => c.out.2.2 (congrArg Prod.snd h)⟩
def regroupMap : Quotient (unitRel (latM 𝔞)) ⊕
    (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)), {a : F // a ∈ latM 𝔞}) → Quotient (latRel 𝔞 𝔟)
  | Sum.inl c => Quotient.mk _ (leftPt 𝔞 𝔟 c)
  | Sum.inr s => Quotient.mk _ (rightPt 𝔞 𝔟 s.1 s.2)
end GlobalTheory.HeckeTwo.Regroup


