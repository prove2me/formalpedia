-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivLatticeClassesFibreSummand
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivLatticeClassesFibreSummand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:19.062465+00:00
-- url     : https://prove2.me/theorems/aadb481e-fda5-42ee-91d0-d78ad5102f2d
-- title:
--   Exists Equiv Lattice Classes Fibre Summand
-- statement:
--   Definitions and structural lemmas for Exists Equiv Lattice Classes Fibre Summand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivLatticeClassesFibreSummand.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Theorems.Thm_GlobalTheory_SlopeTestRemainingChoices_EisFibre_rep_mem
import Theorems.Thm_GlobalTheory_SlopeTestRemainingChoices_EisFibre_rep_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
namespace GlobalTheory.LatFibre
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre
variable {F : Type} [Field F] [NumberField F]
def pairOf {𝔞 𝔟 : Frac F} (x : Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) : LatPair 𝔞 𝔟 :=
  ⟨((x.2 : F), rep x.1), x.2.2, rep_mem x.1, fun h => rep_ne_zero x.1 (congrArg Prod.snd h)⟩
theorem out_mk {𝔞 𝔟 : Frac F} (p : LatPair 𝔞 𝔟) :
    ∃ ε : (𝓞 F)ˣ, (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1 = ((ε : 𝓞 F) : F) * p.1.1 ∧
      (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2 = ((ε : 𝓞 F) : F) * p.1.2 :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (latRel 𝔞 𝔟) p)).symm
lemma ringOfIntegers_unit_coe_ne_zero (ε : (𝓞 F)ˣ) : ((ε : 𝓞 F) : F) ≠ 0 :=
  right_ne_zero_of_mul_eq_one (unit_inv_mul ε)
theorem out_mk_ne {𝔞 𝔟 : Frac F} (x : Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) :
    (Quotient.mk (latRel 𝔞 𝔟) (pairOf x)).out.1.2 ≠ 0 := by
  obtain ⟨ε, -, h2⟩ := out_mk (pairOf x)
  rw [h2]
  exact mul_ne_zero (ringOfIntegers_unit_coe_ne_zero ε) (rep_ne_zero x.1)
def fibreMap (𝔞 𝔟 : Frac F) (x : Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) :
    {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} :=
  ⟨Quotient.mk _ (pairOf x), out_mk_ne x⟩
end GlobalTheory.LatFibre


