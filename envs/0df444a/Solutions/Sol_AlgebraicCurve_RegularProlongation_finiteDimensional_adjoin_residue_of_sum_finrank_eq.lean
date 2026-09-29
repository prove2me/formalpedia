-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.finiteDimensional_adjoin_residue_of_sum_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8ef32e46-8fd7-54f1-9952-558655d67a7e

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_finiteDimensional_adjoin_residue_of_sum_finrank_eq

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (i : ι) :
    FiniteDimensional (IntermediateField.adjoin (IsLocalRing.ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) := by
  exact (RegularProlongation.sum_finrank_adjoin_residue_le A Fb R hR f hf htr).1 i

end S_AlgebraicCurve_RegularProlongation_finiteDimensional_adjoin_residue_of_sum_finrank_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_finiteDimensional_adjoin_residue_of_sum_finrank_eq (solution)
