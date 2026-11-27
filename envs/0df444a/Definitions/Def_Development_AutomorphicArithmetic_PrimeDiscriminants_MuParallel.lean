-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_MuParallel
-- name    : Development_AutomorphicArithmetic_PrimeDiscriminants_MuParallel
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T05:28:08.126945+00:00
-- url     : https://prove2.me/theorems/ffcdc0ce-05a3-4681-8009-fc65b75bbe92
-- title:
--   Mu Parallel
-- statement:
--   Definitions and structural lemmas for Mu Parallel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/MuParallel.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_mem_Psi_iff
import Theorems.Thm_Formalism_HC_HostAx_galE_mem_Psi_iff
import Theorems.Thm_Formalism_HC_HostRaw_sqd_mem_K

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace UpperTheory.Host
open Formalism.BasicNotions NumberField
variable {R : Ranks} (H : Host R)
def psiEquiv : R.Psi ≃ (H.E ≃ₐ[H.K] H.E) where
  toFun g :=
    { (H.sigmaOf (g : R.GG) : H.E ≃+* H.E) with
      commutes' := fun x => by
        have h1 : H.sigmaOf (g : R.GG) H.sqd = H.sqd :=
          (H.galE_mem_Psi_iff _).1 (by rw [show H.galE (H.sigmaOf (g : R.GG)) = g from H.gal.apply_symm_apply _]; exact g.2)
        have h2 : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers (H.sigmaOf (g : R.GG))) := by
          refine IntermediateField.adjoin_simple_le_iff.2 ?_
          rw [IntermediateField.mem_fixedField_iff]
          intro f hf
          exact (Subgroup.zpowers_le.2 (show H.sigmaOf (g : R.GG) ∈ MulAction.stabilizer _ H.sqd from h1)) hf
        exact (IntermediateField.mem_fixedField_iff _ _).1 (h2 x.2) _ (Subgroup.mem_zpowers _) }
  invFun σ := ⟨H.gal (σ.restrictScalars ℚ), (H.galE_mem_Psi_iff _).2 (σ.commutes ⟨H.sqd, H.sqd_mem_K⟩)⟩
  left_inv g := Subtype.ext (H.gal.apply_symm_apply (g : R.GG))
  right_inv σ := AlgEquiv.ext fun x => by
    show H.gal.symm (H.gal (σ.restrictScalars ℚ)) x = σ x
    rw [MulEquiv.symm_apply_apply]
    rfl
end UpperTheory.Host
end


