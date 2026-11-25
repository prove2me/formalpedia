-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_WeylFormNondegenerateGlobal
-- name    : Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_WeylFormNondegenerateGlobal
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:14.770024+00:00
-- url     : https://prove2.me/theorems/93a56d60-0b72-4b62-b9e4-8b1e2ac6860f
-- title:
--   Weyl Form Nondegenerate Global
-- statement:
--   Definitions and structural lemmas for Weyl Form Nondegenerate Global, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/WeylFormNondegenerateGlobal.lean

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_DualWeylIn
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_FinalW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingDividedAdjoint
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingRowAction
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingHighestWeightProof
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_LowerTriangularOverField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST
section bil
variable {σ R : Type} [CommRing R]
lemma tsc_add_left (hB : FockRBilin) (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := (hB σ R f f' g 0).1
lemma tsc_smul_left (hB : FockRBilin) (a : R) (f g : MvPolynomial σ R) :
    fockR (a • f) g = a * fockR f g := (hB σ R f 0 g a).2.1
lemma tsc_symm (hB : FockRBilin) (f g : MvPolynomial σ R) : fockR f g = fockR g f := (hB σ R f 0 g 0).2.2
lemma tsc_add_right (hB : FockRBilin) (f g g' : MvPolynomial σ R) :
    fockR f (g + g') = fockR f g + fockR f g' := by
  rw [tsc_symm hB f, tsc_add_left hB, tsc_symm hB g, tsc_symm hB g']
lemma tsc_smul_right (hB : FockRBilin) (a : R) (f g : MvPolynomial σ R) :
    fockR f (a • g) = a * fockR f g := by
  rw [tsc_symm hB f, tsc_smul_left hB, tsc_symm hB g]
end bil
def tscForm (hB : FockRBilin) {K σ : Type} [Field K] (c : K) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K →ₗ[K] K :=
  LinearMap.mk₂ K (fun P Q => c⁻¹ * fockR P Q)
    (fun P P' Q => by rw [tsc_add_left hB, mul_add])
    (fun a P Q => by rw [tsc_smul_left hB, smul_eq_mul, mul_left_comm])
    (fun P Q Q' => by rw [tsc_add_right hB, mul_add])
    (fun a P Q => by rw [tsc_smul_right hB, smul_eq_mul, mul_left_comm])
end Formalism.L2.G.Model.TS


