-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:57.455048+00:00
-- url     : https://prove2.me/theorems/4fe2b04e-97ad-4eca-90f4-d886dc691a83
-- title:
--   Cube Complex Exact At Of Monomial Basis
-- statement:
--   Definitions and structural lemmas for Cube Complex Exact At Of Monomial Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexExactAtOfMonomialBasis.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
namespace GlobalTheory
variable {ι : Type} (R : Type) [CommRing R]
def Cube.above (w : Finset ι) : Cube.{0} ι R :=
  Cube.mk (fun s => ModuleCat.of R (PLift (w ⊆ s) →₀ R))
    (fun h => Finsupp.lmapDomain R R fun x => ⟨x.down.trans h⟩)
    (fun _ _ => Finsupp.mapDomain_id)
    (fun _ _ _ => Finsupp.mapDomain_comp.symm)
variable {R}
def monomialCoord {κ : Type} (T : κ → Finset ι) {s : Finset ι} {M : Type} [AddCommGroup M]
    [Module R M] (b : Module.Basis {a : κ // T a ⊆ s} R M) :
    M ≃ₗ[R] ⨁ a, (PLift (T a ⊆ s) →₀ R) :=
  b.repr ≪≫ₗ Finsupp.domLCongr (Equiv.sigmaPLiftEquivSubtype fun a => T a ⊆ s).symm ≪≫ₗ
    sigmaFinsuppLequivDFinsupp R
end GlobalTheory


