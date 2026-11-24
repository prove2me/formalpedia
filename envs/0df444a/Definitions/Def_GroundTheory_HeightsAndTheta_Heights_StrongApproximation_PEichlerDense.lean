-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
-- name    : GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:53.976857+00:00
-- url     : https://prove2.me/theorems/58bf9b2b-02b5-49ed-9118-dcf5040dc1d9
-- title:
--   PEichler Dense
-- statement:
--   Definitions and structural lemmas for PEichler Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
namespace EichlerDense
section Ring
variable {R : Type*} [CommRing R] {N : ℕ}
def param (σ : R →+* R) (J : Matrix (Fin N) (Fin N) R) (e f : Fin N → R) (κ : R)
    (p : (Fin N → R) × R) : Matrix (Fin N) (Fin N) R :=
  eich σ J e (perpProj σ J e f p.1)
    (p.2 - σ p.2 - κ * hf σ J (perpProj σ J e f p.1) (perpProj σ J e f p.1))
variable {σ : R →+* R} (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin N) (Fin N) R} (hJ : Jᵀ = J.map σ)
  {e f : Fin N → R} {κ : R} (hκ : κ + κ = 1) (hσκ : σ κ = κ)
include hσ hJ hκ hσκ
end Ring
section Top
variable {X : Type*} [TopologicalSpace X] {S : Type*} [CommRing S] [TopologicalSpace S]
  [IsTopologicalRing S] {N : ℕ} {σ : S →+* S}
end Top
section Field
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Field
end EichlerDense
end StrongApprox
end GroundTheory.Heights₂.Heights


