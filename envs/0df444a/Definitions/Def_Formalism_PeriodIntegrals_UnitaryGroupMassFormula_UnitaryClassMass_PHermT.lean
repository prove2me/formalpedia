-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermT
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermT
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T16:19:36.96616+00:00
-- url     : https://prove2.me/theorems/693bb279-0e3c-4b5e-ae78-c5ee9d15f424
-- title:
--   PHerm T
-- statement:
--   Definitions and structural lemmas for PHerm T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PHermT.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermCL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
def LocInt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) (z : F) (c : 𝓞 F)
    (u : t.adicCompletion F), u ∈ t.adicCompletionIntegers F →
    algebraMap F (t.adicCompletion F) z = algebraMap F (t.adicCompletion F) (c : F) * u →
    ∃ d ∈ t.asIdeal.primeCompl, ∃ a : 𝓞 F, z * (d : F) = (c : F) * (a : F)
def tcoord {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type} (B : Module.Basis ι F E)
    (k : ι) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →ₗ[F] R :=
  (TensorProduct.lid F R).toLinearMap ∘ₗ TensorProduct.map (B.coord k) LinearMap.id
end PI.UnitaryGroupMassFormula.UJClassMass
end


