-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:11.116802+00:00
-- url     : https://prove2.me/theorems/a453e00e-006d-4dc5-9f5e-774533806777
-- title:
--   Loc Dens Vol A
-- statement:
--   Definitions and structural lemmas for Loc Dens Vol A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensVolA.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
namespace VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
def CondAA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) ↔ t ∈ v.adicCompletionIntegers F
section Vol
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]
end Vol
section Ann
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
end Ann
end VolAAW
end PI.VolStabSW


