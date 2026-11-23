-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:35:02.993683+00:00
-- url     : https://prove2.me/theorems/0d257327-61a1-4218-9d2a-25e79656b066
-- title:
--   Loc Dens HL
-- statement:
--   Definitions and structural lemmas for Loc Dens HL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHL.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
namespace LatFactsW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
instance contSMul_herm (σ : E →ₐ[F] E) (a : ℕ) : ContinuousSMul (Fv F v) (HermR (Fv F v) σ a) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  show Continuous fun p : Fv F v × HermR (Fv F v) σ a =>
    p.1 • (p.2 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
  exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
end LatFactsW
open scoped TensorProduct
open NumberField IsDedekindDomain Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW LatFactsW
end PI.VolStabW


