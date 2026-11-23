-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_AdmCpt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_AdmCpt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:12:50.163814+00:00
-- url     : https://prove2.me/theorems/84d0966e-8e16-4a09-9568-00a0dca88aa5
-- title:
--   Adm Cpt
-- statement:
--   Definitions and structural lemmas for Adm Cpt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/AdmCpt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuNeSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW.AdmissibleCompactSupport
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open PI.VolStabW PI.VolStabW.PositiveNearLattice Set Filter
open scoped TensorProduct RestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)
variable {a M : ℕ} (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)
end PI.VolStabW.AdmissibleCompactSupport
namespace PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.VolStabW.AdmissibleCompactSupport
end PI.VolStabW


