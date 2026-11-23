-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:07.036045+00:00
-- url     : https://prove2.me/theorems/e2921ef1-f5b2-4596-8867-2b7e79d94ff6
-- title:
--   Loc Dens Vol B
-- statement:
--   Definitions and structural lemmas for Loc Dens Vol B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensVolB.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
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
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)
def gG (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a : ℕ) :
    Matrix (Fin a × Fin M × Fin d) (Fin a × Fin M × Fin d) F :=
  fun q q' => if q.1 = q'.1 then Algebra.trace F E (σ (b q.2.2) * J q.2.1 q'.2.1 * b q'.2.2) else 0
def cT {a M : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    Fin a × Fin M × Fin d → Fv F v :=
  fun q => crd b (Fv F v) (Y q.1 q.2.1) q.2.2
variable [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
end VolAAW
end PI.VolStabSW


