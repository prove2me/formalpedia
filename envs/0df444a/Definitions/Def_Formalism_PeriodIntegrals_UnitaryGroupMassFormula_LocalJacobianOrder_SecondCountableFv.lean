-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_SecondCountableFv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_SecondCountableFv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:41.889377+00:00
-- url     : https://prove2.me/theorems/cddcdfb0-7490-42dc-b6a7-be88a8f5dd27
-- title:
--   Second Countable Fv
-- statement:
--   Definitions and structural lemmas for Second Countable Fv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/SecondCountableFv.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LocJacOrd.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical
def BoxScale : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (ι : Type) [Fintype ι], Module.finrank F E = 2 →
    ∀ (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure] (x : ι → Fv F v), (∀ i, x i ≠ 0) →
      (μ (Set.univ.pi fun i => {c | sc (E := E) v (x i) * c ∈ OEv (E := E) v})).toReal =
        (μ (Obox (E := E) v ι)).toReal * ∏ i, (absV v (x i) ^ 2)⁻¹
def AbsMul : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
    (∀ x y : Fv F v, absV v (x * y) = absV v x * absV v y) ∧ absV v 1 = 1 ∧
      ∀ x : Fv F v, x ≠ 0 → 0 < absV v x
section Top
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
end Top
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
end
end PI.LocJacOrd.W


