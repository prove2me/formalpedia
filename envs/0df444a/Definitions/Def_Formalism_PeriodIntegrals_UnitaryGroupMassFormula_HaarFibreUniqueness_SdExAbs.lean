-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:07.728163+00:00
-- url     : https://prove2.me/theorems/1ef728c7-6d1e-4899-aefc-6afc34115683
-- title:
--   Sd Ex Abs
-- statement:
--   Definitions and structural lemmas for Sd Ex Abs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExAbs.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SmulMemHermR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.OmFibreUniq.W.SdAbs
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain
open PI.VolStabSW.SdUniqW PI.OmFibreUniq.W.SdCore PI.OmFibreUniq.W.SdChar
open scoped ENNReal
section Abs
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (B : V → V → Fv F v)
theorem B_zero_left (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) (y : V) : B 0 y = 0 := by
  have := hBs 0 0 y
  rwa [zero_smul, zero_mul] at this
def M0 (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) {ι : Type} (β' : ι → V) : AddSubgroup V where
  carrier := {x | ∀ j, B x (β' j) ∈ v.adicCompletionIntegers F}
  add_mem' := fun {a b} ha hb j => by
    simp only [Set.mem_setOf_eq] at *
    rw [hBa]
    exact add_mem (ha j) (hb j)
  zero_mem' := fun j => by
    show B 0 (β' j) ∈ _
    rw [B_zero_left v B hBs]
    exact zero_mem _
  neg_mem' := fun {a} ha j => by
    simp only [Set.mem_setOf_eq] at *
    rw [← neg_one_smul (Fv F v) a, hBs]
    exact mul_mem (neg_mem (one_mem _)) (ha j)
end Abs
end PI.OmFibreUniq.W.SdAbs


