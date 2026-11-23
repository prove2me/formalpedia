-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerSubgroupIntersection_IntInter
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerSubgroupIntersection_IntInter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:44.078818+00:00
-- url     : https://prove2.me/theorems/e264b695-7969-4b0e-9acd-eeae5b0c4d6f
-- title:
--   Int Inter
-- statement:
--   Definitions and structural lemmas for Int Inter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerSubgroupIntersection/IntInter.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GaugeGap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.GaugeCharW
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
def InfFun : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∃ L : Ainf F →+ ℝ, Continuous L ∧
    (∀ a : 𝓞 F, ∃ n : ℤ, L (algebraMap F (Ainf F) (a : F)) = n) ∧ ∃ t, L t = 1 / 2
def IntInter : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a : F),
    (∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) a v ∈ v.adicCompletionIntegers F) →
    ∃ b : 𝓞 F, (b : F) = a
def OpenInt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    IsOpen {y : Af F | ∀ v : HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F}
def ExtChar : Prop :=
  ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (K U : AddSubgroup G), IsOpen (U : Set G) →
    ∀ g : G →+ AddCircle (1 : ℝ), Continuous g → (∀ x ∈ K, x ∈ U → g x = 0) →
    ∃ h : G →+ AddCircle (1 : ℝ), Continuous h ∧ (∀ x ∈ K, h x = 0) ∧ ∀ x ∈ U, h x = g x
end PI.GaugeCharW


