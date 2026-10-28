-- Prove2me | Definitions.Def_OAISPf001
-- name    : OAISPf001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T10:37:27.856535+00:00
-- url     : https://prove2.me/theorems/7a3ce15c-c977-4d5f-b9fb-cf4649c390c0
-- title:
--   Definitions bundle OAISPf001 of the split of OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 65 declarations of OpenAI's Lean: 52 definitions, 2 instances and 11 theorems. The definitions and types are `OAI.PlanarFPP.ForcesBits`, `OAI.PlanarFPP.UpwardFamily`, `OAI.PlanarFPP.coarseColumnIndices`, `OAI.PlanarFPP.coarsePairIndices`, `OAI.PlanarFPP.coarseRegionFactor`, `OAI.PlanarFPP.compositionCandidates`, `OAI.PlanarFPP.compositionCover`, `OAI.PlanarFPP.contactSide`, `OAI.PlanarFPP.contactSign`, `OAI.PlanarFPP.coordinateSupport`, `OAI.PlanarFPP.direction`, `OAI.PlanarFPP.disjointOccurrenceFamily`, `OAI.PlanarFPP.endpointColumn`, `OAI.PlanarFPP.endpointErrorTail`, `OAI.PlanarFPP.endpointErrorTerm`, `OAI.PlanarFPP.endpointExtensionError`, `OAI.PlanarFPP.entranceColumn`, `OAI.PlanarFPP.exitColumn`, `OAI.PlanarFPP.exponentialLikelihood`, `OAI.PlanarFPP.extremeSlope`, `OAI.PlanarFPP.fairFamilyMass`, `OAI.PlanarFPP.finiteExponentialLikelihood`, `OAI.PlanarFPP.firstDyadicExponent`, `OAI.PlanarFPP.gridFailureSeries`, `OAI.PlanarFPP.gridFailureTail`, `OAI.PlanarFPP.gridIndexConstant`, `OAI.PlanarFPP.gridIndexRange`, `OAI.PlanarFPP.gridIntervalLower`, `OAI.PlanarFPP.gridIntervalUpper`, `OAI.PlanarFPP.gridMesh`, `OAI.PlanarFPP.gridMeshExponent`, `OAI.PlanarFPP.gridTestIndices`, `OAI.PlanarFPP.gridVerticalExponent`, `OAI.PlanarFPP.gridWidth`, `OAI.PlanarFPP.increaseFirst`, `OAI.PlanarFPP.iteratedDisjointOccurrence`, `OAI.PlanarFPP.leftSlope`, `OAI.PlanarFPP.meshFloor`, `OAI.PlanarFPP.rCoord`, `OAI.PlanarFPP.rightSlope` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `FirstPassage_BKFamilies`, `FirstPassage_BKForcing`, `FirstPassage_BKQuantization`, `FirstPassage_BKRepeated`, `FirstPassage_CharacteristicLengths`, `FirstPassage_ConnectorProbability`, `FirstPassage_CrossingTrialGeometry`, `FirstPassage_EndpointBounds`, `FirstPassage_EndpointCoarseGeometry`, `FirstPassage_EndpointEvents`, `FirstPassage_EndpointMesh`, `FirstPassage_EndpointTail`, `FirstPassage_ExponentialTilt`, `FirstPassage_ExtremeSlopes`, `FirstPassage_FiniteTiltLaw`, `FirstPassage_GridConnectionGeometry`, `FirstPassage_GridCounting`, `FirstPassage_GridMeshes`, `FirstPassage_GridProbability`, `FirstPassage_GridTail`, `FirstPassage_PlaneGeometry`, `FirstPassage_ProbabilityFoundations`, `FirstPassage_SupportContactEstimate`, `FirstPassage_Supports`, `FirstPassage_WitnessDecomposition`, `FirstPassage_WitnessEntropy`, `FirstPassage_WitnessSelection`.
--
--   **Imports.** It imports the published bundle `Def_PlanarFirstPassage`.
--
--   **Imported by** (directly, in this split): the bundle `OAISPf002`.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFirstPassage

section
-- module Solutions.OAIS_PlanarFPP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

def UpwardFamily (s : Finset α) (A : Finset (Finset α)) : Prop :=
  (∀ x ∈ A, x ⊆ s) ∧ ∀ x ∈ A, ∀ y, x ⊆ y → y ⊆ s → y ∈ A

noncomputable def disjointOccurrenceFamily (s : Finset α) (A B : Finset (Finset α)) : Finset (Finset α) :=
  by
    classical
    exact s.powerset.filter (fun x => ∃ a ∈ A, ∃ b ∈ B, a ⊆ x ∧ b ⊆ x ∧ Disjoint a b)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKRepeated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

noncomputable def fairFamilyMass (s : Finset α) (A : Finset (Finset α)) : ℝ :=
  A.card / (2:ℝ)^s.card

noncomputable def iteratedDisjointOccurrence (s : Finset α) : List (Finset (Finset α)) → Finset (Finset α)
  | [] => s.powerset
  | A :: As => disjointOccurrenceFamily s A (iteratedDisjointOccurrence s As)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

def ForcesBits (s : Finset α) (A : Finset (Finset α)) (x c : Finset α) : Prop :=
  ∀ y ⊆ s, (∀ e ∈ c, e ∈ y ↔ e ∈ x) → y ∈ A

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ProbabilityFoundations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Filter

noncomputable instance rateOneProbability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKQuantization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter
open scoped Topology

noncomputable def roundedSurvival (t : ℕ) (r : ℝ) : ℝ :=
  (⌊(2:ℝ)^t * Real.exp (-r)⌋₊ : ℝ)/(2:ℝ)^t

noncomputable def roundedEdgeCost (t : ℕ) (r : ℝ) : ℝ :=
  -Real.log (roundedSurvival t r)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ExponentialTilt
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Real Set MeasureTheory

noncomputable def exponentialLikelihood (ρ x : ℝ) : ℝ :=
  ρ * exp (-(ρ - 1) * x)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_FiniteTiltLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

noncomputable def finiteExponentialLikelihood (ρ : ℝ) (x : ι → ℝ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (exponentialLikelihood ρ (x i))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CrossingTrialGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

noncomputable def trialSpacing (R s : ℝ) : ℝ := (R+1)*(⌈s⌉₊ : ℝ)

noncomputable def trialWindow (M : ℕ) (R s : ℝ) : ℝ := 100*M*trialSpacing R s

noncomputable def trialOffset (M : ℕ) (R s : ℝ) (j : Fin M) : ℝ :=
  (2*((j.val : ℝ)+1)-(M : ℝ)-1)*3*trialSpacing R s

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Supports
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def coordinateSupport (x r : E →ₗ[ℝ] ℝ) (m a : ℝ) : E →ₗ[ℝ] ℝ :=
  m • x + a • r

@[simp] theorem coordinateSupport_apply (x r : E →ₗ[ℝ] ℝ) (m a : ℝ) (z : E) :
    coordinateSupport x r m a z = m * x z + a * r z := rfl

end
end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ExtremeSlopes
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

noncomputable def leftSlope (φ : ℝ → ℝ) : ℝ := derivWithin φ (Iio 0) 0
noncomputable def rightSlope (φ : ℝ → ℝ) : ℝ := derivWithin φ (Ioi 0) 0

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PlaneGeometry
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

noncomputable def direction (b : ℝ) : Plane := WithLp.toLp 2 ![1, b]
noncomputable def transverseUnit : Plane := WithLp.toLp 2 ![0, 1]
noncomputable def xCoord : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
noncomputable def rCoord (b : ℝ) : Plane →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 - b • xCoord

@[simp] theorem xCoord_apply (z : Plane) : xCoord z = z 0 := rfl
@[simp] theorem rCoord_apply (b : ℝ) (z : Plane) : rCoord b z = z 1 - b * z 0 := rfl
@[simp] theorem xCoord_direction (b : ℝ) : xCoord (direction b) = 1 := rfl
@[simp] theorem rCoord_direction (b : ℝ) : rCoord b (direction b) = 0 := by
  simp [rCoord_apply, direction]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SupportContactEstimate
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter
open scoped Topology

noncomputable def extremeSlope (μ : Plane → ℝ) (b : ℝ) (plus : Bool) : ℝ :=
  if plus then rightSlope (fun t => μ (direction b+t • transverseUnit))
  else leftSlope (fun t => μ (direction b+t • transverseUnit))

def contactSide (plus : Bool) : Set ℝ := if plus then Ioi 0 else Iio 0

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ConnectorProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

def contactSign (plus : Bool) : ℝ := if plus then 1 else -1

@[simp] theorem abs_contactSign (plus : Bool) : |contactSign plus|=1 := by
  cases plus <;> norm_num [contactSign]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CharacteristicLengths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

noncomputable def firstDyadicExponent (p : ℕ → ℝ) (q : ℝ) : ℕ :=
  by
    classical
    exact if h : ∃ j, p j ≤ q then Nat.find h else 0

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridMeshes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter Set MeasureTheory
open scoped Topology

def gridMeshExponent (m j : ℕ) : ℕ := m-(4*j+1)
noncomputable def gridMesh (m j : ℕ) : ℤ := (2 : ℤ)^gridMeshExponent m j
noncomputable def gridWidth (k j : ℕ) : ℤ := (2 : ℤ)^(k-j)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

noncomputable def meshFloor (x d : ℤ) : ℤ := x / d * d

noncomputable def endpointColumn (x : ℤ) (m j : ℕ) : ℤ := meshFloor x (gridMesh m j)

noncomputable def entranceColumn (x : ℤ) (m J : ℕ) : ℤ :=
  endpointColumn x m J-gridMesh m J
noncomputable def exitColumn (x : ℤ) (m J : ℕ) : ℤ := -entranceColumn (-x) m J

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter Finset
open scoped Topology

noncomputable def endpointErrorTerm (j : ℕ) : ℝ := (j : ℝ)^2*(1/2 : ℝ)^j
noncomputable def endpointErrorTail (J : ℕ) : ℝ := ∑' n : ℕ,endpointErrorTerm (n+J)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

noncomputable def endpointExtensionError (K : ℝ) (k J : ℕ) : ℝ :=
  16*(K+200)*(2 : ℝ)^k*endpointErrorTail J

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset Set

noncomputable def gridIndexRange (x : ℝ) : Finset ℤ :=
  Finset.Icc (-(⌈x⌉₊ : ℤ)) ⌈x⌉₊

noncomputable def gridTestIndices (A R L s l w : ℝ) : Finset (ℤ × ℤ) :=
  gridIndexRange ((A+4)*L/l) ×ˢ gridIndexRange (R*s/w+1)

noncomputable def gridIndexConstant (A R : ℝ) : ℝ :=
  2*(2*(A+4)+3)*(2*R+5)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridConnectionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

noncomputable def gridIntervalLower (h w : ℤ) : ℝ := (h : ℝ)*w-2
noncomputable def gridIntervalUpper (j : ℕ) (h w : ℤ) : ℝ :=
  (h : ℝ)*w+(30*(j : ℝ)^2+9)*w+2

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def gridVerticalExponent : ℝ := 50*(1-Real.log 2)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter Finset Set
open scoped Topology

noncomputable def gridFailureSeries (q : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ)^(5*j)*(Real.exp (-q*(j : ℝ)^2)+2*Real.exp (-gridVerticalExponent*(j : ℝ)^2))

noncomputable def gridFailureTail (C q : ℝ) (J : ℕ) : ℝ :=
  C*(∑' n : ℕ,gridFailureSeries q (n+J))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointCoarseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

noncomputable def coarseColumnIndices (A : ℝ) (J : ℕ) : Finset ℤ :=
  gridIndexRange ((A+2)*(2 : ℝ)^(4*J+1))

noncomputable def coarseRegionFactor (A : ℝ) (J : ℕ) : ℝ := (2*A+8)*(2 : ℝ)^(4*J+1)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

noncomputable def coarsePairIndices (A : ℝ) (J : ℕ) : Finset (ℤ×ℤ) :=
  ((coarseColumnIndices A J) ×ˢ (coarseColumnIndices A J)).filter (fun ij => ij.1 < ij.2)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_WitnessDecomposition
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

variable {α : Type*}

noncomputable def total (d : α → ℝ) (xs : List α) : ℝ := (xs.map d).sum
@[simp] theorem total_nil (d : α → ℝ) : total d [] = 0 := rfl
@[simp] theorem total_cons (d : α → ℝ) (x : α) (xs : List α) :
    total d (x :: xs) = d x + total d xs := by simp [total]
@[simp] theorem total_append (d : α → ℝ) (xs ys : List α) :
    total d (xs ++ ys) = total d xs + total d ys := by simp [total]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_WitnessSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

def takeWitnessPacks {α : Type*} : ℕ → List (List α) → List (List α)
  | _,[] => []
  | t,ws::packs => ws.take t :: takeWitnessPacks (t-ws.length) packs

def witnessLabels : List ℕ → List (ℤ×ℤ) → List (ℤ×ℤ)
  | [],_ => []
  | _,[] => []
  | n::ns,i::is => List.replicate n i ++ witnessLabels ns is

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_WitnessEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

noncomputable def spatialNeighbors (i : ℤ×ℤ) : Finset (ℤ×ℤ) :=
  ((Icc (-3 : ℤ) 3) ×ˢ (Icc (-3 : ℤ) 3)).image (fun d => i+d)

noncomputable def spatialItineraries (i : ℤ×ℤ) : ℕ → Finset (List (ℤ×ℤ))
  | 0 => {[]}
  | n+1 => (spatialNeighbors i).biUnion (fun j => (spatialItineraries j n).image (List.cons j))

def increaseFirst : List ℕ → List ℕ
  | [] => []
  | n::ns => (n+1)::ns

noncomputable def compositionCandidates : ℕ → ℕ → Finset (List ℕ)
  | 0,t => {[t]}
  | n+1,0 => {List.replicate (n+2) 0}
  | n+1,t+1 => (compositionCandidates n (t+1)).image (List.cons 0) ∪
      (compositionCandidates (n+1) t).image increaseFirst
termination_by n t => n+t

noncomputable def compositionCover (n t : ℕ) : Finset (List ℕ) :=
  (compositionCandidates n t).filter (fun ns => ns.length=n+1 ∧ ns.sum=t)

end PlanarFPP

end OAI
end


