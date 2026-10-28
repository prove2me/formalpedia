-- Prove2me | Definitions.Def_OAIQ040C001
-- name    : OAIQ040C001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T00:40:48.439656+00:00
-- url     : https://prove2.me/theorems/79d2ea1c-5e9f-4eb0-a93a-14fd3f9cfb15
-- title:
--   Definitions bundle OAIQ040C001 of the split of OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 29 definitions, 5 instances and 7 theorems. The definitions and types are `OAI.Percolation.criticalApproach`, `OAI.Percolation.dyadicGhost`, `OAI.Percolation.earlyCollisionCost`, `OAI.Percolation.edgeExhaustion`, `OAI.Percolation.edgePattern`, `OAI.Percolation.fieldUnion`, `OAI.Percolation.finiteContactSeeds`, `OAI.Percolation.finiteOverwrite`, `OAI.Percolation.finiteProbability`, `OAI.Percolation.levelIndicator`, `OAI.Percolation.logarithmicChainLength`, `OAI.Percolation.maskUnion`, `OAI.Percolation.openSection`, `OAI.Percolation.orParameter`, `OAI.Percolation.pairParameter`, `OAI.Percolation.rawWeightBase`, `OAI.Percolation.restrictedBondExhaustion`, `OAI.Percolation.segmentAut`, `OAI.Percolation.segmentCenter`, `OAI.Percolation.segmentNegativeIndex`, `OAI.Percolation.segmentPositiveIndex`, `OAI.Percolation.segmentPositivePositions`, `OAI.Percolation.singleSprinkle`, `OAI.Percolation.sprinkleParameter`, `OAI.Percolation.suffixCollisionCost`, `OAI.Percolation.terminalGraph`, `OAI.Percolation.traceIntegratingFactor`, `OAI.Percolation.vanishingSprinkle`, `OAI.Percolation.vertexExhaustion`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/UnimodularPercolation, in whole or in part: `UnimodularPercolation_Clusters_Resampling`, `UnimodularPercolation_Criticality_FiniteChanges`, `UnimodularPercolation_Criticality_Operator`, `UnimodularPercolation_Criticality_Sharpness`, `UnimodularPercolation_Criticality_Susceptibility`, `UnimodularPercolation_Deformation_AveragedDecrease`, `UnimodularPercolation_Deformation_Corridors`, `UnimodularPercolation_Deformation_Derivatives`, `UnimodularPercolation_Encounter_TreeBranches`, `UnimodularPercolation_Escape_CollisionTails`, `UnimodularPercolation_Escape_PathSelection`, `UnimodularPercolation_Escape_PositiveEscapes`, `UnimodularPercolation_Exploration_FractionalMoments`, `UnimodularPercolation_Kernel_Bounds`, `UnimodularPercolation_Kernel_DistinctMoments`, `UnimodularPercolation_Kernel_ScaleBudget`, `UnimodularPercolation_Kernel_Spectral`, `UnimodularPercolation_Kernel_Sprinkling`, `UnimodularPercolation_Kernel_TraceBounds`, `UnimodularPercolation_ProductMeasure_Association`, `UnimodularPercolation_Splicing_ReferenceLaws`, `UnimodularPercolation_Splicing_Replay`.
--
--   **Imports.** It imports the published bundle `Def_CayleyPercolation`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ040C002`.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/UnimodularPercolation at commit adc7f12

import Mathlib
import Definitions.Def_CayleyPercolation

section
-- module Solutions.OAIQ040_CM.Compat
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
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel domination, monotone couplings and endpoint bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Coupling

instance labelLaw_isProbabilityMeasure :
    IsProbabilityMeasure (labelLaw : Measure (E → unitInterval)) := by
  dsimp [labelLaw]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end Coupling

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_ProductMeasure_Association
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section WitnessAssociation
attribute [local instance] Classical.propDecidable
open Filter Topology


 noncomputable def edgeExhaustion [Encodable E] (n : ℕ) : Finset E :=
  (Finset.range n).preimage Encodable.encode Encodable.encode_injective.injOn

end WitnessAssociation

section DisjointWitness
attribute [local instance] Classical.propDecidable


def openSection (A : Set (Set E)) (e : E) : Set (Set E) := {ω | insert e ω ∈ A}



noncomputable def finiteProbability (p : unitInterval) (s : Finset E) (A : Set (Set E)) : ℝ :=
  ∑ t ∈ s.powerset, if (t : Set E) ∈ A then
    (p : ℝ) ^ t.card * (1 - p : ℝ) ^ (s.card - t.card) else 0

@[simp] theorem finiteProbability_empty (p : unitInterval) (A : Set (Set E)) :
    finiteProbability p ∅ A = if ∅ ∈ A then 1 else 0 := by
  simp [finiteProbability]

end DisjointWitness

section ORLift
attribute [local instance] Classical.propDecidable

noncomputable def orParameter (q : unitInterval) (m : ℕ) : unitInterval :=
  ⟨1 - (1 - (q : ℝ)) ^ m,
    sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr q.2.2) (by linarith [q.2.1])),
    by linarith [pow_nonneg (sub_nonneg.mpr q.2.2) m]⟩

end ORLift

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Sprinkling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sprinkling estimates for finite and infinite graph operators. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SprinklingLaw
attribute [local instance] Classical.propDecidable

noncomputable def sprinkleParameter (p a : unitInterval) : unitInterval :=
  ⟨(p : ℝ) + (1-p)*a, by
    constructor
    · exact add_nonneg p.2.1 (mul_nonneg (sub_nonneg.mpr p.2.2) a.2.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr a.2.2)]⟩

 def pairParameter (p a : unitInterval) (b : Bool) : unitInterval := if b then p else a

def fieldUnion (f : Bool → Set E) : Set E := f true ∪ f false

end SprinklingLaw

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Sharpness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Russo formulae, exterior exposure and subcritical sharpness. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SharpnessBridge
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology

noncomputable def vertexExhaustion [Encodable V] (n : ℕ) : Finset V :=
  (Finset.range n).preimage Encodable.encode Encodable.encode_injective.injOn

end SharpnessBridge

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isoperimetric energy, symmetric walks and invariant operator traces. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section IsoperimetricEnergy
attribute [local instance] Classical.propDecidable

 
noncomputable def levelIndicator (a t : ℝ) : ℝ := if 0 ≤ t ∧ t < a then 1 else 0

end IsoperimetricEnergy

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_Replay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replay for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceMaskSupport
attribute [local instance] Classical.propDecidable Classical.decEq

 
def maskUnion (masks : List (ℕ × Set E)) : Set E :=
  {e | ∃ q ∈ masks, e ∈ q.2}

@[simp] theorem maskUnion_nil : maskUnion ([] : List (ℕ × Set E)) = ∅ := by
  ext e
  simp [maskUnion]

@[simp] theorem maskUnion_cons (i : ℕ) (M : Set E) (ms : List (ℕ × Set E)) :
    maskUnion ((i,M)::ms) = M ∪ maskUnion ms := by
  ext e
  simp [maskUnion,or_and_right,exists_or]


end TraceMaskSupport

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_ReferenceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference Laws for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SeededTraceLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty E]



def finiteContactSeeds (k : ℕ) (u : Fin k → unitInterval) (i : ℕ) : unitInterval :=
  if hi : 1 ≤ i ∧ i ≤ k then u ⟨i-1,by omega⟩ else 0

end SeededTraceLaw
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_ScaleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale Budget for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section LogarithmicChainLength

noncomputable def logarithmicChainLength (t : ℝ) (n : ℕ) : ℕ := ⌊Real.log n / t⌋₊

end LogarithmicChainLength
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_Resampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resampling for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section RestrictedConnectionLimit
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def restrictedBondExhaustion [Encodable E] (S : Set E) (K : Finset E)
    (n : ℕ) : Finset E := K ∪ (vertexExhaustion (V := E) n).filter (· ∈ S)

end RestrictedConnectionLimit
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_DistinctMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory Function
section PivotalSprinklingGain
attribute [local instance] Classical.propDecidable Classical.decEq

def singleSprinkle (Q : Finset E) (e : (Q : Set E)) : Set (Set E) :=
  {η | Subtype.val ⁻¹' η = {e}}

end PivotalSprinklingGain
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Susceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Susceptibility for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section VanishingSprinkles
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def vanishingSprinkle (n : ℕ) : unitInterval :=
  ⟨1/((n:ℝ)+1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < (n:ℝ)+1)).mpr
      linarith [show (0:ℝ) ≤ (n:ℝ) by positivity]
  ⟩

end VanishingSprinkles
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_FractionalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section DyadicGhostParameters
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def dyadicGhost (j : ℕ) : unitInterval :=
  ⟨(1/2:ℝ)^j,⟨pow_nonneg (by norm_num) _,pow_le_one₀ (by norm_num) (by norm_num)⟩⟩

end DyadicGhostParameters
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_TraceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
section IntegratingFactor

noncomputable def traceIntegratingFactor (q C A t : ℝ) : ℝ :=
  Real.exp (C/(1-A)*(q-t)^(1-A))

end IntegratingFactor
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_Corridors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corridors for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExactCorridorPattern
attribute [local instance] Classical.propDecidable Classical.decEq

def edgePattern (A B : Finset E) : Set (Set E) :=
  {ω | (A : Set E) ⊆ ω ∧ Disjoint (B : Set E) ω}

end ExactCorridorPattern
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_Derivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformRawWeight
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def rawWeightBase (r q : ℝ) (d : ℕ) : ℝ := r⁻¹ * (q⁻¹)^d

end UniformRawWeight
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_AveragedDecrease
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaged Decrease for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionKernels
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

def segmentAut (a : V ≃ V) : (I → V) ≃ (I → V) where
  toFun s := a ∘ s
  invFun s := a.symm ∘ s
  left_inv s := by funext i; exact a.symm_apply_apply (s i)
  right_inv s := by funext i; exact a.apply_symm_apply (s i)

end AnchoredPositionKernels
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_CollisionTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collision Tails for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IntrinsicVisibleBlocks
attribute [local instance] Classical.propDecidable Classical.decEq

def segmentCenter (J : ℕ) : Fin (J+J+1) := ⟨J,by omega⟩

def segmentPositivePositions (J : ℕ) (s : Fin (J+J+1) → V) : Fin (J+1) → V :=
  fun i => s ⟨J+i.val,by omega⟩

end IntrinsicVisibleBlocks
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_PositiveEscapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Escapes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
section QuantitativeEarlyCutoff

 

noncomputable def earlyCollisionCost (ρ : ℝ) (J : ℕ) : ℝ :=
  2*((J:ℝ)+1)*ρ^J/(1-ρ) + 2*ρ^J/(1-ρ)^2

end QuantitativeEarlyCutoff
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CombinedRawAvoidance
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]



noncomputable def suffixCollisionCost (ρ c : ℝ) (J : ℕ) : ℝ :=
  ((J:ℝ)+1)^2*Real.sqrt c + ((J:ℝ)+1)*Real.sqrt c/(1-ρ)



end CombinedRawAvoidance
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_PathSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection of geometrically separated paths from labelled escape events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EscapeGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

def segmentPositiveIndex (J : ℕ) : Fin (J+1) → Fin (J+J+1) :=
  fun i => ⟨J+i.val,by omega⟩
def segmentNegativeIndex (J : ℕ) : Fin (J+1) → Fin (J+J+1) :=
  fun i => ⟨i.val,by omega⟩

end EscapeGeometry
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Operator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical boundedness of the percolation operator under unimodularity and simple edge indexing. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory Filter
open scoped Topology

 
noncomputable def criticalApproach (q : unitInterval) (n : ℕ) : unitInterval :=
  ⟨(q:ℝ)-(q:ℝ)/2*Real.exp (-(n:ℝ)),by
    have he : Real.exp (-(n:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
    have hq := q.2
    have hp := Real.exp_pos (-(n:ℝ))
    constructor <;> nlinarith only [he,hq.1,hq.2,hp]⟩

universe u v

end Percolation





end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_FiniteChanges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite changes of bond configurations and their positive probabilities. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def finiteOverwrite (F P : Finset E) (ω : Set E) : Set E :=
  (ω ∩ (F:Set E)ᶜ) ∪ (P:Set E)

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_TreeBranches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tree branches, cluster retractions and terminal connecting trees. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open SimpleGraph
universe u
variable {V : Type u}
attribute [local instance] Classical.propDecidable Classical.decEq

def terminalGraph (H : SimpleGraph V) (A : Finset V) (v w : Fin 3 → V) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ ((a ∈ A ∧ b ∈ A) ∨
    ∃ i, (a = v i ∧ b = w i) ∨ (a = w i ∧ b = v i))
  symm := ⟨by
    intro a b h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with h | ⟨i,h|h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨i,Or.inr h.symm⟩
    · exact Or.inr ⟨i,Or.inl h.symm⟩⟩
  loopless := ⟨fun a h => H.loopless.irrefl a h.1⟩

end Percolation

end OAI
end


