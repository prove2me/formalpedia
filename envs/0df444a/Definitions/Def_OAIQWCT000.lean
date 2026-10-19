-- Prove2me | Definitions.Def_OAIQWCT000
-- name    : OAIQWCT000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:04:41.115184+00:00
-- url     : https://prove2.me/theorems/76989e69-9843-4f39-8ca2-4d454b40e9af
-- title:
--   OpenAI continuum temperature split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of `OAI.ContinuumTemperature.main_theorem`: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Probability/ContinuumTransition` (OpenAI, *A continuum temperature singularity for a radial pair potential*, OpenAI Math Release, September 24, 2026, result family 228, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also contains the few lemmas those definitions use in their bodies (for example `freeSetoid` is a setoid whose transitivity is the lemma `freeConfig_close_trans`), and OpenAI's `@[simp]` lemmas about these definitions.
--
--   The definitions of the published statement (`Space`, `radialPotential`, `energy`, `Admissible`, `cube`, `boltzmann`, `partition`, `HasCanonicalFreeEnergy`, `MainStatement`) are not repeated: the bundle imports them from the published bundle `Def_ContinuumTransition`. It imports no other bundle.
--
--   Modules: `ActiveSupports.lean`, `AppendAttraction.lean`, `Assignments.lean`, `BadEndpoints.lean`, `BoxTiling.lean`, `CanonicalIntegral.lean`, `CanonicalLimit.lean`, `CellEnergy.lean`, `ConstructionBounds.lean`, `ConstructionCap.lean`, `ConstructionLimit.lean`, `ConstructionMasses.lean`, `ConstructionSequence.lean`, `ConstructionStage.lean`, `ConstructionStep.lean`, `ConvexSupport.lean`, `CubeBoundary.lean`, `CubeCoercivity.lean`, `DensityLimit.lean`, `FixedOccupation.lean`, `FreeFamily.lean`, `FreeGeometry.lean`, `FreeIdeal.lean`, `FreeUpper.lean`, `GeneralGrand.lean`, `GeneralLabels.lean`, `GenericGibbs.lean`, `GibbsQuadratic.lean`, `GrandDomination.lean`, `GrandFinite.lean`, `GrandInteraction.lean`, `GrandPartition.lean`, `GridBoundary.lean`, `InnerGrid.lean`, `KacBlocks.lean`, `KacGrid.lean`, `KacKernel.lean`, `KacRows.lean`, `LaplacePrinciple.lean`, `LatticeBounds.lean`, `LowerGibbs.lean`, `LowerKac.lean`, `MaskedReference.lean`, `ModifiedEnergy.lean`, `MomentEnergy.lean`, `OccupationEnergy.lean`, `PackingGeometry.lean`, `PackingLimit.lean`, `PackingUpper.lean`, `PairEnergy.lean`, `PairMoments.lean`, `PhysicalInsertion.lean`, `PhysicalPressure.lean`, `PressureGeometry.lean`, `ProfileTail.lean`, `QuadraticGrand.lean`, `QuadraticLaplace.lean`, `QuadraticTransform.lean`, `RadialKernel.lean`, `Regroup.lean`, `RootVolume.lean`, `ShellGeometry.lean`, `SpatialProducts.lean`, `TetraVolume.lean`, `Tetrahedron.lean`, `ThermodynamicExtension.lean`, `TrialConfigurations.lean`, `TriangleGeometry.lean`, `TriangleSeparation.lean`, `TripleState.lean`, `UpperLimit.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the solutions of this split. Seven of them, including the two classical results Rockafellar's theorem on limits of convex functions (`convex_pointwise_locally_uniform`) and the Laplace principle (`laplace_principle_eventual`), are published as statements, each with its own proof, and the main theorem is proved from them. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A continuum temperature singularity for a radial pair potential, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/ContinuumTransition at commit adc7f12

import Mathlib
import Definitions.Def_ContinuumTransition

section
-- module Solutions.OAIQW_ContinuumTemperature.PressureGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section

open scoped Topology BigOperators
open Set Filter

noncomputable section

namespace ContinuumTemperature

abbrev Parameter := ℝ × ℝ

def pressureDomain : Set Parameter := {x | 0 < x.1}

def Supports (P : Parameter → ℝ) (x v : Parameter) : Prop :=
  ∀ y ∈ pressureDomain, P x + v.1 * (y.1 - x.1) + v.2 * (y.2 - x.2) ≤ P y

def IsPartialConjugate (Q : Parameter → ℝ) (H : ℝ → ℝ → ℝ) : Prop :=
  ∀ β d : ℝ, 0 < β → 0 ≤ d →
    IsLUB (range (fun h : ℝ => h * d - Q (β, h))) (H β d)

def quadraticObjective (ξ v : Parameter) (β : ℝ) : ℝ :=
  ξ.1 * v.1 + ξ.2 * v.2 + β / 2 * v.2 ^ 2

def SlopeBall (g : Parameter) (γ : ℝ) : Set Parameter :=
  {v | (v.1 - g.1) ^ 2 + (v.2 - g.2) ^ 2 ≤ γ ^ 2}

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConvexSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology
open Filter Set
noncomputable section
namespace ContinuumTemperature

def pDot (v w : Parameter) : ℝ := v.1*w.1+v.2*w.2

def SupportOn (S : Set Parameter) (F : Parameter → ℝ) (x v : Parameter) : Prop :=
  ∀ y ∈ S, F x + pDot v (y-x) ≤ F y

def subgradients (S : Set Parameter) (F : Parameter → ℝ) (x : Parameter) : Set Parameter :=
  {v | SupportOn S F x v}

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.RadialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

noncomputable section
open scoped ContDiff

def shellDelta : ℝ := 1 / 1000

def coreProfile (t r : ℝ) : ℝ :=
  if r < Real.exp (-t) then t ^ 2 + (Real.exp (-t) / r) ^ 12
  else if r ≤ (1 + shellDelta) * Real.exp (-t) then 0
  else if r < 1 then t ^ 2 else 0

noncomputable def baseKernel (x : Space) : ℝ := Real.smoothTransition (2 - 2 * ‖x‖)

noncomputable def kernelProfile (r : ℝ) : ℝ :=
  Real.smoothTransition (2 - 2 * r) / (∫ x : Space, baseKernel x)

noncomputable def kernel (x : Space) : ℝ := kernelProfile ‖x‖

noncomputable def scaledKernelProfile (R r : ℝ) : ℝ := R⁻¹ ^ 3 * kernelProfile (r / R)

def kernelHeight : ℝ := 1 / (∫ x : Space, baseKernel x)

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ProfileTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

def attraction (t : ℝ) (σ R : ℕ → ℝ) (r : ℝ) : ℝ :=
  t * ∑' j, σ j * scaledKernelProfile (R j) r

def physicalProfile (t : ℝ) (σ R : ℕ → ℝ) (r : ℝ) : ℝ :=
  coreProfile t r - attraction t σ R r

def radialWeighted (R r : ℝ) : ℝ :=
  (Icc (0 : ℝ) R).indicator (fun s => s ^ 2 * scaledKernelProfile R s) r

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ShellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

open scoped InnerProductSpace

def shellGraph {ι : Type u_1} (v : ι → EuclideanSpace ℝ (Fin 3)) (r : ℝ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ r ≤ ‖v i - v j‖ ∧ ‖v i - v j‖ ≤ (1 + shellDelta) * r
  symm := ⟨by
    intro i j h
    simpa only [norm_sub_rev] using And.intro h.1.symm h.2⟩
  loopless := ⟨by intro i; simp⟩

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

def pairSum {ι : Type u_1} [Fintype ι] [LinearOrder ι] (f : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LatticeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

def cellIndex (x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℤ := fun k => ⌊4 * x k⌋

abbrev Lattice := Fin 3 → ℤ

def cellRadius (R : ℝ) : ℤ := ⌈4 * R + 1⌉

def nearCells (R : ℝ) (i : Lattice) : Finset Lattice :=
  Fintype.piFinset (fun k => Finset.Icc (i k - cellRadius R) (i k + cellRadius R))

def latticeEnvelope (R : ℝ) (i j : Lattice) : ℝ :=
  if j ∈ nearCells R i then R⁻¹ ^ 3 else 0

def mixedEnvelope (σ R : ℕ → ℝ) (i j : Lattice) : ℝ :=
  ∑' n, σ n * latticeEnvelope (R n) i j

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CubeCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

noncomputable def cubeCells (L : ℝ) : Finset Lattice :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc ⌊-2 * L⌋ ⌊2 * L⌋)

end

end ContinuumTemperature

end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CanonicalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

@[simp] theorem radialPotential_ne_bot (φ : ℝ → ℝ) (x : Space) :
    radialPotential φ x ≠ ⊥ := by
  unfold radialPotential
  split_ifs
  · exact top_ne_bot
  · exact EReal.coe_ne_bot _

def openConfigurations (L : ℝ) (N : ℕ) : Set (Fin N → Space) :=
  {x | (∀ i k, x i k ∈ Ioo (-L / 2) (L / 2)) ∧ Function.Injective x}

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def grandPartition (φ : ℝ → ℝ) (t β h L : ℝ) : ℝ :=
  ∑' N : ℕ, Real.exp (t * h * N) * partition φ β L N

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PairEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def realPairEnergy (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) : ℝ := by
  classical
  exact (1/2 : ℝ) * ∑ i, ∑ j, if i = j then 0 else φ ‖x i - x j‖

noncomputable def symmetricWeight (φ : ℝ → ℝ) (β : ℝ)
    {ι : Type u_1} [Fintype ι] (x : ι → Space) : ℝ :=
  if Function.Injective x then Real.exp (-β * realPairEnergy φ x) else 0

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Assignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

section Assignments
variable {X : Type u_1} [MeasurableSpace X] {ι : Type u_2} [Fintype ι] [DecidableEq ι]

def assignmentRegion (B : ι → Set X) (e : Equiv.Perm ι) : Set (ι → X) :=
  {x | ∀ i, x i ∈ B (e i)}

def binaryRegion (A B : Set X) (s : Finset ι) : Set (ι → X) :=
  {x | ∀ i, if i ∈ s then x i ∈ A else x i ∈ B}

end Assignments

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GeneralLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

section GeneralLabels
variable {ι : Type u_1} [Fintype ι]

noncomputable def generalPartition (φ : ℝ → ℝ) (β : ℝ) (A : Set Space)
    (ι : Type u_2) [Fintype ι] : ℝ :=
  (∫ x in {x : ι → Space | ∀ i, x i ∈ A}, symmetricWeight φ β x) /
    ((Fintype.card ι).factorial : ℝ)

end GeneralLabels

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TrialConfigurations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable section

noncomputable def gridPoint (q : ℝ) (i : Lattice) : Space :=
  WithLp.toLp 2 (fun k => q * (i k : ℝ))

def trialBall (q : ℝ) (i : Lattice) : Set Space := Metric.ball (gridPoint q i) (q / 8)

noncomputable def gridRadius (q : ℝ) : ℤ := ⌈q⁻¹ + 1⌉

noncomputable def gridNeighbors (q : ℝ) (i : Lattice) : Finset Lattice :=
  Fintype.piFinset (fun k => Finset.Icc (i k - gridRadius q) (i k + gridRadius q))

noncomputable def trialEnergyConstant (t q : ℝ) : ℝ :=
  (2 * (gridRadius q).toNat + 1 : ℝ)^3 *
    (t^2 + (Real.exp (-t) / (3*q/4))^12)

noncomputable def interiorGrid (q L : ℝ) : Finset Lattice :=
  Fintype.piFinset (fun _ : Fin 3 =>
    Finset.Icc (-(⌊L/(2*q)-1⌋₊ : ℤ)) (⌊L/(2*q)-1⌋₊ : ℤ))

def trialVolume (q : ℝ) : ℝ := (q/8)^3 * (Real.pi*4/3)

end

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.SpatialProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def setPartition (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (N : ℕ) : ℝ :=
  generalPartition φ β A (Fin N)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.BoxTiling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def tileCenter (ℓ L : ℝ) {k : ℕ} (i : Fin 3 → Fin k) : Space :=
  WithLp.toLp 2 (fun j => (ℓ+2)*((i j : ℝ)+1/2)-L/2)

noncomputable def tileBox (ℓ L : ℝ) {k : ℕ} (i : Fin 3 → Fin k) : Set Space :=
  (fun x => x + tileCenter ℓ L i) '' cube ℓ

noncomputable def tileCount (ℓ L : ℝ) : ℕ := ⌊L/(ℓ+2)⌋₊ ^ 3

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.DensityLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def densityFilter (d : ℝ) : Filter (ℝ × ℕ) :=
  Filter.comap (fun p : ℝ × ℕ => (p.1, (p.2 : ℝ)/p.1^3)) (atTop ×ˢ 𝓝 d)

instance densityFilter_countablyGenerated (d : ℝ) : (densityFilter d).IsCountablyGenerated :=
  inferInstanceAs (Filter.comap _ _).IsCountablyGenerated

def DensityBounded (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
    ∀ L : ℝ, R ≤ L → ∀ n : ℕ, (n : ℝ) ≤ D*L^3 → |a L n| ≤ M

def HasBoxInequality (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ ℓ L : ℝ, 0 < ℓ → 0 < L → ∀ r : Fin (tileCount ℓ L) → ℕ,
    a L (∑ i, r i) ≤ ℓ^3/L^3 * ∑ i, a ℓ (r i)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CanonicalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def finiteCanonical (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) : ℝ :=
  -Real.log (partition φ β L N)/L^3

@[simp] theorem finiteCanonical_zero (φ : ℝ → ℝ) (β L : ℝ) :
    finiteCanonical φ β L 0 = 0 := by simp [finiteCanonical, partition]

noncomputable def canonicalDensity (φ : ℝ → ℝ) (β d : ℝ) : ℝ :=
  liminf (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2) (densityFilter d)

noncomputable def canonicalFreeEnergy (φ : ℝ → ℝ) (β d : ℝ) : ℝ :=
  canonicalDensity φ β d / β

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LaplacePrinciple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def canonicalPressure (φ : ℝ → ℝ) (β μ : ℝ) : ℝ :=
  sSup ((fun d : ℝ => μ*d-canonicalDensity φ β d) '' Ici 0)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def physicalPressure (φ : ℝ → ℝ) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  canonicalPressure φ x.1 (t*x.2)/t

noncomputable def physicalCanonical (φ : ℝ → ℝ) (t β d : ℝ) : ℝ :=
  canonicalDensity φ β d/t

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GeneralGrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

abbrev ConfigFamily := (ι : Type) → [Fintype ι] → (ι → Space) → ℝ

def RelabelInvariant (F : ConfigFamily) : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → Space),
    F ι (x ∘ e) = F κ x

noncomputable def familyIntegral (F : ConfigFamily) (A : Set Space)
    (ι : Type) [Fintype ι] : ℝ :=
  ∫ x in {x : ι → Space | ∀ i, x i ∈ A}, F ι x

noncomputable def familyTerm (F : ConfigFamily) (A : Set Space) (n : ℕ) : ℝ :=
  familyIntegral F A (Fin n)/(n.factorial : ℝ)

noncomputable def grandIntegral (F : ConfigFamily) (A : Set Space) : ℝ :=
  ∑' n : ℕ, familyTerm F A n

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GenericGibbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def gibbsEnergy (V : Space → Space → ℝ) {ι : Type} [Fintype ι]
    (x : ι → Space) : ℝ :=
  (∑ i, ∑ j, if i = j then 0 else V (x i) (x j))/2

noncomputable def gibbsFamily (V : Space → Space → ℝ) (β h : ℝ) : ConfigFamily :=
  fun ι _ x => if Function.Injective x then Real.exp (h*Fintype.card ι-β*gibbsEnergy V x) else 0

noncomputable def occupation {ι : Type} [Fintype ι] (C : Set Space) (x : ι → Space) : ℝ :=
  Fintype.card {i : ι // x i ∈ C}

noncomputable def momentFamily (F : ConfigFamily) (C : Set Space) (c : ℝ) : ConfigFamily :=
  fun ι _ x => F ι x * Real.exp (c*(occupation C x)^2)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.MomentEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

def latticeCell (z : Lattice) : Set Space := {x | cellIndex x = z}

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def physicalCoupling (t : ℝ) (σ R : ℕ → ℝ) (z w : Lattice) : ℝ :=
  (t*kernelHeight)*mixedEnvelope σ R z w

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ModifiedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

def CellLowerBound (t : ℝ) (σ R : ℕ → ℝ) (V : Space → Space → ℝ) : Prop :=
  ∀ x y, (if cellIndex x = cellIndex y then coreProfile t ‖x-y‖ else 0)-
    physicalCoupling t σ R (cellIndex x) (cellIndex y) ≤ V x y

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.QuadraticGrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def quadraticGrandTerm (φ : ℝ → ℝ) (β μ a L : ℝ) (n : ℕ) : ℝ :=
  Real.exp (μ*n+a*(n : ℝ)^2/L^3)*partition φ β L n

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.QuadraticLaplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def quadraticPressure (φ : ℝ → ℝ) (β μ a : ℝ) : ℝ :=
  sSup ((fun d : ℝ => μ*d+a*d^2-canonicalDensity φ β d) '' Ici 0)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ThermodynamicExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

def twoBoxCounts (K k n₁ n₂ : ℕ) : Fin K → ℕ :=
  fun i => if (i : ℕ) < k then n₁ else n₂

noncomputable def mixCount (θ : ℝ) (n : ℕ) : ℕ := ⌊θ*(n : ℝ)^3⌋₊
def mixSide (n : ℕ) : ℝ := (n : ℝ)*((n : ℝ)+2)
noncomputable def mixTotal (θ d₁ d₂ : ℝ) (n : ℕ) : ℕ :=
  mixCount θ n * mixCount d₁ n + (n^3-mixCount θ n)*mixCount d₂ n

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.QuadraticTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def shiftedField (a : ℝ) (x : Parameter) (d : ℝ) : Parameter :=
  (x.1,x.2+x.1*a*d)

def quadraticCost (Q : Parameter → ℝ) (a : ℝ) (x : Parameter) (d : ℝ) : ℝ :=
  Q (shiftedField a x d)-x.1*a*d^2/2

def IsMeanField (Q : Parameter → ℝ) (a : ℝ) (P : Parameter → ℝ) : Prop :=
  ∀ x ∈ pressureDomain, IsLUB (range (quadraticCost Q a x)) (P x)

noncomputable def meanField (Q : Parameter → ℝ) (a : ℝ) (x : Parameter) : ℝ :=
  sSup (range (quadraticCost Q a x))

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ActiveSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter
noncomputable section
namespace ContinuumTemperature

def unlift (a : ℝ) (w : Parameter) : Parameter := (w.1-a*w.2^2/2,w.2)

def activeLifts (Q : Parameter → ℝ) (a : ℝ) (P : Parameter → ℝ)
    (x : Parameter) : Set Parameter := {w |
  quadraticCost Q a x w.2 = P x ∧
  SupportOn pressureDomain Q (shiftedField a x w.2) (unlift a w)}

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TriangleGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def triangleDet (w : Fin 3 → Parameter) : ℝ :=
  ((w 1).1-(w 0).1)*((w 2).2-(w 0).2)-((w 1).2-(w 0).2)*((w 2).1-(w 0).1)

def triangleWeight (w : Fin 3 → Parameter) (z : Parameter) (i : Fin 3) : ℝ :=
  let b := ((z.1-(w 0).1)*((w 2).2-(w 0).2)-(z.2-(w 0).2)*((w 2).1-(w 0).1))/triangleDet w
  let c := (((w 1).1-(w 0).1)*(z.2-(w 0).2)-((w 1).2-(w 0).2)*(z.1-(w 0).1))/triangleDet w
  if i = 0 then 1-b-c else if i = 1 then b else c

def triangleVertex (p : ℝ) (i : Fin 3) : Parameter := if i = 0 then (0,0) else if i = 1 then (3*p/4,p) else (12*p,4*p)
def triangleCenter (p : ℝ) : Parameter := (17*p/4,5*p/3)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature
open Classical

def IsPacking (L : ℝ) (n : ℕ) : Prop :=
  ∃ x : Fin n → Space, (∀ i, x i ∈ cube L) ∧
    ∀ i j, i ≠ j → 1 ≤ ‖x i-x j‖

noncomputable def packingNumber (L : ℝ) : ℕ :=
  Nat.findGreatest (IsPacking L) (cubeCells L).card

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped BigOperators
open Set
namespace ContinuumTemperature
open Classical

def FreeConfig {ι : Type u_1} (t : ℝ) (x : ι → Space) : Prop :=
  ∀ i j, i ≠ j → ‖x i-x j‖ < 1 →
    Real.exp (-t) ≤ ‖x i-x j‖ ∧ ‖x i-x j‖ ≤ (1+shellDelta)*Real.exp (-t)

theorem freeConfig_close_trans {ι : Type u_1} {t : ℝ} {x : ι → Space}
    (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (hx : FreeConfig t x)
    {i j k : ι} (hij : ‖x i-x j‖ < 1) (hjk : ‖x j-x k‖ < 1) :
    ‖x i-x k‖ < 1 := by
  by_cases he : i = j
  · simpa only [he] using hjk
  by_cases hf : j = k
  · simpa only [hf] using hij
  have hi := (hx i j he hij).2
  have hj := (hx j k hf hjk).2
  have hh := norm_sub_le_norm_sub_add_norm_sub (x i) (x j) (x k)
  linarith only [hi,hj,hh,ht]

noncomputable def freeSetoid {ι : Type u_1} {t : ℝ} {x : ι → Space}
    (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (hx : FreeConfig t x) : Setoid ι where
  r i j := ‖x i-x j‖ < 1
  iseqv := ⟨by intro i; simp,
    by intro i j h; rwa [norm_sub_rev],
    by intro i j k; exact freeConfig_close_trans ht hx⟩

noncomputable def freeCluster {ι : Type u_1} [Fintype ι] (x : ι → Space) (i : ι) : Finset ι :=
  Finset.univ.filter (fun j => ‖x i-x j‖ < 1)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.RootVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def rootNeighborhood {ι : Type} [Fintype ι] (a : ι → Space) (r : ℝ) : Set Space :=
  ⋃ i, Metric.closedBall (a i) r

noncomputable def rootCover {ι : Type} [Fintype ι] (s : Finset ι) (r : ℝ) : Set (ι → Space) :=
  {x | ∀ j : {j : ι // j ∉ s}, ∃ i : {i : ι // i ∈ s}, ‖x j-x i‖ ≤ r}

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FreeFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def freeFamily (t d : ℝ) : ConfigFamily :=
  fun ι _ x => if FreeConfig t x then Real.exp (d*Fintype.card ι) else 0

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.BadEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def badEndpoints {ι : Type} [Fintype ι] (t : ℝ) (x : ι → Space) : Finset ι :=
  Finset.univ.filter (fun i => ∃ j, i ≠ j ∧ ‖x i-x j‖ < 1 ∧
    ¬(Real.exp (-t) ≤ ‖x i-x j‖ ∧ ‖x i-x j‖ ≤ (1+shellDelta)*Real.exp (-t)))

noncomputable def idealFamily (d : ℝ) : ConfigFamily :=
  fun ι _ _ => Real.exp (d*Fintype.card ι)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

structure GrandFinite (F : ConfigFamily) (D : Set Space) : Prop where
  integrable : ∀ (ι : Type) [Fintype ι], IntegrableOn (F ι) {x | ∀ i, x i ∈ D}
  summable : Summable (familyTerm F D)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

noncomputable def occupationPairFamily (F : ConfigFamily) (C D : Set Space) : ConfigFamily :=
  fun ι _ x => F ι x*(occupation C x*occupation D x)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FreeUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def clusterActivity (t d : ℝ) : ℝ :=
  Real.exp d*(max 1 (volume.real (Metric.closedBall (0 : Space)
    ((1+shellDelta)*Real.exp (-t)))*Real.exp d))^3

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter Set
namespace ContinuumTemperature

noncomputable def packingDensity : ℝ :=
  sSup ((fun L : ℝ => (packingNumber L : ℝ)/(L+2)^3) '' Ici 0)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def shellVolumeConstant : ℝ :=
  (1+shellDelta)^3*volume.real (Metric.ball (0 : Space) 1)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.UpperLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Filter
namespace ContinuumTemperature

noncomputable def idealCorePressure (h : ℝ) : ℝ := max 0 (max (packingDensity*h) (4*packingDensity*h-9*packingDensity))

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FixedOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def countFamily (F : ConfigFamily) (n : ℕ) : ConfigFamily :=
  fun ι _ x => if Fintype.card ι = n then F ι x else 0

noncomputable def fixedOccupationFamily {κ : Type u_1} (A : κ → Set Space) (s : Finset κ)
    (n : κ → ℕ) (F : ConfigFamily) : ConfigFamily :=
  fun ι _ x => if ∀ k ∈ s, occupation (A k) x = (n k : ℝ) then F ι x else 0

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Tetrahedron
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def tetraRaw (i : Fin 4) : Space :=
  WithLp.toLp 2 (![![0,0,0],![1,1,0],![1,0,1],![0,1,1]] i)

noncomputable def tetraVertex (i : Fin 4) : Space :=
  ((1+shellDelta/2)/Real.sqrt 2) • tetraRaw i

noncomputable def clusterRadius (t : ℝ) : ℝ := shellDelta/8*Real.exp (-t)

def TetraCluster (t : ℝ) (x : Fin 4 → Space) : Prop :=
  ∀ i, ‖(x i-x 0)-Real.exp (-t) • tetraVertex i‖ ≤ clusterRadius t

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TetraVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

def tetraTrial (t r : ℝ) (c : Space) : Set (Fin 4 → Space) :=
  {x | x 0 ∈ Metric.closedBall c (r/2) ∧ ∀ j : Fin 3,
    x j.succ ∈ Metric.closedBall (x 0+Real.exp (-t) • tetraVertex j.succ) (clusterRadius t)}

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.KacKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

noncomputable def scaledKernel (R : ℝ) (x : Space) : ℝ := scaledKernelProfile R ‖x‖

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.KacGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

noncomputable def gridIndex (u : ℝ) (x : Space) : Lattice := fun i => ⌊x i/u⌋

noncomputable def gridCenter (u : ℝ) (k : Lattice) : Space :=
  WithLp.toLp 2 (fun i => u*((k i : ℝ)+1/2))

def gridBox (u : ℝ) (k : Lattice) : Set Space :=
  {x | ∀ i, u*(k i : ℝ) ≤ x i ∧ x i < u*((k i : ℝ)+1)}

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GridBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def indexInterval (m q : ℕ) : Finset ℤ :=
  Finset.Icc (-(m : ℤ)*(q : ℤ)) ((m : ℤ)*(q : ℤ))

noncomputable def edgeResidues (q H : ℕ) : Finset ℤ :=
  Finset.Ico 0 (H : ℤ) ∪ Finset.Ico ((q : ℤ)-(H : ℤ)) (q : ℤ)

noncomputable def edgeIndices (m q H : ℕ) : Finset ℤ :=
  (indexInterval m q).filter (fun k => k%(q : ℤ) ∈ edgeResidues q H)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CubeBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def gridIndices (m q : ℕ) : Finset Lattice :=
  Fintype.piFinset (fun _ : Fin 3 => indexInterval m q)

noncomputable def boundaryIndices (m q H : ℕ) : Finset Lattice :=
  Finset.univ.biUnion (fun i : Fin 3 => Fintype.piFinset
    (fun j : Fin 3 => if j = i then edgeIndices m q H else indexInterval m q))

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PairMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

noncomputable def momentConstant (t β h : ℝ) : ℝ :=
  (2*Real.exp (Real.exp (h+β*(t^2/2)))+(Real.exp (Real.exp (h+β*(t^2/2))))^2)/(β*(t^2/8)/4)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.OccupationEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def interactionFamily (F : ConfigFamily) (W : Space → Space → ℝ) : ConfigFamily :=
  fun ι _ x => F ι x*gibbsEnergy W x

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandInteraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def cellPairEnvelope {κ : Type} [Fintype κ] (F : ConfigFamily)
    (e : κ → Lattice) (J : κ → κ → ℝ) : ConfigFamily :=
  fun ι _ x => ∑ k, ∑ l, (J k l/2)*occupationPairFamily F (latticeCell (e k)) (latticeCell (e l)) ι x

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.MaskedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def blockCut (q : ℕ) (V : Space → Space → ℝ) (x y : Space) : ℝ :=
  if gridIndex ((q : ℝ)/4) x = gridIndex ((q : ℝ)/4) y then V x y else 0

noncomputable def deletedCore (t : ℝ) (σ τ R : ℕ → ℝ) (q : ℕ) (x y : Space) : ℝ :=
  blockCut q (fun x y => coreProfile t ‖x-y‖) x y-
    attraction t σ R ‖x-y‖-attraction t τ R ‖x-y‖

noncomputable def cutReference (t : ℝ) (σ τ R : ℕ → ℝ) (q : ℕ) (x y : Space) : ℝ :=
  blockCut q (fun x y => physicalProfile t σ R ‖x-y‖) x y-attraction t τ R ‖x-y‖

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.KacRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def kacUpper (C R u : ℝ) (c d : Space) : ℝ :=
  if ‖c-d‖ ≤ R+4*u then scaledKernel R (c-d)+4*C*u/R^4 else 0

noncomputable def kacLower (C R u : ℝ) (c d : Space) : ℝ :=
  max 0 (scaledKernel R (c-d)-4*C*u/R^4)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GibbsQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def quadraticBlock (q : ℕ) (φ : ℝ → ℝ) (γ : ℝ) : Space → Space → ℝ :=
  blockCut q (fun x y => φ ‖x-y‖-γ)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.KacBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def kacRowError (C : NNReal) (R u : ℝ) : ℝ :=
  (6*(C : ℝ)*u/R^4)*(2*(R+6*u))^3

noncomputable def cutKac (q : ℕ) (φ : ℝ → ℝ) (a R : ℝ) (x y : Space) : ℝ :=
  blockCut q (fun x y => φ ‖x-y‖) x y-a*scaledKernel R (x-y)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.AppendAttraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

def prepend (a : ℝ) (σ : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | n+1 => σ n

@[simp] theorem prepend_zero (a : ℝ) (σ : ℕ → ℝ) : prepend a σ 0 = a := rfl
@[simp] theorem prepend_succ (a : ℝ) (σ : ℕ → ℝ) (n : ℕ) : prepend a σ (n+1) = σ n := rfl

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.InnerGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def innerGridBox (u : ℝ) (k : Lattice) : Set Space :=
  (fun x : Space => x+gridCenter u k) '' cube (u-2)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LowerGibbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def kacLowerGain (C : NNReal) (S u : ℝ) (m N n : ℕ) : ℝ :=
  ((gridIndices m 1).card*(n : ℝ)^2*((1-kacRowError C S u)/u^3)-
    (gridIndices (m+N) 1).card*n*scaledKernel S 0)/2

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LowerKac
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter
namespace ContinuumTemperature

noncomputable def kacTrialValue (φ : ℝ → ℝ) (C : NNReal) (t β a h d u : ℝ) : ℝ :=
  let n := ⌊d*(u-2)^3⌋₊
  (t*h*((n : ℝ)/u^3)+Real.log (partition φ β (u-2) n)/u^3+
    β*(t*a)/2*(((n : ℝ)/u^3)^2*(1-kacRowError C (u^2) u)-
      ((n : ℝ)/u^3)*scaledKernel (u^2) 0))/t

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FreeIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def threeCore (p : ℝ) (x : Parameter) : ℝ := max 0 (max (p*x.2) (4*p*x.2-9*p))
def threeMeanField (p a : ℝ) (x : Parameter) : ℝ :=
  max 0 (max (p*x.2+x.1*a*p^2/2) (4*p*x.2-9*p+x.1*a*(4*p)^2/2))
def firstMass (p : ℝ) : ℝ := 3/(2*p)
def initialPoint : Parameter := (1,-3/4)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TriangleSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def vertexCoordinate (p : ℝ) (z : Parameter) (i : Fin 3) : ℝ :=
  if i = 0 then 1+(12*z.1-45*z.2)/(36*p)
  else if i = 1 then (12*z.2-4*z.1)/(9*p)
  else (4*z.1-3*z.2)/(36*p)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Regroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def slopeGroups (P : Parameter → ℝ) (x : Parameter) (v : Fin 3 → Parameter) (τ : ℝ) (i : Fin 3) : Set Parameter :=
  subgradients pressureDomain P x ∩ closedBall (v i) τ

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def moderateBox : Set Parameter := {x | 1/4 ≤ x.1 ∧ x.1 ≤ 2 ∧ x.2 ≤ 10}

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TripleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

structure HasVertexTriple (P : Parameter → ℝ) (x : Parameter) (p b : ℝ) : Prop where
  center : SupportOn pressureDomain P x (triangleCenter p)
  hull : subgradients pressureDomain P x = convexHull ℝ (⋃ i, slopeGroups P x (triangleVertex p) b i)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

structure ConstructionCap (t M : ℝ) : Prop where
  t_large : 1 < t
  mass_pos : 0 < M
  strong : 140608*kernelHeight*M ≤ t
  gap : 1024*M < t

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def geometricBudget (n : ℕ) : ℝ := (1/2)^n
def groupRadius (τ : ℝ) (n : ℕ) : ℝ := τ*(1-geometricBudget (n+1))
def locationRadius (n : ℕ) : ℝ := 1/8-geometricBudget n/16

structure ConstructionStage (t p τ : ℝ) (n : ℕ) where
  σ : ℕ → ℝ
  R : ℕ → ℝ
  a : ℝ
  x : Parameter
  σ_nonneg : ∀ k, 0 ≤ σ k
  R_one : ∀ k, 1 ≤ R k
  σ_summable : Summable σ
  a_pos : 0 < a
  mass : a+∑' k, σ k ≤ firstMass p+1-geometricBudget n
  referenceBounded : ∃ B ≥ 0, ∀ k, σ k ≠ 0 → R k ≤ B
  location : dist x initialPoint < locationRadius n
  triple : HasVertexTriple (meanField (physicalPressure (physicalProfile t σ R) t) a) x p (groupRadius τ n)

def ConstructionStage.pressure {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) : Parameter → ℝ :=
  physicalPressure (physicalProfile t s.σ s.R) t

def ConstructionStage.ideal {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) : Parameter → ℝ :=
  meanField s.pressure s.a

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

structure StageTransition {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n)
    (s' : ConstructionStage t p τ (n+1)) (Rnew : ℝ) : Prop where
  range_large : 4 < Rnew
  mass_eq : s'.σ = prepend s.a s.σ
  range_eq : s'.R = prepend Rnew s.R
  next_small : s'.a < geometricBudget n/2
  displacement : dist s'.x s.x < geometricBudget n/32
  approximation : ∀ y ∈ closedBall initialPoint (1/4), |s'.pressure y-s.ideal y| ≤ geometricBudget n

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

structure ConstructionData (p : ℝ) where
  t : ℝ
  τ : ℝ
  γ : ℝ
  τ_pos : 0 < τ
  τ_small : τ ≤ p/100
  γ_pos : 0 < γ
  cap : ConstructionCap t (firstMass p+1)
  geometry : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
    closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w)
  stages : ∀ n, ConstructionStage t p τ n
  ranges : ℕ → ℝ
  initial_zero : (stages 0).σ = fun _ => 0
  initial_mass : (stages 0).a = firstMass p
  transitions : ∀ n, StageTransition (stages n) (stages (n+1)) (ranges n)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionMasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def ConstructionData.masses {p : ℝ} (C : ConstructionData p) (n : ℕ) : ℝ := (C.stages n).a

def prefixMass (σ : ℕ → ℝ) (n k : ℕ) : ℝ := if k < n then σ k else 0

def tailMass (σ : ℕ → ℝ) (n k : ℕ) : ℝ := if n ≤ k then σ k else 0

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def ConstructionData.profile {p : ℝ} (C : ConstructionData p) : ℝ → ℝ :=
  physicalProfile C.t C.masses C.ranges

def ConstructionData.pressure {p : ℝ} (C : ConstructionData p) : Parameter → ℝ :=
  physicalPressure C.profile C.t

end ContinuumTemperature
end
end

end OAI
end


