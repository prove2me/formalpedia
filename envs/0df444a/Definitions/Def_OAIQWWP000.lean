-- Prove2me | Definitions.Def_OAIQWWP000
-- name    : OAIQWWP000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T01:02:16.723977+00:00
-- url     : https://prove2.me/theorems/7b4c29ca-3562-422a-b5eb-7ae518b7b80c
-- title:
--   OpenAI weak pinned distance split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of the weak pinned planar distance theorem (`OAI.WeakPinned.main`). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Geometry/PinnedDistances` (OpenAI, *The weak pinned planar distance theorem*, OpenAI Math Release, September 23, 2026, result family 167, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are the fiber graphs `Core.Fibers` and the prepared-graph conditions `PreparedGraph`, the arithmetic potentials `Global.cellMass`, `Global.totalMass`, `Global.S` and `Global.M` of a number-field model, the scales `overlapScale` and `potentialScale`, and the variance and cut quantities `Variance.varianceCell`, `Variance.weightedIntegral`, `Cuts.tent`, `fiberVariance` and `incomingVariance`. The bundle also contains the lemmas those definitions use in their bodies: several definitions take suprema or integrals that need proofs, or build structures that carry proofs.
--
--   The definitions of the published statement (`Plane`, `distanceFiber`, `k`, `richPairs`, `pairFraction`, `F`) are not repeated: the bundle imports them from the published bundle `Def_PinnedDistances`. It imports no other bundle. A small compatibility section declares, inside namespace `OAI`, lemmas that newer Lean versions provide under names this environment lacks (such as `ite_eq_left`, which is `if_pos`).
--
--   Modules: `ArithmeticGraphs.lean`, `ArithmeticHierarchy.lean`, `ArithmeticSequence.lean`, `ArithmeticVariance.lean`, `ChartLimits.lean`, `CutApproximation.lean`, `CutGeometry.lean`, `EmpiricalCompactness.lean`, `EnergyLaw.lean`, `ExtremalCore.lean`, `FiberOverlap.lean`, `FiberTransport.lean`, `FiniteLaw.lean`, `FiniteObstruction.lean`, `GlobalOverlap.lean`, `GlobalPotentials.lean`, `GridBounds.lean`, `Hierarchy.lean`, `IncomingFibers.lean`, `LimitObstruction.lean`, `LogBounds.lean`, `MeasureLimits.lean`, `MinPotentials.lean`, `MixtureLaw.lean`, `MobiusObstruction.lean`, `Model.lean`, `NormalizedGraphs.lean`, `OverlapRates.lean`, `PartitionIntegrals.lean`, `ProductFormula.lean`, `RandomGrids.lean`, `SmallCells.lean`, `TreeContradiction.lean`, `TreeTransport.lean`, `UnboundedContradiction.lean`, `UniformCore.lean`, `Variance.lean`, `VarianceRates.lean`, `WeightedSelection.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the five solutions of this split. Four of them prove the published intermediate statements `OAI.WeakPinned.sampling_variance_rates`, `OAI.WeakPinned.arithmetic_balanced_length`, `OAI.WeakPinned.arithmetic_no_unbounded` and `OAI.WeakPinned.arithmetic_sequence_impossible`, and the fifth proves `OAI.WeakPinned.main` from them. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The weak pinned planar distance theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 167; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-weak-pinned-planar-distance-theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/PinnedDistances at commit adc7f12

import Mathlib
import Definitions.Def_PinnedDistances

section
-- module Solutions.OAIQW_WeakPinned.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace WeakPinned

def distances (P : Finset Plane) (x : Plane) : Finset ℝ :=
  (P.erase x).image (fun y => dist y x)

def badPins (P : Finset Plane) (ε : ℝ) : Finset Plane :=
  P.filter (fun x => ((distances P x).card : ℝ) < (P.card : ℝ) ^ (1 - ε))

def badPinFraction (P : Finset Plane) (ε : ℝ) : ℝ :=
  (badPins P ε).card / (P.card : ℝ)

def B (n : ℕ) (ε : ℝ) : ℝ :=
  if 0 < n then sSup {a : ℝ | ∃ P : Finset Plane, P.card = n ∧ a = badPinFraction P ε}
  else 0

/- Uniform multiplicity and pinned-distance convergence statements. -/
def MainStatement : Prop :=
  ∀ s : ℝ, 0 < s → Tendsto (fun n : ℕ => F n s) atTop (nhds 0)

end WeakPinned

end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter MeasureTheory
namespace WeakPinned.Bounded

variable {I : Type u1} {X : Type u2} [Fintype I] [MeasurableSpace X] [MeasurableSingletonClass X]

def finiteLaw (w : I → ℝ) (U : I → X) : Measure X :=
  ∑ i,ENNReal.ofReal (w i) • Measure.dirac (U i)

omit [MeasurableSingletonClass X] in
lemma finiteLaw_univ (w : I → ℝ) (U : I → X) (hw : ∀ i,0≤ w i) :
    finiteLaw w U Set.univ=ENNReal.ofReal (∑ i,w i) := by
  simp [finiteLaw,Measure.finsetSum_apply,ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i)]

omit [MeasurableSingletonClass X] in
lemma finiteLaw_probability (w : I → ℝ) (U : I → X)
    (hw : ∀ i,0≤ w i) (hW : ∑ i,w i=1) : IsProbabilityMeasure (finiteLaw w U) := by
  constructor
  rw [finiteLaw_univ w U hw,hW,ENNReal.ofReal_one]

def finiteProbability (w : I → ℝ) (U : I → X) (hw : ∀ i,0≤ w i) (hW : ∑ i,w i=1) :
    ProbabilityMeasure X := ⟨finiteLaw w U,finiteLaw_probability w U hw hW⟩

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.MobiusObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/- A non-atomic obstruction for bounded cross-ratio energy. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

namespace WeakPinned.Bounded

def crossKernel (a c : ℂ) (zw : ℂ × ℂ) : ℝ :=
  min 1 ‖(c - a) * (zw.2 - zw.1) / ((zw.1 - a) * (c - zw.2))‖

def targetKernel (d : ℂ) (zw : ℂ × ℂ) : ℝ :=
  min 1 ‖(zw.1 - zw.2) / (zw.2 - d)‖

def crossEnergy (μ : Measure ℂ) (a c : ℂ) : ℝ :=
  ∫ zw, crossKernel a c zw ∂ μ.prod μ

def targetEnergy (ν : Measure ℂ) (d : ℂ) : ℝ :=
  ∫ zw, targetKernel d zw ∂ ν.prod ν

def mobius (a b c d z : ℂ) : ℂ := b + (c - a) * (d - b) / (z - a)

attribute [local irreducible] crossEnergy targetEnergy

/-- The Riemann sphere as the one-point compactification of the complex plane. -/
abbrev Sphere := OnePoint ℂ
local instance instMeasurableSpaceSphere : MeasurableSpace Sphere := borel Sphere

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open TopologicalSpace
local instance instMeasurableSpaceSphere_1 : MeasurableSpace Sphere := borel Sphere
local instance instBorelSpaceSphere_1 : BorelSpace Sphere := ⟨rfl⟩

/-- The one-point compactification of the complex plane has a countable basis. -/
instance sphereSecondCountable : SecondCountableTopology Sphere := by
  let B : Set (Set Sphere) :=
    (fun U : Set ℂ => OnePoint.some '' U) '' countableBasis ℂ ∪
      Set.range (fun n : ℕ => (OnePoint.some '' Metric.closedBall (0:ℂ) (n:ℝ))ᶜ)
  have hcount : B.Countable := (countable_countableBasis ℂ).image _ |>.union (Set.countable_range _)
  have hbase : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro U hU
      rcases hU with ⟨V,hV,rfl⟩ | ⟨n,rfl⟩
      · exact OnePoint.isOpen_image_coe.mpr ((isBasis_countableBasis ℂ).isOpen hV)
      · exact OnePoint.isOpen_compl_image_coe.mpr ⟨Metric.isClosed_closedBall,isCompact_closedBall _ _⟩
    · intro a U ha hU
      induction a using OnePoint.rec with
      | coe a =>
        have hp : IsOpen (OnePoint.some ⁻¹' U : Set ℂ) := hU.preimage OnePoint.continuous_coe
        obtain ⟨V,hV,haV,hVU⟩ := (isBasis_countableBasis ℂ).mem_nhds_iff.mp (hp.mem_nhds ha)
        refine ⟨OnePoint.some '' V,Or.inl ⟨V,hV,rfl⟩,⟨a,haV,rfl⟩,?_⟩
        rintro z ⟨w,hw,rfl⟩
        exact hVU hw
      | infty =>
        have hc := ((OnePoint.isOpen_iff_of_mem ha).mp hU).2
        obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:ℂ)
        obtain ⟨n,hn⟩ := exists_nat_gt R
        refine ⟨(OnePoint.some '' Metric.closedBall (0:ℂ) (n:ℝ))ᶜ,Or.inr ⟨n,rfl⟩,?_,?_⟩
        · exact OnePoint.infty_notMem_image_coe
        · intro z hz
          induction z using OnePoint.rec with
          | infty => exact ha
          | coe z =>
            by_contra hnot
            have hzR := hR hnot
            have hzn := Metric.closedBall_subset_closedBall hn.le hzR
            exact hz ⟨z,hzn,rfl⟩
  exact hbase.secondCountableTopology hcount

/-- Restriction of a sphere probability measure to the complex plane.
    This is a probability measure when there is no mass at infinity. -/
def finitePart (β : ProbabilityMeasure Sphere) : Measure ℂ :=
  Measure.comap ((↑) : ℂ → Sphere) (β : Measure Sphere)

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.EnergyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace WeakPinned.Bounded

abbrev Quad (X : Type u1) := X × X × X × X
abbrev Expanded (X : Type u2) := Quad X × ((X × X) × (X × X))

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.MixtureLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace WeakPinned.Bounded

variable {I : Type u1} {V : Type u2} {X : Type u3} [Fintype I] [Fintype V]

def edgeWeight (w : I → ℝ) (p : I → V → ℝ) (r : I × V) : ℝ := w r.1*p r.1 r.2

def tripleWeight (w : I → ℝ) (p : I → V → ℝ) (r : I × V × V × V) : ℝ :=
  w r.1*p r.1 r.2.1*p r.1 r.2.2.1*p r.1 r.2.2.2

lemma sum_edgeWeight (w : I → ℝ) (p : I → V → ℝ)
    (hw : ∑ i,w i=1) (hp : ∀ i,∑ x,p i x=1) : ∑ r,edgeWeight w p r=1 := by
  simp only [edgeWeight,Fintype.sum_prod_type,← Finset.mul_sum,hp,mul_one,hw]

lemma sum_tripleWeight (w : I → ℝ) (p : I → V → ℝ)
    (hw : ∑ i,w i=1) (hp : ∀ i,∑ x,p i x=1) : ∑ r,tripleWeight w p r=1 := by
  simp only [tripleWeight,Fintype.sum_prod_type,← Finset.mul_sum,hp,mul_one,hw]

def edgeValue (s : I → V) (U₁ U₂ : V → X) (r : I × V) : Quad X :=
  (U₁ (s r.1),U₂ (s r.1),U₁ r.2,U₂ r.2)

def tripleValue (s : I → V) (U₁ U₂ : V → X) (r : I × V × V × V) : Expanded X :=
  (edgeValue s U₁ U₂ (r.1,r.2.1),((U₁ r.2.2.1,U₂ r.2.2.1),(U₁ r.2.2.2,U₂ r.2.2.2)))

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ProductFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

section

/- The finite-place absolute values are norm-normalized. Dividing their logarithms
   by [K:ℚ] gives the weighted contribution of locally normalized absolute values. -/

noncomputable section
open NumberField
open scoped BigOperators

namespace WeakPinned.Arithmetic

variable {K : Type u1} [Field K]

variable [NumberField K]

def archWeight (v : InfinitePlace K) : ℝ :=
  (v.mult : ℝ) / Module.finrank ℚ K

/-- The finitely many nonunit places for a given finite list of differences. -/
lemma finite_nonunit_places {ι : Type u2} [Finite ι] (z : ι → K)
    (hz : ∀ i, z i ≠ 0) :
    {v : FinitePlace K | ∃ i, v (z i) ≠ 1}.Finite := by
  have he : {v : FinitePlace K | ∃ i, v (z i) ≠ 1} =
      ⋃ i, Function.mulSupport (fun v : FinitePlace K => v (z i)) := by
    ext v
    simp
  rw [he]
  exact Set.finite_iUnion (fun i => FinitePlace.hasFiniteMulSupport (hz i))

lemma finite_raw_ultra (v : FinitePlace K) {x y z : K}
    (_hxy : x ≠ y) (_hyz : y ≠ z) (hxz : x ≠ z) :
    min (-Real.log (v (x-y))) (-Real.log (v (y-z))) ≤ -Real.log (v (x-z)) := by
  have h := v.add_le (x-y) (y-z)
  rw [sub_add_sub_cancel] at h
  have hp : 0 < v (x-z) := FinitePlace.pos_iff.mpr (sub_ne_zero.mpr hxz)
  have hl := Real.log_le_log hp h
  by_cases hc : v (x-y) ≤ v (y-z)
  · rw [max_eq_right hc] at hl
    exact (min_le_right _ _).trans (neg_le_neg hl)
  · rw [max_eq_left (le_of_not_ge hc)] at hl
    exact (min_le_left _ _).trans (neg_le_neg hl)

end WeakPinned.Arithmetic

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.Hierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open NumberField
open scoped BigOperators

/- Deterministic giant-removal identity. -/

noncomputable section
open MeasureTheory
open scoped Topology

namespace WeakPinned.Hierarchy
variable {P : Type u1} [Fintype P] [DecidableEq P]

structure Depth (P : Type u2) where
  value : P → P → ℝ
  symm : ∀ x y, value x y = value y x
  ultra : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    min (value x y) (value y z) ≤ value x z

namespace Depth

variable (d : Depth P)

def share (r : ℝ) (x y : P) : Prop := x = y ∨ r ≤ d.value x y
instance instDecidableShare (r : ℝ) (x y : P) : Decidable (d.share r x y) := Classical.propDecidable _

def cell (r : ℝ) (x : P) : Finset P := Finset.univ.filter (d.share r x)
omit [DecidableEq P] in
@[simp] lemma mem_cell (r : ℝ) (x y : P) : y ∈ d.cell r x ↔ d.share r x y := by
  simp [cell]

def cells (r : ℝ) : Finset (Finset P) := Finset.univ.image (d.cell r)
@[simp] lemma mem_cells (r : ℝ) (C : Finset P) : C ∈ d.cells r ↔ ∃ x, d.cell r x = C := by
  simp [cells]

def giants (r : ℝ) : Finset (Finset P) :=
  (d.cells r).filter (fun C => Fintype.card P < 2*C.card)

@[simp] lemma mem_giants (r : ℝ) (C : Finset P) : C ∈ d.giants r ↔
    C ∈ d.cells r ∧ Fintype.card P < 2*C.card := by simp [giants]

def giant (r : ℝ) : Finset P := (d.giants r).biUnion id

def transformed (r : ℝ) : Multiset (Finset P) :=
  ((d.cells r).filter (fun C => ¬Fintype.card P < 2*C.card)).val +
  ((d.giants r).val.map (fun C => Cᶜ))

def sumCells (f : Finset P → ℝ) (r : ℝ) : ℝ := ((d.transformed r).map f).sum

def pairOverlap (r : ℝ) (x y : P) : ℝ :=
  d.sumCells (fun C => if x ∈ C ∧ y ∈ C then 1 else 0) r

def giantIndicator (r : ℝ) : ℝ := if (d.giants r).Nonempty then 1 else 0

def outsideIndicator (r : ℝ) (x : P) : ℝ :=
  if (d.giants r).Nonempty ∧ x ∉ d.giant r then 1 else 0

def radius : ℝ := ∑ x, ∑ y, |d.value x y|

/-- The last level containing a giant. -/
def M : ℝ := sSup {r : ℝ | (d.giants r).Nonempty}

def potential (x : P) : ℝ := ∫ r : ℝ, d.outsideIndicator r x

def overlapLength (x y : P) (_ : x ≠ y) : ℝ := ∫ r : ℝ, d.pairOverlap r x y

end Depth
end WeakPinned.Hierarchy

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.RandomGrids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology

/- Square-grid construction and the finite-shift sharing law. -/

noncomputable section
open MeasureTheory
open scoped Topology ENNReal
namespace WeakPinned.Grid

def bin (l s x : ℝ) : ℤ := ⌊(x-s)/l⌋
def shares (l s x y : ℝ) : ℝ := if bin l s x = bin l s y then 1 else 0

/-- Normalized Lebesgue measure on a half-open interval of positive length. -/
def uniformInterval (l : ℝ) : Measure ℝ :=
  (ENNReal.ofReal l)⁻¹ • volume.restrict (Set.Ioc 0 l)

open ProbabilityTheory in
/-- A fair binary step of length `l`. -/
def binaryStep (l : ℝ) : Measure ℝ := bernoulliMeasure 0 l ⟨1/2, by norm_num⟩

instance binaryStep_probability (l : ℝ) : IsProbabilityMeasure (binaryStep l) := by
  unfold binaryStep
  infer_instance

/-- One initial uniform shift followed by independent fair coarsening bits,
    before introducing phase and orientation. -/
def incrementLaw : ℕ → Measure ℝ
  | 0 => uniformInterval 1
  | n+1 => binaryStep (2^n)

def axisLaw : Measure (ℕ → ℝ) := Measure.infinitePi incrementLaw

def shift (n : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range (n+1), ω i

/-- Both independent axis constructions, before phase and rotation. -/
abbrev GridSample := (ℕ → ℝ) × (ℕ → ℝ)
def squareLaw : Measure GridSample := axisLaw.prod axisLaw

def shiftZ (m : ℤ) (ω : ℕ → ℝ) : ℝ := shift m.toNat ω

def shareAt (m : ℤ) (ω : GridSample) (x y : ℝ × ℝ) : Prop :=
  bin ((2:ℝ)^m) (shiftZ m ω.1) x.1 = bin ((2:ℝ)^m) (shiftZ m ω.1) y.1 ∧
  bin ((2:ℝ)^m) (shiftZ m ω.2) x.2 = bin ((2:ℝ)^m) (shiftZ m ω.2) y.2

lemma shareAt_symm (m : ℤ) (ω : GridSample) (x y : ℝ × ℝ) :
    shareAt m ω x y ↔ shareAt m ω y x := by simp [shareAt, eq_comm]

def minScale (ω : GridSample) (x y : ℝ × ℝ) : ℤ := sInf {m | shareAt m ω x y}

def gridDepth (ω : GridSample) (x y : ℝ × ℝ) : ℝ :=
  -(minScale ω x y : ℝ) * Real.log 2

lemma minScale_symm (ω : GridSample) (x y : ℝ × ℝ) :
    minScale ω x y = minScale ω y x := by
  unfold minScale
  congr 1
  ext m
  exact shareAt_symm m ω x y

def polarPair (t θ : ℝ) : ℝ × ℝ := (Real.exp t * Real.cos θ, Real.exp t * Real.sin θ)

def polarMean (t θ : ℝ) : ℝ :=
  (∫ ω, gridDepth ω (0,0) (polarPair t θ) ∂squareLaw) + t

/-- The universal archimedean error mean, before any configuration is chosen. -/
def kappa : ℝ := ∫ ξ, ∫ θ, polarMean (-ξ) θ
  ∂uniformInterval (2*Real.pi) ∂uniformInterval (Real.log 2)

def rotateC (ξ θ : ℝ) (z : ℂ) : ℂ :=
  (Real.exp (-ξ) : ℂ) * Complex.exp ((θ : ℂ)*Complex.I) * z

def rotatePair (ξ θ : ℝ) (z : ℂ) : ℝ × ℝ :=
  ((rotateC ξ θ z).re, (rotateC ξ θ z).im)

abbrev FullSample := (ℝ × ℝ) × GridSample

def phaseLaw : Measure (ℝ × ℝ) :=
  (uniformInterval (Real.log 2)).prod (uniformInterval (2*Real.pi))

def fullLaw : Measure FullSample := phaseLaw.prod squareLaw

/-- Actual jointly defined hierarchy depth in the original complex plane. -/
def depth (ω : FullSample) (z w : ℂ) : ℝ :=
  gridDepth ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w) - ω.1.1

def error (ω : FullSample) (z w : ℂ) : ℝ := depth ω z w + Real.log ‖z-w‖

lemma depth_symm (ω : FullSample) (z w : ℂ) : depth ω z w = depth ω w z := by
  simp only [depth,gridDepth,minScale_symm ω.2 (rotatePair ω.1.1 ω.1.2 z)
    (rotatePair ω.1.1 ω.1.2 w)]

end WeakPinned.Grid

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ArithmeticHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal

noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
namespace WeakPinned.Global
open Hierarchy
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]
variable (Z : P → K) (hZ : Function.Injective Z)
include hZ

def good (v : InfinitePlace K) (ω : Grid.FullSample) : Prop :=
  ∀ x y z : P, x ≠ y → y ≠ z → x ≠ z →
    min (Grid.depth ω (v.embedding (Z x)) (v.embedding (Z y)))
      (Grid.depth ω (v.embedding (Z y)) (v.embedding (Z z))) ≤
        Grid.depth ω (v.embedding (Z x)) (v.embedding (Z z))

instance good_decidable (v : InfinitePlace K) (ω : Grid.FullSample) : Decidable (good Z v ω) :=
  Classical.propDecidable _

def arch (v : InfinitePlace K) (ω : Grid.FullSample) : Depth P where
  value x y := if good Z v ω ∧ x ≠ y then Grid.depth ω (v.embedding (Z x)) (v.embedding (Z y)) else 0
  symm x y := by
    by_cases h : good Z v ω
    · by_cases hxy : x = y
      · subst y; rfl
      · simp [h, hxy, Ne.symm hxy, Grid.depth_symm]
    · simp [h]
  ultra x y z hxy hyz hxz := by
    by_cases h : good Z v ω
    · simpa [h,hxy,hyz,hxz] using h x y z hxy hyz hxz
    · simp [h]

def finite (v : FinitePlace K) : Depth P where
  value x y := if x = y then 0 else -Real.log (v (Z x-Z y))
  symm x y := by
    by_cases hxy : x = y
    · subst y; rfl
    · simp only [hxy,Ne.symm hxy,reduceIte]
      rw [← neg_sub (Z x) (Z y), map_neg_eq_map]
  ultra x y z hxy hyz hxz := by
    simp only [hxy,hyz,hxz,reduceIte]
    exact Arithmetic.finite_raw_ultra v (hZ.ne hxy) (hZ.ne hyz) (hZ.ne hxz)

abbrev DiffPair := {p : P × P // p.1 ≠ p.2}

def badPlaces : Finset (FinitePlace K) :=
  (Arithmetic.finite_nonunit_places (fun p : DiffPair (P := P) => Z p.1.1 - Z p.1.2)
    (fun p => sub_ne_zero.mpr (hZ.ne p.2))).toFinset

def S (x : P) : ℝ :=
  (∑ v : InfinitePlace K, Arithmetic.archWeight v * ∫ ω, (arch Z v ω).potential x ∂Grid.fullLaw) +
    (Module.finrank ℚ K : ℝ)⁻¹ * ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).potential x

def L (x y : P) (hxy : x ≠ y) : ℝ :=
  (∑ v : InfinitePlace K, Arithmetic.archWeight v * ∫ ω, (arch Z v ω).overlapLength x y hxy ∂Grid.fullLaw) +
    (Module.finrank ℚ K : ℝ)⁻¹ * ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).overlapLength x y hxy

def M : ℝ :=
  (∑ v : InfinitePlace K, Arithmetic.archWeight v * ∫ ω, (arch Z v ω).M ∂Grid.fullLaw) +
    (Module.finrank ℚ K : ℝ)⁻¹ * ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).M

end WeakPinned.Global

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u3} [Fintype P] [DecidableEq P]
variable (d : Depth P)

def count (r : ℝ) (C : Finset P) : ℝ := (d.transformed r).count C

def mass (C : Finset P) : ℝ := if 2 ≤ C.card then ∫ r, d.count r C else 0

end WeakPinned.Hierarchy.Depth

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.Variance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators

/- Finite off-diagonal variance. All diagonal terms are identically zero,
   not O(1/n): singleton cells may persist forever. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace WeakPinned.Variance

variable {P : Type u1} [Fintype P] [DecidableEq P]

def prob (B : Finset P) (x : P) : ℝ := if x ∈ B then 1 / B.card else 0

def pairProb (B : Finset P) (x y : P) : ℝ :=
  if x ∈ B ∧ y ∈ B ∧ x ≠ y then 1 / ((B.card : ℝ) * (B.card - 1)) else 0

/-- Mixed cell probability, including B=P without an undefined outside branch.
    The outside column formula is never used when B=P. -/
def mixedProb (B : Finset P) (x y : P) : ℝ :=
  if x ∈ B ∧ x ≠ y then
    if y ∈ B then 1 / ((Fintype.card P : ℝ) * (B.card - 1))
    else 1 / ((Fintype.card P : ℝ) * B.card)
  else 0

lemma sum_prob (B : Finset P) (hB : B.Nonempty) : ∑ x, prob B x = 1 := by
  classical
  rw [show (∑ x, prob B x) = ∑ x ∈ B, 1 / (B.card : ℝ) by simp [prob]]
  simp [hB.card_ne_zero]

def signedPair (B : Finset P) (x y : P) : ℝ :=
  pairProb B x y - 2 * mixedProb B x y + pairProb Finset.univ x y

/-- Exact cell probabilities, with the diagonal excluded. -/
def pairCell (B C : Finset P) : ℝ := ∑ x ∈ C, ∑ y ∈ C, pairProb B x y

def mixedCell (B C : Finset P) : ℝ := ∑ x ∈ C, ∑ y ∈ C, mixedProb B x y

def cellProb (B C : Finset P) : ℝ := ((B ∩ C).card : ℝ) / B.card

def signedCell (B C : Finset P) : ℝ := pairCell B C - 2 * mixedCell B C +
    pairCell Finset.univ C

section CellIntegral
variable {Ω : Type u3} [MeasurableSpace Ω]

section Quantitative
local instance instMeasurableSpaceFinset_solutions_r129475_1 : MeasurableSpace (Finset P) := ⊤
local instance instDiscreteMeasurableSpaceFinset_solutions_r129475_1 : DiscreteMeasurableSpace (Finset P) := ⟨fun _ => trivial⟩
variable {I : Type u5} [Fintype I]

def varianceCell (w : I → ℝ) (B : I → Finset P) (T : ℝ) (D : Finset P) : ℝ :=
  if T < D.card then
    ∑ i, w i * (cellProb (B i) D - cellProb Finset.univ D)^2
  else (1/2) * ∑ i, w i *
    (if 2 / ((B i).card : ℝ) ≤ cellProb (B i) D then (cellProb (B i) D)^2 else 0)

end Quantitative

end CellIntegral

end WeakPinned.Variance

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ArithmeticVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.Global
open Hierarchy
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]
variable (Z : P → K) (hZ : Function.Injective Z)

def cellMass (C : Finset P) : ℝ :=
  (∑ v : InfinitePlace K, Arithmetic.archWeight v * ∫ ω, (arch Z v ω).mass C ∂Grid.fullLaw) +
    (Module.finrank ℚ K : ℝ)⁻¹ * ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).mass C

end WeakPinned.Global

namespace WeakPinned.Variance
variable {P : Type u3} [Fintype P] [DecidableEq P]

/-- Finite linear model of the actual occurrence integral on expressions
    vanishing on singleton and empty cells. Multiplicities are in m. -/
def weightedIntegral (m : Finset P → ℝ) (f : Finset P → ℝ) : ℝ := ∑ C, m C * f C

def weightedOverlap (m : Finset P → ℝ) (x y : P) : ℝ :=
  weightedIntegral m (fun C => if x ∈ C ∧ y ∈ C then 1 else 0)

end WeakPinned.Variance

namespace WeakPinned.Global
open Hierarchy Variance
variable {P : Type u5} [Fintype P] [DecidableEq P]
variable {K : Type u6} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

def totalMass (C : Finset P) : ℝ := cellMass Z₁ h₁ C + cellMass Z₂ h₂ C

def totalPotential (x : P) : ℝ := S Z₁ h₁ x + S Z₂ h₂ x

def baseConstant : ℝ := 2*Grid.kappa - M Z₁ h₁ - M Z₂ h₂

end WeakPinned.Global

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.SmallCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable (d : Depth P)

def sourceGiant (x : P) (r : ℝ) : Prop := Fintype.card P < 2*(d.cell r x).card
instance instDecidableSourceGiant (x : P) (r : ℝ) : Decidable (d.sourceGiant x r) := Classical.propDecidable _

def sourceM (x : P) : ℝ := sSup {r : ℝ | d.sourceGiant x r}

def smallCells (y : P) (T : ℝ) : Finset (Finset P) := by
  classical
  exact Finset.univ.filter (fun C => ∃ r : ℝ, C = d.cell r y ∧ (C.card : ℝ) < T)

def smallNeighbors (y : P) (T : ℝ) : Finset P := (d.smallCells y T).biUnion id

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.SmallFiber
open MeasureTheory
variable {P : Type u3} [Fintype P] [DecidableEq P]

/-- Probability of a finite subset; the fiber weights used below will be the
    exact uniform probabilities on the original retained distance fibers. -/
def mass (p : P → ℝ) (C : Finset P) : ℝ := ∑ y ∈ C, p y

end WeakPinned.SmallFiber

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy
variable {P : Type u5} [Fintype P] [DecidableEq P]

def minusError (d d' : Depth P) (p : P → ℝ) (x : P) (h H r : ℝ) : ℝ :=
  mass p (d.cell r x ∪ d'.cell (h-r-H) x)ᶜ

def plusError (d d' : Depth P) (p : P → ℝ) (x : P) (h H r : ℝ) : ℝ :=
  mass p (d.cell r x ∩ d'.cell (h-r+H) x)

end WeakPinned.SmallFiber

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy
variable {P : Type u6} [Fintype P] [DecidableEq P]

/-- Actual source cell, not a giant-complement occurrence. -/
def activeMass (d : Depth P) (p : P → ℝ) (x : P) (T lam r : ℝ) : ℝ := by
  classical
  exact if ¬d.sourceGiant x r ∧ ((d.cell r x).card : ℝ) < T ∧ mass p (d.cell r x) < lam
    then mass p (d.cell r x) else 0

def nongiantMass (d : Depth P) (p : P → ℝ) (x : P) (r : ℝ) : ℝ :=
  if ¬d.sourceGiant x r then mass p (d.cell r x) else 0

def straddle (d : Depth P) (x : P) (h H r : ℝ) : ℝ :=
  if d.sourceGiant x (h-r-H) ∧ ¬d.sourceGiant x (h-r+H) then 1 else 0

def neighborMass (d d' : Depth P) (p : P → ℝ) (x : P) (T t : ℝ) : ℝ := by
  classical
  exact ∑ y, p y * (if x ∈ (d.smallNeighbors y T).erase y then d'.outsideIndicator t y else 0)

end WeakPinned.SmallFiber

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy
variable {P : Type u7} [Fintype P] [DecidableEq P]

/-- Exact edge law induced by fiber sampling; no independence of fiber
    labels or levels is postulated. -/
def edgeLaw {I : Type u8} [Fintype I] (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (a b : P) : ℝ :=
  ∑ i, if x i = a then w i * p i b else 0

end WeakPinned.SmallFiber

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.FiberOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy Variance
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]

def slice (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (lam : ℝ) (C : Finset P) : ℝ :=
  ∑ i, w i * (if x i ∈ C ∧ mass (p i) C < lam then mass (p i) C else 0)

def edgeCell (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (C : Finset P) : ℝ :=
  ∑ a ∈ C, ∑ b ∈ C, edgeLaw w p x a b

end WeakPinned.SmallFiber

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.GlobalOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.Global
open Hierarchy Variance SmallFiber
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]
variable {K : Type u3} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
include h₁ h₂

omit h₁ h₂ in
def placeAverage (V : Finset (FinitePlace K)) (A : InfinitePlace K → ℝ) (F : FinitePlace K → ℝ) : ℝ :=
  (∑ v, Arithmetic.archWeight v * A v) + (Module.finrank ℚ K:ℝ)⁻¹ * ∑ v ∈ V, F v

end WeakPinned.Global

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ExtremalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology

/- Finite extremal core construction. The truncated-fiber score gives the same
   core as pruning while avoiding an arbitrary pruning order. It uses the
   original fibers without a generic-position hypothesis. -/

noncomputable section
open scoped BigOperators
namespace WeakPinned.Core
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]

structure Fibers (V : Type u3) (I : Type u4) [DecidableEq V] where
  source : I → V
  targets : I → Finset V
  no_loop : ∀ e, source e ∉ targets e
  disjoint : ∀ e f, e ≠ f → source e=source f → Disjoint (targets e) (targets f)

namespace Fibers
variable (G : Fibers V I)

def size (C : Finset V) (e : I) : ℕ := (G.targets e ∩ C).card

def contribution (K : ℝ) (C : Finset V) (e : I) : ℝ :=
  if G.source e ∈ C then max ((G.size C e : ℝ)-K) 0 else 0

def score (K : ℝ) (C : Finset V) : ℝ := ∑ e, G.contribution K C e

def active (K : ℝ) (C : Finset V) (e : I) : Prop :=
  G.source e ∈ C ∧ K < (G.size C e : ℝ)

instance instDecidableActive (K : ℝ) (C : Finset V) (e : I) : Decidable (G.active K C e) := Classical.propDecidable _

def edge (K : ℝ) (C : Finset V) (x y : V) : Prop :=
  ∃ e, G.active K C e ∧ G.source e=x ∧ y ∈ G.targets e ∩ C

instance instDecidableEdge (K : ℝ) (C : Finset V) (x y : V) : Decidable (G.edge K C x y) := Classical.propDecidable _

def degree (K : ℝ) (C : Finset V) (v : V) : ℝ :=
  (Finset.univ.filter (G.edge K C v)).card + (Finset.univ.filter (fun x => G.edge K C x v)).card

def fiberDegree (K : ℝ) (C : Finset V) (v : V) (e : I) : ℝ :=
  if G.active K C e then
    (if G.source e=v then (G.size C e : ℝ) else 0) +
    (if v ∈ G.targets e ∩ C then 1 else 0)
  else 0

omit [Fintype V] [Fintype I] in
lemma edge_unique (_K : ℝ) (_C : Finset V) (x y : V) {e f : I}
    (he : G.source e=x) (hf : G.source f=x) (hye : y ∈ G.targets e) (hyf : y ∈ G.targets f) : e=f := by
  by_contra hn
  exact Finset.disjoint_left.mp (G.disjoint e f hn (he.trans hf.symm)) hye hyf

def penalty (a : ℝ) (C : Finset V) : ℝ := a*(C.card : ℝ)*((C.card : ℝ)-1)

def objective (K a : ℝ) (C : Finset V) : ℝ := G.score K C-penalty a C

end Fibers
end WeakPinned.Core

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u5} {I : Type u6} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

def edgeSet (K : ℝ) (C : Finset V) : Finset (V × V) :=
  Finset.univ.filter (fun xy => G.edge K C xy.1 xy.2)

omit [Fintype V] in
lemma edge_indicator (K : ℝ) (C : Finset V) (x y : V) :
    (∑ e, if G.active K C e ∧ G.source e=x ∧ y ∈ G.targets e ∩ C then (1:ℝ) else 0)=
      if G.edge K C x y then 1 else 0 := by
  classical
  by_cases hh : G.edge K C x y
  · obtain ⟨e,he,hs,hy⟩ := hh
    rw [ite_eq_left ⟨e,he,hs,hy⟩,Finset.sum_eq_single e]
    · simp [he,hs,hy]
    · intro f _ hfe
      rw [ite_eq_right]
      rintro ⟨_,hfs,hfy⟩
      exact hfe (G.edge_unique K C x y hfs hs (Finset.mem_inter.mp hfy).1 (Finset.mem_inter.mp hy).1)
    · simp
  · have hn : ∀ e, ¬(G.active K C e ∧ G.source e=x ∧ y ∈ G.targets e ∩ C) :=
      fun e he => hh ⟨e,he⟩
    simp only [ite_eq_right (hn _),Finset.sum_const_zero,ite_eq_right hh]

lemma edgeSet_card (K : ℝ) (C : Finset V) :
    ((G.edgeSet K C).card : ℝ)=∑ e, if G.active K C e then (G.size C e : ℝ) else 0 := by
  classical
  have he (e : I) : (∑ xy : V × V, if G.active K C e ∧ G.source e=xy.1 ∧ xy.2 ∈ G.targets e ∩ C then (1:ℝ) else 0)=
      if G.active K C e then (G.size C e : ℝ) else 0 := by
    by_cases ha : G.active K C e
    · simp only [ha,true_and,Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (G.source e)]
      · simp only [true_and]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
        change ((Finset.univ.filter (fun y => y ∈ G.targets e ∩ C)).card : ℝ) = (G.size C e : ℝ)
        simp only [size,Finset.mem_inter]
        congr 2
        ext y
        simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    · simp [ha]
  change ((Finset.univ.filter (fun xy : V × V => G.edge K C xy.1 xy.2)).card : ℝ)=_
  rw [← Finset.sum_boole]
  simp_rw [← G.edge_indicator K C]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun e _ => he e)

end WeakPinned.Core.Fibers

namespace WeakPinned
open WeakPinned.Core

def fiberIndices (P : Finset Plane) (s : ℝ) : Finset (Plane × ℝ) :=
  (richPairs P s).image (fun xy => (xy.1,dist xy.2 xy.1))

lemma index_source_mem (P : Finset Plane) (s : ℝ) (e : fiberIndices P s) : e.val.1 ∈ P := by
  obtain ⟨xy,hxy,he⟩ := Finset.mem_image.mp e.property
  obtain ⟨hP,_,_⟩ := Finset.mem_filter.mp hxy
  rw [← he]
  exact (Finset.mem_product.mp hP).1

lemma index_radius_pos (P : Finset Plane) (s : ℝ) (e : fiberIndices P s) : 0 < e.val.2 := by
  obtain ⟨xy,hxy,he⟩ := Finset.mem_image.mp e.property
  obtain ⟨_,hne,_⟩ := Finset.mem_filter.mp hxy
  rw [← he]
  exact dist_pos.mpr hne.symm

def planarFibers (P : Finset Plane) (s : ℝ) : Core.Fibers P (fiberIndices P s) where
  source e := ⟨e.val.1,index_source_mem P s e⟩
  targets e := Finset.univ.filter (fun y : P => dist y.val e.val.1=e.val.2)
  no_loop e := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,dist_self]
    exact (index_radius_pos P s e).ne
  disjoint e f hef hsrc := by
    apply Finset.disjoint_left.mpr
    intro y hye hyf
    have hs : e.val.1=f.val.1 := congrArg Subtype.val hsrc
    have he := (Finset.mem_filter.mp hye).2
    have hf := (Finset.mem_filter.mp hyf).2
    apply hef
    apply Subtype.ext
    apply Prod.ext hs
    rw [← he,← hf,hs]

/-- Return from a subset of labelled vertices to the original plane, retaining
    all distances and its exact cardinality. -/
def planeSubset (P : Finset Plane) (C : Finset P) : Finset Plane := C.image Subtype.val

end WeakPinned

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.UniformCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

/-- Retain a specified family of the original fibers, restricted to D.
    This never alters a source or creates a new distance coincidence. -/
def retained (D : Finset V) (Q : I → Prop) [DecidablePred Q] : Fibers V I where
  source := G.source
  targets e := if Q e then G.targets e ∩ D else ∅
  no_loop e := by
    split_ifs
    · exact fun h => G.no_loop e (Finset.mem_inter.mp h).1
    · simp
  disjoint e f hef hs := by
    apply Finset.disjoint_left.mpr
    intro y hy hf
    by_cases he : Q e <;> by_cases hh : Q f
    · simp only [he,hh,ite_eq_left] at hy hf
      exact (Finset.disjoint_left.mp (G.disjoint e f hef hs))
        (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hf).1
    all_goals simp [he,hh] at hy hf

end WeakPinned.Core.Fibers

namespace WeakPinned
open scoped BigOperators

def heavyFiber (P : Finset Plane) (s K lam : ℝ) (C D : Finset P)
    (e : fiberIndices P s) : Prop :=
  (planarFibers P s).active K C e ∧
    lam*((planarFibers P s).size C e : ℝ) ≤ (planarFibers P s).size D e

instance instDecidablePredSubtypeProdPlaneRealMemFinsetFiberIndicesHeavyFiber (P : Finset Plane) (s K lam : ℝ) (C D : Finset P) :
    DecidablePred (heavyFiber P s K lam C D) := Classical.decPred _

end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology

def Theta (s : ℝ) : ℝ := limsup (fun n : ℕ => F n s) atTop

def criticalExponent : ℝ := sSup {s : ℝ | 0 < s ∧ 0 < Theta s}

end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology

def cutoff (s : ℝ) (N : ℕ) : ℝ := (N : ℝ)^s/Real.log N

end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology BigOperators

def heavyCount (P : Finset Plane) (s K lam : ℝ) (C D : Finset P) : ℝ :=
  ∑ e, if heavyFiber P s K lam C D e ∧ (planarFibers P s).source e ∈ D
    then ((planarFibers P s).size D e : ℝ) else 0

/-- Uniform subset bounds for the finite planar core. -/
structure PreparedCore (s γ c η : ℝ) (P : Finset Plane) (C : Finset P) : Prop where
  card_two : 2 ≤ C.card
  half : (P.card+1)/2 < C.card
  large_fiber : (C.card : ℝ)^γ ≤ cutoff s P.card
  lower : (Theta s-η)*(C.card : ℝ)*((C.card : ℝ)-1) ≤
    ((planarFibers P s).edgeSet (cutoff s P.card) C).card
  upper : (((planarFibers P s).edgeSet (cutoff s P.card) C).card : ℝ) ≤
    (Theta s+η/8)*(C.card : ℝ)*((C.card : ℝ)-1)
  degree : ∀ x ∈ C, 2*(Theta s-η)*((C.card : ℝ)-1) ≤
    (planarFibers P s).degree (cutoff s P.card) C x
  subset : ∀ D : Finset P,
    heavyCount P s (cutoff s P.card) (1/Real.log C.card) C D ≤
      (Theta s+η)*(D.card : ℝ)*((D.card : ℝ)-1)
  small : ∀ D : Finset P, (D.card : ℝ) ≤ (C.card : ℝ)^(1-c) →
    heavyCount P s (cutoff s P.card) (1/Real.log C.card) C D ≤
      η*(D.card : ℝ)*((D.card : ℝ)-1)

end WeakPinned

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.IncomingFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

def edges : Finset (V × V) := G.edgeSet (-1) Finset.univ

def edgeCount : ℝ := G.edges.card

def edgeLaw (x y : V) : ℝ := if (x,y) ∈ G.edges then 1/G.edgeCount else 0

def fiberWeight (e : I) : ℝ := (G.targets e).card / G.edgeCount

def incoming (y : V) : Finset V := Finset.univ.filter (fun x => (x,y) ∈ G.edges)

def incomingWeight (y : V) : ℝ := (G.incoming y).card / G.edgeCount

omit [Fintype I] in
lemma active_univ_neg_one (e : I) : G.active (-1) Finset.univ e := by
  refine ⟨Finset.mem_univ _,?_⟩
  have h := Nat.cast_nonneg (α:=ℝ) (G.size Finset.univ e)
  linarith

lemma edgeCount_eq : G.edgeCount = ∑ e, ((G.targets e).card : ℝ) := by
  unfold edgeCount edges
  rw [edgeSet_card]
  simp [G.active_univ_neg_one,size]

omit [Fintype I] in
lemma fiberWeight_nonneg (e : I) : 0 ≤ G.fiberWeight e := by
  unfold fiberWeight edgeCount
  positivity

lemma sum_fiberWeight (hG : 0 < G.edgeCount) : ∑ e, G.fiberWeight e=1 := by
  simp only [fiberWeight,← Finset.sum_div,← G.edgeCount_eq,div_self hG.ne']

end WeakPinned.Core.Fibers

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u3} {I : Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

abbrev Active (K : ℝ) (C : Finset V) := {e : I // G.active K C e}

instance instFintypeActive (K : ℝ) (C : Finset V) : Fintype (G.Active K C) := by
  classical
  exact Fintype.ofFinite _

def onCore (K : ℝ) (C : Finset V) : Fibers C (G.Active K C) where
  source e := ⟨G.source e.val,e.property.1⟩
  targets e := Finset.univ.filter (fun y : C => y.val ∈ G.targets e.val)
  no_loop e := by simpa using G.no_loop e.val
  disjoint e f hef hs := by
    apply Finset.disjoint_left.mpr
    intro y hye hyf
    have hne : e.val ≠ f.val := fun h => hef (Subtype.ext h)
    have hs' : G.source e.val=G.source f.val := congrArg Subtype.val hs
    exact Finset.disjoint_left.mp (G.disjoint _ _ hne hs')
      (Finset.mem_filter.mp hye).2 (Finset.mem_filter.mp hyf).2

end WeakPinned.Core.Fibers

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u5} {I : Type u6} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

def heavyCount (lam : ℝ) (D : Finset V) : ℝ :=
  ∑ e, if lam*((G.targets e).card : ℝ) ≤ (G.size D e : ℝ) ∧ G.source e ∈ D
    then (G.size D e : ℝ) else 0

end WeakPinned.Core.Fibers

namespace WeakPinned
open scoped BigOperators
open WeakPinned.Core

abbrev coreGraph (P : Finset Plane) (s : ℝ) (C : Finset P) :=
  (planarFibers P s).onCore (cutoff s P.card) C

structure PreparedGraph (V : Type u7) (I : Type u8) [Fintype V] [Fintype I] [DecidableEq V]
    (G : Fibers V I) (θ γ c η : ℝ) : Prop where
  card_ge : 2 ≤ Fintype.card V
  lower : (θ-η)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1) ≤ G.edgeCount
  upper : G.edgeCount ≤ (θ+η/8)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)
  degree : ∀ x, 2*(θ-η)*((Fintype.card V : ℝ)-1) ≤ G.degree (-1) Finset.univ x
  fiber : ∀ e, (Fintype.card V : ℝ)^γ < ((G.targets e).card : ℝ)
  subset : ∀ D, G.heavyCount (1/Real.log (Fintype.card V : ℝ)) D ≤ (θ+η)*(D.card : ℝ)*((D.card : ℝ)-1)
  small : ∀ D, (D.card : ℝ) ≤ (Fintype.card V : ℝ)^(1-c) →
    G.heavyCount (1/Real.log (Fintype.card V : ℝ)) D ≤ η*(D.card : ℝ)*((D.card : ℝ)-1)

end WeakPinned

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ArithmeticGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance SmallFiber
variable {V : Type u3} {I : Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

def qCell (C : Finset V) : ℝ := ∑ x ∈ C, ∑ y ∈ C, G.edgeLaw x y

end WeakPinned.Core.Fibers

namespace WeakPinned
open scoped BigOperators
open Variance SmallFiber Global
variable {V : Type u8} {I : Type u9} [Fintype V] [Fintype I] [DecidableEq V]
variable {G : Core.Fibers V I} {θ γ c η : ℝ}
variable {K : Type u10} [Field K] [NumberField K]
variable (Z₁ Z₂ : V → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

def overlapScale : ℝ := weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (pairCell Finset.univ)
def potentialScale : ℝ := ∑ x, prob Finset.univ x * totalPotential Z₁ Z₂ h₁ h₂ x

def smallOverlapScale (c : ℝ) : ℝ := weightedIntegral (totalMass Z₁ Z₂ h₁ h₂)
  (fun C => if (C.card : ℝ) ≤ (Fintype.card V : ℝ)^(1-c) then pairCell Finset.univ C else 0)

end WeakPinned

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.OverlapRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance
variable {V : Type u4} {I : Type u5} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

def retainedWeight (T : ℝ) (y : V) : ℝ := if T≤((G.incoming y).card:ℝ) then G.incomingWeight y else 0

def retainedSet (T : ℝ) (y : V) : Finset V := if T≤((G.incoming y).card:ℝ) then G.incoming y else Finset.univ

end WeakPinned.Core.Fibers

namespace WeakPinned
open Filter Variance Global
open scoped Topology BigOperators
variable {V : ℕ → Type u6} {I : ℕ → Type u7} {K : ℕ → Type u8} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

def fiberVariance (j : ℕ) : ℝ := weightedIntegral (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
  (varianceCell (G j).fiberWeight (G j).targets ((Fintype.card (V j):ℝ)^(1-c)))

def incomingVariance (j : ℕ) : ℝ := weightedIntegral (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
  (varianceCell ((G j).retainedWeight ((Fintype.card (V j):ℝ)^γ))
    ((G j).retainedSet ((Fintype.card (V j):ℝ)^γ)) ((Fintype.card (V j):ℝ)^(1-c)))

end WeakPinned

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.MinPotentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
open scoped BigOperators
variable {P : Type u3} [Fintype P] [DecidableEq P] (d : Depth P)

/-- The last level at which the vertex belongs to the nested giant. -/
def departure (x : P) : ℝ := sSup {r : ℝ | x ∈ d.giant r}

end WeakPinned.Hierarchy.Depth

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace WeakPinned.MinKernel
variable {P : Type u4} [Fintype P]

def step (a : ℝ) : ℝ → ℝ := (Set.Ioc 0 a).indicator (fun _ => 1)

def tail (p a : P → ℝ) (r : ℝ) : ℝ := ∑ x, p x*step (a x) r

def energy (p a b : P → ℝ) : ℝ := ∑ x, ∑ y, p x*p y*min (a x) (b y)

end WeakPinned.MinKernel

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
open scoped BigOperators
variable {P : Type u5} [Fintype P] [DecidableEq P]
variable (d : Depth P)

def outsideMass (p : P → ℝ) (r : ℝ) : ℝ := ∑ x, p x*d.outsideIndicator r x

end WeakPinned.Hierarchy.Depth

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.GlobalPotentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15 u16

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

def placeUnion : Finset (NumberField.FinitePlace K)  := by
  classical
  exact badPlaces Z₁ h₁ ∪ badPlaces Z₂ h₂

def average (f : Depth P → Depth P → ℝ) : ℝ :=
  (∑ v : NumberField.InfinitePlace K, Arithmetic.archWeight v *
    ∫ ω, f (arch Z₁ v ω) (arch Z₂ v ω) ∂Grid.fullLaw) +
  (Module.finrank ℚ K : ℝ)⁻¹ * ∑ v ∈ placeUnion Z₁ Z₂ h₁ h₂,
    f (finite Z₁ h₁ v) (finite Z₂ h₂ v)

def AverageIntegrable (f : Depth P → Depth P → ℝ) : Prop :=
  ∀ v : NumberField.InfinitePlace K,
    Integrable (fun ω => f (arch Z₁ v ω) (arch Z₂ v ω)) Grid.fullLaw

end WeakPinned.Global

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u4} [Fintype P] [DecidableEq P]
variable {K : Type u5} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit Z₁ Z₂ h₁ h₂ in
def potentialEval (p : P → ℝ) (d d' : Depth P) : ℝ := ∑ y, p y*(d.potential y+d'.potential y)
omit Z₁ Z₂ h₁ h₂ in
def massEval (q : Finset P → ℝ) (d d' : Depth P) : ℝ :=
  weightedIntegral d.mass q+weightedIntegral d'.mass q

end WeakPinned.Global

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.CutApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section

namespace WeakPinned.Cuts
open scoped BigOperators

def tent (δ u : ℝ) : ℝ := max 0 (min (u-δ) (1-δ-u))

def cutError (δ p a : ℝ) : ℝ := |tent δ p-tent δ a|+tent δ a*|p-a|
end WeakPinned.Cuts

namespace WeakPinned.Variance
open scoped BigOperators
open Cuts
variable {P : Type u1} {I : Type u2} [Fintype P] [Fintype I] [DecidableEq P]

noncomputable def familyCutError (w : I → ℝ) (B : I → Finset P) (δ : ℝ) (C : Finset P) : ℝ :=
  ∑ i, w i*cutError δ (cellProb (B i) C) (cellProb Finset.univ C)

end WeakPinned.Variance

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.TreeTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section

/- Finite tree transport by laminar-cut telescoping, without optimal-coupling selection. -/

noncomputable section
open scoped BigOperators
namespace WeakPinned.Cuts
variable {P : Type u1} [Fintype P] [DecidableEq P]

def Laminar (s : Finset (Finset P)) : Prop :=
  ∀ A ∈ s, ∀ B ∈ s, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

def value (s : Finset (Finset P)) (d : Finset P → ℝ) (a : ℝ) (x : P) : ℝ :=
  a + ∑ C ∈ s, if x ∈ C then d C else 0

def mass (b : P → ℝ) (C : Finset P) : ℝ := ∑ x ∈ C, b x

def ind (C : Finset P) (x : P) : ℝ := if x ∈ C then 1 else 0

def distance (s : Finset (Finset P)) (l : Finset P → ℝ) (x y : P) : ℝ :=
  ∑ C ∈ s, l C*|ind C x-ind C y|

def rootDistance (s : Finset (Finset P)) (l : Finset P → ℝ) (y : P) : ℝ :=
  ∑ C ∈ s, l C*ind C y

def coeff (l : Finset P → ℝ) (y : P) (C : Finset P) : ℝ :=
  if y ∈ C then -l C else l C

def cost (s : Finset (Finset P)) (l : Finset P → ℝ) (p q : P → ℝ) : ℝ :=
  ∑ C ∈ s, l C*|mass p C-mass q C|

def fluctuation (s : Finset (Finset P)) (l : Finset P → ℝ) (x x' y : P) : ℝ :=
  |distance s l x y-distance s l x' y|

def doubleMean (s : Finset (Finset P)) (l : Finset P → ℝ) (p : P → ℝ) (y : P) : ℝ :=
  ∑ x', p x'*∑ x, p x*fluctuation s l x x' y

end WeakPinned.Cuts

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.CutGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable (d : Depth P)

def allCuts : Finset (Finset P) := by
  classical
  exact Finset.univ.filter (fun C => ∃ r : ℝ, C ∈ d.cells r)

def cutAt (f : Finset P → ℝ) (C : Finset P) (r : ℝ) : ℝ :=
  if C ∈ d.cells r then f C else 0

def cutLength (f : Finset P → ℝ) (C : Finset P) : ℝ := ∫ r, d.cutAt f C r

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u2} [Fintype P] [DecidableEq P]
variable (d : Depth P)

def differenceTail (x y : P) (u : ℝ) : Finset P :=
  Finset.univ.filter (fun z => z=y ∨ (z ≠ x ∧ u ≤ d.value y z-d.value x z))

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u3} [Fintype P] [DecidableEq P]
variable (d : Depth P)

def aboveCell (f : Finset P → ℝ) (a : ℝ) (x : P) (r : ℝ) : ℝ :=
  if a < r then f (d.cell r x) else 0

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Tail
open MeasureTheory
open scoped NNReal
variable {P : Type u5} [Fintype P]

def step (a u : ℝ) : ℝ := if u ≤ a then 1 else 0

def law (b : ℝ) (p : P → ℝ) (f : P → ℝ) (u : ℝ) : ℝ := b+∑ z, p z*step (f z) u

end WeakPinned.Tail

namespace WeakPinned.Tail
open MeasureTheory Hierarchy
open scoped NNReal
variable {P : Type u7} [Fintype P] [DecidableEq P]

def offTwo (p : P → ℝ) (x y z : P) : ℝ := if z=x ∨ z=y then 0 else p z

end WeakPinned.Tail

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.FiberTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators

noncomputable section

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance Cuts
open scoped BigOperators
variable {P : Type u5} [Fintype P] [DecidableEq P]
variable {K : Type u6} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
include h₁ h₂

variable {I : Type u7} [Fintype I]
omit Z₁ Z₂ h₁ h₂ in
def fiberCutDiscrepancy (w : I → ℝ) (p : I → P → ℝ) (src : I → P) (δ : ℝ) (d d' : Depth P) : ℝ :=
  ∑ i, w i*∑ y, p i y*|distance d.allCuts (d.cutLength (fun C => tent δ (mass (p i) C))) (src i) y-
    rootDistance d'.allCuts (d'.cutLength (fun C => tent δ (mass (p i) C))) y|

end WeakPinned.Global
noncomputable section
namespace WeakPinned.Cuts
open MeasureTheory Hierarchy Variance
open scoped BigOperators
variable {P : Type u8} [Fintype P] [DecidableEq P]

def charge (d : Depth P) (δ : ℝ) (p a : P → ℝ) : ℝ :=
  ∑ C ∈ d.allCuts, d.cutLength (fun B => cutError δ (mass p B) (mass a B)) C

end WeakPinned.Cuts
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.TreeContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section

noncomputable section
namespace WeakPinned.Core.Fibers
open MeasureTheory Hierarchy Variance Cuts
open scoped BigOperators
variable {V : Type u3} {I : Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype V] in
lemma prob_nn (B : Finset V) (x : V) : 0≤prob B x := by
  unfold prob
  split_ifs <;> positivity

def conditionalSource (y : V) : V → ℝ :=
  if (G.incoming y).Nonempty then prob (G.incoming y) else prob Finset.univ

def omittedMass (T : ℝ) : ℝ := ∑ y, if ((G.incoming y).card:ℝ)<T then G.incomingWeight y else 0

end WeakPinned.Core.Fibers

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.UnboundedContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23

section
noncomputable section

namespace WeakPinned.Global
open Hierarchy Variance Cuts MeasureTheory
open scoped BigOperators
variable {P : Type u10} [Fintype P] [DecidableEq P]
variable {K : Type u11} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

def localTotalIntegral (f : Finset P → ℝ) (d d' : Depth P) : ℝ :=
  weightedIntegral d.mass f+weightedIntegral d'.mass f

end WeakPinned.Global

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.WeightedSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField
variable {P : Type u2} [Fintype P] [DecidableEq P]
variable {K : Type u3} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit Z₁ Z₂ h₁ h₂ in
def scaleEval (d d' : Depth P) : ℝ :=
  massEval (pairCell Finset.univ) d d' + potentialEval (prob Finset.univ) d d'

def archMean (f : Depth P → Depth P → ℝ) (v : InfinitePlace K) : ℝ :=
  ∫ ω, f (arch Z₁ v ω) (arch Z₂ v ω) ∂ Grid.fullLaw

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.LogBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

section
/- Finite log-distance normalization. The diagonal is excluded in the energy
   and counted explicitly, with mass 1/n, in the ball estimate. -/

noncomputable section
open scoped BigOperators
namespace WeakPinned.Bounded
variable {P : Type u1} [Fintype P] [DecidableEq P]

def logCost (u : P → ℂ) (x y : P) : ℝ :=
  if x=y then 0 else |Real.log ‖u x-u y‖|

def logAverage (u : P → ℂ) : ℝ :=
  (∑ x, ∑ y, logCost u x y)/((Fintype.card P : ℝ)*((Fintype.card P : ℝ)-1))

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField MeasureTheory
open scoped BigOperators

variable {P : Type u3} [Fintype P] [DecidableEq P]

def pairMean (f : P → P → ℝ) : ℝ := ∑ x, ∑ y, pairProb Finset.univ x y * f x y

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField MeasureTheory
open scoped BigOperators
variable {P : Type u4} [Fintype P] [DecidableEq P]

def singleScale (d : Depth P) : ℝ :=
  weightedIntegral d.mass (pairCell Finset.univ)+∑ x, prob Finset.univ x*d.potential x

def rawDepth (u : P → ℂ) (x y : P) : ℝ := -Real.log ‖u x-u y‖
def pairGridError (u : P → ℂ) (ω : Grid.FullSample) (x y : P) : ℝ :=
  if x=y then 0 else |Grid.error ω (u x) (u y)|

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open Variance
variable {P : Type u6} [Fintype P] [DecidableEq P]

def logNormalize (u : P → ℂ) (x : P) : ℂ := (Real.exp (pairMean (rawDepth u)) : ℂ)*u x

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.EmpiricalCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace WeakPinned.Bounded
attribute [local instance] Classical.propDecidable
local instance instMeasurableSpaceSphere_2 : MeasurableSpace Sphere := borel Sphere
local instance instBorelSpaceSphere_2 : BorelSpace Sphere := ⟨rfl⟩

variable {V : Type u1} {X : Type u2} [Fintype V] [MeasurableSpace X] [MeasurableSingletonClass X]

def uniformLaw (U : V → X) : Measure X := finiteLaw (fun _ => (Fintype.card V:ℝ)⁻¹) U

omit [MeasurableSingletonClass X] in
lemma uniformLaw_probability (U : V → X) (hn : 0<Fintype.card V) : IsProbabilityMeasure (uniformLaw U) := by
  apply finiteLaw_probability
  · intro; positivity
  · simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hn.ne')

def uniformProbability (U : V → X) (hn : 0<Fintype.card V) : ProbabilityMeasure X :=
  ⟨uniformLaw U,uniformLaw_probability U hn⟩

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ChartLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded

abbrev pairCoe : ℂ × ℂ → Sphere × Sphere := Prod.map OnePoint.some OnePoint.some
abbrev quadCoe : Quad ℂ → Quad Sphere := Prod.map OnePoint.some
  (Prod.map OnePoint.some pairCoe)
abbrev expandedCoe : Expanded ℂ → Expanded Sphere := Prod.map quadCoe (Prod.map pairCoe pairCoe)

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace WeakPinned.Bounded
open Variance
variable {V : Type u11} {I : Type u12} [Fintype V] [DecidableEq V] [Fintype I]
variable (G : Core.Fibers V I)
local instance instMeasurableSpaceSphere_3 : MeasurableSpace Sphere := borel Sphere

local instance instBorelSpaceSphere_3_r129475_1 : BorelSpace Sphere := ⟨rfl⟩
omit [Fintype I] in
lemma graph_edgeWeight_nonneg (r : I × V) :
    0≤edgeWeight G.fiberWeight (fun e => prob (G.targets e)) r :=
  mul_nonneg (G.fiberWeight_nonneg _) (Core.Fibers.prob_nn _ _)

omit [Fintype I] in
lemma graph_tripleWeight_nonneg (r : I × V × V × V) :
    0≤tripleWeight G.fiberWeight (fun e => prob (G.targets e)) r :=
  mul_nonneg (mul_nonneg (mul_nonneg (G.fiberWeight_nonneg _) (Core.Fibers.prob_nn _ _))
    (Core.Fibers.prob_nn _ _)) (Core.Fibers.prob_nn _ _)

def edgeProbability (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) : ProbabilityMeasure (Quad Sphere) :=
  finiteProbability (edgeWeight G.fiberWeight (fun e => prob (G.targets e)))
    (edgeValue G.source U₁ U₂) (graph_edgeWeight_nonneg G)
      (sum_edgeWeight _ _ (G.sum_fiberWeight hG) (fun e => sum_prob _ (hB e)))

def expandedProbability (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) : ProbabilityMeasure (Expanded Sphere) :=
  finiteProbability (tripleWeight G.fiberWeight (fun e => prob (G.targets e)))
    (tripleValue G.source U₁ U₂) (graph_tripleWeight_nonneg G)
      (sum_tripleWeight _ _ (G.sum_fiberWeight hG) (fun e => sum_prob _ (hB e)))

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.GridBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Grid

def level (ω : FullSample) (r : ℝ) : ℤ := ⌊(-r-ω.1.1)/Real.log 2⌋

def label (ω : FullSample) (r : ℝ) (z : ℂ) : ℤ × ℤ :=
  (bin ((2:ℝ)^level ω r) (shiftZ (level ω r) ω.2.1) (rotatePair ω.1.1 ω.1.2 z).1,
   bin ((2:ℝ)^level ω r) (shiftZ (level ω r) ω.2.2) (rotatePair ω.1.1 ω.1.2 z).2)

/-- Side length in the original (unrotated) plane, after scaling by exp m. -/
def side (ω : FullSample) (r m : ℝ) : ℝ := Real.exp (m+ω.1.1)*(2:ℝ)^level ω r

end WeakPinned.Grid

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.PartitionIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace WeakPinned.Bounded
open Hierarchy Variance
variable {P : Type u2} [Fintype P] [DecidableEq P]

variable {I : Type u3} [Fintype I]

def meanCellDiscrep (w : I → ℝ) (B : I → Finset P) (C : Finset P) : ℝ :=
  ∑ i,w i*|cellProb (B i) C-cellProb Finset.univ C|

end WeakPinned.Bounded

end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Hierarchy.Depth
variable {P : Type u4} [Fintype P] [DecidableEq P]
variable (d : Depth P)

def transformCell (C : Finset P) : Finset P := if Fintype.card P<2*C.card then Cᶜ else C

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Bounded
open Hierarchy Variance
variable {P : Type u5} {I : Type u6} [Fintype P] [DecidableEq P] [Fintype I]

def testDiscrep (w : I → ℝ) (B : I → Finset P) (f : P → ℝ) : ℝ :=
  ∑ i,w i*|(∑ x,prob (B i) x*f x)-(∑ x,prob Finset.univ x*f x)|

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.VarianceRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

section
noncomputable section
open scoped BigOperators Topology ZeroAtInfty
open Filter MeasureTheory
namespace WeakPinned.Bounded

local instance instMeasurableSpaceSphere_4_r129475_1 : MeasurableSpace Sphere := borel Sphere
local instance instBorelSpaceSphere_4_r129475_1 : BorelSpace Sphere := ⟨rfl⟩
def sphereTest (f : C(Sphere,ℝ)) : C₀(ℂ,ℝ) where
  toFun := fun z => f (z:Sphere)-f OnePoint.infty
  continuous_toFun := (f.continuous.comp OnePoint.continuous_coe).sub continuous_const
  zero_at_infty' := by
    have hco : Tendsto ((↑) : ℂ → Sphere) (cocompact ℂ) (𝓝 OnePoint.infty) :=
      OnePoint.tendsto_coe_infty.mono_left cocompact_le_coclosedCompact
    simpa using ((f.continuous.tendsto OnePoint.infty).comp hco).sub_const (f OnePoint.infty)

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace WeakPinned.Bounded
open Variance
local instance instMeasurableSpaceSphere_6 : MeasurableSpace Sphere := borel Sphere

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace WeakPinned.Bounded
local instance instMeasurableSpaceSphere_7 : MeasurableSpace Sphere := borel Sphere

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.MeasureLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction NNReal ENNReal
namespace WeakPinned.Bounded
local instance instMeasurableSpaceSphere_8 : MeasurableSpace Sphere := borel Sphere
local instance instBorelSpaceSphere_8 : BorelSpace Sphere := ⟨rfl⟩

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded

local instance instMeasurableSpaceSphere_9 : MeasurableSpace Sphere := borel Sphere

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.FiniteObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded
local instance instMeasurableSpaceSphere_10 : MeasurableSpace Sphere := borel Sphere

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace WeakPinned.Bounded
open Variance
local instance instMeasurableSpaceSphere_11 : MeasurableSpace Sphere := borel Sphere
local instance instBorelSpaceSphere_11_r129475_1 : BorelSpace Sphere := ⟨rfl⟩
local instance instMeasurableSingletonClassQuadSphere_1_r129475_1 : MeasurableSingletonClass (Quad Sphere) := inferInstance
local instance instMeasurableSingletonClassProdSphere_1_r129475_1 : MeasurableSingletonClass ((Sphere × Sphere) × (Sphere × Sphere)) := inferInstance
local instance instMeasurableSingletonClassExpandedSphere_1_r129475_1 : MeasurableSingletonClass (Expanded Sphere) := Prod.instMeasurableSingletonClass
variable {V : Type u1} {I : Type u2} [Fintype V] [DecidableEq V] [Fintype I]
variable (G : Core.Fibers V I)

def zEquation : Set (Expanded ℂ) := {r | (r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
    (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)}
def wEquation : Set (Expanded ℂ) := {r | (r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
    (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)}

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.LimitObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded
local instance instMeasurableSpaceSphere_12 : MeasurableSpace Sphere := borel Sphere
local instance instBorelSpaceSphere_12 : BorelSpace Sphere := ⟨rfl⟩

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.NormalizedGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace WeakPinned.Bounded
local instance instMeasurableSpaceSphere_13 : MeasurableSpace Sphere := borel Sphere

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ArithmeticSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

section
noncomputable section

noncomputable section

namespace WeakPinned.Transfer
open MvPolynomial

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Complexified variables; the extra variable forces a square root of -1
    into the field, so every archimedean place is complex. -/
abbrev Variables (ι : Type u5) := Option (Bool × ι)

def secondCoord (b : Bool) (z : Plane) : ℂ :=
  if b then ⟨z 0, -z 1⟩ else ⟨z 0, z 1⟩

def complexAssignment {ι : Type u6} (x : ι → Plane) : Variables ι → ℂ :=
  fun j => j.elim Complex.I (fun bi => secondCoord bi.1 (x bi.2))

def distancePoly {ι : Type u7} (a b : ι) : MvPolynomial (Variables ι) ℚ :=
  (X (some (false, a)) - X (some (false, b))) *
  (X (some (true, a)) - X (some (true, b)))

end WeakPinned.Transfer

end
end
end

end OAI
end


