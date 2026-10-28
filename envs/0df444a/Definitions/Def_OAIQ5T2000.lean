-- Prove2me | Definitions.Def_OAIQ5T2000
-- name    : OAIQ5T2000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T09:20:54.916227+00:00
-- url     : https://prove2.me/theorems/e594ed71-656c-4dab-a83f-3f52e689ff9a
-- title:
--   Definitions bundle OAIQ5T2000 of the split of OpenAI, Sharp One-Third Stability of Brenier Maps
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem358.one_third_stability`, carved from OpenAI's openai/math development (OpenAI, *Sharp One-Third Stability of Brenier Maps*, OpenAI Math Release, September 25, 2026, result family 374, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 338 declarations of OpenAI's Lean: 123 definitions, 4 inductive types or structures, 6 instances and 205 theorems. The definitions and types are `OAI.Problem358.AffineHalfspaceSpeed.speed`, `OAI.Problem358.AffinePlaneGraph.faceCoefficient`, `OAI.Problem358.AffinePlaneGraph.graph`, `OAI.Problem358.AffinePlaneGraph.interfaceGraph`, `OAI.Problem358.AffinePlaneGraph.intrinsicCutCoefficient`, `OAI.Problem358.AffinePlaneGraph.tangentProjection`, `OAI.Problem358.AffinePlaneGraph.unitNormal`, `OAI.Problem358.AffineSlice.fiber`, `OAI.Problem358.CellGeometry.closedCell`, `OAI.Problem358.CellGeometry.faceMoment`, `OAI.Problem358.CellGeometry.massLinearMap`, `OAI.Problem358.CellGeometry.normalizedConfigInclusion`, `OAI.Problem358.CellGeometry.normalizedMassMap`, `OAI.Problem358.CellGeometry.positiveMassConfigurations`, `OAI.Problem358.CellLaplacian.apply`, `OAI.Problem358.CellLaplacian.coordinateLinearMap`, `OAI.Problem358.CellLaplacian.linearMap`, `OAI.Problem358.CellLaplacian.massResidual`, `OAI.Problem358.CellLaplacian.normalizedEquiv`, `OAI.Problem358.CellLaplacian.normalizedLinearMap`, `OAI.Problem358.CellLaplacian.normalizedSpace`, `OAI.Problem358.CellLaplacian.siteFlux`, `OAI.Problem358.CellLaplacian.weightedMean`, `OAI.Problem358.CellLaplacian.zeroSumProjection`, `OAI.Problem358.ClosedCoverConnectivity.maximalCell`, `OAI.Problem358.ConvexTriangularSampler.conditionalDensity`, `OAI.Problem358.ConvexTriangularSampler.scalarDomain`, `OAI.Problem358.ConvexTriangularSampler.sectionBody`, `OAI.Problem358.ConvexTriangularSampler.sectionDensity`, `OAI.Problem358.ConvexTriangularSampler.valid`, `OAI.Problem358.FaceDerivative.cellLinearMap`, `OAI.Problem358.FaceDerivative.linearMap`, `OAI.Problem358.FaceDerivative.pairVariation`, `OAI.Problem358.FiniteAffine.Maximizes`, `OAI.Problem358.FiniteAffine.potential`, `OAI.Problem358.FiniteAffine.sourceDual`, `OAI.Problem358.FiniteAffine.targetDual`, `OAI.Problem358.FiniteAffine.targetDualAt`, `OAI.Problem358.FiniteCoupling.IsOptimal`, `OAI.Problem358.FiniteCoupling.cost` and 87 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Brenier, in whole or in part: `Brenier_AffineCertificate`, `Brenier_AffineTies`, `Brenier_Argmax`, `Brenier_Atomic`, `Brenier_CanonicalLaplacian`, `Brenier_CellContinuity`, `Brenier_CellDerivative`, `Brenier_CellEnergy`, `Brenier_CellFaces`, `Brenier_CellGeometry`, `Brenier_CellMeasure`, `Brenier_Conjugacy`, `Brenier_ConvexDensity`, `Brenier_ConvexQuantiles`, `Brenier_CutDerivative`, `Brenier_DensityCDF`, `Brenier_FaceContinuity`, `Brenier_FacetConnectivity`, `Brenier_FiniteCoupling`, `Brenier_FixedMass`, `Brenier_Interfaces`, `Brenier_Laplacian`, `Brenier_LineDerivative`, `Brenier_MassDerivative`, `Brenier_MaxCalculus`, `Brenier_Midpoint`, `Brenier_Minimizers`, `Brenier_MomentAlgebra`, `Brenier_MovingTrace`, `Brenier_NormalizedSections`, `Brenier_Potential`, `Brenier_PrefixSampling`, `Brenier_PrefixSections`, `Brenier_PrescribedCells`, `Brenier_Sections`, `Brenier_StationaryMoment`, `Brenier_SupportingInterpolation`, `Brenier_SurfaceCoordinates`, `Brenier_SurfaceMeasure`, `Brenier_TriangularDomination`, `Brenier_TriangularRecursion`, `Brenier_Uniform`.
--
--   **Imports.** It imports the published bundle `Def_Brenier`.
--
--   **Imported by** (directly, in this split): the statement `OAI.Problem358.FixedMassIntercepts.exists_actual_atomic_intercept_path`; the proofs of `OAI.Problem358.FixedMassIntercepts.exists_actual_atomic_intercept_path` and `OAI.Problem358.one_third_stability`.
-- source:
--   OpenAI, Sharp One-Third Stability of Brenier Maps, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 374; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Brenier at commit adc7f12

import Mathlib
import Definitions.Def_Brenier

section
-- module Solutions.OAIQ5_T2.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_AffineCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Problem358.FiniteAffine

variable {ι F : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The convex potential used by a finite-affine transport map. -/
def potential (y : ι → F) (c : ι → ℝ) (x : F) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪x, y i⟫ + c i)

/-- An index is active when its affine form dominates every other form. -/
def Maximizes (y : ι → F) (c : ι → ℝ) (x : F) (i : ι) : Prop :=
  ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y i⟫ + c i

/-- The source term of the quadratic Kantorovich certificate. -/
def sourceDual (y : ι → F) (c : ι → ℝ) (x : F) : ℝ :=
  ‖x‖ ^ 2 - 2 * potential y c x

/-- The target term at a specified site. -/
def targetDualAt (y : ι → F) (c : ι → ℝ) (i : ι) : ℝ :=
  ‖y i‖ ^ 2 + 2 * c i

/-- A Borel extension of the target term from the finite set of sites. -/
def targetDual (y : ι → F) (c : ι → ℝ) (z : F) : ℝ :=
  ∑ i, ({y i} : Set F).indicator (fun _ => targetDualAt y c i) z

end Problem358.FiniteAffine

end

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_AffineTies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace

namespace Problem358

/-- A level set of a nonzero linear functional given by an inner product is null. -/
theorem haar_inner_level_null {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsAddHaarMeasure μ] {v : V} (hv : v ≠ 0) (c : ℝ) :
    μ {x : V | ⟪v, x⟫_ℝ = c} = 0 := by
  let S : AffineSubspace ℝ V :=
    (affineSpan ℝ ({c} : Set ℝ)).comap (innerₗ V v).toAffineMap
  have hS : (S : Set V) = {x : V | ⟪v, x⟫_ℝ = c} := by
    ext x
    simp [S]
  rw [← hS]
  apply addHaar_affineSubspace μ S
  intro htop
  have h0 : (0 : V) ∈ S := htop ▸ AffineSubspace.mem_top ℝ V 0
  have hv' : v ∈ S := htop ▸ AffineSubspace.mem_top ℝ V v
  rw [← SetLike.mem_coe, hS] at h0 hv'
  simp only [Set.mem_ofPred_eq, inner_zero_right] at h0 hv'
  exact hv (inner_self_eq_zero.mp (hv'.trans h0.symm))

/-- Distinct affine slopes can agree only on a Haar-null hyperplane. -/
theorem haar_affine_tie_null {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsAddHaarMeasure μ] {v w : V} (hvw : v ≠ w)
    (a b : ℝ) : μ {x : V | ⟪x, v⟫_ℝ + a = ⟪x, w⟫_ℝ + b} = 0 := by
  convert haar_inner_level_null μ (sub_ne_zero.mpr hvw) (b - a) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, inner_sub_left]
  rw [real_inner_comm v x, real_inner_comm w x]
  constructor <;> intro h <;> linarith

/-- In a countable affine family, equality of values almost everywhere forces equality of slopes. -/
theorem ae_affine_tie_implies_slopes_eq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsAddHaarMeasure μ] {ι : Type*} [Countable ι]
    (y : ι → V) (c : ι → ℝ) :
    ∀ᵐ x ∂μ, ∀ i j, ⟪x, y i⟫_ℝ + c i = ⟪x, y j⟫_ℝ + c j → y i = y j := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases h : y i = y j
  · exact Filter.Eventually.of_forall (fun _ _ => h)
  · have hne : ∀ᵐ x ∂μ, ⟪x, y i⟫_ℝ + c i ≠ ⟪x, y j⟫_ℝ + c j := by
      rw [ae_iff]
      simpa only [not_not] using haar_affine_tie_null μ h (c i) (c j)
    exact hne.mono (fun _ hx heq => (hx heq).elim)

/-- Uniform restrictions preserve the nullity of affine ties; no volume assumptions
    on the source set are needed for this fact. -/
theorem uniform_ae_affine_tie_implies_slopes_eq {d : ℕ} (K : Set (E d))
    {ι : Type*} [Countable ι] (y : ι → E d) (c : ι → ℝ) :
    ∀ᵐ x ∂uniformMeasure K, ∀ i j,
      ⟪x, y i⟫_ℝ + c i = ⟪x, y j⟫_ℝ + c j → y i = y j := by
  have hac : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  exact hac.ae_le (ae_affine_tie_implies_slopes_eq volume y c)

end Problem358

end

/-!+# Generic lines avoid affine subspaces of codimension at least two

This is the general-position step used in the cell-connectivity argument.
It does not assert that a nonempty cell intersection has positive surface measure.
-/

section

open scoped RealInnerProductSpace

namespace Problem358.TripleCell

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The affine score whose slope is `y` and whose intercept is `c`. -/
def score (y : V) (c : ℝ) (x : V) : ℝ := ⟪x, y⟫ + c

end Problem358.TripleCell

end

namespace Problem358.GenericSegment

open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def affineScore (v : V) (c : ℝ) (x : V) : ℝ := inner ℝ v x + c

end Problem358.GenericSegment

/-! General-position segments for finite strictly active affine families. -/

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Argmax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Problem358

/-- A finite nonempty family of measurable scores has a measurable maximizing
index. The maximizing score is measurable as well; no measurability assumption
on individual index singletons is needed. -/
theorem exists_measurable_finset_argmax {X ι : Type*}
    [MeasurableSpace X] [MeasurableSpace ι]
    (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i)) :
    ∀ (s : Finset ι), s.Nonempty →
      ∃ g : X → ι, Measurable g ∧ (∀ x, g x ∈ s) ∧
        Measurable (fun x => f (g x) x) ∧
        ∀ x i, i ∈ s → f i x ≤ f (g x) x := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro hs
      exact False.elim (Finset.not_nonempty_empty hs)
  | @insert a s ha ih =>
      intro hs
      by_cases hsn : s.Nonempty
      · obtain ⟨g, hg, hgm, hfg, hmax⟩ := ih hsn
        let p : X → Prop := fun x => f (g x) x ≤ f a x
        let k : X → ι := fun x => if p x then a else g x
        have hp : MeasurableSet {x | p x} := measurableSet_le hfg (hf a)
        have hk : Measurable k := Measurable.ite hp measurable_const hg
        have hfk : Measurable (fun x => f (k x) x) := by
          have hval : (fun x => f (k x) x) =
              (fun x => if p x then f a x else f (g x) x) := by
            funext x
            simp only [k]
            split_ifs <;> rfl
          rw [hval]
          exact Measurable.ite hp (hf a) hfg
        refine ⟨k, hk, ?_, hfk, ?_⟩
        · intro x
          dsimp [k]
          split_ifs
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hgm x)
        · intro x i hi
          dsimp [k]
          split_ifs with hx
          · rcases Finset.mem_insert.mp hi with rfl | hi
            · exact le_rfl
            · exact (hmax x i hi).trans hx
          · rcases Finset.mem_insert.mp hi with rfl | hi
            · exact (lt_of_not_ge hx).le
            · exact hmax x i hi
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
        subst s
        refine ⟨fun _ => a, measurable_const, ?_, hf a, ?_⟩
        · intro x
          simp
        · intro x i hi
          have hia : i = a := by simpa using hi
          subst i
          exact le_rfl

/-- A measurable choice of an index maximizing a finite measurable family. -/
theorem exists_measurable_argmax {X ι : Type*}
    [MeasurableSpace X] [MeasurableSpace ι] [Fintype ι] [Nonempty ι]
    (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i)) :
    ∃ g : X → ι, Measurable g ∧ Measurable (fun x => f (g x) x) ∧
      ∀ x i, f i x ≤ f (g x) x := by
  classical
  obtain ⟨g, hg, _, hfg, hmax⟩ :=
    exists_measurable_finset_argmax f hf Finset.univ Finset.univ_nonempty
  exact ⟨g, hg, hfg, fun x i => hmax x i (Finset.mem_univ i)⟩

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Atomic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

/-- The coupling which matches equally indexed atoms without splitting mass. -/
def atomicMatchingPlan {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) : Measure (E d × E d) :=
  ∑ i, w i • Measure.dirac (y i, z i)

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Uniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.UniformSource

variable {d : ℕ} {K : Set (E d)}

/-- Normalization of a compact body with nonempty interior gives a probability measure. -/
theorem probability (hK : IsCompact K) (hinterior : (interior K).Nonempty) :
    IsProbabilityMeasure (uniformMeasure K) := by
  constructor
  rw [uniformMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Measure.measure_pos_of_nonempty_interior volume hinterior).ne'
    hK.measure_ne_top

theorem supported (hK : MeasurableSet K) : IsSupported (uniformMeasure K) K := by
  simp [IsSupported, uniformMeasure, Measure.restrict_apply hK.compl]

theorem ae_mem (hK : MeasurableSet K) : ∀ᵐ x ∂uniformMeasure K, x ∈ K :=
  ae_iff.mpr (supported hK)

/-- Continuous functions on a compact source are integrable after normalization,
including the zero-volume case. -/
theorem integrable_continuousOn {F : Type*} [NormedAddCommGroup F]
    (hK : IsCompact K) {f : E d → F} (hf : ContinuousOn f K) :
    Integrable f (uniformMeasure K) := by
  by_cases hv : volume K = 0
  · have hzero : uniformMeasure K = 0 := by
      simp [uniformMeasure, Measure.restrict_eq_zero.mpr hv]
    rw [hzero]
    exact integrable_zero_measure
  · exact (hf.integrableOn_compact hK).smul_measure (ENNReal.inv_ne_top.mpr hv)

end Problem358.UniformSource

end

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace Problem358

/-- A level set of a real scalar product is an affine subspace. -/
def innerLevelSubspace {d : ℕ} (a : E d) (b : ℝ) : AffineSubspace ℝ (E d) where
  carrier := {x | inner ℝ a x = b}
  smul_vsub_vadd_mem' := by
    intro t p q r hp hq hr
    change inner ℝ a p = b at hp
    change inner ℝ a q = b at hq
    change inner ℝ a r = b at hr
    change inner ℝ a (t • (p - q) + r) = b
    simp only [inner_add_right, inner_smul_right, inner_sub_right, hp, hq, hr]
    ring

end Problem358

end

noncomputable section
open Set MeasureTheory
open scoped ENNReal Topology

namespace Problem358.UniformSource

/-- The topological support of normalized volume on a convex body is the whole body. -/
theorem subset_support {d : ℕ} {K : Set (E d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : (interior K).Nonempty) :
    K ⊆ (uniformMeasure K).support := by
  have hi : interior K ⊆ (uniformMeasure K).support := by
    intro x hx
    apply (Measure.mem_support_iff_forall x).mpr
    intro U hU
    have hpos : 0 < volume (U ∩ K) :=
      Measure.measure_pos_of_mem_nhds volume (Filter.inter_mem hU (mem_interior_iff_mem_nhds.mp hx))
    rw [uniformMeasure, Measure.smul_apply, Measure.restrict_apply' hK.measurableSet,
      smul_eq_mul]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hK.measure_ne_top) hpos.ne'
  have hclosure : closure (interior K) ⊆ (uniformMeasure K).support :=
    closure_minimal hi Measure.isClosed_support
  have hKclosure : closure (interior K) = K := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne, hK.isClosed.closure_eq]
  rwa [hKclosure] at hclosure

end Problem358.UniformSource

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace Problem358
namespace CellGeometry

variable {d : ℕ} {ι : Type*}

/-- The closed cell of one affine branch, including ties. -/
def closedCell (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i : ι) : Set (E d) :=
  {x | x ∈ K ∧ ∀ j, inner ℝ x (y j) + c j ≤ inner ℝ x (y i) + c i}

end CellGeometry
end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace Problem358

/-- The closed cell of an affine score, before restriction to the source set. -/
def scoreCell {d : ℕ} {ι : Type*} (y : ι → E d) (c : ι → ℝ) (i : ι) : Set (E d) :=
  {x | ∀ j, inner ℝ (y j) x + c j ≤ inner ℝ (y i) x + c i}

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.NormalizedCell

variable {X : Type*} [MeasurableSpace X]

/-- The probability law obtained by normalizing the restriction to a positive finite cell. -/
def measure (ρ : Measure X) (P : Set X) : Measure X :=
  (ρ P)⁻¹ • ρ.restrict P

end Problem358.NormalizedCell

namespace Problem358

/-- The probability law obtained by conditioning a measure on a positive finite cell. -/
def normalizedCellLaw {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) (P : Set X) : Measure X :=
  (ρ P)⁻¹ • ρ.restrict P

variable {X V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Measure X} {P : Set X}

/-- Multiplying a normalized cell law by its original mass recovers the restricted measure. -/
lemma mass_smul_normalizedCellLaw (hpos : ρ P ≠ 0) (hfin : ρ P ≠ ∞) :
    ENNReal.ofReal (ρ.real P) • normalizedCellLaw ρ P = ρ.restrict P := by
  rw [Measure.real_def, ENNReal.ofReal_toReal hfin, normalizedCellLaw, smul_smul,
    ENNReal.mul_inv_cancel hpos hfin, one_smul]

end Problem358

end

/-! Coordinate assembly and source normalization for genuine vector cell moments.
The scalar moving-cell calculus is an explicit input; no differentiability of a
cell or of its coefficients is assumed implicitly. -/

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_MovingTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators Topology RealInnerProductSpace

namespace Problem358.MovingCellTrace

/-- The indicator of a nonnegative affine cut. -/
def cutIndicator (r : ℝ) : ℝ := (Set.Ici (0 : ℝ)).indicator (fun _ => 1) r

end Problem358.MovingCellTrace

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CutDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace Problem358.AffineHalfspaceSpeed

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The normal velocity of an affine cut, in a fixed transverse coordinate. -/
def speed (n u v : V) (r h : ℝ) (x : V) : ℝ :=
  (r + ⟪v, x⟫_ℝ) / (⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ)

end Problem358.AffineHalfspaceSpeed

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Interfaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Topology

namespace Problem358

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- If an affine slice meets the interior of a convex set, its relative interior
contains no new boundary points of the ambient convex set. -/
theorem interior_affine_preimage_eq (f : U →ᵃ[ℝ] V) (hf : Continuous f)
    {K : Set V} (hK : Convex ℝ K) (hmeet : (f ⁻¹' interior K).Nonempty) :
    interior (f ⁻¹' K) = f ⁻¹' interior K := by
  apply Subset.antisymm ?_ (preimage_interior_subset_interior_preimage hf)
  intro x hx
  obtain ⟨p, hp⟩ := hmeet
  have hone := AffineMap.lineMap_apply_one (k := ℝ) p x
  obtain ⟨t, ht1, ht⟩ := AffineMap.lineMap_continuous.tendsto' _ _ hone |>.eventually_mem
    (mem_interior_iff_mem_nhds.mp hx) |>.exists_gt
  have hft : AffineMap.lineMap (f p) (f x) t ∈ K := by
    simpa only [Set.mem_preimage, f.apply_lineMap] using ht
  change f x ∈ interior K
  apply hK.openSegment_interior_self_subset_interior hp hft
  nth_rw 1 [← AffineMap.lineMap_apply_zero (k := ℝ) (f p) (f x), ← image_openSegment]
  exact ⟨1, Ioo_subset_openSegment ⟨zero_lt_one, ht1⟩,
    AffineMap.lineMap_apply_one (k := ℝ) (f p) (f x)⟩

/-- Boundary commutes with an affine slice through the interior of a closed convex set. -/
theorem frontier_affine_preimage_eq (f : U →ᵃ[ℝ] V) (hf : Continuous f)
    {K : Set V} (hclosed : IsClosed K) (hK : Convex ℝ K)
    (hmeet : (f ⁻¹' interior K).Nonempty) :
    frontier (f ⁻¹' K) = f ⁻¹' frontier K := by
  rw [frontier, frontier, (hclosed.preimage hf).closure_eq, hclosed.closure_eq,
    interior_affine_preimage_eq f hf hK hmeet, Set.preimage_sdiff]

/-- The ambient boundary cuts an interior-crossing affine slice in a Haar-null set.
This applies to the hyperplane and lower-dimensional fibers in cell differentiation. -/
theorem haar_affine_preimage_frontier_null [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [IsAddHaarMeasure μ]
    (f : U →ᵃ[ℝ] V) {K : Set V} (hclosed : IsClosed K) (hK : Convex ℝ K)
    (hmeet : (f ⁻¹' interior K).Nonempty) : μ (f ⁻¹' frontier K) = 0 := by
  rw [← frontier_affine_preimage_eq f f.continuous_of_finiteDimensional hclosed hK hmeet]
  exact (Convex.affine_preimage f hK).addHaar_frontier μ

/-- Continuous integrands restricted to a convex body are continuous almost
 everywhere along an affine slice crossing its interior. -/
theorem ae_continuousAt_indicator_on_affine_slice [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [IsAddHaarMeasure μ]
    (f : U →ᵃ[ℝ] V) {K : Set V} (hclosed : IsClosed K) (hK : Convex ℝ K)
    (hmeet : (f ⁻¹' interior K).Nonempty)
    {W : Type*} [TopologicalSpace W] [Zero W] {g : V → W}
    (hg : ContinuousOn g (interior K)) :
    ∀ᵐ x ∂μ, ContinuousAt (K.indicator g) (f x) := by
  have haway : ∀ᵐ x ∂μ, f x ∉ frontier K := by
    rw [ae_iff]
    simpa only [not_not, Set.preimage] using
      haar_affine_preimage_frontier_null μ f hclosed hK hmeet
  exact haway.mono fun x hx => hg.continuousAt_indicator hx

/-- Moving-slice indicators converge almost everywhere before invoking dominated
convergence; no differentiability in the transverse parameter is required. -/
theorem ae_tendsto_indicator_on_affine_slice [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [IsAddHaarMeasure μ]
    (f : U →ᵃ[ℝ] V) {K : Set V} (hclosed : IsClosed K) (hK : Convex ℝ K)
    (hmeet : (f ⁻¹' interior K).Nonempty)
    {W : Type*} [TopologicalSpace W] [Zero W] {g : V → W}
    (hg : ContinuousOn g (interior K))
    {A : Type*} {l : Filter A} {F : A → U → V}
    (hF : ∀ᵐ x ∂μ, Filter.Tendsto (fun a => F a x) l (𝓝 (f x))) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun a => K.indicator g (F a x)) l
      (𝓝 (K.indicator g (f x))) := by
  filter_upwards [ae_continuousAt_indicator_on_affine_slice μ f hclosed hK hmeet hg,
    hF] with x hx hFx
  exact hx.tendsto.comp hFx

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_SurfaceCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Topology

namespace Problem358.TangentNormalCoordinates

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Tangential directions to the normal `v`. -/
abbrev Tangent (v : V) := (ℝ ∙ v)ᗮ

/-- The unit-speed isometry from the real line to the span of a nonzero normal. -/
def normalLineEquiv (n : V) (hn : n ≠ 0) : ℝ ≃ₗᵢ[ℝ] (ℝ ∙ n) :=
  (LinearIsometryEquiv.toSpanUnitSingleton ((‖n‖⁻¹ : ℝ) • n)
    (norm_smul_inv_norm hn)).trans
    (LinearIsometryEquiv.ofEq _ _
      (Submodule.span_singleton_smul_eq
        (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hn))) n))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem normalLineEquiv_coe [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (hn : n ≠ 0) (t : ℝ) :
    ((normalLineEquiv n hn t : ℝ ∙ n) : V) = t • ((‖n‖⁻¹ : ℝ) • n) := by
  simp [normalLineEquiv]

/-- Full orthogonal normal/tangent coordinates for an arbitrary nonzero normal. -/
def normalEquiv (n : V) (hn : n ≠ 0) :
    WithLp 2 (ℝ × Tangent n) ≃ₗᵢ[ℝ] V :=
  (LinearIsometryEquiv.withLpProdCongr 2 (normalLineEquiv n hn)
    (LinearIsometryEquiv.refl ℝ (Tangent n))).trans
    (ℝ ∙ n).orthogonalDecomposition.symm

/-- Unit-speed normal displacement plus a tangential vector. -/
def normalMap (n : V) (p : ℝ × Tangent n) : V :=
  p.1 • ((‖n‖⁻¹ : ℝ) • n) + (p.2 : V)

@[simp]
theorem normalEquiv_apply (n : V) (hn : n ≠ 0) (p : ℝ × Tangent n) :
    normalEquiv n hn (WithLp.toLp 2 p) = normalMap n p := by
  simp [normalEquiv, normalMap, Submodule.orthogonalDecomposition_symm_apply]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem inner_normalMap [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (hn : n ≠ 0) (p : ℝ × Tangent n) :
    ⟪n, normalMap n p⟫_ℝ = p.1 * ‖n‖ := by
  have ht : ⟪n, (p.2 : V)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.2.property
  have hn0 : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  simp only [normalMap, inner_add_right, inner_smul_right, ht, add_zero,
    real_inner_self_eq_norm_sq]
  field_simp

/-- Translated coordinates for a hyperplane through `base`. -/
def affineMap (n base : V) (p : ℝ × Tangent n) : V :=
  base + normalMap n p

@[simp]
theorem inner_affineMap (n : V) (hn : n ≠ 0) (base : V) (p : ℝ × Tangent n) :
    ⟪n, affineMap n base p⟫_ℝ = ⟪n, base⟫_ℝ + p.1 * ‖n‖ := by
  simp [affineMap, inner_add_right, inner_normalMap n hn]

/-- Tangent-first affine coordinates, convenient for iterated strip integrals. -/
def tangentMap (n base : V) (p : Tangent n × ℝ) : V :=
  affineMap n base (p.2, p.1)

end Problem358.TangentNormalCoordinates

end

noncomputable section

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace Problem358.AffinePlaneGraph

variable {X V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A nearby affine plane written as a graph in one fixed transverse direction.
The denominator is nonzero precisely when the direction remains transverse. -/
def graph (base : X → V) (u n : V) (c : ℝ) (x : X) : V :=
  base x - ((⟪n, base x⟫ + c) / ⟪n, u⟫) • u

end Problem358.AffinePlaneGraph

end

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Topology

namespace Problem358.TangentNormalCoordinates

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem inner_unitNormal [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (hn : n ≠ 0) :
    ⟪n, (‖n‖⁻¹ : ℝ) • n⟫_ℝ = ‖n‖ := by
  have h : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  simp only [inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

end Problem358.TangentNormalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace BigOperators

namespace Problem358.PositiveCellFullDerivative

open TangentNormalCoordinates MovingCellTrace

/-- The signed face integral in a full affine-cell variation. -/
def faceVariation {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Set (E d)) (y v : ι → E d) (c r : ι → ℝ)
    (w : E d → ℝ) (i j : ι) (z : E d) : ℝ :=
  ∫ a : Tangent (y i - y j),
    ((r i - r j + ⟪v i - v j, z + (a : E d)⟫_ℝ) / ‖y i - y j‖) *
      (K.indicator w (z + (a : E d)) *
        ∏ k ∈ (Finset.univ.erase i).erase j,
          cutIndicator ((⟪z + (a : E d), y i⟫_ℝ + c i) -
            (⟪z + (a : E d), y k⟫_ℝ + c k)))

end Problem358.PositiveCellFullDerivative

end

/-! Actual vector moment and real mass differentials for positive affine cells.
This specializes the proved scalar moving-cell formula, not an assumed derivative. -/

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_SurfaceMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intrinsic affine-plane measure and orientation invariance

Surface measure is defined by translating canonical volume on a linear subspace.
The resulting ambient measure does not depend on the chosen basepoint in the
affine plane. In particular reversing a hyperplane equation preserves its measure.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped RealInnerProductSpace

namespace Problem358.IntrinsicSurface

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Canonical volume on a subspace, translated into the ambient space. -/
def planeMeasure (W : Submodule ℝ E) (base : E) : Measure E :=
  Measure.map (fun w : W => base + (w : E)) volume

/-- A canonical basepoint of the affine equation `inner n x + c = 0`. -/
def normalBase (n : E) (c : ℝ) : E := (-c / ‖n‖ ^ 2) • n

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem normalBase_neg (n : E) (c : ℝ) :
    normalBase (-n) (-c) = normalBase n c := by
  simp [normalBase, neg_div, neg_smul]

/-- Intrinsic measure of a hyperplane, with a fixed canonical basepoint. -/
def hyperplaneMeasure (n : E) (c : ℝ) : Measure E :=
  planeMeasure (ℝ ∙ n)ᗮ (normalBase n c)

/-- Intrinsic tie-plane measure for a pair of affine scores. -/
def interfaceMeasure (y z : E) (a b : ℝ) : Measure E :=
  hyperplaneMeasure (y - z) (a - b)

end Problem358.IntrinsicSurface

end

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace Problem358.TransverseSurface

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Height on an affine plane, measured along a fixed transverse direction. -/
def height (n u : V) (c : ℝ) (x : V) : ℝ := (⟪n, x⟫ + c) / ⟪n, u⟫

/-- Retraction onto an affine plane along the transverse direction. -/
def retract (n u : V) (c : ℝ) (x : V) : V := x - height n u c x • u

end Problem358.TransverseSurface

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical first-moment coefficients of common affine-cell faces. -/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*}

/-- The vector face coefficient used by both mass site-motion and stationary
first-moment differentiation. The diagonal is zero by the normal-length factor. -/
def faceMoment (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i j : ι) : E d :=
  ((volume K).toReal * ‖y i - y j‖)⁻¹ •
    ∫ x in closedCell K y c i ∩ closedCell K y c j, x
      ∂IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)

@[simp] theorem faceMoment_self (K : Set (E d)) (y : ι → E d)
    (c : ι → ℝ) (i : ι) : faceMoment K y c i i = 0 := by
  simp [faceMoment]

end Problem358.CellGeometry

end

/-! Identification of the cut-product trace with the genuine common cell face. -/

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_FaceContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Problem358.AffinePlaneGraph

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Unit transverse vector of a nonzero reference normal. -/
def unitNormal (n : E d) : E d := ‖n‖⁻¹ • n

/-- Fixed tangential coordinates relative to a chosen point of the reference plane. -/
def tangentProjection (n z : E d) : E d → (ℝ ∙ n)ᗮ :=
  fun x => (ℝ ∙ n)ᗮ.orthogonalProjectionOnto (x - z)

/-- Reference-normal graph coordinates for a varying selected interface. -/
def interfaceGraph (n₀ z : E d) (a : ι → E d) (b : ι → ℝ) (i j : ι) :
    (ℝ ∙ n₀)ᗮ → E d :=
  graph (fun x => z + (x : E d)) (unitNormal n₀) (a i - a j) (b i - b j)

/-- A transverse face coefficient; the fixed-plane measure and transverse
normal factor together are the disintegration coefficient in cell derivatives. -/
def faceCoefficient (K : Set (E d)) (n₀ z : E d) (J : Finset ι)
    (i j : ι) (w : E d → ℝ) (p : (ι → E d) × (ι → ℝ)) : ℝ :=
  (∫ x : (ℝ ∙ n₀)ᗮ,
    K.indicator w (interfaceGraph n₀ z p.1 p.2 i j x) *
      ∏ k ∈ J, MovingCellTrace.cutIndicator
        (⟪interfaceGraph n₀ z p.1 p.2 i j x, p.1 i - p.1 k⟫ +
          (p.2 i - p.2 k))) /
    ⟪p.1 i - p.1 j, unitNormal n₀⟫

end Problem358.AffinePlaneGraph

end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Problem358.AffinePlaneGraph

variable {d : ℕ} {ι : Type*}

/-- The normalized intrinsic integral over an interface with additional affine
cuts. Unlike the local `faceCoefficient`, this definition uses no reference
normal or basepoint. -/
def intrinsicCutCoefficient (K : Set (E d)) (J : Finset ι) (i j : ι)
    (w : E d → ℝ) (p : (ι → E d) × (ι → ℝ)) : ℝ :=
  (∫ x, K.indicator w x * ∏ k ∈ J, MovingCellTrace.cutIndicator
    (⟪x, p.1 i - p.1 k⟫ + (p.2 i - p.2 k))
    ∂IntrinsicSurface.hyperplaneMeasure (p.1 i - p.1 j) (p.2 i - p.2 j)) /
      ‖p.1 i - p.1 j‖

end Problem358.AffinePlaneGraph

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_FacetConnectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connectivity of finite closed covers and active-cell intersection graphs. -/

noncomputable section
open Set

namespace Problem358

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]

/-- Distinct cover members are adjacent when they meet. -/
def closedCoverGraph (s : ι → Set X) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (s i ∩ s j).Nonempty
  symm := ⟨by
    intro i j hij
    exact ⟨hij.1.symm, by simpa only [inter_comm] using hij.2⟩⟩
  loopless := ⟨by
    intro i hi
    exact hi.1 rfl⟩

namespace ClosedCoverConnectivity

/-- The closed weak-maximizer cell of a continuous finite family. -/
def maximalCell (K : Set X) (f : ι → X → ℝ) (i : ι) : Set X :=
  {x | x ∈ K ∧ ∀ j, f j x ≤ f i x}

end ClosedCoverConnectivity

end Problem358

end

/-! Connectivity through strict two-cell interfaces. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Problem358.PositiveFacet

variable {V W ι : Type*} [TopologicalSpace V] [TopologicalSpace W] [Finite ι]

/-- Edges are interior ties with no third maximizing branch. For affine
families these are precisely the local witnesses of positive-area facets. -/
def strictTieGraph (K : Set V) (f : ι → V → ℝ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ ∃ x ∈ interior K, f i x = f j x ∧
    ∀ k, k ≠ i → k ≠ j → f k x < f i x
  symm := ⟨by
    rintro i j ⟨hij, x, hx, heq, hlt⟩
    exact ⟨hij.symm, x, hx, heq.symm, fun k hkj hki =>
      (hlt k hki hkj).trans_eq heq⟩⟩
  loopless := ⟨fun i hi => hi.1 rfl⟩

end Problem358.PositiveFacet

end

/-! Connectivity of the strict-facet graph of an active affine partition. -/

/-! Positive surface measures on every edge of the connected strict-facet graph. -/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped Topology InnerProductSpace

namespace Problem358.PositiveFacet

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Finite ι]

/-- The surface face in a tie hyperplane, translated from an arbitrary point
of that plane. This is an intrinsic measure domain, not ambient volume. -/
def surfaceFace (K : Set E) (y : ι → E) (c : ι → ℝ) (i j : ι) (base : E) :
    Set ((ℝ ∙ (y i - y j))ᗮ) :=
  {w | base + (w : E) ∈ K ∧
    TripleCell.score (y i) (c i) (base + (w : E)) =
      TripleCell.score (y j) (c j) (base + (w : E)) ∧
    ∀ k, TripleCell.score (y k) (c k) (base + (w : E)) ≤
      TripleCell.score (y i) (c i) (base + (w : E))}

end Problem358.PositiveFacet

end

/-! Positive-mass convex affine partitions have a connected positive-facet graph. -/

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Laplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebraic facts about the weighted cell-adjacency Laplacian. -/

noncomputable section
open scoped BigOperators

namespace Problem358
namespace CellLaplacian

variable {ι : Type*} [Fintype ι]

/-- The intercept derivative of the cell masses, written in coordinates. -/
def apply (g : ι → ι → ℝ) (q : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, g i j * (q i - q j)

lemma sum_apply (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (q : ι → ℝ) : ∑ i, apply g q i = 0 := by
  have hswap : (∑ i, ∑ j, g i j * q j) = ∑ i, ∑ j, g i j * q i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  simp only [apply, mul_sub, Finset.sum_sub_distrib]
  rw [hswap, sub_self]

lemma energy_identity (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (q : ι → ℝ) :
    2 * (∑ i, q i * apply g q i) = ∑ i, ∑ j, g i j * (q i - q j) ^ 2 := by
  have hswap : (∑ i, ∑ j, q j * (g i j * (q j - q i))) =
      ∑ i, ∑ j, q i * (g i j * (q i - q j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  calc
    2 * (∑ i, q i * apply g q i) =
        (∑ i, ∑ j, q i * (g i j * (q i - q j))) +
        (∑ i, ∑ j, q j * (g i j * (q j - q i))) := by
      rw [hswap]
      have he : (∑ i, q i * apply g q i) =
          ∑ i, ∑ j, q i * (g i j * (q i - q j)) := by
        simp only [apply, Finset.mul_sum]
      rw [he]
      ring
    _ = ∑ i, ∑ j, (q i * (g i j * (q i - q j)) +
        q j * (g i j * (q j - q i))) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma eq_of_positive_edge_of_apply_eq_zero
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (q : ι → ℝ)
    (hq : apply g q = 0) {i j : ι} (hij : 0 < g i j) : q i = q j := by
  have he : (∑ i, ∑ j, g i j * (q i - q j) ^ 2) = 0 := by
    rw [← energy_identity g hsym q, hq]
    simp
  have hrow : (∑ j, g i j * (q i - q j) ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      Finset.sum_nonneg (fun l _ => mul_nonneg (hnonneg k l) (sq_nonneg _)))).mp he i
      (Finset.mem_univ i)
  have hterm : g i j * (q i - q j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      mul_nonneg (hnonneg i k) (sq_nonneg _))).mp hrow j (Finset.mem_univ j)
  have hsquare : (q i - q j) ^ 2 = 0 := (mul_eq_zero.mp hterm).resolve_left hij.ne'
  nlinarith [sq_nonneg (q i - q j)]

/-- Connectivity may be supplied by any graph whose edges have positive weights. -/
lemma constant_of_apply_eq_zero
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (q : ι → ℝ) (hq : apply g q = 0) : ∃ c : ℝ, ∀ i, q i = c := by
  let : Nonempty ι := hG.nonempty
  let i₀ : ι := Classical.choice inferInstance
  refine ⟨q i₀, fun i => ?_⟩
  have hwalk : ∀ {u v : ι}, G.Walk u v → q u = q v := by
    intro u v p
    induction p with
    | nil => rfl
    | @cons u v w huv p ih =>
        exact (eq_of_positive_edge_of_apply_eq_zero g hsym hnonneg q hq
          (hpos u v huv)).trans ih
  obtain ⟨p⟩ := hG i i₀
  exact hwalk p

/-- The mass-weighted normalization eliminates the constant kernel. -/
lemma eq_zero_of_normalized_kernel
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m q : ι → ℝ) (hm : ∑ i, m i = 1)
    (hq : apply g q = 0) (hmean : ∑ i, m i * q i = 0) : q = 0 := by
  obtain ⟨c, hc⟩ := constant_of_apply_eq_zero g hsym hnonneg G hG hpos q hq
  have hc0 : c = 0 := by
    simp_rw [hc] at hmean
    rw [← Finset.sum_mul, hm, one_mul] at hmean
    exact hmean
  funext i
  simpa [hc0] using hc i

lemma pairing_symmetric (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (q r : ι → ℝ) :
    (∑ i, apply g q i * r i) = ∑ i, q i * apply g r i := by
  have hswap : (∑ i, ∑ j, g i j * q j * r i) =
      ∑ i, ∑ j, g i j * q i * r j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  calc
    (∑ i, apply g q i * r i) =
        (∑ i, ∑ j, g i j * q i * r i) -
        (∑ i, ∑ j, g i j * q j * r i) := by
      simp only [apply, Finset.sum_mul, mul_sub, sub_mul, Finset.sum_sub_distrib]
    _ = (∑ i, ∑ j, g i j * q i * r i) -
        (∑ i, ∑ j, g i j * q i * r j) := by rw [hswap]
    _ = ∑ i, q i * apply g r i := by
      simp only [apply, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
        apply Finset.sum_congr rfl <;> intro j hj <;> ring

/-- The cell Laplacian as an operator on Euclidean coordinate space. -/
def linearMap (g : ι → ι → ℝ) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun q := WithLp.toLp 2 (apply g q)
  map_add' q r := by
    ext i
    simp only [PiLp.add_apply, apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  map_smul' c q := by
    ext i
    simp only [PiLp.smul_apply, apply, smul_eq_mul,
      RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

@[simp] lemma linearMap_apply (g : ι → ι → ℝ) (q : EuclideanSpace ℝ ι) (i : ι) :
    linearMap g q i = apply g q i := rfl

lemma linearMap_isSymmetric (g : ι → ι → ℝ)
    (hsym : ∀ i j, g i j = g j i) : (linearMap g).IsSymmetric := by
  intro q r
  simpa only [PiLp.inner_apply, Real.inner_apply, linearMap_apply, mul_comm]
    using pairing_symmetric g hsym q r

/-- The image of a connected symmetric cell Laplacian is the zero-sum hyperplane. -/
lemma mem_range_iff_sum_eq_zero
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (z : EuclideanSpace ℝ ι) :
    z ∈ LinearMap.range (linearMap g) ↔ ∑ i, z i = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    exact sum_apply g hsym q
  · intro hz
    have hr : LinearMap.range (linearMap g) =
        (LinearMap.ker (linearMap g))ᗮ := by
      rw [← (linearMap_isSymmetric g hsym).orthogonal_range,
        Submodule.orthogonal_orthogonal]
    rw [hr, Submodule.mem_orthogonal]
    intro q hq
    have hzero : linearMap g q = 0 := hq
    have hq' : apply g q = 0 := by
      funext i
      exact congrArg (fun x : EuclideanSpace ℝ ι => x i) hzero
    obtain ⟨c, hc⟩ := constant_of_apply_eq_zero g hsym hnonneg G hG hpos q hq'
    simp only [PiLp.inner_apply, Real.inner_apply]
    simp_rw [hc]
    rw [← Finset.mul_sum, hz, mul_zero]

lemma exists_apply_eq_of_sum_eq_zero
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (z : ι → ℝ) (hz : ∑ i, z i = 0) : ∃ q : ι → ℝ, apply g q = z := by
  have hz' : WithLp.toLp 2 z ∈ LinearMap.range (linearMap g) :=
    (mem_range_iff_sum_eq_zero g hsym hnonneg G hG hpos _).mpr hz
  obtain ⟨q, hq⟩ := hz'
  refine ⟨q, funext (fun i => ?_)⟩
  exact congrArg (fun x : EuclideanSpace ℝ ι => x i) hq

lemma apply_sub_const (g : ι → ι → ℝ) (q : ι → ℝ) (c : ℝ) :
    apply g (fun i => q i - c) = apply g q := by
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

lemma apply_sub (g : ι → ι → ℝ) (q r : ι → ℝ) :
    apply g (q - r) = apply g q - apply g r := by
  funext i
  simp only [apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The mass-weighted normalization determines the solution of the cell equation uniquely. -/
lemma existsUnique_normalized_solution
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m z : ι → ℝ) (hm : ∑ i, m i = 1) (hz : ∑ i, z i = 0) :
    ∃! q : ι → ℝ, apply g q = z ∧ ∑ i, m i * q i = 0 := by
  obtain ⟨q, hq⟩ := exists_apply_eq_of_sum_eq_zero g hsym hnonneg G hG hpos z hz
  let c := ∑ i, m i * q i
  let q' : ι → ℝ := fun i => q i - c
  have hq' : apply g q' = z := (apply_sub_const g q c).trans hq
  have hmean : ∑ i, m i * q' i = 0 := by
    simp only [q', mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hm, one_mul]
    exact sub_self c
  refine ⟨q', ⟨hq', hmean⟩, ?_⟩
  rintro r ⟨hr, hrmean⟩
  have hkernel : apply g (r - q') = 0 := by rw [apply_sub, hr, hq', sub_self]
  have hdiffmean : ∑ i, m i * (r - q') i = 0 := by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, hrmean, hmean, sub_self]
  have hdiff := eq_zero_of_normalized_kernel g hsym hnonneg G hG hpos m (r - q')
    hm hkernel hdiffmean
  exact sub_eq_zero.mp hdiff

end CellLaplacian
end Problem358

namespace Problem358.CellLaplacian

variable {ι : Type*} [Fintype ι]

/-- The weighted intercept normalization functional. -/
def weightedMean (m : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun q := ∑ i, m i * q i
  map_add' q r := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c q := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm (m _) c]
    exact (Finset.mul_sum _ _ _).symm

/-- The hyperplane of intercepts with weighted average zero. -/
def normalizedSpace (m : ι → ℝ) : Submodule ℝ (ι → ℝ) := (weightedMean m).ker

@[simp] lemma mem_normalizedSpace (m q : ι → ℝ) :
    q ∈ normalizedSpace m ↔ ∑ i, m i * q i = 0 := Iff.rfl

/-- The weighted Laplacian on coordinate functions, without a change of norm. -/
def coordinateLinearMap (g : ι → ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := apply g
  map_add' q r := by
    funext i
    simp only [apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  map_smul' c q := by
    funext i
    simp only [apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

@[simp] lemma coordinateLinearMap_apply (g : ι → ι → ℝ) (q : ι → ℝ) :
    coordinateLinearMap g q = apply g q := rfl

/-- The normalized mass Jacobian, with codomain the zero-sum mass variations. -/
def normalizedLinearMap (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (m : ι → ℝ) : normalizedSpace m →ₗ[ℝ] normalizedSpace (fun _ : ι => 1) :=
  ((coordinateLinearMap g).comp (normalizedSpace m).subtype).codRestrict
    (normalizedSpace (fun _ : ι => 1)) (by
      intro q
      change (∑ i, 1 * apply g q i) = 0
      simpa only [one_mul] using sum_apply g hsym q)

@[simp] lemma normalizedLinearMap_apply (g : ι → ι → ℝ)
    (hsym : ∀ i j, g i j = g j i) (m : ι → ℝ) (q : normalizedSpace m) :
    (normalizedLinearMap g hsym m q : ι → ℝ) = apply g q := rfl

lemma normalizedLinearMap_bijective
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1) :
    Function.Bijective (normalizedLinearMap g hsym m) := by
  constructor
  · intro q r hqr
    apply Subtype.ext
    have happly : apply g q = apply g r := congrArg Subtype.val hqr
    have hkernel : apply g ((q : ι → ℝ) - r) = 0 := by
      rw [apply_sub, happly, sub_self]
    have hmean : ∑ i, m i * ((q : ι → ℝ) - r) i = 0 := by
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      change weightedMean m q - weightedMean m r = 0
      rw [q.property, r.property, sub_self]
    exact sub_eq_zero.mp
      (eq_zero_of_normalized_kernel g hsym hnonneg G hG hpos m _ hm hkernel hmean)
  · intro z
    have hz : ∑ i, (z : ι → ℝ) i = 0 := by
      simpa only [mem_normalizedSpace, one_mul] using z.property
    obtain ⟨q, hq, _⟩ :=
      existsUnique_normalized_solution g hsym hnonneg G hG hpos m z hm hz
    exact ⟨⟨q, hq.2⟩, Subtype.ext hq.1⟩

/-- The invertible normalized cell-mass Jacobian.
This is the continuous-linear-equivalence interface needed by the implicit function theorem.
Its existence makes no assertion of a uniform bound on the inverse. -/
def normalizedEquiv
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1) :
    normalizedSpace m ≃L[ℝ] normalizedSpace (fun _ : ι => 1) :=
  (LinearEquiv.ofBijective (normalizedLinearMap g hsym m)
    (normalizedLinearMap_bijective g hsym hnonneg G hG hpos m hm)).toContinuousLinearEquiv

@[simp] lemma normalizedEquiv_apply
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1) (q : normalizedSpace m) :
    (normalizedEquiv g hsym hnonneg G hG hpos m hm q : ι → ℝ) = apply g q := rfl

/-- Applying the inverse solves the normalized cell-mass equation. -/
@[simp] lemma apply_normalizedEquiv_symm
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (z : normalizedSpace (fun _ : ι => 1)) :
    apply g ((normalizedEquiv g hsym hnonneg G hG hpos m hm).symm z) = z :=
  congrArg Subtype.val ((normalizedEquiv g hsym hnonneg G hG hpos m hm).apply_symm_apply z)

end Problem358.CellLaplacian

end

/-! Implicit-function glue for normalized prescribed cell masses. -/

noncomputable section
open scoped BigOperators Topology ContDiff

namespace Problem358.CellLaplacian
variable {ι : Type*} [Fintype ι]

/-- A continuous linear projection onto zero-sum mass variations. -/
def zeroSumProjection (m : ι → ℝ) (hm : ∑ i, m i = 1) :
    (ι → ℝ) →L[ℝ] normalizedSpace (fun _ : ι => 1) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => ⟨fun i => z i - (∑ j, z j) * m i, by
      simp only [mem_normalizedSpace, one_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hm, mul_one, sub_self]⟩
    map_add' := by
      intro z w
      apply Subtype.ext
      funext i
      change z i + w i - (∑ j, (z j + w j)) * m i =
        (z i - (∑ j, z j) * m i) + (w i - (∑ j, w j) * m i)
      rw [Finset.sum_add_distrib]
      ring
    map_smul' := by
      intro a z
      apply Subtype.ext
      funext i
      change a * z i - (∑ j, a * z j) * m i =
        a * (z i - (∑ j, z j) * m i)
      rw [← Finset.mul_sum]
      ring }

@[simp] theorem zeroSumProjection_apply (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (z : ι → ℝ) (i : ι) :
    (zeroSumProjection m hm z : ι → ℝ) i = z i - (∑ j, z j) * m i := rfl

/-- The mass residual for an ordinary coordinate-valued mass map. -/
def massResidual {P : Type*} (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (M : P × normalizedSpace m → (ι → ℝ)) :
    P × normalizedSpace m → normalizedSpace (fun _ : ι => 1) :=
  fun x => zeroSumProjection m hm (M x - m)

end Problem358.CellLaplacian

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CanonicalLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized cell Laplacian with its actual intrinsic geometric weights.

All graph hypotheses in the algebraic inverse theorem are discharged here for
positive-mass convex affine cells. No analytic differentiability assertion is
made: the resulting equivalence is ready to identify with the mass Jacobian.
-/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace BigOperators

namespace Problem358.PositiveFacet

variable {d : ℕ} {ι : Type*}

/-- Canonical normalized intrinsic area of the common closed cell face. -/
def canonicalFaceWeight (K : Set (E d)) (y : ι → E d) (c : ι → ℝ)
    (i j : ι) : ℝ :=
  (IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)
    (CellGeometry.closedCell K y c i ∩ CellGeometry.closedCell K y c j)).toReal /
      ((volume K).toReal * ‖y i - y j‖)

@[simp] theorem canonicalFaceWeight_self (K : Set (E d)) (y : ι → E d)
    (c : ι → ℝ) (i : ι) : canonicalFaceWeight K y c i i = 0 := by
  simp [canonicalFaceWeight]

end Problem358.PositiveFacet

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem358.CellLaplacian

variable {ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The mass variation caused by motion of the sites, in face coordinates. -/
def siteFlux (b : ι → ι → V) (v : ι → V) (i : ι) : ℝ :=
  ∑ j, inner ℝ (b i j) (v i - v j)

end Problem358.CellLaplacian

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Conjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace Problem358

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The convex conjugate with the source variable restricted to `K`. -/
def restrictedConjugate (K : Set V) (u : V → ℝ) (y : V) : ℝ :=
  sSup ((fun x => inner ℝ x y - u x) '' K)

end Problem358

end

/-! # Supporting slopes at differentiability points

The elementary local step used to identify the equality locus of a
Fenchel certificate.  No convexity assumption is needed once a supporting
inequality is supplied.
-/

/-! # Almost-everywhere uniqueness of supporting slopes

Rademacher's theorem and the null boundary of a convex set provide the
regularity needed by the local supporting-slope lemmas.
-/

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_DensityCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace Problem358

/-- A positive continuous density on an open bounded interval. Endpoint values are irrelevant. -/
structure PositiveIntervalDensity where
  lower : ℝ
  upper : ℝ
  density : ℝ → ℝ
  lower_lt_upper : lower < upper
  integrable : IntervalIntegrable density volume lower upper
  continuousOn : ContinuousOn density (Ioo lower upper)
  positive : ∀ x ∈ Ioo lower upper, 0 < density x
  integral_one : (∫ x in lower..upper, density x) = 1

namespace PositiveIntervalDensity

variable (D : PositiveIntervalDensity)

/-- The cumulative integral starting at the lower endpoint. -/
def cdf (x : ℝ) : ℝ := ∫ t in D.lower..x, D.density t

@[simp] lemma cdf_lower : D.cdf D.lower = 0 := by simp [cdf]
@[simp] lemma cdf_upper : D.cdf D.upper = 1 := D.integral_one

lemma cdf_continuousOn : ContinuousOn D.cdf (Icc D.lower D.upper) := by
  change ContinuousOn (fun x : ℝ => ∫ t in D.lower..x, D.density t) (Icc D.lower D.upper)
  simpa only [uIcc_of_le D.lower_lt_upper.le] using
    (intervalIntegral.continuousOn_primitive_interval' D.integrable left_mem_uIcc)

lemma cdf_hasDerivAt {x : ℝ} (hx : x ∈ Ioo D.lower D.upper) :
    HasDerivAt D.cdf (D.density x) x := by
  have hx' : x ∈ uIcc D.lower D.upper := by
    rw [uIcc_of_le D.lower_lt_upper.le]
    exact ⟨hx.1.le, hx.2.le⟩
  exact intervalIntegral.integral_hasDerivAt_right
    (D.integrable.mono_set (uIcc_subset_uIcc left_mem_uIcc hx'))
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo D.continuousOn x hx)
    (D.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hx))

lemma cdf_strictMonoOn : StrictMonoOn D.cdf (Icc D.lower D.upper) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) D.cdf_continuousOn
  intro x hx
  have hx' : x ∈ Ioo D.lower D.upper := by simpa only [interior_Icc] using hx
  rw [(D.cdf_hasDerivAt hx').deriv]
  exact D.positive x hx'

lemma cdf_image : D.cdf '' Icc D.lower D.upper = Icc (0 : ℝ) 1 := by
  simpa only [D.cdf_lower, D.cdf_upper] using
    D.cdf_continuousOn.image_Icc_of_monotoneOn D.lower_lt_upper.le
      D.cdf_strictMonoOn.monotoneOn

/-- Cumulative integration is an order isomorphism between the two compact intervals. -/
def cdfOrderIso : Icc D.lower D.upper ≃o Icc (0 : ℝ) 1 :=
  (StrictMonoOn.orderIso D.cdf (Icc D.lower D.upper) D.cdf_strictMonoOn).trans
    (OrderIso.setCongr _ _ D.cdf_image)

/-- The inverse cumulative map, including its continuous endpoint extension. -/
def quantile (s : Icc (0 : ℝ) 1) : ℝ := (D.cdfOrderIso.symm s).1

lemma quantile_mem (s : Icc (0 : ℝ) 1) : D.quantile s ∈ Icc D.lower D.upper :=
  (D.cdfOrderIso.symm s).2

lemma quantile_continuous : Continuous D.quantile := by
  exact continuous_subtype_val.comp D.cdfOrderIso.symm.toHomeomorph.continuous

lemma cdf_quantile (s : Icc (0 : ℝ) 1) : D.cdf (D.quantile s) = s := by
  have h := congrArg Subtype.val (D.cdfOrderIso.apply_symm_apply s)
  exact h

lemma quantile_mem_interior {s : Icc (0 : ℝ) 1} (hs : (s : ℝ) ∈ Ioo (0 : ℝ) 1) :
    D.quantile s ∈ Ioo D.lower D.upper := by
  have hm := D.quantile_mem s
  have hc := D.cdf_quantile s
  constructor
  · apply lt_of_le_of_ne hm.1
    intro heq
    rw [← heq, D.cdf_lower] at hc
    linarith [hs.1]
  · apply lt_of_le_of_ne hm.2
    intro heq
    rw [heq, D.cdf_upper] at hc
    linarith [hs.2]

/-- A globally continuous extension of the quantile, constant outside the unit interval. -/
def quantileReal (s : ℝ) : ℝ := D.quantile (Set.projIcc 0 1 (by norm_num) s)

lemma quantileReal_continuous : Continuous D.quantileReal :=
  D.quantile_continuous.comp continuous_projIcc

lemma quantileReal_eq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    D.quantileReal s = D.quantile ⟨s, hs⟩ := by
  rw [quantileReal, Set.projIcc_of_mem _ hs]

lemma cdf_quantileReal {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    D.cdf (D.quantileReal s) = s := by
  rw [D.quantileReal_eq s hs]
  exact D.cdf_quantile ⟨s, hs⟩

lemma quantileReal_mem_interior {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    D.quantileReal s ∈ Ioo D.lower D.upper := by
  rw [D.quantileReal_eq s ⟨hs.1.le, hs.2.le⟩]
  exact D.quantile_mem_interior hs

/-- The one-dimensional inverse-density derivative used in the triangular coupling. -/
lemma quantileReal_hasDerivAt {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt D.quantileReal (D.density (D.quantileReal s))⁻¹ s := by
  apply HasDerivAt.of_local_left_inverse D.quantileReal_continuous.continuousAt
    (D.cdf_hasDerivAt (D.quantileReal_mem_interior hs))
    (D.positive _ (D.quantileReal_mem_interior hs)).ne'
  filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
  exact D.cdf_quantileReal ⟨ht.1.le, ht.2.le⟩

lemma cdf_image_Ioo : D.cdf '' Ioo D.lower D.upper = Ioo (0 : ℝ) 1 := by
  simpa only [D.cdf_lower, D.cdf_upper] using
    D.cdf_continuousOn.image_Ioo_of_strictMonoOn D.lower_lt_upper.le D.cdf_strictMonoOn

lemma quantileReal_mem (s : ℝ) : D.quantileReal s ∈ Icc D.lower D.upper :=
  D.quantile_mem _

lemma quantileReal_cdf {x : ℝ} (hx : x ∈ Icc D.lower D.upper) :
    D.quantileReal (D.cdf x) = x := by
  have hc : D.cdf x ∈ Icc (0 : ℝ) 1 := by
    rw [← D.cdf_image]
    exact ⟨x, hx, rfl⟩
  apply D.cdf_strictMonoOn.injOn (D.quantileReal_mem _) hx
  exact D.cdf_quantileReal hc

/-- The probability distribution with the given density, restricted to its open interval. -/
def densityMeasure : Measure ℝ :=
  (volume.restrict (Ioo D.lower D.upper)).withDensity (fun x => ENNReal.ofReal (D.density x))

lemma densityMeasure_ae_mem : ∀ᵐ x ∂D.densityMeasure, x ∈ Ioo D.lower D.upper :=
  (ae_restrict_mem measurableSet_Ioo).filter_mono
    (withDensity_absolutelyContinuous _ _).ae_le

lemma cdf_aemeasurable : AEMeasurable D.cdf D.densityMeasure := by
  apply AEMeasurable.mono_ac _ (withDensity_absolutelyContinuous _ _)
  exact (D.cdf_continuousOn.mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo

/-- The change-of-variables theorem sends the positive density to the unit uniform law. -/
lemma map_cdf_densityMeasure :
    Measure.map D.cdf D.densityMeasure = volume.restrict (Ioo (0 : ℝ) 1) := by
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar volume
    measurableSet_Ioo.nullMeasurableSet
    (fun x hx => (D.cdf_hasDerivAt hx).hasDerivWithinAt.hasFDerivWithinAt)
    (D.cdf_strictMonoOn.injOn.mono Ioo_subset_Icc_self)
  simp only [ContinuousLinearMap.det_toSpanSingleton] at hmap
  have hden : (volume.restrict (Ioo D.lower D.upper)).withDensity
      (fun x => ENNReal.ofReal |D.density x|) = D.densityMeasure := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [abs_of_pos (D.positive x hx)]
  rw [hden, D.cdf_image_Ioo] at hmap
  exact hmap

/-- The quantile constructed above really has the prescribed density law. -/
lemma map_quantileReal_uniform :
    Measure.map D.quantileReal (volume.restrict (Ioo (0 : ℝ) 1)) = D.densityMeasure := by
  rw [← D.map_cdf_densityMeasure,
    AEMeasurable.map_map_of_aemeasurable D.quantileReal_continuous.measurable.aemeasurable
      D.cdf_aemeasurable]
  calc
    Measure.map (D.quantileReal ∘ D.cdf) D.densityMeasure = Measure.map id D.densityMeasure := by
      apply Measure.map_congr
      filter_upwards [D.densityMeasure_ae_mem] with x hx
      exact D.quantileReal_cdf ⟨hx.1.le, hx.2.le⟩
    _ = D.densityMeasure := Measure.map_id

instance densityMeasure_isProbabilityMeasure : IsProbabilityMeasure D.densityMeasure := by
  let : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by
    simp [Real.volume_Ioo]⟩
  rw [← D.map_quantileReal_uniform]
  exact (Measure.isProbabilityMeasure_map_iff
    D.quantileReal_continuous.measurable.aemeasurable).2 inferInstance

/-- Inverse thresholds reduce parameter measurability to cumulative-integral evaluations. -/
lemma quantileReal_lt_iff {s r : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    D.quantileReal s < r ↔ D.lower < r ∧ (D.upper ≤ r ∨ s < D.cdf r) := by
  have hq := D.quantileReal_mem_interior hs
  have hc := D.cdf_quantileReal ⟨hs.1.le, hs.2.le⟩
  constructor
  · intro h
    refine ⟨hq.1.trans h, ?_⟩
    by_cases hr : D.upper ≤ r
    · exact Or.inl hr
    · right
      have hmono := D.cdf_strictMonoOn (D.quantileReal_mem s)
        ⟨(hq.1.trans h).le, (lt_of_not_ge hr).le⟩ h
      rwa [hc] at hmono
  · rintro ⟨hr0, hr1 | hr1⟩
    · exact hq.2.trans_le hr1
    · by_cases hr : D.upper ≤ r
      · exact hq.2.trans_le hr
      · apply (D.cdf_strictMonoOn.lt_iff_lt (D.quantileReal_mem s)
          ⟨hr0.le, (lt_of_not_ge hr).le⟩).mp
        rwa [hc]

/-- Parameter integrals over measurable moving real intervals are measurable. -/
lemma measurable_intervalIntegral_family {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω × ℝ → ℝ} (hf : Measurable f) {a b : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => ∫ t in a ω..b ω, f (ω, t)) := by
  have hhalf (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b) :
      Measurable (fun ω => ∫ t in Ioc (a ω) (b ω), f (ω, t)) := by
    let S : Set (Ω × ℝ) := {z | a z.1 < z.2 ∧ z.2 ≤ b z.1}
    have hS : MeasurableSet S :=
      (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hb.comp measurable_fst))
    have hi : Measurable (fun ω => ∫ t, S.indicator f (ω, t)) :=
      (hf.indicator hS).stronglyMeasurable.integral_prod_right'.measurable
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      simp only [S, Set.indicator_apply, Set.mem_Ioc, Set.mem_ofPred_eq]
  exact (hhalf a b ha hb).sub (hhalf b a hb ha)

lemma quantileReal_of_nonpos {s : ℝ} (hs : s ≤ 0) : D.quantileReal s = D.lower := by
  have hzero : D.quantileReal 0 = D.lower := by
    simpa only [D.cdf_lower] using
      D.quantileReal_cdf (left_mem_Icc.mpr D.lower_lt_upper.le)
  calc
    D.quantileReal s = D.quantileReal 0 := by
      unfold quantileReal
      rw [Set.projIcc_of_le_left _ hs, Set.projIcc_left]
    _ = D.lower := hzero

lemma quantileReal_of_one_le {s : ℝ} (hs : 1 ≤ s) : D.quantileReal s = D.upper := by
  have hone : D.quantileReal 1 = D.upper := by
    simpa only [D.cdf_upper] using
      D.quantileReal_cdf (right_mem_Icc.mpr D.lower_lt_upper.le)
  calc
    D.quantileReal s = D.quantileReal 1 := by
      unfold quantileReal
      rw [Set.projIcc_of_right_le _ hs, Set.projIcc_right]
    _ = D.upper := hone

/-- The continuous extensions are jointly measurable even for parameters outside (0,1). -/
theorem measurable_quantileReal_family_global {Ω : Type*} [MeasurableSpace Ω]
    (D : Ω → PositiveIntervalDensity)
    (hlower : Measurable fun ω => (D ω).lower)
    (hupper : Measurable fun ω => (D ω).upper)
    (hcdf : ∀ r : ℝ, Measurable fun ω => (D ω).cdf r)
    {s : Ω → ℝ} (hs : Measurable s) :
    Measurable (fun ω => (D ω).quantileReal (s ω)) := by
  apply measurable_of_Iio
  intro r
  have heq : (fun ω => (D ω).quantileReal (s ω)) ⁻¹' Iio r =
      ({ω | s ω ≤ 0} ∩ {ω | (D ω).lower < r}) ∪
      ({ω | 1 ≤ s ω} ∩ {ω | (D ω).upper < r}) ∪
      ({ω | 0 < s ω} ∩ {ω | s ω < 1} ∩ {ω | (D ω).lower < r} ∩
        ({ω | (D ω).upper ≤ r} ∪ {ω | s ω < (D ω).cdf r})) := by
    ext ω
    by_cases h0 : s ω ≤ 0
    · have h1 : ¬ 1 ≤ s ω := by linarith
      simp [h0, h1, not_lt.mpr h0, (D ω).quantileReal_of_nonpos h0]
    · by_cases h1 : 1 ≤ s ω
      · simp [h0, h1, not_lt.mpr h1, (D ω).quantileReal_of_one_le h1]
      · have hsi : s ω ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_not_ge h0, lt_of_not_ge h1⟩
        simpa [h0, h1, hsi.1, hsi.2] using (D ω).quantileReal_lt_iff hsi (r := r)
  rw [heq]
  exact (((measurableSet_le hs measurable_const).inter
    (measurableSet_lt hlower measurable_const)).union
      ((measurableSet_le measurable_const hs).inter
        (measurableSet_lt hupper measurable_const))).union
    ((((measurableSet_lt measurable_const hs).inter
        (measurableSet_lt hs measurable_const)).inter
          (measurableSet_lt hlower measurable_const)).inter
      ((measurableSet_le hupper measurable_const).union
        (measurableSet_lt hs (hcdf r))))

theorem measurable_joint_quantileReal_global {Ω : Type*} [MeasurableSpace Ω]
    (D : Ω → PositiveIntervalDensity)
    (hlower : Measurable fun ω => (D ω).lower)
    (hupper : Measurable fun ω => (D ω).upper)
    (hdensity : Measurable fun z : Ω × ℝ => (D z.1).density z.2) :
    Measurable (fun z : Ω × ℝ => (D z.1).quantileReal z.2) := by
  apply measurable_quantileReal_family_global (fun z : Ω × ℝ => D z.1)
    (hlower.comp measurable_fst) (hupper.comp measurable_fst)
    _ measurable_snd
  intro r
  exact (measurable_intervalIntegral_family hdensity hlower measurable_const).comp measurable_fst

lemma quantileReal_strictMonoOn : StrictMonoOn D.quantileReal (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  by_contra h
  have hle : D.quantileReal t ≤ D.quantileReal s := le_of_not_gt h
  have hc := D.cdf_strictMonoOn.monotoneOn (D.quantileReal_mem t)
    (D.quantileReal_mem s) hle
  rw [D.cdf_quantileReal ht, D.cdf_quantileReal hs] at hc
  exact (not_le_of_gt hst) hc

/-- Conditional densities only need to exist on the measurable set of valid prefixes.
Their quantiles extend to a globally measurable map without imposing any density law
at the invalid prefixes. The extension agrees at every real argument on valid fibers. -/
theorem exists_measurable_quantile_extension {Ω : Type*} [MeasurableSpace Ω]
    (S : Set Ω) (hS : MeasurableSet S) (D : S → PositiveIntervalDensity)
    (hlower : Measurable fun ω => (D ω).lower)
    (hupper : Measurable fun ω => (D ω).upper)
    (hdensity : Measurable fun z : S × ℝ => (D z.1).density z.2) :
    ∃ Q : Ω × ℝ → ℝ, Measurable Q ∧
      (∀ ω : S, ∀ s : ℝ, Q (ω, s) = (D ω).quantileReal s) ∧
      (∀ ω : S, Measure.map (fun s => Q (ω, s))
        (volume.restrict (Ioo (0 : ℝ) 1)) = (D ω).densityMeasure) ∧
      (∀ ω : S, ∀ s ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun t => Q (ω, t)) ((D ω).density (Q (ω, s)))⁻¹ s) ∧
      (∀ ω : S, StrictMonoOn (fun s => Q (ω, s)) (Icc (0 : ℝ) 1)) := by
  have hQ₀ := measurable_joint_quantileReal_global D hlower hupper hdensity
  have hemb : MeasurableEmbedding (Prod.map (Subtype.val : S → Ω) (id : ℝ → ℝ)) :=
    (MeasurableEmbedding.subtype_coe hS).prodMap MeasurableEmbedding.id
  obtain ⟨Q, hQ, hext⟩ := hemb.exists_measurable_extend hQ₀ (fun _ => inferInstance)
  have hmatch (ω : S) (s : ℝ) : Q (ω, s) = (D ω).quantileReal s :=
    congrFun hext (ω, s)
  refine ⟨Q, hQ, hmatch, ?_, ?_, ?_⟩
  · intro ω
    have heq : (fun s => Q (ω, s)) = (D ω).quantileReal := funext (hmatch ω)
    rw [heq]
    exact (D ω).map_quantileReal_uniform
  · intro ω s hs
    have heq : (fun t => Q (ω, t)) = (D ω).quantileReal := funext (hmatch ω)
    rw [heq, hmatch ω s]
    exact (D ω).quantileReal_hasDerivAt hs
  · intro ω
    have heq : (fun s => Q (ω, s)) = (D ω).quantileReal := funext (hmatch ω)
    rw [heq]
    exact (D ω).quantileReal_strictMonoOn

end PositiveIntervalDensity
end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Sections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped Topology

namespace Problem358
namespace AffineSlice

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A vertical affine section of a set in a product vector space. -/
def fiber (K : Set (U × V)) (p : U) : Set V := (fun y => (p, y)) ⁻¹' K

omit [NormedSpace ℝ U] [NormedSpace ℝ V] in
theorem isClosed_fiber {K : Set (U × V)} (hK : IsClosed K) (p : U) :
    IsClosed (fiber K p) := hK.preimage (continuous_const.prodMk continuous_id)

omit [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem fiber_subset_projection (K : Set (U × V)) (p : U) :
    fiber K p ⊆ Prod.snd '' K := fun y hy => ⟨(p, y), hy, rfl⟩

omit [NormedSpace ℝ U] [NormedSpace ℝ V] in
theorem isCompact_fiber {K : Set (U × V)} (hK : IsCompact K) (p : U) :
    IsCompact (fiber K p) :=
  (hK.image continuous_snd).of_isClosed_subset (isClosed_fiber hK.isClosed p)
    (fiber_subset_projection K p)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  (μ : Measure V) [IsAddHaarMeasure μ]

/-- Fiber volume is continuous at every prefix whose fiber crosses the interior.
This supplies the density-continuity step of triangular uniform parametrization. -/
theorem continuousAt_fiberMeasure {K : Set (U × V)} (hK : IsCompact K)
    (hconv : Convex ℝ K) {p : U} (hp : ∃ y : V, (p, y) ∈ interior K) :
    ContinuousAt (fun q => μ (fiber K q)) p := by
  let f : V →ᵃ[ℝ] U × V := (AffineMap.const ℝ V p).prod (AffineMap.id ℝ V)
  have hmeet : (f ⁻¹' interior K).Nonempty := hp
  have hlim : ∀ᵐ y ∂μ,
      Tendsto (fun q : U => K.indicator (fun _ => (1 : ℝ)) (q, y)) (𝓝 p)
        (𝓝 (K.indicator (fun _ => (1 : ℝ)) (p, y))) := by
    apply ae_tendsto_indicator_on_affine_slice μ f hK.isClosed hconv hmeet
      continuousOn_const
    exact ae_of_all μ fun y => by
      simpa [f] using (continuous_id.prodMk (continuous_const :
        Continuous (fun _ : U => y))).tendsto p
  have hevent : ∀ᵐ y ∂μ, ∀ᶠ q in 𝓝 p, y ∈ fiber K q ↔ y ∈ fiber K p := by
    filter_upwards [hlim] with y hy
    apply (tendsto_indicator_const_apply_iff_eventually (𝓝 p) (1 : ℝ) y).mp
    have heq : ∀ q : U, (fiber K q).indicator (fun _ : V => (1 : ℝ)) y =
        K.indicator (fun _ : U × V => (1 : ℝ)) (q, y) := by
      intro q
      exact Set.indicator_comp_right (s := K) (g := fun _ : U × V => (1 : ℝ))
        (x := y) (fun z : V => (q, z))
    simpa only [heq] using hy
  exact tendsto_measure_of_ae_tendsto_indicator (𝓝 p)
    (isClosed_fiber hK.isClosed p).measurableSet
    (fun q => (isClosed_fiber hK.isClosed q).measurableSet)
    (hK.image continuous_snd).measurableSet (hK.image continuous_snd).measure_ne_top
    (Eventually.of_forall (fiber_subset_projection K)) hevent

/-- The same slice-volume continuity in real, rather than extended-real, values. -/
theorem continuousAt_fiberMeasureReal {K : Set (U × V)} (hK : IsCompact K)
    (hconv : Convex ℝ K) {p : U} (hp : ∃ y : V, (p, y) ∈ interior K) :
    ContinuousAt (fun q => μ.real (fiber K q)) p := by
  have hfin : μ (fiber K p) ≠ ⊤ := (isCompact_fiber hK p).measure_ne_top
  exact ContinuousAt.comp (f := fun q => μ (fiber K q)) (g := ENNReal.toReal)
    (ENNReal.continuousAt_toReal hfin) (continuousAt_fiberMeasure μ hK hconv hp)

omit [NormedSpace ℝ U] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- A fiber crossing the interior has positive volume. -/
theorem fiberMeasure_pos {K : Set (U × V)} {p : U}
    (hp : ∃ y : V, (p, y) ∈ interior K) : 0 < μ (fiber K p) := by
  obtain ⟨y, hy⟩ := hp
  apply measure_pos_of_nonempty_interior
  refine ⟨y, ?_⟩
  exact preimage_interior_subset_interior_preimage
    (continuous_const.prodMk continuous_id) hy

omit [NormedSpace ℝ U] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- Positivity survives conversion to real for compact fibers. -/
theorem fiberMeasureReal_pos {K : Set (U × V)} (hK : IsCompact K) {p : U}
    (hp : ∃ y : V, (p, y) ∈ interior K) : 0 < μ.real (fiber K p) := by
  exact ENNReal.toReal_pos (fiberMeasure_pos μ hp).ne' (isCompact_fiber hK p).measure_ne_top

end AffineSlice
end Problem358

end

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem358
namespace SectionMeasure

/-- The fiber of a product set over its first coordinate. -/
def fiber {A B : Type*} (U : Set (A × B)) (a : A) : Set B :=
  {b | (a, b) ∈ U}

/-- A fiber is nonempty exactly when its prefix belongs to the projection. -/
theorem fiber_nonempty_iff {A B : Type*} (U : Set (A × B)) (a : A) :
    (fiber U a).Nonempty ↔ a ∈ Prod.fst '' U := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨(a, b), hb, rfl⟩
  · rintro ⟨⟨a', b⟩, hab, ha⟩
    dsimp at ha
    subst a'
    exact ⟨b, hab⟩

/-- Prefix domains of open sets are open. -/
theorem isOpen_projection {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {U : Set (A × B)} (hU : IsOpen U) : IsOpen (Prod.fst '' U) :=
  isOpenMap_fst _ hU

/-- A nonempty bounded open convex subset of the real line is its endpoint interval. -/
theorem eq_Ioo_csInf_csSup_of_open_convex {S : Set ℝ}
    (hS : IsOpen S) (hc : Convex ℝ S) (hne : S.Nonempty)
    (hl : BddBelow S) (hu : BddAbove S) :
    S = Ioo (sInf S) (sSup S) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS x hx
    have hm : x - ε / 2 ∈ S := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      have ht : x - ε / 2 - x = -(ε / 2) := by ring
      rw [ht, abs_neg, abs_of_pos (by positivity)]
      linarith)
    have hp : x + ε / 2 ∈ S := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      have ht : x + ε / 2 - x = ε / 2 := by ring
      rw [ht, abs_of_pos (by positivity)]
      linarith)
    exact ⟨(csInf_le hl hm).trans_lt (by linarith),
      lt_of_lt_of_le (by linarith : x < x + ε / 2) (le_csSup hu hp)⟩
  · exact (show IsConnected S from ⟨hne, Real.convex_iff_isPreconnected.mp hc⟩).Ioo_csInf_csSup_subset hl hu

end SectionMeasure
end Problem358

namespace Problem358.SectionMarginal

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite ν]

/-- Integrating a product density over the second coordinate computes its
actual first marginal. -/
theorem map_fst_withDensity (q : A × B → ℝ≥0∞) (hq : Measurable q) :
    Measure.map Prod.fst ((μ.prod ν).withDensity q) =
      μ.withDensity (fun a => ∫⁻ b, q (a, b) ∂ν) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs,
    withDensity_apply q (hs.preimage measurable_fst),
    withDensity_apply _ hs,
    ← lintegral_indicator (hs.preimage measurable_fst),
    lintegral_prod _ ((hq.indicator (hs.preimage measurable_fst)).aemeasurable),
    ← lintegral_indicator hs]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ s <;> simp [ha]

/-- A body restricted from a product measure has section-volume density in its
first marginal. This remains valid for zero and infinite total body measure. -/
theorem map_fst_restrict (U : Set (A × B)) (hU : MeasurableSet U) :
    Measure.map Prod.fst ((μ.prod ν).restrict U) =
      μ.withDensity (fun a => ν {b | (a, b) ∈ U}) := by
  rw [← withDensity_indicator_one hU]
  change Measure.map Prod.fst ((μ.prod ν).withDensity
    (U.indicator (fun _ => (1 : ℝ≥0∞)))) = _
  rw [map_fst_withDensity μ ν _ (measurable_const.indicator hU)]
  congr 1
  funext a
  change (∫⁻ b, ({b | (a, b) ∈ U}.indicator (fun _ => (1 : ℝ≥0∞))) b ∂ν) = _
  have hs : MeasurableSet {b | (a, b) ∈ U} :=
    hU.preimage (measurable_const.prodMk measurable_id)
  rw [lintegral_indicator hs]
  simp

/-- The normalized body law has the common total-volume normalization, rather
than a separate normalization of each prefix. -/
theorem map_fst_normalized_restrict (U : Set (A × B)) (hU : MeasurableSet U) :
    Measure.map Prod.fst (((μ.prod ν) U)⁻¹ • (μ.prod ν).restrict U) =
      ((μ.prod ν) U)⁻¹ • μ.withDensity (fun a => ν {b | (a, b) ∈ U}) := by
  rw [Measure.map_smul, map_fst_restrict μ ν U hU]

end Problem358.SectionMarginal

end

noncomputable section
open Set MeasureTheory

namespace Problem358.SectionMeasure

/-- The lower endpoint of a nonempty open scalar fiber is upper semicontinuous
in its prefix. No convexity is needed for this regularity statement. -/
theorem upperSemicontinuous_fiber_inf {A : Type*} [TopologicalSpace A]
    {U : Set (A × ℝ)} (hU : IsOpen U)
    (hb : ∀ a ∈ Prod.fst '' U, BddBelow (fiber U a)) :
    UpperSemicontinuous (fun a : Prod.fst '' U => sInf (fiber U a.val)) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro r
  have hopen : IsOpen (Prod.fst '' (U ∩ Prod.snd ⁻¹' Iio r)) :=
    isOpen_projection (hU.inter (isOpen_Iio.preimage continuous_snd))
  have heq : (fun a : Prod.fst '' U => sInf (fiber U a.val)) ⁻¹' Iio r =
      Subtype.val ⁻¹' (Prod.fst '' (U ∩ Prod.snd ⁻¹' Iio r)) := by
    ext a
    change sInf (fiber U a.val) < r ↔ a.val ∈ Prod.fst '' (U ∩ Prod.snd ⁻¹' Iio r)
    rw [csInf_lt_iff (hb a.val a.property) ((fiber_nonempty_iff U a.val).2 a.property)]
    constructor
    · rintro ⟨t, ht, htr⟩
      exact ⟨(a.val, t), ⟨ht, htr⟩, rfl⟩
    · rintro ⟨⟨a', t⟩, ⟨ht, htr⟩, ha⟩
      dsimp at ha
      subst a'
      exact ⟨t, ht, htr⟩
  rw [heq]
  exact hopen.preimage continuous_subtype_val

/-- The upper endpoint is lower semicontinuous on the valid-prefix domain. -/
theorem lowerSemicontinuous_fiber_sup {A : Type*} [TopologicalSpace A]
    {U : Set (A × ℝ)} (hU : IsOpen U)
    (hb : ∀ a ∈ Prod.fst '' U, BddAbove (fiber U a)) :
    LowerSemicontinuous (fun a : Prod.fst '' U => sSup (fiber U a.val)) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro r
  have hopen : IsOpen (Prod.fst '' (U ∩ Prod.snd ⁻¹' Ioi r)) :=
    isOpen_projection (hU.inter (isOpen_Ioi.preimage continuous_snd))
  have heq : (fun a : Prod.fst '' U => sSup (fiber U a.val)) ⁻¹' Ioi r =
      Subtype.val ⁻¹' (Prod.fst '' (U ∩ Prod.snd ⁻¹' Ioi r)) := by
    ext a
    change r < sSup (fiber U a.val) ↔ a.val ∈ Prod.fst '' (U ∩ Prod.snd ⁻¹' Ioi r)
    rw [lt_csSup_iff (hb a.val a.property) ((fiber_nonempty_iff U a.val).2 a.property)]
    constructor
    · rintro ⟨t, ht, hrt⟩
      exact ⟨(a.val, t), ⟨ht, hrt⟩, rfl⟩
    · rintro ⟨⟨a', t⟩, ⟨ht, hrt⟩, ha⟩
      dsimp at ha
      subst a'
      exact ⟨t, ht, hrt⟩
  rw [heq]
  exact hopen.preimage continuous_subtype_val

/-- Lower scalar-section endpoints are Borel functions of their valid prefix. -/
theorem measurable_fiber_inf {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [OpensMeasurableSpace A]
    {U : Set (A × ℝ)} (hU : IsOpen U)
    (hb : ∀ a ∈ Prod.fst '' U, BddBelow (fiber U a)) :
    Measurable (fun a : Prod.fst '' U => sInf (fiber U a.val)) :=
  (upperSemicontinuous_fiber_inf hU hb).measurable

/-- Upper scalar-section endpoints are Borel functions of their valid prefix. -/
theorem measurable_fiber_sup {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [OpensMeasurableSpace A]
    {U : Set (A × ℝ)} (hU : IsOpen U)
    (hb : ∀ a ∈ Prod.fst '' U, BddAbove (fiber U a)) :
    Measurable (fun a : Prod.fst '' U => sSup (fiber U a.val)) :=
  (lowerSemicontinuous_fiber_sup hU hb).measurable

end Problem358.SectionMeasure

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_ConvexDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal

namespace Problem358
namespace AffineSlice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The scalar projection of a convex body's interior is a bounded open interval,
and its whole projection lies in the corresponding closed interval. -/
theorem exists_projection_interval {K : Set (ℝ × V)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : (interior K).Nonempty) :
    ∃ a b : ℝ, a < b ∧ Prod.fst '' interior K = Ioo a b ∧
      Prod.fst '' K ⊆ Icc a b := by
  let S : Set ℝ := Prod.fst '' interior K
  have hS : IsOpen S := isOpenMap_fst _ isOpen_interior
  have hSc : Convex ℝ S := hconv.interior.linear_image (LinearMap.fst ℝ ℝ V)
  have hSn : S.Nonempty := hne.image Prod.fst
  have hsub : S ⊆ Prod.fst '' K := Set.image_mono interior_subset
  have hbound := (hK.image continuous_fst).isBounded.subset hsub
  have hI := SectionMeasure.eq_Ioo_csInf_csSup_of_open_convex
    hS hSc hSn hbound.bddBelow hbound.bddAbove
  have hab : sInf S < sSup S := by
    obtain ⟨x, hx⟩ := hSn
    rw [hI] at hx
    exact hx.1.trans hx.2
  refine ⟨sInf S, sSup S, hab, hI, ?_⟩
  have hclosure : K = closure (interior K) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne, hK.isClosed.closure_eq]
  calc
    Prod.fst '' K = Prod.fst '' closure (interior K) := congrArg _ hclosure
    _ ⊆ closure S := image_closure_subset_closure_image continuous_fst
    _ = Icc (sInf S) (sSup S) := by
      nth_rw 1 [hI]
      exact closure_Ioo hab.ne

/-- Fubini identity for the real-valued volume of compact fibers. -/
theorem integral_fiberMeasureReal (μ : Measure V) [IsAddHaarMeasure μ]
    {K : Set (ℝ × V)} (hK : IsCompact K) :
    (∫ t, μ.real (fiber K t)) = (volume.prod μ).real K := by
  have hm : Measurable (fun t : ℝ => μ (fiber K t)) :=
    measurable_measure_prodMk_left hK.measurableSet
  have hlen : (∫⁻ t, μ (fiber K t)) = (volume.prod μ) K :=
    (Measure.prod_apply hK.measurableSet).symm
  change (∫ t, (μ (fiber K t)).toReal) = ((volume.prod μ) K).toReal
  rw [integral_toReal hm.aemeasurable (ae_of_all _ fun t => (isCompact_fiber hK t).measure_lt_top),
    hlen]

theorem integrable_fiberMeasureReal (μ : Measure V) [IsAddHaarMeasure μ]
    {K : Set (ℝ × V)} (hK : IsCompact K) :
    Integrable (fun t => μ.real (fiber K t)) volume := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_measure_prodMk_left hK.measurableSet).aemeasurable
  rw [← Measure.prod_apply hK.measurableSet]
  exact hK.measure_ne_top

/-- A compact convex body supplies an actual positive normalized 1D section density. -/
theorem exists_positiveIntervalDensity_of_convex_body
    (μ : Measure V) [IsAddHaarMeasure μ]
    {K : Set (ℝ × V)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : (interior K).Nonempty) :
    ∃ D : PositiveIntervalDensity,
      D.density = (fun t => μ.real (fiber K t) / (volume.prod μ).real K) ∧
      Ioo D.lower D.upper = Prod.fst '' interior K := by
  obtain ⟨a, b, hab, hproj, hprojK⟩ := exists_projection_interval hK hconv hne
  let M : ℝ := (volume.prod μ).real K
  have hM : 0 < M := ENNReal.toReal_pos
    (measure_pos_of_nonempty_interior (volume.prod μ) hne).ne' hK.measure_ne_top
  have hm := integrable_fiberMeasureReal μ hK
  have hzero : ∀ t, t ∉ Icc a b → μ.real (fiber K t) = 0 := by
    intro t ht
    have hemp : fiber K t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact ht (hprojK ⟨(t, v), hv, rfl⟩)
    simp [hemp]
  have hint : (∫ t in a..b, μ.real (fiber K t)) = M := by
    rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    exact integral_fiberMeasureReal μ hK
  refine ⟨{
    lower := a
    upper := b
    density := fun t => μ.real (fiber K t) / M
    lower_lt_upper := hab
    integrable := (hm.div_const M).intervalIntegrable
    continuousOn := ?_
    positive := ?_
    integral_one := ?_ }, rfl, hproj.symm⟩
  · intro t ht
    have htp : ∃ v : V, (t, v) ∈ interior K := by
      have hmem : t ∈ Prod.fst '' interior K := hproj ▸ ht
      obtain ⟨⟨u, v⟩, huv, hu⟩ := hmem
      exact ⟨v, by simpa only using hu ▸ huv⟩
    exact ((continuousAt_fiberMeasureReal μ hK hconv htp).div_const M).continuousWithinAt
  · intro t ht
    have hmem : t ∈ Prod.fst '' interior K := hproj ▸ ht
    obtain ⟨⟨u, v⟩, huv, hu⟩ := hmem
    have htp : ∃ v : V, (t, v) ∈ interior K := ⟨v, by simpa only using hu ▸ huv⟩
    exact div_pos (fiberMeasureReal_pos μ hK htp) hM
  · rw [intervalIntegral.integral_div, hint, div_self hM.ne']

/-- The density object obtained from a convex body has exactly its scalar marginal law. -/
theorem densityMeasure_eq_scalar_marginal
    (μ : Measure V) [IsAddHaarMeasure μ]
    {K : Set (ℝ × V)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : (interior K).Nonempty) (D : PositiveIntervalDensity)
    (hden : D.density = fun t => μ.real (fiber K t) / (volume.prod μ).real K)
    (hI : Ioo D.lower D.upper = Prod.fst '' interior K) :
    D.densityMeasure = Measure.map Prod.fst
      (((volume.prod μ) K)⁻¹ • (volume.prod μ).restrict K) := by
  have hM : 0 < (volume.prod μ).real K := ENNReal.toReal_pos
    (measure_pos_of_nonempty_interior (volume.prod μ) hne).ne' hK.measure_ne_top
  have hclosure : K = closure (interior K) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne, hK.isClosed.closure_eq]
  have hproj : Prod.fst '' K ⊆ Icc D.lower D.upper := calc
    Prod.fst '' K = Prod.fst '' closure (interior K) := congrArg _ hclosure
    _ ⊆ closure (Prod.fst '' interior K) := image_closure_subset_closure_image continuous_fst
    _ = closure (Ioo D.lower D.upper) := congrArg closure hI.symm
    _ = Icc D.lower D.upper := closure_Ioo D.lower_lt_upper.ne
  rw [SectionMarginal.map_fst_normalized_restrict volume μ K hK.measurableSet]
  change (volume.restrict (Ioo D.lower D.upper)).withDensity
    (fun t => ENNReal.ofReal (D.density t)) =
    ((volume.prod μ) K)⁻¹ • volume.withDensity (fun t => μ (fiber K t))
  have hm : Measurable (fun t : ℝ => μ (fiber K t)) :=
    measurable_measure_prodMk_left hK.measurableSet
  rw [← withDensity_indicator measurableSet_Ioo, ← withDensity_smul _ hm]
  apply withDensity_congr_ae
  filter_upwards [volume.ae_ne D.lower, volume.ae_ne D.upper] with t hl hu
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases ht : t ∈ Ioo D.lower D.upper
  · rw [indicator_of_mem ht, hden]
    change ENNReal.ofReal ((μ (fiber K t)).toReal / ((volume.prod μ) K).toReal) = _
    change 0 < ((volume.prod μ) K).toReal at hM
    rw [ENNReal.ofReal_div_of_pos hM,
      ENNReal.ofReal_toReal (isCompact_fiber hK t).measure_ne_top,
      ENNReal.ofReal_toReal hK.measure_ne_top, div_eq_mul_inv, mul_comm]
  · rw [indicator_of_notMem ht]
    have hemp : fiber K t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hp := hproj ⟨(t, v), hv, rfl⟩
      exact ht ⟨lt_of_le_of_ne hp.1 (Ne.symm hl), lt_of_le_of_ne hp.2 hu⟩
    simp [hemp]

end AffineSlice
end Problem358

end

noncomputable section
open MeasureTheory Set

namespace Problem358
namespace PositiveIntervalDensity

/-- The endpoints of any chosen interval-density description are measurable when
the intervals are precisely the fibers of an open set. No measurability of the
choice of density bundles is needed. -/
theorem measurable_endpoints_of_open_fibers {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [OpensMeasurableSpace A]
    {U : Set (A × ℝ)} (hU : IsOpen U)
    (D : (Prod.fst '' U) → PositiveIntervalDensity)
    (hsupport : ∀ a, Ioo (D a).lower (D a).upper = SectionMeasure.fiber U a.val) :
    Measurable (fun a => (D a).lower) ∧ Measurable (fun a => (D a).upper) := by
  have hl : (fun a => (D a).lower) =
      (fun a : Prod.fst '' U => sInf (SectionMeasure.fiber U a.val)) := by
    funext a
    rw [← hsupport a, csInf_Ioo (D a).lower_lt_upper]
  have hr : (fun a => (D a).upper) =
      (fun a : Prod.fst '' U => sSup (SectionMeasure.fiber U a.val)) := by
    funext a
    rw [← hsupport a, csSup_Ioo (D a).lower_lt_upper]
  constructor
  · rw [hl]
    apply SectionMeasure.measurable_fiber_inf hU
    intro a ha
    rw [← hsupport ⟨a, ha⟩]
    exact bddBelow_Ioo
  · rw [hr]
    apply SectionMeasure.measurable_fiber_sup hU
    intro a ha
    rw [← hsupport ⟨a, ha⟩]
    exact bddAbove_Ioo

/-- Existential positive-density data on each open scalar fiber already determine
a jointly measurable family of actual quantile transports. In particular arbitrary
choices of the scalar density bundles do not leave a parameter-measurability gap. -/
theorem exists_quantiles_of_open_fiber_densities {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [OpensMeasurableSpace A]
    {U : Set (A × ℝ)} (hU : IsOpen U) (p : A × ℝ → ℝ) (hp : Measurable p)
    (hex : ∀ a : Prod.fst '' U, ∃ D : PositiveIntervalDensity,
      D.density = (fun t => p (a.val, t)) ∧
      Ioo D.lower D.upper = SectionMeasure.fiber U a.val) :
    ∃ Q : A × ℝ → ℝ, Measurable Q ∧
      (∀ a : Prod.fst '' U, Measure.map (fun s => Q (a.val, s))
        (volume.restrict (Ioo (0 : ℝ) 1)) =
          (volume.restrict (SectionMeasure.fiber U a.val)).withDensity
            (fun t => ENNReal.ofReal (p (a.val, t)))) ∧
      (∀ a : Prod.fst '' U, ∀ s ∈ Ioo (0 : ℝ) 1, (a.val, Q (a.val, s)) ∈ U) ∧
      (∀ a : Prod.fst '' U, ∀ s ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun t => Q (a.val, t)) (p (a.val, Q (a.val, s)))⁻¹ s) ∧
      (∀ a : Prod.fst '' U, StrictMonoOn (fun s => Q (a.val, s)) (Icc (0 : ℝ) 1)) ∧
      (∀ a : Prod.fst '' U, ∀ s ∈ Ioo (0 : ℝ) 1, 0 < p (a.val, Q (a.val, s))) := by
  classical
  choose D hdensity hsupport using hex
  obtain ⟨hlower, hupper⟩ := measurable_endpoints_of_open_fibers hU D hsupport
  have hd : Measurable (fun z : (Prod.fst '' U) × ℝ => (D z.1).density z.2) := by
    have heq : (fun z : (Prod.fst '' U) × ℝ => (D z.1).density z.2) =
        (fun z : (Prod.fst '' U) × ℝ => p (z.1.val, z.2)) := by
      funext z
      exact congrFun (hdensity z.1) z.2
    rw [heq]
    exact hp.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨Q, hQ, hmatch, hlaw, hderiv, hstrict⟩ :=
    exists_measurable_quantile_extension (Prod.fst '' U)
      (SectionMeasure.isOpen_projection hU).measurableSet D hlower hupper hd
  refine ⟨Q, hQ, ?_, ?_, ?_, hstrict, ?_⟩
  · intro a
    rw [hlaw a, densityMeasure, hsupport a, hdensity a]
  · intro a s hs
    have hm := (D a).quantileReal_mem_interior hs
    rw [← hmatch a s, hsupport a] at hm
    exact hm
  · intro a s hs
    simpa only [hdensity a] using hderiv a s hs
  · intro a s hs
    have hpos := (D a).positive _ ((D a).quantileReal_mem_interior hs)
    simpa only [hdensity a, ← hmatch a s] using hpos

end PositiveIntervalDensity
end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_ConvexQuantiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal

namespace Problem358.ConvexTriangularSampler

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]

/-- Prefixes whose remaining section meets the interior of the body. -/
def valid (K : Set (U × (ℝ × V))) : Set U := Prod.fst '' interior K

/-- The remaining compact body after fixing a valid prefix. -/
def sectionBody (K : Set (U × (ℝ × V))) (x : U) : Set (ℝ × V) :=
  AffineSlice.fiber K x

omit [NormedSpace ℝ U] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma isCompact_sectionBody {K : Set (U × (ℝ × V))} (hK : IsCompact K) (x : U) :
    IsCompact (sectionBody K x) := AffineSlice.isCompact_fiber hK x

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma convex_sectionBody {K : Set (U × (ℝ × V))} (hK : Convex ℝ K) (x : U) :
    Convex ℝ (sectionBody K x) := by
  exact hK.affine_preimage ((AffineMap.const ℝ (ℝ × V) x).prod (AffineMap.id ℝ (ℝ × V)))

omit [NormedSpace ℝ U] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma sectionBody_interior_nonempty {K : Set (U × (ℝ × V))} (x : valid K) :
    (interior (sectionBody K x)).Nonempty := by
  obtain ⟨⟨y, z⟩, hyz, hy⟩ := x.property
  have hyx : y = (x : U) := hy
  refine ⟨z, preimage_interior_subset_interior_preimage
    (continuous_const.prodMk continuous_id) ?_⟩
  change ((x : U), z) ∈ interior K
  simpa only [hyx] using hyz

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma interior_sectionBody {K : Set (U × (ℝ × V))} (hK : Convex ℝ K)
    (x : valid K) :
    interior (sectionBody K x) = (fun z : ℝ × V => ((x : U), z)) ⁻¹' interior K := by
  let f : (ℝ × V) →ᵃ[ℝ] U × (ℝ × V) :=
    (AffineMap.const ℝ (ℝ × V) (x : U)).prod (AffineMap.id ℝ (ℝ × V))
  have hm : (f ⁻¹' interior K).Nonempty := by
    obtain ⟨⟨y, z⟩, hyz, hy⟩ := x.property
    have hyx : y = (x : U) := hy
    refine ⟨z, ?_⟩
    change ((x : U), z) ∈ interior K
    simpa only [hyx] using hyz
  exact interior_affine_preimage_eq f (continuous_const.prodMk continuous_id) hK hm

variable (μ : Measure V) [IsAddHaarMeasure μ]
  {K : Set (U × (ℝ × V))} (hK : IsCompact K) (hc : Convex ℝ K)

/-- The density is chosen only after its concrete geometric existence has been proved. -/
@[irreducible] def conditionalDensity (x : valid K) : PositiveIntervalDensity :=
  (AffineSlice.exists_positiveIntervalDensity_of_convex_body μ
    (isCompact_sectionBody hK x) (convex_sectionBody hc x)
    (sectionBody_interior_nonempty x)).choose

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
lemma conditionalDensity_spec (x : valid K) :
    (conditionalDensity μ hK hc x).density =
      (fun t => μ.real (AffineSlice.fiber (sectionBody K x) t) /
        (volume.prod μ).real (sectionBody K x)) ∧
    Ioo (conditionalDensity μ hK hc x).lower (conditionalDensity μ hK hc x).upper =
      Prod.fst '' interior (sectionBody K x) := by
  unfold conditionalDensity
  exact (AffineSlice.exists_positiveIntervalDensity_of_convex_body μ
    (isCompact_sectionBody hK x) (convex_sectionBody hc x)
    (sectionBody_interior_nonempty x)).choose_spec

/-- The concrete section-density ratio is jointly measurable even at invalid prefixes. -/
def sectionDensity (K : Set (U × (ℝ × V))) (μ : Measure V) (x : U) (t : ℝ) : ℝ :=
  μ.real (AffineSlice.fiber (sectionBody K x) t) /
    (volume.prod μ).real (sectionBody K x)

omit [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [BorelSpace U] [BorelSpace V] in
lemma measurable_sectionDensity (hKm : MeasurableSet K) :
    Measurable (fun z : U × ℝ => sectionDensity K μ z.1 z.2) := by
  let K' : Set ((U × ℝ) × V) :=
    (fun z : (U × ℝ) × V => (z.1.1, (z.1.2, z.2))) ⁻¹' K
  have hK' : MeasurableSet K' := hKm.preimage (by fun_prop)
  have hn : Measurable (fun z : U × ℝ => μ (Prod.mk z ⁻¹' K')) :=
    measurable_measure_prodMk_left hK'
  have hd : Measurable (fun x : U => (volume.prod μ) (Prod.mk x ⁻¹' K)) :=
    measurable_measure_prodMk_left hKm
  exact hn.ennreal_toReal.div (hd.ennreal_toReal.comp measurable_fst)

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
lemma conditionalDensity_density (x : valid K) :
    (conditionalDensity μ hK hc x).density = sectionDensity K μ x :=
  (conditionalDensity_spec μ hK hc x).1

/-- The open set of valid prefixes extended by one scalar coordinate. -/
def scalarDomain (K : Set (U × (ℝ × V))) : Set (U × ℝ) :=
  Prod.map id Prod.fst '' interior K

omit [NormedSpace ℝ U] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma isOpen_scalarDomain (K : Set (U × (ℝ × V))) : IsOpen (scalarDomain K) :=
  (IsOpenMap.id.prodMap isOpenMap_fst) _ isOpen_interior

omit [NormedSpace ℝ U] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma mem_scalarDomain {x : U} {t : ℝ} :
    (x,t) ∈ scalarDomain K ↔ ∃ z : V, (x,(t,z)) ∈ interior K := by
  constructor
  · rintro ⟨⟨y,u,z⟩, hy, heq⟩
    have heq' : (y,u) = (x,t) := heq
    obtain ⟨hyx,hut⟩ := Prod.mk.inj heq'
    exact ⟨z, by simpa only [hyx,hut] using hy⟩
  · rintro ⟨z,hz⟩
    exact ⟨(x,t,z),hz,rfl⟩

omit [NormedSpace ℝ U] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma projection_scalarDomain : Prod.fst '' scalarDomain K = valid K := by
  ext x
  constructor
  · rintro ⟨⟨y,t⟩, hyt, hy⟩
    have hyx : y = x := hy
    obtain ⟨z,hz⟩ := mem_scalarDomain.mp hyt
    exact ⟨(y,t,z),hz,hyx⟩
  · rintro ⟨⟨y,t,z⟩, hy, hyx⟩
    exact ⟨(y,t), mem_scalarDomain.mpr ⟨z,hy⟩,hyx⟩

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma fiber_scalarDomain (hc : Convex ℝ K) (x : valid K) :
    SectionMeasure.fiber (scalarDomain K) x = Prod.fst '' interior (sectionBody K x) := by
  ext t
  change ((x : U),t) ∈ scalarDomain K ↔ _
  rw [mem_scalarDomain, interior_sectionBody hc x]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨(t,z),hz,rfl⟩
  · rintro ⟨⟨u,z⟩, huz, hu⟩
    have hut : u = t := hu
    exact ⟨z, by simpa only [Set.mem_preimage, hut] using huz⟩

omit [FiniteDimensional ℝ U] in
/-- A compact convex body has a globally jointly measurable conditional scalar sampler.
Its law, derivative and interior support are all derived from the body itself. -/
theorem exists_measurable_conditional_quantile (hK : IsCompact K) (hc : Convex ℝ K) :
    ∃ Q : U × ℝ → ℝ, Measurable Q ∧
      (∀ x ∈ valid K, Measure.map (fun s => Q (x,s))
        (volume.restrict (Ioo (0 : ℝ) 1)) =
        Measure.map Prod.fst (((volume.prod μ) (sectionBody K x))⁻¹ •
          (volume.prod μ).restrict (sectionBody K x))) ∧
      (∀ x ∈ valid K, ∀ s ∈ Ioo (0 : ℝ) 1,
        ∃ z : V, (x,(Q (x,s),z)) ∈ interior K) ∧
      (∀ x ∈ valid K, ∀ s ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun t => Q (x,t))
          ((volume.prod μ).real (sectionBody K x) /
            μ.real (AffineSlice.fiber (sectionBody K x) (Q (x,s)))) s) ∧
      (∀ x ∈ valid K, StrictMonoOn (fun s => Q (x,s)) (Icc (0 : ℝ) 1)) := by
  have hex : ∀ a : Prod.fst '' scalarDomain K, ∃ D : PositiveIntervalDensity,
      D.density = (fun t => sectionDensity K μ a.val t) ∧
      Ioo D.lower D.upper = SectionMeasure.fiber (scalarDomain K) a.val := by
    intro a
    have ha : a.val ∈ valid K :=
      (Set.ext_iff.mp (projection_scalarDomain (K := K)) a.val).mp a.property
    let x : valid K := ⟨a.val,ha⟩
    refine ⟨conditionalDensity μ hK hc x, conditionalDensity_density μ hK hc x, ?_⟩
    rw [(conditionalDensity_spec μ hK hc x).2, fiber_scalarDomain hc x]
  obtain ⟨Q,hQ,hlaw,hmem,hderiv,hstrict,_⟩ :=
    PositiveIntervalDensity.exists_quantiles_of_open_fiber_densities
      (isOpen_scalarDomain K) (fun z => sectionDensity K μ z.1 z.2)
      (measurable_sectionDensity μ hK.measurableSet) hex
  refine ⟨Q,hQ,?_,?_,?_,?_⟩
  · intro x hx
    let a : Prod.fst '' scalarDomain K := ⟨x, by rwa [projection_scalarDomain]⟩
    let b : valid K := ⟨x,hx⟩
    rw [hlaw a]
    have hd := AffineSlice.densityMeasure_eq_scalar_marginal μ
      (isCompact_sectionBody hK x) (convex_sectionBody hc x)
      (sectionBody_interior_nonempty b) (conditionalDensity μ hK hc b)
      (conditionalDensity_spec μ hK hc b).1 (conditionalDensity_spec μ hK hc b).2
    rw [PositiveIntervalDensity.densityMeasure,
      (conditionalDensity_spec μ hK hc b).2,
      conditionalDensity_density μ hK hc b, ← fiber_scalarDomain hc b] at hd
    exact hd
  · intro x hx s hs
    let a : Prod.fst '' scalarDomain K := ⟨x, by rwa [projection_scalarDomain]⟩
    exact mem_scalarDomain.mp (hmem a s hs)
  · intro x hx s hs
    let a : Prod.fst '' scalarDomain K := ⟨x, by rwa [projection_scalarDomain]⟩
    simpa only [sectionDensity, inv_div] using hderiv a s hs
  · intro x hx
    exact hstrict ⟨x, by rwa [projection_scalarDomain]⟩

end Problem358.ConvexTriangularSampler

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_FiniteCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem358
namespace FiniteCoupling

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The cost of a finite real-valued transport matrix. -/
def cost (c w : ι → κ → ℝ) : ℝ := ∑ i, ∑ j, w i j * c i j

/-- Optimality among nonnegative matrices with the same two marginals. -/
def IsOptimal (c w : ι → κ → ℝ) : Prop :=
  (∀ i j, 0 ≤ w i j) ∧
  ∀ q : ι → κ → ℝ, (∀ i j, 0 ≤ q i j) →
    (∀ i, ∑ j, q i j = ∑ j, w i j) →
    (∀ j, ∑ i, q i j = ∑ i, w i j) → cost c w ≤ cost c q

/-- Transfer mass from the diagonal corners to the off-diagonal corners. -/
def rectangleSwap (w : ι → κ → ℝ) (ε : ℝ) (i k : ι) (j l : κ)
    (u : ι) (v : κ) : ℝ :=
  w u v + ε * ((if u = i then 1 else 0) - (if u = k then 1 else 0)) *
    ((if v = l then 1 else 0) - (if v = j then 1 else 0))

end FiniteCoupling

end Problem358

end

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem358
namespace PositiveFiniteCoupling

variable {ι : Type*} [Fintype ι]

/-- Retain only the strictly positive entries of a finite nonnegative weight family. -/
abbrev Support (w : ι → ℝ) := {i : ι // 0 < w i}

noncomputable instance supportFintype (w : ι → ℝ) : Fintype (Support w) :=
  by classical exact Subtype.fintype _

variable {κ : Type*} [Fintype κ]

abbrev Pairs (w : ι → κ → ℝ) := Support (fun ij : ι × κ => w ij.1 ij.2)

end PositiveFiniteCoupling
end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_MaxCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology NNReal

namespace Problem358.FiniteMaxDerivative

variable {ι X : Type*} [Fintype ι] [Nonempty ι]

/-- The maximum of a nonempty finite family of real-valued functions. -/
def maxValue (f : ι → X → ℝ) (x : X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)

end Problem358.FiniteMaxDerivative

end

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators NNReal

namespace Problem358
namespace FiniteMaxDerivative

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The maximum of a nonempty finite family of real numbers. -/
def finiteMax (f : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

lemma le_finiteMax (f : ι → ℝ) (i : ι) : f i ≤ finiteMax f :=
  Finset.le_sup' f (Finset.mem_univ i)

lemma finiteMax_le {f : ι → ℝ} {r : ℝ} (h : ∀ i, f i ≤ r) : finiteMax f ≤ r :=
  Finset.sup'_le Finset.univ_nonempty f (fun i _ => h i)

lemma finiteMax_eq {f : ι → ℝ} {i : ι} (h : ∀ j, f j ≤ f i) : finiteMax f = f i :=
  le_antisymm (finiteMax_le h) (le_finiteMax f i)

/-- A strict maximizer remains the maximizer for a sufficiently small affine perturbation. -/
lemma eventually_finiteMax_eq (f q : ι → ℝ) (i : ι)
    (hi : ∀ j, j ≠ i → f j < f i) :
    (fun t : ℝ => finiteMax (fun j => f j + t * q j)) =ᶠ[𝓝 0]
      (fun t => f i + t * q i) := by
  have h : ∀ᶠ t : ℝ in 𝓝 0, ∀ j, f j + t * q j ≤ f i + t * q i := by
    rw [Filter.eventually_all]
    intro j
    by_cases hji : j = i
    · subst j
      exact Filter.Eventually.of_forall (fun _ => le_rfl)
    · have hj : ContinuousAt (fun t : ℝ => f j + t * q j) 0 := by fun_prop
      have hi' : ContinuousAt (fun t : ℝ => f i + t * q i) 0 := by fun_prop
      exact (hj.eventually_lt hi' (by simpa using hi j hji)).mono (fun _ ht => ht.le)
  exact h.mono (fun _ ht => finiteMax_eq ht)

/-- Directional derivative of a finite maximum at a strict maximizer. -/
lemma hasDerivAt_finiteMax (f q : ι → ℝ) (i : ι)
    (hi : ∀ j, j ≠ i → f j < f i) :
    HasDerivAt (fun t : ℝ => finiteMax (fun j => f j + t * q j)) (q i) 0 := by
  have h : HasDerivAt (fun t : ℝ => f i + t * q i) (q i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (q i)).const_add (f i)
  exact h.congr_of_eventuallyEq (eventually_finiteMax_eq f q i hi)

/-- The maximum is uniformly Lipschitz in an affine parameter, independently of offsets. -/
lemma lipschitzWith_finiteMax (f q : ι → ℝ) (B : ℝ≥0)
    (hq : ∀ i, |q i| ≤ B) :
    LipschitzWith B (fun t : ℝ => finiteMax (fun i => f i + t * q i)) := by
  apply LipschitzWith.of_le_add_mul B
  intro t s
  apply finiteMax_le
  intro i
  calc
    f i + t * q i = (f i + s * q i) + (t - s) * q i := by ring
    _ ≤ finiteMax (fun j => f j + s * q j) + |(t - s) * q i| :=
      add_le_add (le_finiteMax (fun j => f j + s * q j) i) (le_abs_self _)
    _ ≤ finiteMax (fun j => f j + s * q j) + B * dist t s := by
      rw [abs_mul, Real.dist_eq]
      exact add_le_add le_rfl (by
        calc
          |t - s| * |q i| ≤ |t - s| * (B : ℝ) :=
            mul_le_mul_of_nonneg_left (hq i) (abs_nonneg _)
          _ = (B : ℝ) * |t - s| := mul_comm _ _)

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma aestronglyMeasurable_finiteMax (f : ι → α → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x => finiteMax (fun i => f i x)) μ := by
  have h : AEStronglyMeasurable (Finset.univ.sup' Finset.univ_nonempty f) μ := by
    exact Finset.sup'_induction Finset.univ_nonempty f
      (p := fun g : α → ℝ => AEStronglyMeasurable g μ)
      (fun g hg h hh => hg.sup hh) (fun i _ => hf i)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact (Finset.sup'_apply Finset.univ_nonempty f x).symm

/-- Every finite-valued measurable selection is integrable for a finite measure. -/
lemma integrable_finite_selection {ι : Type*} [Fintype ι] [Nonempty ι]
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (q : ι → ℝ) (k : α → ι)
    (hk : ∀ i, MeasurableSet {x | k x = i}) :
    Integrable (fun x => q (k x)) μ := by
  classical
  have h : Integrable
      (fun x => ∑ i, {x | k x = i}.indicator (fun _ => q i) x) μ :=
    integrable_finsetSum _ (fun i _ => (integrable_const (q i)).indicator (hk i))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp [Set.indicator_apply]

/-- Integrate a finite-valued selection by summing its fiber masses. -/
lemma integral_finite_selection {ι : Type*} [Fintype ι] [Nonempty ι]
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (q : ι → ℝ) (k : α → ι)
    (hk : ∀ i, MeasurableSet {x | k x = i}) :
    (∫ x, q (k x) ∂μ) = ∑ i, μ.real {x | k x = i} * q i := by
  classical
  calc
    (∫ x, q (k x) ∂μ) =
        ∫ x, ∑ i, {x | k x = i}.indicator (fun _ => q i) x ∂μ := by
      congr 1
      funext x
      simp [Set.indicator_apply]
    _ = ∑ i, ∫ x, {x | k x = i}.indicator (fun _ => q i) x ∂μ := by
      exact integral_finsetSum _ (fun i _ => (integrable_const (q i)).indicator (hk i))
    _ = ∑ i, μ.real {x | k x = i} * q i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_indicator (hk i)]
      simp

/-- Differentiate an integral of finite maxima when its active index is unique almost everywhere.
The Lipschitz bound is independent of the point and hence integrable for every finite measure. -/
theorem hasDerivAt_integral_finiteMax [IsFiniteMeasure μ]
    (f : ι → α → ℝ) (q : ι → ℝ) (k : α → ι)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hint : Integrable (fun x => finiteMax (fun i => f i x)) μ)
    (hk : ∀ᵐ x ∂μ, ∀ j, j ≠ k x → f j x < f (k x) x)
    (hqk : AEStronglyMeasurable (fun x => q (k x)) μ) :
    HasDerivAt (fun t : ℝ => ∫ x, finiteMax (fun i => f i x + t * q i) ∂μ)
      (∫ x, q (k x) ∂μ) 0 := by
  let B : ℝ≥0 := ∑ i, ‖q i‖₊
  have hq : ∀ i, |q i| ≤ (B : ℝ) := by
    intro i
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      (show (0 : ℝ≥0) ≤ ‖q j‖₊ from zero_le)) (Finset.mem_univ i)
    exact_mod_cast h
  have hmeas : ∀ t : ℝ,
      AEStronglyMeasurable (fun x => finiteMax (fun i => f i x + t * q i)) μ := by
    intro t
    exact aestronglyMeasurable_finiteMax _ (fun i => (hf i).add_const _)
  have hbase : Integrable (fun x => finiteMax (fun i => f i x + (0 : ℝ) * q i)) μ := by
    simpa using hint
  have hlip : ∀ᵐ x ∂μ,
      LipschitzOnWith (Real.nnabs (B : ℝ))
        (fun t : ℝ => finiteMax (fun i => f i x + t * q i)) Set.univ := by
    apply Filter.Eventually.of_forall
    intro x
    simpa using (lipschitzWith_finiteMax (fun i => f i x) q B hq)
  exact (hasDerivAt_integral_of_dominated_loc_of_lip
    (s := Set.univ) (bound := fun _ : α => (B : ℝ))
    (Filter.univ_mem) (Filter.Eventually.of_forall hmeas) hbase hqk hlip
    (integrable_const _) (hk.mono (fun x hx => hasDerivAt_finiteMax _ q (k x) hx))).2

end FiniteMaxDerivative
end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped RealInnerProductSpace Topology

namespace Problem358
namespace MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A finite maximum of affine functions, with slopes `y` and intercepts `c`. -/
def potential (y : ι → V) (c : ι → ℝ) (x : V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪x, y i⟫ + c i)

theorem affine_le_potential (y : ι → V) (c : ι → ℝ) (x : V) (i : ι) :
    ⟪x, y i⟫ + c i ≤ potential y c x := by
  exact Finset.le_sup' (fun i => ⟪x, y i⟫ + c i) (Finset.mem_univ i)

theorem potential_le (y : ι → V) (c : ι → ℝ) (x : V) (a : ℝ)
    (h : ∀ i, ⟪x, y i⟫ + c i ≤ a) : potential y c x ≤ a := by
  exact Finset.sup'_le Finset.univ_nonempty _ (fun i _ => h i)

theorem affine_eq_potential (y : ι → V) (c : ι → ℝ) (x : V) (i : ι)
    (h : ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y i⟫ + c i) :
    potential y c x = ⟪x, y i⟫ + c i := by
  exact le_antisymm (potential_le y c x _ h) (affine_le_potential y c x i)

theorem continuous_potential (y : ι → V) (c : ι → ℝ) :
    Continuous (potential y c) := by
  have h := Continuous.finset_sup' (s := Finset.univ) Finset.univ_nonempty
    (fun i _ => (continuous_id.inner continuous_const).add continuous_const
      : ∀ i ∈ (Finset.univ : Finset ι), Continuous (fun x : V => ⟪x, y i⟫ + c i))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [potential, Finset.sup'_apply]

end MaxPotential
end Problem358

end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace Topology

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem potential_intercept_sub_le (y : ι → V) (c b : ι → ℝ) (x : V) :
    potential y c x - potential y b x ≤ ‖c - b‖ := by
  have h : potential y c x ≤ potential y b x + ‖c - b‖ := by
    apply potential_le
    intro i
    have hi : c i - b i ≤ ‖c - b‖ := by
      calc
        c i - b i ≤ |c i - b i| := le_abs_self _
        _ = ‖(c - b) i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖c - b‖ := norm_le_pi_norm _ _
    linarith [affine_le_potential y b x i]
  linarith

theorem norm_potential_intercept_sub_le (y : ι → V) (c b : ι → ℝ) (x : V) :
    ‖potential y c x - potential y b x‖ ≤ ‖c - b‖ := by
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have h := potential_intercept_sub_le y b c x
    rw [norm_sub_rev] at h
    linarith
  · exact potential_intercept_sub_le y c b x

theorem norm_potential_le (y : ι → V) (c : ι → ℝ) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (x : V) :
    ‖potential y c x‖ ≤ (L : ℝ) * ‖x‖ + ‖c‖ := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => ⟪x, y i⟫ + c i)
  change potential y c x = _ at hmax
  rw [hmax]
  calc
    ‖⟪x, y i⟫ + c i‖ ≤ ‖⟪x, y i⟫‖ + ‖c i‖ := norm_add_le _ _
    _ ≤ ‖x‖ * ‖y i‖ + ‖c i‖ := add_le_add (norm_inner_le_norm _ _) le_rfl
    _ ≤ ‖x‖ * (L : ℝ) + ‖c‖ := add_le_add
      (mul_le_mul_of_nonneg_left (hy i) (norm_nonneg _)) (norm_le_pi_norm _ _)
    _ = (L : ℝ) * ‖x‖ + ‖c‖ := by ring

variable [MeasurableSpace V] [OpensMeasurableSpace V]
variable (ρ : Measure V) [IsFiniteMeasure ρ]

theorem integrable_potential (y : ι → V) (c : ι → ℝ) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (hρ : Integrable (fun x : V => ‖x‖) ρ) :
    Integrable (potential y c) ρ := by
  apply ((hρ.const_mul (L : ℝ)).add (integrable_const ‖c‖)).mono'
    (continuous_potential y c).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_potential_le y c L hy)

omit [OpensMeasurableSpace V] in
/-- Integrating the potential preserves its uniform intercept continuity. -/
theorem norm_integral_potential_sub_le (y : ι → V) (c b : ι → ℝ)
    (hc : Integrable (potential y c) ρ) (hb : Integrable (potential y b) ρ) :
    ‖(∫ x, potential y c x ∂ρ) - ∫ x, potential y b x ∂ρ‖ ≤
      ‖c - b‖ * ρ.real Set.univ := by
  rw [← integral_sub hc hb]
  apply norm_integral_le_of_norm_le_const
  exact Filter.Eventually.of_forall (norm_potential_intercept_sub_le y c b)

variable [IsProbabilityMeasure ρ]

omit [OpensMeasurableSpace V] in
theorem lipschitzWith_integral_potential (y : ι → V)
    (hρ : ∀ c, Integrable (potential y c) ρ) :
    LipschitzWith 1 (fun c : ι → ℝ => ∫ x, potential y c x ∂ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro c b
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul, probReal_univ,
    mul_one] using norm_integral_potential_sub_le ρ y c b (hρ c) (hρ b)

/-- The elementary coercivity estimate for each intercept coordinate. -/
theorem intercept_le_integral_potential (y : ι → V) (c : ι → ℝ) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (hρ : Integrable (fun x : V => ‖x‖) ρ) (i : ι) :
    c i ≤ (∫ x, potential y c x ∂ρ) + (L : ℝ) * ∫ x, ‖x‖ ∂ρ := by
  have hpoint : ∀ x : V, c i - (L : ℝ) * ‖x‖ ≤ potential y c x := by
    intro x
    have hi : -((L : ℝ) * ‖x‖) ≤ ⟪x, y i⟫ := by
      have hbound : ‖⟪x, y i⟫‖ ≤ (L : ℝ) * ‖x‖ := by
        calc
          ‖⟪x, y i⟫‖ ≤ ‖x‖ * ‖y i‖ := norm_inner_le_norm _ _
          _ ≤ ‖x‖ * (L : ℝ) := mul_le_mul_of_nonneg_left (hy i) (norm_nonneg _)
          _ = (L : ℝ) * ‖x‖ := mul_comm _ _
      rw [Real.norm_eq_abs] at hbound
      exact (abs_le.mp hbound).1
    linarith [affine_le_potential y c x i]
  have hint := integral_mono_ae
    ((integrable_const (c i)).sub (hρ.const_mul (L : ℝ)))
    (integrable_potential ρ y c L hy hρ) (Filter.Eventually.of_forall hpoint)
  change (∫ x, c i - (L : ℝ) * ‖x‖ ∂ρ) ≤ ∫ x, potential y c x ∂ρ at hint
  rw [integral_sub (integrable_const (c i)) (hρ.const_mul (L : ℝ)),
    integral_const, probReal_univ, one_smul, integral_const_mul] at hint
  linarith

end Problem358.MaxPotential

end

/-! Uniqueness of finite affine intercepts from connected full-support sources.
This route uses finite-range continuity, not differentiability of moving cells. -/

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace BigOperators Topology

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V]

omit [InnerProductSpace ℝ V] in
/-- A continuous function with finite essential range is constant on every
connected subset of the measure's support. -/
theorem eqOn_of_finite_ae_range (ρ : Measure V) {K : Set V}
    (hK : IsPreconnected K) (hKs : K ⊆ ρ.support)
    {f : V → ℝ} (hf : Continuous f) {A : Set ℝ} (hA : A.Finite)
    (hae : ∀ᵐ x ∂ρ, f x ∈ A) {x z : V} (hx : x ∈ K) (hz : z ∈ K) :
    f x = f z := by
  have hs : ρ.support ⊆ f ⁻¹' A :=
    Measure.support_subset_of_isClosed (hA.isClosed.preimage hf) hae
  have hi : (f '' K).Finite := hA.subset (by
    rintro _ ⟨w, hw, rfl⟩
    exact hs (hKs hw))
  have hc := hK.image f hf.continuousOn
  have hh : (f '' K).Subsingleton := by
    by_contra h
    exact hi.not_infinite (hc.infinite_of_nontrivial (not_subsingleton_iff.mp h))
  exact hh (mem_image_of_mem f hx) (mem_image_of_mem f hz)

/-- If the same positive-mass selector is active for two finite affine potentials,
then their intercept difference is constant on the index set. -/
theorem intercept_sub_eq_of_common_selector (ρ : Measure V) {K : Set V}
    (hK : IsPreconnected K) (hKs : K ⊆ ρ.support)
    (hKae : ∀ᵐ x ∂ρ, x ∈ K) (y : ι → V) (c b : ι → ℝ) (k : V → ι)
    (hc : ∀ᵐ x ∂ρ, potential y c x = ⟪x, y (k x)⟫ + c (k x))
    (hb : ∀ᵐ x ∂ρ, potential y b x = ⟪x, y (k x)⟫ + b (k x))
    (hpos : ∀ i, ρ {x | k x = i} ≠ 0) (i j : ι) :
    c i - b i = c j - b j := by
  have heq : ∀ᵐ x ∂ρ, potential y c x - potential y b x = c (k x) - b (k x) := by
    filter_upwards [hc, hb] with x hcx hbx
    rw [hcx, hbx]
    ring
  have hdata : ∀ᵐ x ∂ρ, x ∈ K ∧
      potential y c x - potential y b x = c (k x) - b (k x) := hKae.and heq
  obtain ⟨x, hxi, hxK, hxeq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (hpos i)
    (ae_restrict_of_ae hdata)
  obtain ⟨z, hzj, hzK, hzeq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (hpos j)
    (ae_restrict_of_ae hdata)
  change k x = i at hxi
  change k z = j at hzj
  have hrange : ∀ᵐ x ∂ρ, potential y c x - potential y b x ∈
      Set.range (fun i => c i - b i) := heq.mono (fun x hx => ⟨k x, hx.symm⟩)
  have hconst := eqOn_of_finite_ae_range ρ hK hKs
    ((continuous_potential y c).sub (continuous_potential y b))
    (Set.finite_range (fun i => c i - b i)) hrange hxK hzK
  simpa only [Pi.sub_apply, hxeq, hzeq, hxi, hzj] using hconst

/-- Weighted normalization removes the common additive intercept constant. -/
theorem intercept_eq_of_common_selector (ρ : Measure V) {K : Set V}
    (hK : IsPreconnected K) (hKs : K ⊆ ρ.support)
    (hKae : ∀ᵐ x ∂ρ, x ∈ K) (y : ι → V) (c b m : ι → ℝ) (k : V → ι)
    (hsum : ∑ i, m i = 1) (hc0 : ∑ i, m i * c i = 0)
    (hb0 : ∑ i, m i * b i = 0)
    (hc : ∀ᵐ x ∂ρ, potential y c x = ⟪x, y (k x)⟫ + c (k x))
    (hb : ∀ᵐ x ∂ρ, potential y b x = ⟪x, y (k x)⟫ + b (k x))
    (hpos : ∀ i, ρ {x | k x = i} ≠ 0) : c = b := by
  funext i
  have hconst := intercept_sub_eq_of_common_selector ρ hK hKs hKae y c b k hc hb hpos
  have hz : (∑ j, m j * (c j - b j)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, hc0, hb0, sub_self]
  have hi : (∑ j, m j * (c j - b j)) = c i - b i := by
    calc
      (∑ j, m j * (c j - b j)) = ∑ j, m j * (c i - b i) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hconst j i]
      _ = c i - b i := by rw [← Finset.sum_mul, hsum, one_mul]
  exact sub_eq_zero.mp (hi.symm.trans hz)

omit [MeasurableSpace V] in
/-- Convexity of the maximum in its intercepts, at the midpoint. -/
theorem potential_midpoint_le (y : ι → V) (c b : ι → ℝ) (x : V) :
    potential y (fun i => (c i + b i) / 2) x ≤
      (potential y c x + potential y b x) / 2 := by
  apply potential_le
  intro i
  linarith [affine_le_potential y c x i, affine_le_potential y b x i]

omit [MeasurableSpace V] in
/-- Equality in midpoint convexity forces a strict active index at one endpoint
also to be active at the other endpoint. -/
theorem active_of_midpoint_eq (y : ι → V) (c b : ι → ℝ) (x : V) (k : ι)
    (hstrict : ∀ j, j ≠ k → ⟪x, y j⟫ + c j < ⟪x, y k⟫ + c k)
    (heq : potential y (fun i => (c i + b i) / 2) x =
      (potential y c x + potential y b x) / 2) :
    potential y b x = ⟪x, y k⟫ + b k := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun j => ⟪x, y j⟫ + (c j + b j) / 2)
  change potential y (fun i => (c i + b i) / 2) x = _ at hj
  have hc := affine_le_potential y c x j
  have hb := affine_le_potential y b x j
  have hcj : potential y c x = ⟪x, y j⟫ + c j := by linarith
  have hbj : potential y b x = ⟪x, y j⟫ + b j := by linarith
  have hjk : j = k := by
    by_contra h
    have hlt := hstrict j h
    have hk := affine_le_potential y c x k
    linarith
  simpa only [hjk] using hbj

/-- Integrated midpoint equality upgrades a strict selector at the first endpoint
to a common almost-everywhere selector. -/
theorem ae_common_selector_of_integral_midpoint_eq (ρ : Measure V)
    (y : ι → V) (c b : ι → ℝ) (k : V → ι)
    (hc : Integrable (potential y c) ρ) (hb : Integrable (potential y b) ρ)
    (hm : Integrable (potential y (fun i => (c i + b i) / 2)) ρ)
    (hstrict : ∀ᵐ x ∂ρ, ∀ j, j ≠ k x →
      ⟪x, y j⟫ + c j < ⟪x, y (k x)⟫ + c (k x))
    (heq : (∫ x, potential y (fun i => (c i + b i) / 2) x ∂ρ) =
      ((∫ x, potential y c x ∂ρ) + ∫ x, potential y b x ∂ρ) / 2) :
    ∀ᵐ x ∂ρ, potential y b x = ⟪x, y (k x)⟫ + b (k x) := by
  have hae : (fun x => potential y (fun i => (c i + b i) / 2) x) =ᵐ[ρ]
      (fun x => (potential y c x + potential y b x) / 2) := by
    apply (integral_eq_iff_of_ae_le hm ((hc.add hb).div_const 2)
      (Filter.Eventually.of_forall (potential_midpoint_le y c b))).mp
    simpa only [integral_div, Pi.add_apply, integral_add hc hb] using heq
  filter_upwards [hstrict, hae] with x hx he
  exact active_of_midpoint_eq y c b x (k x) hx he

/-- Two normalized minimizers have equality in integrated midpoint convexity. -/
theorem integral_midpoint_eq_of_minimizers (ρ : Measure V)
    (y : ι → V) (c b m : ι → ℝ)
    (hc0 : ∑ i, m i * c i = 0) (hb0 : ∑ i, m i * b i = 0)
    (hint : ∀ a : ι → ℝ, Integrable (potential y a) ρ)
    (hcmin : ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y c x ∂ρ) ≤ ∫ x, potential y a x ∂ρ)
    (hbmin : ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y b x ∂ρ) ≤ ∫ x, potential y a x ∂ρ) :
    (∫ x, potential y (fun i => (c i + b i) / 2) x ∂ρ) =
      ((∫ x, potential y c x ∂ρ) + ∫ x, potential y b x ∂ρ) / 2 := by
  have hm0 : (∑ i, m i * ((c i + b i) / 2)) = 0 := by
    calc
      (∑ i, m i * ((c i + b i) / 2)) =
          ((∑ i, m i * c i) + ∑ i, m i * b i) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hc0, hb0]; norm_num
  have hlo := hcmin (fun i => (c i + b i) / 2) hm0
  have hcb := hcmin b hb0
  have hbc := hbmin c hc0
  have hup := integral_mono (hint (fun i => (c i + b i) / 2))
    (((hint c).add (hint b)).div_const 2) (potential_midpoint_le y c b)
  simp only [integral_div, Pi.add_apply, integral_add (hint c) (hint b)] at hup
  linarith

/-- Uniqueness of normalized intercept minimizers.  The only geometric inputs are
connected full support and almost-everywhere strictness of the chosen cells.
No cell boundary differentiability or implicit-function theorem is required. -/
theorem normalized_minimizer_unique (ρ : Measure V) {K : Set V}
    (hK : IsPreconnected K) (hKs : K ⊆ ρ.support)
    (hKae : ∀ᵐ x ∂ρ, x ∈ K) (y : ι → V) (c b m : ι → ℝ) (k : V → ι)
    (hsum : ∑ i, m i = 1) (hc0 : ∑ i, m i * c i = 0)
    (hb0 : ∑ i, m i * b i = 0)
    (hint : ∀ a : ι → ℝ, Integrable (potential y a) ρ)
    (hcmin : ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y c x ∂ρ) ≤ ∫ x, potential y a x ∂ρ)
    (hbmin : ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y b x ∂ρ) ≤ ∫ x, potential y a x ∂ρ)
    (hstrict : ∀ᵐ x ∂ρ, ∀ j, j ≠ k x →
      ⟪x, y j⟫ + c j < ⟪x, y (k x)⟫ + c (k x))
    (hpos : ∀ i, ρ {x | k x = i} ≠ 0) : c = b := by
  have hc : ∀ᵐ x ∂ρ, potential y c x = ⟪x, y (k x)⟫ + c (k x) := by
    filter_upwards [hstrict] with x hx
    apply affine_eq_potential
    intro j
    by_cases hj : j = k x
    · simp only [hj, le_refl]
    · exact (hx j hj).le
  have hb := ae_common_selector_of_integral_midpoint_eq ρ y c b k
    (hint c) (hint b) (hint _) hstrict
    (integral_midpoint_eq_of_minimizers ρ y c b m hc0 hb0 hint hcmin hbmin)
  exact intercept_eq_of_common_selector ρ hK hKs hKae y c b m k hsum hc0 hb0 hc hb hpos

end Problem358.MaxPotential

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Minimizers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem358

variable {ι : Type*} [Fintype ι]

/-- Positive weighted mean-zero coordinates bounded above are bounded below too. -/
theorem normalized_intercept_lower_bound
    (m c : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (hmean : ∑ i, m i * c i = 0) {R : ℝ} (hR : 0 ≤ R)
    (hupper : ∀ i, c i ≤ R) (i : ι) : -R / m i ≤ c i := by
  classical
  have hnonneg : ∀ j, 0 ≤ m j * (R - c j) :=
    fun j => mul_nonneg (hm j).le (sub_nonneg.mpr (hupper j))
  have htotal : (∑ j, m j * (R - c j)) = R := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, hmean]
    ring
  have hi : m i * (R - c i) ≤ R := by
    have hs := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    simpa only [htotal] using hs
  apply (div_le_iff₀ (hm i)).mpr
  have hprod : 0 ≤ m i * R := mul_nonneg (hm i).le hR
  nlinarith

/-- A continuous objective whose coordinate lower bounds control its sublevel sets
attains a minimum on the positive weighted normalization hyperplane. This is the
coercivity step in the prescribed-cell-mass variational argument. -/
theorem exists_minimum_on_normalized_intercepts
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (F : (ι → ℝ) → ℝ) (hF : Continuous F) (B : ℝ)
    (hlower : ∀ c : ι → ℝ, (∑ i, m i * c i) = 0 → ∀ i, c i - B ≤ F c) :
    ∃ c : ι → ℝ, (∑ i, m i * c i) = 0 ∧
      ∀ d : ι → ℝ, (∑ i, m i * d i) = 0 → F c ≤ F d := by
  classical
  let S : Set (ι → ℝ) := {c | (∑ i, m i * c i) = 0 ∧ F c ≤ F 0}
  let R : ℝ := max 0 (F 0 + B)
  have hR : 0 ≤ R := le_max_left _ _
  have hupper : ∀ c ∈ S, ∀ i, c i ≤ R := by
    intro c hc i
    have hci := hlower c hc.1 i
    have hFB : F 0 + B ≤ R := le_max_right _ _
    linarith [hc.2]
  have hclosed : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_le hF continuous_const
  have hbox : S ⊆ Set.Icc (fun i => -R / m i) (fun _ => R) := by
    intro c hc
    exact ⟨fun i => normalized_intercept_lower_bound m c hm hsum hc.1 hR
      (hupper c hc) i, hupper c hc⟩
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed hbox
  have hzero : (0 : ι → ℝ) ∈ S := by simp [S]
  obtain ⟨c, hc, hmin⟩ := hcompact.exists_isMinOn ⟨0, hzero⟩ hF.continuousOn
  refine ⟨c, hc.1, ?_⟩
  intro d hd
  by_cases hle : F d ≤ F 0
  · exact hmin ⟨hd, hle⟩
  · exact hc.2.trans (le_of_not_ge hle)

/-- The mass-residual gradient vanishes if it annihilates the normalization
hyperplane and its unweighted coordinate sum is zero. -/
theorem normalized_stationary_gradient_eq_zero
    (m g : ι → ℝ) (hsum : ∑ i, m i = 1) (hgsum : ∑ i, g i = 0)
    (hstationary : ∀ q : ι → ℝ, (∑ i, m i * q i) = 0 →
      (∑ i, g i * q i) = 0) : g = 0 := by
  classical
  funext i
  let q : ι → ℝ := fun j => (if j = i then 1 else 0) - m i
  have hq : (∑ j, m j * q j) = 0 := by
    simp [q, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
  have hg := hstationary q hq
  simpa [q, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hgsum] using hg

/-- First-order optimality on the weighted normalization hyperplane, in a
form directly applicable after differentiating the integral of a finite maximum. -/
theorem gradient_eq_zero_of_normalized_minimum
    (m g c : ι → ℝ) (hsum : ∑ i, m i = 1) (hgsum : ∑ i, g i = 0)
    (hc : ∑ i, m i * c i = 0) (F : (ι → ℝ) → ℝ)
    (hmin : ∀ d : ι → ℝ, (∑ i, m i * d i) = 0 → F c ≤ F d)
    (hderiv : ∀ q : ι → ℝ,
      HasDerivAt (fun t : ℝ => F (c + t • q)) (∑ i, g i * q i) 0) :
    g = 0 := by
  apply normalized_stationary_gradient_eq_zero m g hsum hgsum
  intro q hq
  have hline : ∀ t : ℝ, (∑ i, m i * (c + t • q) i) = 0 := by
    intro t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
    rw [Finset.sum_add_distrib, hc]
    simp_rw [← mul_assoc, mul_comm (m _) t, mul_assoc]
    rw [← Finset.mul_sum, hq]
    ring
  have hlocal : IsLocalMin (fun t : ℝ => F (c + t • q)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa using hmin (c + t • q) (hline t)
  exact hlocal.hasDerivAt_eq_zero (hderiv q)

/-- Abstract prescribed-mass existence from a coercive potential objective and
its cell-mass directional derivative. Geometry is isolated in `hlower`, `hMsum`,
and `hderiv`; no existence or stationarity assumption is hidden in the conclusion. -/
theorem exists_prescribed_masses_of_variational_objective
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (F : (ι → ℝ) → ℝ) (hF : Continuous F) (B : ℝ)
    (hlower : ∀ c : ι → ℝ, (∑ i, m i * c i) = 0 → ∀ i, c i - B ≤ F c)
    (M : (ι → ℝ) → ι → ℝ) (hMsum : ∀ c, ∑ i, M c i = 1)
    (hderiv : ∀ c q : ι → ℝ,
      HasDerivAt (fun t : ℝ => F (c + t • q))
        (∑ i, (M c i - m i) * q i) 0) :
    ∃ c : ι → ℝ, (∑ i, m i * c i) = 0 ∧ M c = m := by
  classical
  obtain ⟨c, hc, hmin⟩ := exists_minimum_on_normalized_intercepts m hm hsum F hF B hlower
  refine ⟨c, hc, ?_⟩
  have hresidual : (fun i => M c i - m i) = 0 := by
    apply gradient_eq_zero_of_normalized_minimum m _ c hsum _ hc F hmin (hderiv c)
    rw [Finset.sum_sub_distrib, hMsum c, hsum]
    ring
  funext i
  have hi := congrFun hresidual i
  exact sub_eq_zero.mp hi

end Problem358

end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
variable (ρ : Measure V) [IsProbabilityMeasure ρ]

/-- The finite-target variational objective as a function of affine intercepts. -/
def objective (y : ι → V) (m c : ι → ℝ) : ℝ :=
  (∫ x, potential y c x ∂ρ) - ∑ i, m i * c i

theorem continuous_objective (y : ι → V) (m : ι → ℝ) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (hρ : Integrable (fun x : V => ‖x‖) ρ) :
    Continuous (objective ρ y m) := by
  apply Continuous.sub
  · exact (lipschitzWith_integral_potential ρ y
      (fun c => integrable_potential ρ y c L hy hρ)).continuous
  · fun_prop

/-- A cell-mass derivative formula suffices to solve the prescribed mass problem.
The only analytic input beyond integrability is the explicit directional derivative
of the integral of the maximum; normalization and minimization are proved here. -/
theorem exists_prescribed_masses (y : ι → V) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (hρ : Integrable (fun x : V => ‖x‖) ρ)
    (M : (ι → ℝ) → ι → ℝ) (hMsum : ∀ c, ∑ i, M c i = 1)
    (hderiv : ∀ c q : ι → ℝ,
      HasDerivAt (fun t : ℝ => ∫ x, potential y (c + t • q) x ∂ρ)
        (∑ i, M c i * q i) 0) :
    ∃ c : ι → ℝ, (∑ i, m i * c i) = 0 ∧ M c = m := by
  refine exists_prescribed_masses_of_variational_objective m hm hsum
    (objective ρ y m) (continuous_objective ρ y m L hy hρ)
    ((L : ℝ) * ∫ x, ‖x‖ ∂ρ) ?_ M hMsum ?_
  · intro c hc i
    have hi := intercept_le_integral_potential ρ y c L hy hρ i
    simp only [objective, hc, sub_zero]
    linarith
  · intro c q
    have hlin : HasDerivAt (fun t : ℝ => ∑ i, m i * (c + t • q) i)
        (∑ i, m i * q i) 0 := by
      have heq : (fun t : ℝ => ∑ i, m i * (c + t • q) i) =
          (fun t => (∑ i, m i * c i) + t * ∑ i, m i * q i) := by
        funext t
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [heq]
      simpa only [zero_add, one_mul, Pi.add_apply, id_eq] using!
        (hasDerivAt_const 0 (∑ i, m i * c i)).add
          ((hasDerivAt_id 0).mul_const (∑ i, m i * q i))
    simpa only [objective, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] using!
      (hderiv c q).sub hlin

end Problem358.MaxPotential

end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (ρ : Measure V) [IsProbabilityMeasure ρ]

/-- Prescribed finite cell masses, with null affine ties as the only geometric input.
The maximizing selector is globally measurable, including on exceptional tie sets. -/
theorem exists_prescribed_cell_masses (y : ι → V) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (hρ : Integrable (fun x : V => ‖x‖) ρ)
    (hties : ∀ c : ι → ℝ, ∀ᵐ x ∂ρ, ∀ i j, i ≠ j →
      ⟪x, y i⟫ + c i ≠ ⟪x, y j⟫ + c j) :
    ∃ (c : ι → ℝ) (k : V → ι),
      (∑ i, m i * c i) = 0 ∧ Measurable k ∧
      (∀ x j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) ∧
      (∀ i, ρ.real {x | k x = i} = m i) := by
  classical
  have hchoices : ∀ c : ι → ℝ, ∃ k : V → ι, Measurable k ∧
      ∀ x j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x) := by
    intro c
    obtain ⟨k, hk, _, hmax⟩ := exists_measurable_argmax
      (fun i (x : V) => ⟪x, y i⟫ + c i)
      (fun i => ((continuous_id.inner continuous_const).add continuous_const).measurable)
    exact ⟨k, hk, hmax⟩
  choose k hk hmax using hchoices
  have hfib : ∀ c i, MeasurableSet {x | k c x = i} := by
    intro c i
    exact (hk c) (measurableSet_singleton i)
  let M : (ι → ℝ) → ι → ℝ := fun c i => ρ.real {x | k c x = i}
  have hMsum : ∀ c, ∑ i, M c i = 1 := by
    intro c
    have hint := FiniteMaxDerivative.integral_finite_selection (μ := ρ)
      (fun _ : ι => (1 : ℝ)) (k c) (hfib c)
    simpa [M] using hint.symm
  have hderiv : ∀ c q : ι → ℝ,
      HasDerivAt (fun t : ℝ => ∫ x, potential y (c + t • q) x ∂ρ)
        (∑ i, M c i * q i) 0 := by
    intro c q
    have hstrict : ∀ᵐ x ∂ρ, ∀ j, j ≠ k c x →
        ⟪x, y j⟫ + c j < ⟪x, y (k c x)⟫ + c (k c x) := by
      filter_upwards [hties c] with x hx
      intro j hj
      exact lt_of_le_of_ne (hmax c x j) (hx j (k c x) hj)
    have hq : Measurable q := Measurable.of_discrete
    have hi := FiniteMaxDerivative.hasDerivAt_integral_finiteMax
      (μ := ρ) (fun i (x : V) => ⟪x, y i⟫ + c i) q (k c)
      (fun i => ((continuous_id.inner continuous_const).add continuous_const).aestronglyMeasurable)
      (integrable_potential ρ y c L hy hρ) hstrict
      (hq.comp (hk c)).aestronglyMeasurable
    rw [FiniteMaxDerivative.integral_finite_selection q (k c) (hfib c)] at hi
    simpa only [potential, FiniteMaxDerivative.finiteMax, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, add_assoc, M] using! hi
  obtain ⟨c, hc, hMc⟩ := exists_prescribed_masses ρ y m hm hsum L hy hρ M hMsum hderiv
  exact ⟨c, k c, hc, hk c, hmax c, fun i => congrFun hMc i⟩

end Problem358.MaxPotential

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_PrescribedCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Problem358.MaxPotential

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- An absolutely continuous probability with finite first moment realizes every
strictly positive finite mass vector by an affine maximum partition. -/
theorem exists_prescribed_cell_masses_of_ac_volume
    (ρ : Measure (E d)) [IsProbabilityMeasure ρ]
    (hac : ρ ≪ (volume : Measure (E d)))
    (hρ : Integrable (fun x : E d => ‖x‖) ρ)
    (y : ι → E d) (hinj : Function.Injective y) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) :
    ∃ (c : ι → ℝ) (k : E d → ι),
      (∑ i, m i * c i) = 0 ∧ Measurable k ∧
      (∀ x j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) ∧
      (∀ i, ρ.real {x | k x = i} = m i) := by
  let L : NNReal := ∑ i, ‖y i‖₊
  have hL : ∀ i, ‖y i‖ ≤ L := by
    intro i
    have hi : ‖y i‖₊ ≤ L :=
      Finset.single_le_sum (fun j _ => (show (0 : NNReal) ≤ ‖y j‖₊ from zero_le)) (Finset.mem_univ i)
    exact_mod_cast hi
  apply exists_prescribed_cell_masses ρ y m hm hsum L hL hρ
  intro c
  filter_upwards [hac.ae_le (ae_affine_tie_implies_slopes_eq volume y c)] with x hx
  intro i j hij heq
  exact hij (hinj (hx i j heq))

/-- The prescribed-mass affine partition exists for the uniform source on a compact body.
Compactness supplies the first moment; no cell calculus is assumed. -/
theorem exists_prescribed_cell_masses_uniform
    (K : Set (E d)) [IsProbabilityMeasure (uniformMeasure K)]
    (hK : IsCompact K) (y : ι → E d) (hinj : Function.Injective y) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) :
    ∃ (c : ι → ℝ) (k : E d → ι),
      (∑ i, m i * c i) = 0 ∧ Measurable k ∧
      (∀ x j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) ∧
      (∀ i, (uniformMeasure K).real {x | k x = i} = m i) := by
  have hac : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hae : ∀ᵐ x ∂uniformMeasure K, x ∈ K :=
    Measure.ae_smul_measure (ae_restrict_mem hK.measurableSet) _
  have hnorm : Integrable (fun x : E d => ‖x‖) (uniformMeasure K) := by
    have hi := ContinuousOn.integrableOn_compact hK continuous_norm.continuousOn
      (μ := uniformMeasure K)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at hi
  exact exists_prescribed_cell_masses_of_ac_volume (uniformMeasure K) hac hnorm
    y hinj m hm hsum

end Problem358.MaxPotential

end

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace BigOperators Topology ENNReal

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V]

/-- Prescribed cell masses yield the supporting inequality for the integrated
potential. This is the elementary subgradient argument, with no differentiation. -/
theorem integral_subgradient_of_cell_masses (ρ : Measure V) [IsFiniteMeasure ρ]
    (y : ι → V) (c a m : ι → ℝ) (k : V → ι)
    (hk : ∀ i, MeasurableSet {x | k x = i})
    (hmax : ∀ᵐ x ∂ρ, ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x))
    (hmass : ∀ i, ρ.real {x | k x = i} = m i)
    (hc : Integrable (potential y c) ρ) (ha : Integrable (potential y a) ρ) :
    (∫ x, potential y c x ∂ρ) + (∑ i, m i * (a i - c i)) ≤
      ∫ x, potential y a x ∂ρ := by
  have hsel := FiniteMaxDerivative.integrable_finite_selection (μ := ρ)
    (fun i => a i - c i) k hk
  have hle : ∀ᵐ x ∂ρ, potential y c x + (a (k x) - c (k x)) ≤ potential y a x := by
    filter_upwards [hmax] with x hx
    rw [affine_eq_potential y c x (k x) hx]
    linarith [affine_le_potential y a x (k x)]
  have hi := integral_mono_ae (hc.add hsel) ha hle
  simp only [Pi.add_apply] at hi
  rw [integral_add hc hsel, FiniteMaxDerivative.integral_finite_selection (fun i => a i - c i) k hk] at hi
  simpa only [hmass] using hi

/-- Every normalized prescribed-mass solution minimizes the normalized objective. -/
theorem isMin_of_cell_masses (ρ : Measure V) [IsFiniteMeasure ρ]
    (y : ι → V) (c m : ι → ℝ) (k : V → ι)
    (hc0 : ∑ i, m i * c i = 0)
    (hk : ∀ i, MeasurableSet {x | k x = i})
    (hmax : ∀ᵐ x ∂ρ, ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x))
    (hmass : ∀ i, ρ.real {x | k x = i} = m i)
    (hint : ∀ a : ι → ℝ, Integrable (potential y a) ρ) :
    ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y c x ∂ρ) ≤ ∫ x, potential y a x ∂ρ := by
  intro a ha0
  have h := integral_subgradient_of_cell_masses ρ y c a m k hk hmax hmass (hint c) (hint a)
  simpa only [mul_sub, Finset.sum_sub_distrib, ha0, hc0, sub_self, add_zero] using h

/-- Prescribed positive masses determine normalized intercepts uniquely for a
connected full-support source. Only affine null ties, not cell calculus, are needed. -/
theorem prescribed_cell_masses_unique (ρ : Measure V) [IsFiniteMeasure ρ] {K : Set V}
    (hK : IsPreconnected K) (hKs : K ⊆ ρ.support) (hKae : ∀ᵐ x ∂ρ, x ∈ K)
    (y : ι → V) (c b m : ι → ℝ) (k l : V → ι)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (hc0 : ∑ i, m i * c i = 0) (hb0 : ∑ i, m i * b i = 0)
    (hk : ∀ i, MeasurableSet {x | k x = i})
    (hl : ∀ i, MeasurableSet {x | l x = i})
    (hmaxc : ∀ᵐ x ∂ρ, ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x))
    (hmaxb : ∀ᵐ x ∂ρ, ∀ j, ⟪x, y j⟫ + b j ≤ ⟪x, y (l x)⟫ + b (l x))
    (hmassc : ∀ i, ρ.real {x | k x = i} = m i)
    (hmassb : ∀ i, ρ.real {x | l x = i} = m i)
    (hties : ∀ᵐ x ∂ρ, ∀ i j, i ≠ j →
      ⟪x, y i⟫ + c i ≠ ⟪x, y j⟫ + c j)
    (hint : ∀ a : ι → ℝ, Integrable (potential y a) ρ) : c = b := by
  apply normalized_minimizer_unique ρ hK hKs hKae y c b m k hsum hc0 hb0 hint
    (isMin_of_cell_masses ρ y c m k hc0 hk hmaxc hmassc hint)
    (isMin_of_cell_masses ρ y b m l hb0 hl hmaxb hmassb hint)
  · filter_upwards [hties, hmaxc] with x hx hmax
    intro j hj
    exact lt_of_le_of_ne (hmax j) (hx j (k x) hj)
  · intro i hz
    have hzero : ρ.real {x | k x = i} = 0 := by simp [measureReal_def, hz]
    have := hm i
    rw [hmassc i] at hzero
    linarith

end Problem358.MaxPotential

end

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Problem358.MaxPotential

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- On a compact convex body, positive prescribed masses and weighted normalization
uniquely determine the intercepts of distinct affine sites. -/
theorem uniform_prescribed_cell_masses_unique {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (y : ι → E d) (hy : Function.Injective y) (c b m : ι → ℝ) (k l : E d → ι)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (hc0 : ∑ i, m i * c i = 0) (hb0 : ∑ i, m i * b i = 0)
    (hk : ∀ i, MeasurableSet {x | k x = i})
    (hl : ∀ i, MeasurableSet {x | l x = i})
    (hmaxc : ∀ᵐ x ∂uniformMeasure K, ∀ j,
      ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x))
    (hmaxb : ∀ᵐ x ∂uniformMeasure K, ∀ j,
      ⟪x, y j⟫ + b j ≤ ⟪x, y (l x)⟫ + b (l x))
    (hmassc : ∀ i, (uniformMeasure K).real {x | k x = i} = m i)
    (hmassb : ∀ i, (uniformMeasure K).real {x | l x = i} = m i) : c = b := by
  let := UniformSource.probability hK hne
  apply prescribed_cell_masses_unique (uniformMeasure K) hconv.isPreconnected
    (UniformSource.subset_support hK hconv hne) (UniformSource.ae_mem hK.measurableSet)
    y c b m k l hm hsum hc0 hb0 hk hl hmaxc hmaxb hmassc hmassb
  · filter_upwards [uniform_ae_affine_tie_implies_slopes_eq K y c] with x hx
    intro i j hij heq
    exact hij (hy (hx i j heq))
  · intro a
    exact UniformSource.integrable_continuousOn hK (continuous_potential y a).continuousOn

end Problem358.MaxPotential

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_FixedMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ContDiff

namespace Problem358.FixedMassIntercepts

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The actual closed-cell mass vector, without a choice of maximizing selector. -/
def masses (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) : ι → ℝ :=
  fun i => (uniformMeasure K).real (CellGeometry.closedCell K y c i)

/-- Null ties identify every maximizing selector's fibers with the closed cells. -/
theorem closedCell_ae_eq_selector {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (hy : Function.Injective y) (c : ι → ℝ)
    (k : E d → ι)
    (hk : ∀ x j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) (i : ι) :
    CellGeometry.closedCell K y c i =ᵐ[uniformMeasure K] {x | k x = i} := by
  filter_upwards [UniformSource.ae_mem hK,
    uniform_ae_affine_tie_implies_slopes_eq K y c] with x hx ht
  apply propext
  change (x ∈ K ∧ ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y i⟫ + c i) ↔ k x = i
  constructor
  · intro hc
    apply hy
    exact ht (k x) i (le_antisymm (hc.2 (k x)) (hk x i))
  · intro hi
    exact ⟨hx, fun j => by simpa only [hi] using hk x j⟩

/-- The selector law and geometric closed-cell masses have exactly the same real masses. -/
theorem masses_eq_selector {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (hy : Function.Injective y) (c : ι → ℝ)
    (k : E d → ι)
    (hk : ∀ x j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) (i : ι) :
    masses K y c i = (uniformMeasure K).real {x | k x = i} := by
  exact congrArg ENNReal.toReal
    (measure_congr (closedCell_ae_eq_selector hK y hy c k hk i))

variable [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Prescribed positive masses uniquely determine a normalized intercept vector.
This is an actual existence and uniqueness result for the geometric cells; it has
no cell-differentiability hypothesis. -/
theorem existsUnique_normalized {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y) :
    ∃! c : CellLaplacian.normalizedSpace m, masses K y c = m := by
  let := UniformSource.probability hK hne
  obtain ⟨c, k, hc, hk, hmax, hmass⟩ :=
    MaxPotential.exists_prescribed_cell_masses_uniform K hK y hy m hm hsum
  have hcm : masses K y c = m := by
    funext i
    exact (masses_eq_selector hK.measurableSet y hy c k hmax i).trans (hmass i)
  refine ⟨⟨c, hc⟩, hcm, ?_⟩
  intro b hb
  obtain ⟨l, hl, _, hlmax⟩ := exists_measurable_argmax
    (fun i (x : E d) => ⟪x, y i⟫ + (b : ι → ℝ) i)
    (fun i => ((continuous_id.inner continuous_const).add continuous_const).measurable)
  apply Subtype.ext
  apply MaxPotential.uniform_prescribed_cell_masses_unique hK hconv hne
    y hy b c m l k hm hsum b.property hc
    (fun i => hl (measurableSet_singleton i))
    (fun i => hk (measurableSet_singleton i))
    (Eventually.of_forall hlmax) (Eventually.of_forall hmax)
  · intro i
    exact (masses_eq_selector hK.measurableSet y hy b l hlmax i).symm.trans
      (congrFun hb i)
  · exact hmass

/-- The canonical normalized intercept vector. It is zero on configurations with
repeated sites; all uses of the prescribed-mass specification have distinct sites. -/
def intercepts {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) : CellLaplacian.normalizedSpace m :=
  if hy : Function.Injective y then
    (existsUnique_normalized hK hconv hne m hm hsum y hy).choose
  else 0

end Problem358.FixedMassIntercepts

end

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The actual closed-cell masses, restricted to normalized intercepts. -/
def normalizedMassMap (K : Set (E d)) (m : ι → ℝ) :
    ((ι → E d) × CellLaplacian.normalizedSpace m) → (ι → ℝ) :=
  fun p i => (uniformMeasure K).real (closedCell K p.1 p.2 i)

/-- Include the normalization hyperplane into the unrestricted configuration space. -/
def normalizedConfigInclusion (m : ι → ℝ) :
    ((ι → E d) × CellLaplacian.normalizedSpace m) →L[ℝ] ((ι → E d) × (ι → ℝ)) :=
  (ContinuousLinearMap.id ℝ (ι → E d)).prodMap (CellLaplacian.normalizedSpace m).subtypeL

@[simp] theorem normalizedConfigInclusion_apply (m : ι → ℝ)
    (p : (ι → E d) × CellLaplacian.normalizedSpace m) :
    normalizedConfigInclusion m p = (p.1, (p.2 : ι → ℝ)) := rfl

end Problem358.CellGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_LineDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace Problem358.FaceDerivative

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A face contribution to the mass derivative, with its scalar and vector moments
made explicit. The input is the site and intercept variation `(v,r)`. -/
def linearMap (A M : ℝ) (B : V) : V × ℝ →L[ℝ] ℝ :=
  A⁻¹ • (M • ContinuousLinearMap.snd ℝ V ℝ +
    (innerSL ℝ B).comp (ContinuousLinearMap.fst ℝ V ℝ))

@[simp] lemma linearMap_apply (A M : ℝ) (B v : V) (r : ℝ) :
    linearMap A M B (v, r) = (r / A) * M + (1 / A) * ⟪v, B⟫_ℝ := by
  change A⁻¹ * (M * r + ⟪B, v⟫_ℝ) = _
  rw [real_inner_comm B v]
  ring

section Finite
variable {ι : Type*}

/-- Extract the difference of the two site and intercept perturbations. -/
def pairVariation (i j : ι) : ((ι → V) × (ι → ℝ)) →L[ℝ] V × ℝ :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => V) i -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => V) j) : (ι → V) →L[ℝ] V).comp
    (ContinuousLinearMap.fst ℝ (ι → V) (ι → ℝ))).prod
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) : (ι → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.snd ℝ (ι → V) (ι → ℝ)))

@[simp] lemma pairVariation_apply (i j : ι) (v : ι → V) (r : ι → ℝ) :
    pairVariation i j (v, r) = (v i - v j, r i - r j) := rfl

/-- Face derivatives assembled into one continuous linear cell-mass derivative.
The index set can exclude the diagonal or any inactive faces. -/
def cellLinearMap (J : Finset ι) (i : ι) (A M : ι → ℝ) (B : ι → V) :
    ((ι → V) × (ι → ℝ)) →L[ℝ] ℝ :=
  ∑ j ∈ J, (linearMap (A j) (M j) (B j)).comp (pairVariation i j)

@[simp] lemma cellLinearMap_apply (J : Finset ι) (i : ι)
    (A M : ι → ℝ) (B v : ι → V) (r : ι → ℝ) :
    cellLinearMap J i A M B (v, r) =
      ∑ j ∈ J, (((r i - r j) / A j) * M j +
        (1 / A j) * ⟪v i - v j, B j⟫_ℝ) := by
  simp [cellLinearMap]

end Finite

end Problem358.FaceDerivative

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_MassDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized cell-mass line derivative with canonical coefficients. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual mass derivative as a bounded linear map in sites and intercepts. -/
def massLinearMap (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i : ι) :
    ((ι → E d) × (ι → ℝ)) →L[ℝ] ℝ :=
  FaceDerivative.cellLinearMap Finset.univ i (fun _ => 1)
    (PositiveFacet.canonicalFaceWeight K y c i) (faceMoment K y c i)

omit [DecidableEq ι] in
@[simp] theorem massLinearMap_apply (K : Set (E d))
    (y v : ι → E d) (c r : ι → ℝ) (i : ι) :
    massLinearMap K y c i (v, r) =
      ∑ j, (PositiveFacet.canonicalFaceWeight K y c i j * (r i - r j) +
        ⟪faceMoment K y c i j, v i - v j⟫) := by
  simp only [massLinearMap, FaceDerivative.cellLinearMap_apply, div_one, one_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm, real_inner_comm]

/-- Distinct configurations with strictly positive actual cell masses. -/
def positiveMassConfigurations (K : Set (E d)) : Set ((ι → E d) × (ι → ℝ)) :=
  {p | Function.Injective p.1 ∧ ∀ i, 0 < (uniformMeasure K).real (closedCell K p.1 p.2 i)}

end Problem358.CellGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Midpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral identities for the midpoint cell estimate

The integral estimates assume domination by a midpoint coupling.
-/

/-!+# Transfer of midpoint couplings from coordinates to Euclidean space

The construction of a coordinate coupling remains an explicit hypothesis.
The volume-preserving change of representation includes
normalization and the midpoint domination inequality.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem358.MidpointCoordinates

abbrev Coordinates (d : ℕ) := Fin d → ℝ

def coordinateUniform {d : ℕ} (K : Set (E d)) : Measure (Coordinates d) :=
  (volume ((WithLp.toLp 2) ⁻¹' K))⁻¹ •
    volume.restrict ((WithLp.toLp 2) ⁻¹' K)

def liftPair {d : ℕ} (p : Coordinates d × Coordinates d) : E d × E d :=
  (WithLp.toLp 2 p.1, WithLp.toLp 2 p.2)

end Problem358.MidpointCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_MomentAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.MidpointEnergy
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The concave quadratic used in the midpoint argument. -/
def quadraticPotential (R : ℝ) (x : F) : ℝ := R ^ 2 - ‖x‖ ^ 2

end Problem358.MidpointEnergy

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_TriangularRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem358.TriangularRecursion

/-- Conditional scalar sampling functions indexed by the length of the existing prefix. -/
abbrev ConditionalFamily := (n : ℕ) → (Fin n → ℝ) → ℝ → ℝ

/-- Successive conditional sampling, using the last input coordinate at each step. -/
def sample (Q : ConditionalFamily) : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)
  | 0 => fun s => s
  | n + 1 => fun s =>
      Fin.snoc (sample Q n (Fin.init s))
        (Q n (sample Q n (Fin.init s)) (s (Fin.last n)))

@[simp] theorem sample_init (Q : ConditionalFamily) (n : ℕ) (s : Fin (n+1) → ℝ) :
    Fin.init (sample Q (n+1) s) = sample Q n (Fin.init s) := by
  simp [sample]

@[simp] theorem sample_last (Q : ConditionalFamily) (n : ℕ) (s : Fin (n+1) → ℝ) :
    sample Q (n+1) s (Fin.last n) = Q n (sample Q n (Fin.init s)) (s (Fin.last n)) := by
  simp [sample]

@[simp] theorem sample_snoc (Q : ConditionalFamily) (n : ℕ) (s : Fin n → ℝ) (t : ℝ) :
    sample Q (n+1) (Fin.snoc s t) = Fin.snoc (sample Q n s) (Q n (sample Q n s) t) := by
  simp [sample]

/-- The coupled midpoint of two samplers driven by the same parameter tuple. -/
def midpoint (Q R : ConditionalFamily) (n : ℕ) (s : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (sample Q n s i + sample R n s i) / 2

/-- The last-coordinate midpoint fibre, with the original input prefix as parameter. -/
def midpointFiber (Q R : ConditionalFamily) (n : ℕ) (s : Fin n → ℝ) (t : ℝ) : ℝ :=
  (Q n (sample Q n s) t + R n (sample R n s) t) / 2

end Problem358.TriangularRecursion

end

/-! Finite-prefix density normalization for the canonical triangular sampler.
These are conditional identities, not existence of geometric section data. -/

noncomputable section
open Set
open scoped BigOperators
open Problem358.TriangularRecursion

namespace Problem358.TriangularDensity

abbrev Coordinates (n : ℕ) := Fin n → ℝ

def InUnitCube {n : ℕ} (u : Coordinates n) : Prop := ∀ i, u i ∈ Ioo (0 : ℝ) 1

/-- Recursive product of the canonical sampler's longitudinal derivatives. -/
def diagonalProduct (q dq : ConditionalFamily) : (n : ℕ) → Coordinates n → ℝ
  | 0, _ => 1
  | n + 1, u => diagonalProduct q dq n (Fin.init u) *
      dq n (sample q n (Fin.init u)) (u (Fin.last n))

@[simp] theorem diagonalProduct_snoc (q dq : ConditionalFamily) (n : ℕ)
    (s : Coordinates n) (t : ℝ) :
    diagonalProduct q dq (n + 1) (Fin.snoc s t) =
      diagonalProduct q dq n s * dq n (sample q n s) t := by
  simp only [diagonalProduct, Fin.init_snoc, Fin.snoc_last]

end Problem358.TriangularDensity

end

/-! Positivity and almost-everywhere parameter support for finite triangular samplers. -/

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_NormalizedSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Classical
open scoped ENNReal

namespace Problem358.NormalizedSections

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

def sectionMass (ν : Measure B) (q : A → B → ℝ≥0∞) (a : A) : ℝ≥0∞ :=
  ∫⁻ b, q a b ∂ν

def sectionDensity (ν : Measure B) (q : A → B → ℝ≥0∞) (a : A) (b : B) : ℝ≥0∞ :=
  q a b / sectionMass ν q a

def sectionLaw (ν : Measure B) (q : A → B → ℝ≥0∞) (a : A) : Measure B :=
  ν.withDensity (sectionDensity ν q a)

theorem measurable_sectionMass (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) :
    Measurable (sectionMass ν q) := hq.lintegral_prod_right

/-- The normalized section laws form a genuine measurable kernel. -/
def sectionKernel (ν : Measure B) [SFinite ν] (q : A → B → ℝ≥0∞) :
    ProbabilityTheory.Kernel A B :=
  (ProbabilityTheory.Kernel.const A ν).withDensity (sectionDensity ν q)

/-- Indicator density of a measurable region in a product space. -/
def setDensity (U : Set (A × B)) (a : A) (b : B) : ℝ≥0∞ :=
  U.indicator (fun _ => 1) (a, b)

theorem measurable_setDensity {U : Set (A × B)} (hU : MeasurableSet U) :
    Measurable (Function.uncurry (setDensity U)) :=
  (measurable_const.indicator hU).comp (measurable_fst.prodMk measurable_snd)

/-- Positive, finite fibers form a measurable parameter set. -/
def goodSections (ν : Measure B) (q : A → B → ℝ≥0∞) : Set A :=
  {a | sectionMass ν q a ≠ 0 ∧ sectionMass ν q a ≠ ∞}

theorem measurableSet_goodSections (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) :
    MeasurableSet (goodSections ν q) := by
  exact (measurableSet_eq_fun (measurable_sectionMass ν hq) measurable_const).compl.inter
    (measurableSet_eq_fun (measurable_sectionMass ν hq) measurable_const).compl

/-- Complete the conditional kernel by any fixed point on exceptional fibers. -/
def completedSectionKernel (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (b₀ : B) :
    ProbabilityTheory.Kernel A B :=
  ProbabilityTheory.Kernel.piecewise (measurableSet_goodSections ν hq)
    (sectionKernel ν q) (ProbabilityTheory.Kernel.const A (Measure.dirac b₀))

end Problem358.NormalizedSections

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_PrefixSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem358.FinitePrefix

abbrev Coordinates (n : ℕ) := Fin n → ℝ

/-- Append two finite coordinate blocks, with their usual sup norms. -/
def append (n m : ℕ) :
    (Coordinates n × Coordinates m) ≃L[ℝ] Coordinates (n + m) where
  __ := Fin.appendHomeomorph n m
  map_add' p q := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_smul' c p := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

@[simp] theorem append_apply (n m : ℕ) (p : Coordinates n × Coordinates m) :
    append n m p = Fin.append p.1 p.2 := rfl

/-- Reassemble a bounded prefix and its complementary coordinate block. -/
def join {n d : ℕ} (h : n ≤ d) :
    (Coordinates n × Coordinates (d - n)) ≃L[ℝ] Coordinates d :=
  (append n (d - n)).trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin d => ℝ)
      (finCongr (Nat.add_sub_of_le h)))

/-- Index of a coordinate in the prefix. -/
def leftIndex {n d : ℕ} (h : n ≤ d) (i : Fin n) : Fin d := i.castLE h

/-- Index of a coordinate in the complementary block. -/
def rightIndex {n d : ℕ} (h : n ≤ d) (i : Fin (d - n)) : Fin d :=
  Fin.cast (Nat.add_sub_of_le h) (Fin.natAdd n i)

@[simp] theorem join_left {n d : ℕ} (h : n ≤ d)
    (a : Coordinates n) (b : Coordinates (d - n)) (i : Fin n) :
    join h (a, b) (leftIndex h i) = a i := by
  change Fin.append a b (Fin.cast (Nat.add_sub_of_le h).symm (leftIndex h i)) = a i
  have hi : Fin.cast (Nat.add_sub_of_le h).symm (leftIndex h i) =
      Fin.castAdd (d - n) i := by ext; rfl
  rw [hi, Fin.append_left]

@[simp] theorem join_right {n d : ℕ} (h : n ≤ d)
    (a : Coordinates n) (b : Coordinates (d - n)) (i : Fin (d - n)) :
    join h (a, b) (rightIndex h i) = b i := by
  change Fin.append a b
    (Fin.cast (Nat.add_sub_of_le h).symm (Fin.cast (Nat.add_sub_of_le h) (Fin.natAdd n i))) = b i
  simp

/-- The actual bounded prefix. -/
def headBlock {n d : ℕ} (h : n ≤ d) (x : Coordinates d) : Coordinates n :=
  fun i => x (leftIndex h i)

/-- The remaining coordinates after a bounded prefix. -/
def tailBlock {n d : ℕ} (h : n ≤ d) (x : Coordinates d) : Coordinates (d - n) :=
  fun i => x (rightIndex h i)

@[simp] theorem prefix_join {n d : ℕ} (h : n ≤ d)
    (a : Coordinates n) (b : Coordinates (d - n)) : headBlock h (join h (a,b)) = a := by
  ext i
  exact join_left h a b i

@[simp] theorem suffix_join {n d : ℕ} (h : n ≤ d)
    (a : Coordinates n) (b : Coordinates (d - n)) : tailBlock h (join h (a,b)) = b := by
  ext i
  exact join_right h a b i

@[simp] theorem join_symm_apply {n d : ℕ} (h : n ≤ d) (x : Coordinates d) :
    (join h).symm x = (headBlock h x, tailBlock h x) := by
  obtain ⟨⟨a,b⟩, rfl⟩ := (join h).surjective x
  simp

@[simp] theorem join_prefix_suffix {n d : ℕ} (h : n ≤ d) (x : Coordinates d) :
    join h (headBlock h x, tailBlock h x) = x := by
  rw [← join_symm_apply]
  exact (join h).apply_symm_apply x

@[simp] theorem init_headBlock {n d : ℕ} (h : n < d) (x : Coordinates d) :
    Fin.init (headBlock (Nat.succ_le_of_lt h) x) = headBlock h.le x := by
  ext i
  rfl

@[simp] theorem last_headBlock {n d : ℕ} (h : n < d) (x : Coordinates d) :
    headBlock (Nat.succ_le_of_lt h) x (Fin.last n) = x ⟨n,h⟩ := rfl

def scalarBlock : ℝ ≃L[ℝ] Coordinates 1 :=
  (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).symm

/-- Regroup a prefix, its next scalar coordinate, and the final remainder. -/
def tripleSplit {n d : ℕ} (h : n < d) :
    (Coordinates n × (ℝ × Coordinates (d - (n + 1)))) ≃L[ℝ] Coordinates d :=
  ((ContinuousLinearEquiv.refl ℝ (Coordinates n)).prodCongr
    ((scalarBlock.prodCongr (ContinuousLinearEquiv.refl ℝ _)).trans
      (append 1 (d - (n + 1))))).trans
    ((append n (1 + (d - (n + 1)))).trans
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin d => ℝ)
        (finCongr (by omega : n + (1 + (d - (n + 1))) = d))))

@[simp] theorem tripleSplit_left {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n+1))) (i : Fin n) :
    tripleSplit h (x,t,z) (leftIndex h.le i) = x i := by
  change Fin.append x (Fin.append (fun _ : Fin 1 => t) z)
    (Fin.cast (by omega : d = n + (1 + (d - (n+1)))) (leftIndex h.le i)) = x i
  have hi : Fin.cast (by omega : d = n + (1 + (d - (n+1)))) (leftIndex h.le i) =
      Fin.castAdd (1 + (d - (n+1))) i := by ext; rfl
  rw [hi, Fin.append_left]

@[simp] theorem tripleSplit_next {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n+1))) :
    tripleSplit h (x,t,z) ⟨n,h⟩ = t := by
  change Fin.append x (Fin.append (fun _ : Fin 1 => t) z)
    (Fin.cast (by omega : d = n + (1 + (d - (n+1)))) ⟨n,h⟩) = t
  have hi : Fin.cast (by omega : d = n + (1 + (d - (n+1)))) ⟨n,h⟩ =
      Fin.natAdd n (Fin.castAdd (d - (n+1)) (0 : Fin 1)) := by ext; rfl
  rw [hi, Fin.append_right, Fin.append_left]

/-- Taking the next prefix after installing a scalar is exactly `Fin.snoc`. -/
@[simp] theorem headBlock_tripleSplit {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n+1))) :
    headBlock (Nat.succ_le_of_lt h) (tripleSplit h (x,t,z)) = Fin.snoc x t := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    change tripleSplit h (x,t,z) ⟨n,h⟩ = t
    exact tripleSplit_next h x t z
  · change tripleSplit h (x,t,z) (leftIndex h.le j) = _
    simp

/-- Membership of the reconstructed point gives the precise next-prefix invariant. -/
theorem snoc_mem_prefix_image {n d : ℕ} (h : n < d)
    {K : Set (Coordinates d)} {x : Coordinates n} {t : ℝ}
    {z : Coordinates (d - (n+1))}
    (hy : tripleSplit h (x,t,z) ∈ interior K) :
    Fin.snoc x t ∈ headBlock (Nat.succ_le_of_lt h) '' interior K := by
  exact ⟨tripleSplit h (x,t,z), hy, headBlock_tripleSplit h x t z⟩

end Problem358.FinitePrefix

end

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace Problem358.FinitePrefix

/-- The valid coordinate prefixes are the projections of the body's interior. -/
def prefixDomain {d n : ℕ} (K : Set (Coordinates d)) (h : n ≤ d) : Set (Coordinates n) :=
  headBlock h '' interior K

/-- The remaining section after a fixed coordinate prefix. -/
def prefixSection {d n : ℕ} (K : Set (Coordinates d)) (h : n ≤ d)
    (a : Coordinates n) : Set (Coordinates (d - n)) :=
  {b | join h (a,b) ∈ K}

@[simp] lemma join_zero (d : ℕ) (a : Coordinates 0) (b : Coordinates d) :
    join (Nat.zero_le d) (a,b) = b := by
  ext i
  have hi : rightIndex (Nat.zero_le d) i = i := by
    ext
    simp [rightIndex]
  simpa only [hi] using join_right (Nat.zero_le d) a b i

@[simp] lemma join_full {d : ℕ} (a : Coordinates d) (b : Coordinates (d-d)) :
    join (le_refl d) (a,b) = a := by
  ext i
  exact join_left (le_refl d) a b i

@[simp] lemma prefixDomain_full {d : ℕ} (K : Set (Coordinates d)) :
    prefixDomain K (le_refl d) = interior K := by
  change id '' interior K = interior K
  exact image_id _

end Problem358.FinitePrefix

end

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Problem358.FinitePrefix

/-- Before any coordinates are chosen, the remaining section is the full body. -/
@[simp] theorem prefixSection_zero {d : ℕ} (K : Set (Coordinates d))
    (a : Coordinates 0) :
    prefixSection K (Nat.zero_le d) a = K := by
  ext b
  simp only [prefixSection, mem_ofPred_eq, join_zero]

/-- The initial density is the volume of the full body. -/
@[simp] theorem volume_prefixSection_zero {d : ℕ} (K : Set (Coordinates d))
    (a : Coordinates 0) :
    volume (prefixSection K (Nat.zero_le d) a) = volume K := by
  rw [prefixSection_zero]

@[simp] theorem volumeReal_prefixSection_zero {d : ℕ} (K : Set (Coordinates d))
    (a : Coordinates 0) :
    (volume (prefixSection K (Nat.zero_le d) a)).toReal = (volume K).toReal := by
  rw [volume_prefixSection_zero]

end Problem358.FinitePrefix

end

noncomputable section
open MeasureTheory

namespace Problem358.FinitePrefix

/-- The final coordinates of the three-block split are its final input block. -/
@[simp] theorem tripleSplit_right {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n + 1)))
    (i : Fin (d - (n + 1))) :
    tripleSplit h (x, t, z) (rightIndex (Nat.succ_le_of_lt h) i) = z i := by
  change Fin.append x (Fin.append (fun _ : Fin 1 => t) z)
    (Fin.cast (by omega : d = n + (1 + (d - (n+1))))
      (rightIndex (Nat.succ_le_of_lt h) i)) = z i
  have hi : Fin.cast (by omega : d = n + (1 + (d - (n+1))))
      (rightIndex (Nat.succ_le_of_lt h) i) =
      Fin.natAdd n (Fin.natAdd 1 i) := by
    ext
    simp only [rightIndex, Fin.val_cast, Fin.val_natAdd]
    omega
  rw [hi, Fin.append_right, Fin.append_right]

@[simp] theorem tailBlock_tripleSplit {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n + 1))) :
    tailBlock (Nat.succ_le_of_lt h) (tripleSplit h (x, t, z)) = z := by
  ext i
  exact tripleSplit_right h x t z i

/-- Regroup the next scalar coordinate with the remaining tail. -/
def tailJoin {n d : ℕ} (h : n < d) :
    (ℝ × Coordinates (d - (n + 1))) ≃L[ℝ] Coordinates (d - n) :=
  (((ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).symm.prodCongr
    (ContinuousLinearEquiv.refl ℝ _)).trans (append 1 (d - (n + 1)))).trans
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (d - n) => ℝ)
        (finCongr (by omega : 1 + (d - (n + 1)) = d - n)))

end Problem358.FinitePrefix

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_TriangularDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.TriangularDomination

/-- A weighted change of variables that only needs an upper change-of-variables bound. -/
def WeightedDomination {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (F : A → B) (J : A → ℝ≥0∞) : Prop :=
  ∀ w : B → ℝ≥0∞, Measurable w →
    (∫⁻ a, J a * w (F a) ∂μ) ≤ ∫⁻ b, w b ∂ν

end Problem358.TriangularDomination

end

/-! The measurable geometric Jacobian weight for two finite triangular samplers.
The weight is defined globally, but its identification with the geometric mean
of diagonal products only uses positivity on valid sampling parameters. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open Problem358.TriangularRecursion

namespace Problem358.TriangularDensity

/-- Product of the geometric means of the paired longitudinal derivatives. -/
def geometricWeight (q r dq dr : ConditionalFamily) :
    (n : ℕ) → Coordinates n → ℝ≥0∞
  | 0, _ => 1
  | n + 1, u => geometricWeight q r dq dr n (Fin.init u) *
      ENNReal.ofReal (Real.sqrt
        (dq n (sample q n (Fin.init u)) (u (Fin.last n)) *
         dr n (sample r n (Fin.init u)) (u (Fin.last n))))

@[simp] theorem geometricWeight_zero (q r dq dr : ConditionalFamily)
    (u : Coordinates 0) : geometricWeight q r dq dr 0 u = 1 := rfl

@[simp] theorem geometricWeight_snoc (q r dq dr : ConditionalFamily) (n : ℕ)
    (s : Coordinates n) (t : ℝ) :
    geometricWeight q r dq dr (n + 1) (Fin.snoc s t) =
      geometricWeight q r dq dr n s * ENNReal.ofReal (Real.sqrt
        (dq n (sample q n s) t * dr n (sample r n s) t)) := by
  simp only [geometricWeight, Fin.init_snoc, Fin.snoc_last]

end Problem358.TriangularDensity

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_PrefixSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace Problem358.FinitePrefix

/-- The same body in prefix/next-coordinate/remainder coordinates. -/
def stepBody {d n : ℕ} (K : Set (Coordinates d)) (h : n < d) :
    Set (Coordinates n × (ℝ × Coordinates (d-(n+1)))) :=
  tripleSplit h ⁻¹' K

lemma interior_stepBody {d n : ℕ} (K : Set (Coordinates d)) (h : n < d) :
    interior (stepBody K h) = tripleSplit h ⁻¹' interior K :=
  ((tripleSplit h).toHomeomorph.preimage_interior K).symm

@[simp] lemma headBlock_tripleSplit_prefix {d n : ℕ} (h : n < d)
    (a : Coordinates n) (t : ℝ) (b : Coordinates (d-(n+1))) :
    headBlock h.le (tripleSplit h (a,t,b)) = a := by
  ext i
  exact tripleSplit_left h a t b i

lemma valid_stepBody {d n : ℕ} (K : Set (Coordinates d)) (h : n < d) :
    ConvexTriangularSampler.valid (stepBody K h) = prefixDomain K h.le := by
  ext a
  constructor
  · rintro ⟨⟨a',t,b⟩,hp,ha⟩
    have haa : a' = a := ha
    subst a'
    rw [interior_stepBody] at hp
    exact ⟨tripleSplit h (a,t,b),hp,headBlock_tripleSplit_prefix h a t b⟩
  · rintro ⟨x,hx,ha⟩
    obtain ⟨⟨a',t,b⟩,rfl⟩ := (tripleSplit h).surjective x
    have haa : a' = a := (headBlock_tripleSplit_prefix h a' t b).symm.trans ha
    subst a'
    refine ⟨(a,t,b),?_,rfl⟩
    rw [interior_stepBody]
    exact hx

/-- Each actual finite prefix admits a globally measurable next-coordinate quantile.
The conditional law is the precise normalized remaining-body scalar marginal. -/
theorem exists_prefix_quantile {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d) :
    ∃ Q : Coordinates n × ℝ → ℝ, Measurable Q ∧
      (∀ a ∈ prefixDomain K h.le, Measure.map (fun s => Q (a,s))
        (volume.restrict (Ioo (0 : ℝ) 1)) =
        Measure.map Prod.fst
          (((volume.prod volume) (ConvexTriangularSampler.sectionBody (stepBody K h) a))⁻¹ •
            (volume.prod volume).restrict
              (ConvexTriangularSampler.sectionBody (stepBody K h) a))) ∧
      (∀ a ∈ prefixDomain K h.le, ∀ s ∈ Ioo (0 : ℝ) 1,
        Fin.snoc a (Q (a,s)) ∈ prefixDomain K (Nat.succ_le_of_lt h)) ∧
      (∀ a ∈ prefixDomain K h.le, ∀ s ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun t => Q (a,t))
          ((ConvexTriangularSampler.sectionDensity (stepBody K h) volume a (Q (a,s)))⁻¹) s) ∧
      (∀ a ∈ prefixDomain K h.le, ∀ s ∈ Ioo (0 : ℝ) 1,
        0 < (ConvexTriangularSampler.sectionDensity (stepBody K h) volume a (Q (a,s)))⁻¹) := by
  have hk : IsCompact (stepBody K h) :=
    (tripleSplit h).toHomeomorph.isCompact_preimage.mpr hK
  have hcv : Convex ℝ (stepBody K h) := hc.linear_preimage (tripleSplit h).toLinearMap
  obtain ⟨Q,hQ,hlaw,hmem,hderiv,hstrict⟩ :=
    ConvexTriangularSampler.exists_measurable_conditional_quantile
      (volume : Measure (Coordinates (d-(n+1)))) hk hcv
  refine ⟨Q,hQ,?_,?_,?_,?_⟩
  · simpa only [valid_stepBody] using hlaw
  · intro a ha s hs
    rw [← valid_stepBody K h] at ha
    obtain ⟨b,hb⟩ := hmem a ha s hs
    rw [interior_stepBody] at hb
    exact snoc_mem_prefix_image h hb
  · intro a ha s hs
    rw [← valid_stepBody K h] at ha
    simpa only [ConvexTriangularSampler.sectionDensity, inv_div] using hderiv a ha s hs
  · intro a ha s hs
    rw [← valid_stepBody K h] at ha
    obtain ⟨b,hb⟩ := hmem a ha s hs
    have hsec : (Q (a,s),b) ∈ interior
        (ConvexTriangularSampler.sectionBody (stepBody K h) a) :=
      preimage_interior_subset_interior_preimage
        (continuous_const.prodMk continuous_id) hb
    have hparent : 0 < (volume.prod volume).real
        (ConvexTriangularSampler.sectionBody (stepBody K h) a) :=
      ENNReal.toReal_pos (measure_pos_of_nonempty_interior _ ⟨(Q (a,s),b),hsec⟩).ne'
        (ConvexTriangularSampler.isCompact_sectionBody hk a).measure_ne_top
    have hchild : 0 < volume.real
        (AffineSlice.fiber (ConvexTriangularSampler.sectionBody (stepBody K h) a) (Q (a,s))) :=
      AffineSlice.fiberMeasureReal_pos volume
        (ConvexTriangularSampler.isCompact_sectionBody hk a) ⟨b,hsec⟩
    simpa only [ConvexTriangularSampler.sectionDensity, inv_div] using div_pos hparent hchild

/-- The concrete conditional family, extended by zero beyond the ambient dimension. -/
def bodyQuantileFamily {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) : TriangularRecursion.ConditionalFamily :=
  fun n a t => if h : n < d then (exists_prefix_quantile hK hc h).choose (a,t) else 0

/-- Jointly measurable actual inverse section-density diagonal derivative. -/
def bodyDerivativeFamily {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) : TriangularRecursion.ConditionalFamily :=
  fun n a t => if h : n < d then
    (ConvexTriangularSampler.sectionDensity (stepBody K h) volume a
      (bodyQuantileFamily hK hc n a t))⁻¹ else 0

end Problem358.FinitePrefix

end

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace Problem358.FinitePrefix

/-- The actual first-coordinate marginal of normalized volume on the body. -/
def prefixLaw {d n : ℕ} (K : Set (Coordinates d)) (h : n ≤ d) :
    Measure (Coordinates n) :=
  Measure.map (headBlock h) ((volume K)⁻¹ • volume.restrict K)

@[simp] theorem prefixLaw_full {d : ℕ} (K : Set (Coordinates d)) :
    prefixLaw K (le_refl d) = (volume K)⁻¹ • volume.restrict K := by
  change Measure.map id _ = _
  exact Measure.map_id

theorem measurableSet_stepBody {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) : MeasurableSet (stepBody K h) :=
  hK.preimage (tripleSplit h).continuous.measurable

/-- The next-coordinate conditional law, completed by a point on null prefixes. -/
def prefixKernel {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) : Kernel (Coordinates n) ℝ :=
  (NormalizedSections.completedSectionKernel (volume.prod volume)
    (NormalizedSections.measurable_setDensity (measurableSet_stepBody hK h))
    (0, 0)).map Prod.fst

end Problem358.FinitePrefix

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_StationaryMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem358.StationaryMoment

open MidpointEnergy

variable {ι A F : Type*} [Fintype ι] [MeasurableSpace A]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Geometric data sufficient for one symmetric cell-moment comparison.
In particular, `midpoint_dominated` records the difficult geometric input. -/
structure MidpointComparisonData (Ω : Type*) [MeasurableSpace Ω]
    (M α β : ι → ℝ) (Δ : ι → F) (ρ : Measure F) (R : ℝ) where
  sample : ι → Measure Ω
  sample_probability : ∀ i, IsProbabilityMeasure (sample i)
  leftPoint : ι → Ω → F
  rightPoint : ι → Ω → F
  middleCell : ι → Measure F
  middleCell_finite : ∀ i, IsFiniteMeasure (middleCell i)
  geometricMass : ι → ℝ
  left_memLp : ∀ i, MemLp (leftPoint i) 2 (sample i)
  right_memLp : ∀ i, MemLp (rightPoint i) 2 (sample i)
  left_mass_nonneg : ∀ i, 0 ≤ α i
  right_mass_nonneg : ∀ i, 0 ≤ β i
  left_mass_le : ∀ i, α i ≤ 2 * M i
  geometric_mass_ge : ∀ i, M i / 2 ≤ geometricMass i
  geometric_mass_sq : ∀ i, geometricMass i ^ 2 = α i * β i
  left_bounded : ∀ i, ∀ᵐ a ∂sample i, ‖leftPoint i a‖ ≤ R
  right_bounded : ∀ i, ∀ᵐ a ∂sample i, ‖rightPoint i a‖ ≤ R
  middle_bounded : ∀ i, ∀ᵐ x ∂middleCell i, ‖x‖ ≤ R
  middle_partition : (∑ i, middleCell i) = ρ
  left_partition : (∑ i, ENNReal.ofReal (α i) • Measure.map (leftPoint i) (sample i)) = ρ
  right_partition : (∑ i, ENNReal.ofReal (β i) • Measure.map (rightPoint i) (sample i)) = ρ
  midpoint_dominated : ∀ i, ENNReal.ofReal (geometricMass i) •
    Measure.map (fun a => (1 / 2 : ℝ) • (leftPoint i a + rightPoint i a)) (sample i) ≤
      middleCell i
  moment_difference : ∀ i,
    α i • (∫ a, leftPoint i a ∂sample i) - β i • (∫ a, rightPoint i a ∂sample i) = Δ i

end Problem358.StationaryMoment

end

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358.StationaryMoment

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- Weighted pair marginals recover the raw unnormalized vector moments. -/
theorem pair_moment_difference
    (π : Measure (F × F)) (ρminus ρplus : Measure F) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hleft : ENNReal.ofReal α • Measure.map Prod.fst π = ρminus)
    (hright : ENNReal.ofReal β • Measure.map Prod.snd π = ρplus) :
    α • (∫ p : F × F, p.1 ∂π) - β • (∫ p : F × F, p.2 ∂π) =
      (∫ x : F, x ∂ρminus) - ∫ x : F, x ∂ρplus := by
  have hf : (∫ x : F, x ∂Measure.map Prod.fst π) = (∫ p : F × F, p.1 ∂π) :=
    integral_map_of_stronglyMeasurable measurable_fst stronglyMeasurable_id
  have hg : (∫ x : F, x ∂Measure.map Prod.snd π) = (∫ p : F × F, p.2 ∂π) :=
    integral_map_of_stronglyMeasurable measurable_snd stronglyMeasurable_id
  rw [← hleft, ← hright, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hα, ENNReal.toReal_ofReal hβ, hf, hg]

/-- Construct the abstract moment witness directly from genuine pair couplings
of the three finite cell partitions. Squared-integrability and the moment
identity are consequences, rather than extra assumptions. -/
def midpointComparisonData_of_pair_couplings
    (π : ι → Measure (F × F)) [∀ i, IsProbabilityMeasure (π i)]
    (ρminus ρplus ρmiddle : ι → Measure F) [∀ i, IsFiniteMeasure (ρmiddle i)]
    (ρ : Measure F) (M α β γ : ι → ℝ) (R : ℝ)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hαM : ∀ i, α i ≤ 2 * M i) (hγM : ∀ i, M i / 2 ≤ γ i)
    (hγsq : ∀ i, γ i ^ 2 = α i * β i)
    (hπ : ∀ i, ∀ᵐ p : F × F ∂π i, ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    (hmiddle : ∀ i, ∀ᵐ x : F ∂ρmiddle i, ‖x‖ ≤ R)
    (hleftLaw : ∀ i, ENNReal.ofReal (α i) • Measure.map Prod.fst (π i) = ρminus i)
    (hrightLaw : ∀ i, ENNReal.ofReal (β i) • Measure.map Prod.snd (π i) = ρplus i)
    (hleftPartition : (∑ i, ρminus i) = ρ)
    (hrightPartition : (∑ i, ρplus i) = ρ)
    (hmiddlePartition : (∑ i, ρmiddle i) = ρ)
    (hdom : ∀ i, ENNReal.ofReal (γ i) •
      Measure.map (fun p : F × F => (1 / 2 : ℝ) • (p.1 + p.2)) (π i) ≤ ρmiddle i) :
    MidpointComparisonData (F × F) M α β
      (fun i => (∫ x : F, x ∂ρminus i) - ∫ x : F, x ∂ρplus i) ρ R where
  sample := π
  sample_probability := fun _ => inferInstance
  leftPoint := fun _ => Prod.fst
  rightPoint := fun _ => Prod.snd
  middleCell := ρmiddle
  middleCell_finite := fun _ => inferInstance
  geometricMass := γ
  left_memLp := fun i => MemLp.of_bound continuous_fst.aestronglyMeasurable R
    ((hπ i).mono (fun _ h => h.1))
  right_memLp := fun i => MemLp.of_bound continuous_snd.aestronglyMeasurable R
    ((hπ i).mono (fun _ h => h.2))
  left_mass_nonneg := hα
  right_mass_nonneg := hβ
  left_mass_le := hαM
  geometric_mass_ge := hγM
  geometric_mass_sq := hγsq
  left_bounded := fun i => (hπ i).mono (fun _ h => h.1)
  right_bounded := fun i => (hπ i).mono (fun _ h => h.2)
  middle_bounded := hmiddle
  middle_partition := hmiddlePartition
  left_partition := by simpa only [hleftLaw] using hleftPartition
  right_partition := by simpa only [hrightLaw] using hrightPartition
  midpoint_dominated := hdom
  moment_difference := fun i => pair_moment_difference (π i) (ρminus i) (ρplus i)
    (hα i) (hβ i) (hleftLaw i) (hrightLaw i)

end Problem358.StationaryMoment

end

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem358.StationaryMoment

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- The ordinary measurable, almost-everywhere partition properties of cells. -/
structure AECellPartition (ρ : Measure F) (P : ι → Set F) : Prop where
  measurable : ∀ i, MeasurableSet (P i)
  disjoint : Pairwise (fun i j => AEDisjoint ρ (P i) (P j))
  cover : ∀ᵐ x ∂ρ, x ∈ ⋃ i, P i

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [BorelSpace F]
  [SecondCountableTopology F] in
theorem AECellPartition.sum_restrict {ρ : Measure F} {P : ι → Set F}
    (h : AECellPartition ρ P) : (∑ i, ρ.restrict (P i)) = ρ := by
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion_ae h.disjoint
    (fun i => (h.measurable i).nullMeasurableSet)]
  exact Measure.restrict_eq_self_of_ae_mem h.cover

omit [InnerProductSpace ℝ F] [BorelSpace F] [SecondCountableTopology F] in
/-- Conditioning preserves an almost-everywhere source ball bound. -/
theorem normalizedCellLaw_ae_norm_le {ρ : Measure F} {R : ℝ}
    (hR : ∀ᵐ x ∂ρ, ‖x‖ ≤ R) (P : Set F) :
    ∀ᵐ x ∂normalizedCellLaw ρ P, ‖x‖ ≤ R :=
  Measure.ae_smul_measure (ae_restrict_of_ae hR) _

omit [InnerProductSpace ℝ F] [BorelSpace F] [SecondCountableTopology F] in
/-- A normalized-cell coupling inherits both source ball bounds. -/
theorem normalized_pair_ae_norm_le {ρ : Measure F} {R : ℝ}
    (hR : ∀ᵐ x ∂ρ, ‖x‖ ≤ R) (P Q : Set F) (π : Measure (F × F))
    (hleft : Measure.map Prod.fst π = normalizedCellLaw ρ P)
    (hright : Measure.map Prod.snd π = normalizedCellLaw ρ Q) :
    ∀ᵐ p : F × F ∂π, ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R := by
  have hl : ∀ᵐ x ∂Measure.map Prod.fst π, ‖x‖ ≤ R := by
    rw [hleft]
    exact normalizedCellLaw_ae_norm_le hR P
  have hr : ∀ᵐ x ∂Measure.map Prod.snd π, ‖x‖ ≤ R := by
    rw [hright]
    exact normalizedCellLaw_ae_norm_le hR Q
  exact (ae_of_ae_map measurable_fst.aemeasurable hl).and
    (ae_of_ae_map measurable_snd.aemeasurable hr)

/-- Actual normalized couplings of three cell partitions supply the moment
comparison data. All measure-scaling, partition, boundedness and raw-moment
identities follow from their definitions; midpoint domination remains the
explicit geometric input. -/
def midpointComparisonData_of_normalized_cells
    (ρ : Measure F) [IsFiniteMeasure ρ]
    (Pminus Pplus Pmiddle : ι → Set F)
    (hminus : AECellPartition ρ Pminus) (hplus : AECellPartition ρ Pplus)
    (hmiddle : AECellPartition ρ Pmiddle)
    (hminus_pos : ∀ i, ρ (Pminus i) ≠ 0) (hplus_pos : ∀ i, ρ (Pplus i) ≠ 0)
    (π : ι → Measure (F × F)) [∀ i, IsProbabilityMeasure (π i)]
    (hleft : ∀ i, Measure.map Prod.fst (π i) = normalizedCellLaw ρ (Pminus i))
    (hright : ∀ i, Measure.map Prod.snd (π i) = normalizedCellLaw ρ (Pplus i))
    (M γ : ι → ℝ) (R : ℝ) (hR : ∀ᵐ x ∂ρ, ‖x‖ ≤ R)
    (hαM : ∀ i, ρ.real (Pminus i) ≤ 2 * M i)
    (hγM : ∀ i, M i / 2 ≤ γ i)
    (hγsq : ∀ i, γ i ^ 2 = ρ.real (Pminus i) * ρ.real (Pplus i))
    (hdom : ∀ i, ENNReal.ofReal (γ i) •
      Measure.map (fun p : F × F => (1 / 2 : ℝ) • (p.1 + p.2)) (π i) ≤
        ρ.restrict (Pmiddle i)) :
    MidpointComparisonData (F × F) M (fun i => ρ.real (Pminus i))
      (fun i => ρ.real (Pplus i))
      (fun i => (∫ x in Pminus i, x ∂ρ) - ∫ x in Pplus i, x ∂ρ) ρ R := by
  apply midpointComparisonData_of_pair_couplings π
    (fun i => ρ.restrict (Pminus i)) (fun i => ρ.restrict (Pplus i))
    (fun i => ρ.restrict (Pmiddle i)) ρ M
    (fun i => ρ.real (Pminus i)) (fun i => ρ.real (Pplus i)) γ R
  · exact fun _ => measureReal_nonneg
  · exact fun _ => measureReal_nonneg
  · exact hαM
  · exact hγM
  · exact hγsq
  · exact fun i => normalized_pair_ae_norm_le hR _ _ _ (hleft i) (hright i)
  · exact fun _ => ae_restrict_of_ae hR
  · intro i
    rw [hleft i]
    exact mass_smul_normalizedCellLaw (hminus_pos i) (measure_ne_top _ _)
  · intro i
    rw [hright i]
    exact mass_smul_normalizedCellLaw (hplus_pos i) (measure_ne_top _ _)
  · exact hminus.sum_restrict
  · exact hplus.sum_restrict
  · exact hmiddle.sum_restrict
  · exact hdom

/-- A genuine pair law with normalized cell marginals and the geometric
midpoint domination. No moment inequality is a field of this witness. -/
structure NormalizedMidpointWitness (ρ : Measure F) (P Q H : ι → Set F) where
  coupling : ι → Measure (F × F)
  probability : ∀ i, IsProbabilityMeasure (coupling i)
  left_marginal : ∀ i, Measure.map Prod.fst (coupling i) = normalizedCellLaw ρ (P i)
  right_marginal : ∀ i, Measure.map Prod.snd (coupling i) = normalizedCellLaw ρ (Q i)
  midpoint_dominated : ∀ i, ENNReal.ofReal (Real.sqrt (ρ.real (P i) * ρ.real (Q i))) •
    Measure.map (fun p : F × F => (1 / 2 : ℝ) • (p.1 + p.2)) (coupling i) ≤
      ρ.restrict (H i)

end Problem358.StationaryMoment

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_SupportingInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Problem358.SupportingMapInterpolation

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A globally supporting selection; finite affine maximizers satisfy this directly. -/
def Supports (u : F → ℝ) (T : F → F) : Prop :=
  ∀ x z, u x + ⟪z - x, T x⟫ ≤ u z

def quotient (u : F → ℝ) (h : ℝ) (e x : F) : ℝ :=
  (u (x + h • e) - u x) / h

def slope (T : F → F) (e x : F) : ℝ := ⟪e, T x⟫

end Problem358.SupportingMapInterpolation

end

end OAI
end


