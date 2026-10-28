-- Prove2me | Definitions.Def_OAIQ058B000
-- name    : OAIQ058B000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:39:20.285991+00:00
-- url     : https://prove2.me/theorems/cd04aa69-c2a3-4cf2-9180-32067d60f353
-- title:
--   Definitions bundle OAIQ058B000 of the split of OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 209 declarations of OpenAI's Lean: 131 definitions, 2 inductive types or structures, 7 instances and 69 theorems. The definitions and types are `OAI.BorsukNine.Admissible`, `OAI.BorsukNine.FiniteObstruction.Family`, `OAI.BorsukNine.FiniteObstruction.Labels`, `OAI.BorsukNine.FiniteObstruction.TenSystem`, `OAI.BorsukNine.HasPositiveLine`, `OAI.BorsukNine.NegativeQuadratic`, `OAI.BorsukNine.SimplicialChains.Chain`, `OAI.BorsukNine.SimplicialChains.F₂`, `OAI.BorsukNine.SimplicialChains.IsFineLabel`, `OAI.BorsukNine.SimplicialChains.SignedVertex`, `OAI.BorsukNine.SimplicialChains.SubdivisionCarrier`, `OAI.BorsukNine.SimplicialChains.annulus`, `OAI.BorsukNine.SimplicialChains.approximation`, `OAI.BorsukNine.SimplicialChains.augmentation`, `OAI.BorsukNine.SimplicialChains.barycenter`, `OAI.BorsukNine.SimplicialChains.boundary`, `OAI.BorsukNine.SimplicialChains.characteristicAugmentation`, `OAI.BorsukNine.SimplicialChains.characteristicDegree`, `OAI.BorsukNine.SimplicialChains.cone`, `OAI.BorsukNine.SimplicialChains.contigMap`, `OAI.BorsukNine.SimplicialChains.contigSimplex`, `OAI.BorsukNine.SimplicialChains.cross`, `OAI.BorsukNine.SimplicialChains.crossEmbedding`, `OAI.BorsukNine.SimplicialChains.crossFacet`, `OAI.BorsukNine.SimplicialChains.crossFundamental`, `OAI.BorsukNine.SimplicialChains.crossGeometricMap`, `OAI.BorsukNine.SimplicialChains.crossRidge`, `OAI.BorsukNine.SimplicialChains.crossTower`, `OAI.BorsukNine.SimplicialChains.degreeChains`, `OAI.BorsukNine.SimplicialChains.dropLast`, `OAI.BorsukNine.SimplicialChains.faceEquiv`, `OAI.BorsukNine.SimplicialChains.facetCenter`, `OAI.BorsukNine.SimplicialChains.fineCrossMap`, `OAI.BorsukNine.SimplicialChains.flip`, `OAI.BorsukNine.SimplicialChains.flipAt`, `OAI.BorsukNine.SimplicialChains.hemisphereComplex`, `OAI.BorsukNine.SimplicialChains.labelRegion`, `OAI.BorsukNine.SimplicialChains.mapChains`, `OAI.BorsukNine.SimplicialChains.mapSimplex`, `OAI.BorsukNine.SimplicialChains.maxIndex` and 93 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Borsuk_LocalParity_LocalModel`, `Borsuk_LocalParity_RegularBase`, `Borsuk_LocalParity_RegularPatch`, `Borsuk_LocalParity_SphereBlock`, `Borsuk_LocalParity_SphereParity`, `Borsuk_MatrixGeometry_BlockVector`, `Borsuk_MatrixGeometry_FibreHomotopy`, `Borsuk_MatrixGeometry_FibreTransport`, `Borsuk_MatrixGeometry_LineRepresentative`, `Borsuk_MatrixGeometry_MatrixCompression`, `Borsuk_MatrixGeometry_MatrixFibre`, `Borsuk_MatrixGeometry_MatrixKernel`, `Borsuk_MatrixGeometry_MatrixReflection`, `Borsuk_MatrixGeometry_MatrixTransport`, `Borsuk_MatrixGeometry_PositiveSlice`, `Borsuk_MatrixGeometry_Rank`, `Borsuk_MatrixGeometry_ReflectionTransport`, `Borsuk_MatrixGeometry_SignedExtension`, `Borsuk_MatrixGeometry_SpectralChart`, `Borsuk_MatrixGeometry_SymmetricCoordinates`, `Borsuk_MatrixGeometry_SymmetricEntries`, `Borsuk_Projectors_Basic`, `Borsuk_Projectors_CompactTargetHits`, `Borsuk_Projectors_CoordinateSum`, `Borsuk_Projectors_FiniteOpenGlue`, `Borsuk_Projectors_FinitePatch`, `Borsuk_Projectors_NegativeQuadratic`, `Borsuk_Projectors_NullImage`, `Borsuk_Projectors_RaySet`, `Borsuk_Projectors_SimplexPoint`, `Borsuk_Projectors_Within`, `Borsuk_Simplicial_Approximation`, `Borsuk_Simplicial_CharacteristicDegree`, `Borsuk_Simplicial_Coefficients`, `Borsuk_Simplicial_ContigSimplexBoundary`, `Borsuk_Simplicial_CrossChainDimensionBound`, `Borsuk_Simplicial_CrossEmbedding`, `Borsuk_Simplicial_DoubleEraseSumFun`, `Borsuk_Simplicial_Equivariance`, `Borsuk_Simplicial_F2`, `Borsuk_Simplicial_FineCrossMap`, `Borsuk_Simplicial_Flip`, `Borsuk_Simplicial_LabelRegion`, `Borsuk_Simplicial_Maps`, `Borsuk_Simplicial_MaxIndex`, `Borsuk_Simplicial_NormMap`, `Borsuk_Simplicial_Refinement`, `Borsuk_Simplicial_SignVector`, `Borsuk_Simplicial_SignedVertex`, `Borsuk_Simplicial_SimplexMemDegreeAll`, `Borsuk_Simplicial_SubdivSimplex`, `Borsuk_Simplicial_UnitRadial`, `Borsuk_SmithTheory_CharacteristicCochains`, `Borsuk_SmithTheory_Involution`, `Borsuk_SphereGeometry_HemisphereChart`, `Borsuk_SphereGeometry_HomogeneousLift`, `Borsuk_SphereGeometry_IntegralLift`, `Borsuk_SphereGeometry_NormSphere`, `Borsuk_SphereGeometry_OddSphereMap`, `Borsuk_SphereGeometry_SphereExtension`, `Borsuk_SphereGeometry_SphereMeasure`, `Borsuk_SphereGeometry_TraceSphere`, `Borsuk_Support_ActiveChambers`, `Borsuk_Support_AllPairs`, `Borsuk_Support_ChamberPath`, `Borsuk_Support_Chambers`, `Borsuk_Support_DisjointChambers`, `Borsuk_Support_FacetTangent`, `Borsuk_Support_LocalMix`, `Borsuk_Support_MixedHomotopy`, `Borsuk_Support_NegativeFibre`, `Borsuk_Support_PurityChart`, `Borsuk_Support_PurityGeometry`, `Borsuk_Support_SupportIncidence`, `Borsuk_TenLabels_Labels`.
--
--   **Imports.** It imports the published bundle `Def_BorsukNine`.
--
--   **Imported by** (directly, in this split): the statements `OAI.BorsukNine.Admissible.chart_surgery_impossible`, `OAI.BorsukNine.Admissible.face_extends_four`, `OAI.BorsukNine.Admissible.face_extends_three`, `OAI.BorsukNine.Admissible.localBlockMix_hit`, `OAI.BorsukNine.Admissible.localBlockMix_ne_zero`, `OAI.BorsukNine.Admissible.localBlockModel_ne_zero`, `OAI.BorsukNine.Admissible.localBlockModel_ray`, `OAI.BorsukNine.Admissible.mixedHomotopy_hit`, `OAI.BorsukNine.Admissible.mixedHomotopy_zero`, `OAI.BorsukNine.Admissible.no_free_ridge`, `OAI.BorsukNine.Admissible.original_ray_level`, `OAI.BorsukNine.Admissible.regularPatch_isOpen`, `OAI.BorsukNine.Admissible.regular_facet_level_even`, `OAI.BorsukNine.Admissible.tetra_no_free_triangle`, `OAI.BorsukNine.Admissible.traceHomotopy_ray`, `OAI.BorsukNine.FiniteObstruction.c1390`, `OAI.BorsukNine.FiniteObstruction.c31252`, `OAI.BorsukNine.FiniteObstruction.c31264`, `OAI.BorsukNine.FiniteObstruction.c31437`, `OAI.BorsukNine.FiniteObstruction.c31469`, `OAI.BorsukNine.FiniteObstruction.c31472`, `OAI.BorsukNine.FiniteObstruction.c31476`, `OAI.BorsukNine.FiniteObstruction.c31481`, `OAI.BorsukNine.FiniteObstruction.c31520`, `OAI.BorsukNine.FiniteObstruction.c31524`, `OAI.BorsukNine.FiniteObstruction.c31527`, `OAI.BorsukNine.FiniteObstruction.c32571`, `OAI.BorsukNine.FiniteObstruction.c32577`, `OAI.BorsukNine.FiniteObstruction.c32582`, `OAI.BorsukNine.FiniteObstruction.c32601`, `OAI.BorsukNine.FiniteObstruction.c32606`, `OAI.BorsukNine.FiniteObstruction.c32611`, `OAI.BorsukNine.FiniteObstruction.c32621`, `OAI.BorsukNine.FiniteObstruction.c32629`, `OAI.BorsukNine.FiniteObstruction.c32630`, `OAI.BorsukNine.FiniteObstruction.c32662`, `OAI.BorsukNine.FiniteObstruction.c32668`, `OAI.BorsukNine.FiniteObstruction.c32671`, `OAI.BorsukNine.FiniteObstruction.c32689`, `OAI.BorsukNine.FiniteObstruction.c32696`, `OAI.BorsukNine.FiniteObstruction.c32711`, `OAI.BorsukNine.FiniteObstruction.c32712`, `OAI.BorsukNine.FiniteObstruction.c32720`, `OAI.BorsukNine.FiniteObstruction.c32728`, `OAI.BorsukNine.FiniteObstruction.c32742`, `OAI.BorsukNine.FiniteObstruction.c32743`, `OAI.BorsukNine.FiniteObstruction.c32744`, `OAI.BorsukNine.FiniteObstruction.c32745`, `OAI.BorsukNine.FiniteObstruction.c32746`, `OAI.BorsukNine.FiniteObstruction.c32747`, `OAI.BorsukNine.FiniteObstruction.c32755`, `OAI.BorsukNine.FiniteObstruction.c32778`, `OAI.BorsukNine.FiniteObstruction.c32780`, `OAI.BorsukNine.FiniteObstruction.c32783`, `OAI.BorsukNine.FiniteObstruction.c32784`, `OAI.BorsukNine.FiniteObstruction.c32785`, `OAI.BorsukNine.FiniteObstruction.c32786`, `OAI.BorsukNine.FiniteObstruction.c32795`, `OAI.BorsukNine.FiniteObstruction.c32800`, `OAI.BorsukNine.FiniteObstruction.c32804`, `OAI.BorsukNine.FiniteObstruction.c32813`, `OAI.BorsukNine.FiniteObstruction.c32815`, `OAI.BorsukNine.FiniteObstruction.no_ten_system` and `OAI.BorsukNine.trace_patch_models`; the proofs of `OAI.BorsukNine.Admissible.chart_surgery_impossible`, `OAI.BorsukNine.Admissible.face_extends_four`, `OAI.BorsukNine.Admissible.face_extends_three`, `OAI.BorsukNine.Admissible.localBlockMix_hit`, `OAI.BorsukNine.Admissible.localBlockMix_ne_zero`, `OAI.BorsukNine.Admissible.localBlockModel_ne_zero`, `OAI.BorsukNine.Admissible.localBlockModel_ray`, `OAI.BorsukNine.Admissible.mixedHomotopy_hit`, `OAI.BorsukNine.Admissible.mixedHomotopy_zero`, `OAI.BorsukNine.Admissible.no_free_ridge`, `OAI.BorsukNine.Admissible.original_ray_level`, `OAI.BorsukNine.Admissible.regularPatch_isOpen`, `OAI.BorsukNine.Admissible.regular_facet_level_even`, `OAI.BorsukNine.Admissible.tetra_no_free_triangle`, `OAI.BorsukNine.Admissible.traceHomotopy_ray`, `OAI.BorsukNine.FiniteObstruction.c1390`, `OAI.BorsukNine.FiniteObstruction.c31252`, `OAI.BorsukNine.FiniteObstruction.c31264`, `OAI.BorsukNine.FiniteObstruction.c31437`, `OAI.BorsukNine.FiniteObstruction.c31469`, `OAI.BorsukNine.FiniteObstruction.c31472`, `OAI.BorsukNine.FiniteObstruction.c31476`, `OAI.BorsukNine.FiniteObstruction.c31481`, `OAI.BorsukNine.FiniteObstruction.c31520`, `OAI.BorsukNine.FiniteObstruction.c31524`, `OAI.BorsukNine.FiniteObstruction.c31527`, `OAI.BorsukNine.FiniteObstruction.c32571`, `OAI.BorsukNine.FiniteObstruction.c32577`, `OAI.BorsukNine.FiniteObstruction.c32582`, `OAI.BorsukNine.FiniteObstruction.c32601`, `OAI.BorsukNine.FiniteObstruction.c32606`, `OAI.BorsukNine.FiniteObstruction.c32611`, `OAI.BorsukNine.FiniteObstruction.c32621`, `OAI.BorsukNine.FiniteObstruction.c32629`, `OAI.BorsukNine.FiniteObstruction.c32630`, `OAI.BorsukNine.FiniteObstruction.c32662`, `OAI.BorsukNine.FiniteObstruction.c32668`, `OAI.BorsukNine.FiniteObstruction.c32671`, `OAI.BorsukNine.FiniteObstruction.c32689`, `OAI.BorsukNine.FiniteObstruction.c32696`, `OAI.BorsukNine.FiniteObstruction.c32711`, `OAI.BorsukNine.FiniteObstruction.c32712`, `OAI.BorsukNine.FiniteObstruction.c32720`, `OAI.BorsukNine.FiniteObstruction.c32728`, `OAI.BorsukNine.FiniteObstruction.c32742`, `OAI.BorsukNine.FiniteObstruction.c32743`, `OAI.BorsukNine.FiniteObstruction.c32744`, `OAI.BorsukNine.FiniteObstruction.c32745`, `OAI.BorsukNine.FiniteObstruction.c32746`, `OAI.BorsukNine.FiniteObstruction.c32747`, `OAI.BorsukNine.FiniteObstruction.c32755`, `OAI.BorsukNine.FiniteObstruction.c32778`, `OAI.BorsukNine.FiniteObstruction.c32780`, `OAI.BorsukNine.FiniteObstruction.c32783`, `OAI.BorsukNine.FiniteObstruction.c32784`, `OAI.BorsukNine.FiniteObstruction.c32785`, `OAI.BorsukNine.FiniteObstruction.c32786`, `OAI.BorsukNine.FiniteObstruction.c32795`, `OAI.BorsukNine.FiniteObstruction.c32800`, `OAI.BorsukNine.FiniteObstruction.c32804`, `OAI.BorsukNine.FiniteObstruction.c32813`, `OAI.BorsukNine.FiniteObstruction.c32815`, `OAI.BorsukNine.FiniteObstruction.no_ten_system`, `OAI.BorsukNine.main_theorem` and `OAI.BorsukNine.trace_patch_models`.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_BorsukNine

section
-- module Solutions.OAIQ058_BK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h

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
-- module Solutions.OAIQ058_BK.Borsuk_Support_Chambers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section Chambers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def safeNormals (Z : Set E) : Set E := {x | ∀ z ∈ Z, ⟪x,z⟫ ≠ 0}

def signChamber (Z : Set E) (c : E) : Set E := {x | ∀ z ∈ Z, 0 < ⟪c,z⟫ * ⟪x,z⟫}

end Chambers
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_DisjointChambers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixEmbedding
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
local notation "D" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν

noncomputable def isometryMatrix (e : D →ₗᵢ[ℝ] E) : Matrix ν μ ℝ :=
  Matrix.toEuclideanLin.symm e.toLinearMap

noncomputable def matrixEmbed (e : D →ₗᵢ[ℝ] E) : Matrix μ μ ℝ →ₗ[ℝ] Matrix ν ν ℝ where
  toFun B := isometryMatrix e * B * (isometryMatrix e)ᴴ
  map_add' B C := by simp only [Matrix.mul_add,Matrix.add_mul]
  map_smul' t B := by simp only [Matrix.mul_smul,Matrix.smul_mul]; rfl

end MatrixEmbedding
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixCompression
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
local notation "D" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν

noncomputable def matrixCompress (e : D →ₗᵢ[ℝ] E) : Matrix ν ν ℝ →ₗ[ℝ] Matrix μ μ ℝ where
  toFun Q := (isometryMatrix e)ᴴ * Q * isometryMatrix e
  map_add' Q R := by simp only [Matrix.mul_add,Matrix.add_mul]
  map_smul' t Q := by simp only [Matrix.mul_smul,Matrix.smul_mul]; rfl

end MatrixCompression

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_F2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

variable {V : Type*} [DecidableEq V]
abbrev F₂ := ZMod 2
abbrev Chain (K : PreAbstractSimplicialComplex V) := {s : Finset V // s ∈ K} →₀ F₂

noncomputable def simplex (K : PreAbstractSimplicialComplex V) (s : Finset V) : Chain K := by
  classical
  exact if h : s ∈ K then Finsupp.single ⟨s, h⟩ 1 else 0

omit [DecidableEq V] in
lemma simplex_of_mem (K : PreAbstractSimplicialComplex V) {s : Finset V} (hs : s ∈ K) :
    simplex K s = Finsupp.single ⟨s, hs⟩ 1 := by simp [simplex, hs]

omit [DecidableEq V] in
@[simp] lemma simplex_empty (K : PreAbstractSimplicialComplex V) : simplex K ∅ = 0 := by
  have h : (∅ : Finset V) ∉ K := fun h => (K.isRelLowerSet_faces h).1.ne_empty rfl
  simp [simplex, h]

noncomputable def boundary (K : PreAbstractSimplicialComplex V) : Chain K →ₗ[F₂] Chain K := by
  classical
  exact Finsupp.linearCombination F₂ (fun s => ∑ a ∈ s.val, simplex K (s.val.erase a))

lemma boundary_simplex (K : PreAbstractSimplicialComplex V) {s : Finset V} (hs : s ∈ K) :
    boundary K (simplex K s) = ∑ a ∈ s, simplex K (s.erase a) := by
  classical
  simp [simplex_of_mem K hs, boundary, Finsupp.linearCombination_single]

lemma boundary_simplex_subset (K : PreAbstractSimplicialComplex V)
    {s t : Finset V} (ht : t ∈ K) (hs : s ⊆ t) :
    boundary K (simplex K s) = ∑ a ∈ s, simplex K (s.erase a) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact boundary_simplex K ((K.isRelLowerSet_faces ht).2 hs hn)

omit [DecidableEq V] in
lemma chain_add_self (K : PreAbstractSimplicialComplex V) (c : Chain K) : c + c = 0 := by
  ext s
  exact CharTwo.add_self_eq_zero _

lemma double_erase_sum (K : PreAbstractSimplicialComplex V) (s : Finset V) :
    (∑ a ∈ s, ∑ b ∈ s.erase a, simplex K ((s.erase a).erase b)) = 0 := by
  classical
  let g (p : V × V) : Chain K := if p.1 = p.2 then 0 else simplex K ((s.erase p.1).erase p.2)
  have hg : (∑ a ∈ s, ∑ b ∈ s.erase a, simplex K ((s.erase a).erase b)) =
      ∑ p ∈ s ×ˢ s, g p := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [← Finset.filter_ne, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hab : a = b <;> simp [g, hab, Finset.filter_ne]
  rw [hg]
  apply Finset.sum_involution (fun p _ => p.swap)
  · intro p hp
    dsimp [g]
    by_cases he : p.1 = p.2
    · simp [he]
    · simp only [he, ite_false, Ne.symm he, Finset.erase_right_comm]
      exact chain_add_self K _
  · intro p hp hg he
    have h : p.1 = p.2 := congrArg Prod.snd he
    exact hg (by simp [g, h])
  · intro p hp
    exact Prod.swap_swap p
  · intro p hp
    exact Finset.mem_product.mpr (And.symm (Finset.mem_product.mp hp))

lemma boundary_twice_simplex (K : PreAbstractSimplicialComplex V)
    {s : Finset V} (hs : s ∈ K) : boundary K (boundary K (simplex K s)) = 0 := by
  classical
  rw [boundary_simplex K hs, map_sum]
  have h (a : V) : boundary K (simplex K (s.erase a)) =
      ∑ b ∈ s.erase a, simplex K ((s.erase a).erase b) :=
    boundary_simplex_subset K hs (Finset.erase_subset a s)
  simp_rw [h]
  exact double_erase_sum K s

lemma boundary_sq (K : PreAbstractSimplicialComplex V) :
    (boundary K).comp (boundary K) = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := boundary_twice_simplex K s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs, smul_zero, LinearMap.zero_apply]

noncomputable def augmentation (K : PreAbstractSimplicialComplex V) : Chain K →ₗ[F₂] F₂ :=
  Finsupp.linearCombination F₂ (fun s => if s.val.card = 1 then 1 else 0)

omit [DecidableEq V] in
lemma augmentation_simplex (K : PreAbstractSimplicialComplex V) {s : Finset V} (hs : s ∈ K) :
    augmentation K (simplex K s) = if s.card = 1 then 1 else 0 := by
  simp [simplex_of_mem K hs, augmentation, Finsupp.linearCombination_single]

omit [DecidableEq V] in
lemma augmentation_simplex_subset (K : PreAbstractSimplicialComplex V)
    {s t : Finset V} (ht : t ∈ K) (hs : s ⊆ t) :
    augmentation K (simplex K s) = if s.card = 1 then 1 else 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact augmentation_simplex K ((K.isRelLowerSet_faces ht).2 hs hn)

lemma augmentation_boundary_simplex (K : PreAbstractSimplicialComplex V)
    {s : Finset V} (hs : s ∈ K) : augmentation K (boundary K (simplex K s)) = 0 := by
  classical
  rw [boundary_simplex K hs, map_sum]
  have hh (a : V) (ha : a ∈ s) : augmentation K (simplex K (s.erase a)) =
      if s.card = 2 then 1 else 0 := by
    rw [augmentation_simplex_subset K hs (Finset.erase_subset a s), Finset.card_erase_of_mem ha]
    have hc : s.card - 1 = 1 ↔ s.card = 2 := by omega
    simp only [hc]
  rw [Finset.sum_congr rfl hh]
  by_cases hc : s.card = 2
  · simpa [hc] using (show (2 : F₂) = 0 by decide)
  · simp [hc]

lemma augmentation_boundary (K : PreAbstractSimplicialComplex V) :
    (augmentation K).comp (boundary K) = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := augmentation_boundary_simplex K s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs, smul_zero, LinearMap.zero_apply]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Maps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]
section Maps
variable {W : Type*} [DecidableEq W]

noncomputable def mapSimplex (L : PreAbstractSimplicialComplex W) (f : V → W)
    (s : Finset V) : Chain L :=
  if (s.image f).card = s.card then simplex L (s.image f) else 0

omit [DecidableEq V] in
@[simp] lemma mapSimplex_empty (L : PreAbstractSimplicialComplex W) (f : V → W) :
    mapSimplex L f ∅ = 0 := by simp [mapSimplex]

noncomputable def mapChains (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) : Chain K →ₗ[F₂] Chain L :=
  Finsupp.linearCombination F₂ (fun s => mapSimplex L f s.val)

omit [DecidableEq V] in
lemma mapChains_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) : mapChains K L f (simplex K s) = mapSimplex L f s := by
  simp [simplex_of_mem K hs, mapChains, Finsupp.linearCombination_single]

omit [DecidableEq V] in
lemma mapChains_simplex_subset (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s t : Finset V} (ht : t ∈ K) (hs : s ⊆ t) :
    mapChains K L f (simplex K s) = mapSimplex L f s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact mapChains_simplex K L f ((K.isRelLowerSet_faces ht).2 hs hn)

lemma image_erase_of_injOn (f : V → W) (s : Finset V) (h : Set.InjOn f s)
    {a : V} (ha : a ∈ s) : (s.erase a).image f = (s.image f).erase (f a) := by
  ext b
  constructor
  · intro hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      exact (Finset.mem_erase.mp hx).1 (h (Finset.mem_of_mem_erase hx) ha he)
    · exact Finset.mem_image_of_mem f (Finset.mem_of_mem_erase hx)
  · intro hb
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨fun he => hne (congrArg f he), hx⟩, rfl⟩

lemma image_erase_collision (f : V → W) (s : Finset V) {a b : V}
    (hb : b ∈ s) (hne : a ≠ b) (he : f a = f b) : (s.erase a).image f = s.image f := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image_of_mem f (Finset.mem_of_mem_erase hx)
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    by_cases ha : x = a
    · subst x
      exact Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨Ne.symm hne, hb⟩, he.symm⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨ha, hx⟩, rfl⟩

lemma mapSimplex_boundary_degenerate (L : PreAbstractSimplicialComplex W)
    (f : V → W) (s : Finset V) (h : ¬ Set.InjOn f s) :
    (∑ a ∈ s, mapSimplex L f (s.erase a)) = 0 := by
  classical
  change ¬ ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b at h
  push Not at h
  obtain ⟨a, ha, b, hb, he, hne⟩ := h
  rw [Finset.sum_eq_add a b hne]
  · have hima := image_erase_collision f s hb hne he
    have himb := image_erase_collision f s ha hne.symm he.symm
    have hc : mapSimplex L f (s.erase a) = mapSimplex L f (s.erase b) := by
      simp only [mapSimplex, hima, himb, Finset.card_erase_of_mem ha, Finset.card_erase_of_mem hb]
    rw [hc]
    exact chain_add_self L _
  · intro c hc hca
    have hn : ¬ Set.InjOn f (s.erase c) := by
      intro hinj
      exact hne (hinj (Finset.mem_erase.mpr ⟨Ne.symm hca.1, ha⟩)
        (Finset.mem_erase.mpr ⟨Ne.symm hca.2, hb⟩) he)
    simp only [mapSimplex, Finset.card_image_iff, ite_eq_right hn]
  · exact fun hn => (hn ha).elim
  · exact fun hn => (hn hb).elim

lemma mapChains_boundary_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) {s : Finset V} (hs : s ∈ K) :
    boundary L (mapChains K L f (simplex K s)) =
      mapChains K L f (boundary K (simplex K s)) := by
  rw [mapChains_simplex K L f hs, boundary_simplex K hs, map_sum]
  have h (a : V) : mapChains K L f (simplex K (s.erase a)) = mapSimplex L f (s.erase a) :=
    mapChains_simplex_subset K L f hs (Finset.erase_subset a s)
  simp_rw [h]
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hinj), boundary_simplex L (hf s hs)]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      have hj : Set.InjOn f (s.erase a) := hinj.mono (Finset.erase_subset a s)
      rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hj), image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, ite_eq_right (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]

lemma mapChains_boundary (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) :
    (boundary L).comp (mapChains K L f) = (mapChains K L f).comp (boundary K) := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := mapChains_boundary_simplex K L f hf s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs]

omit [DecidableEq V] in
lemma mapChains_augmentation_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) {s : Finset V} (hs : s ∈ K) :
    augmentation L (mapChains K L f (simplex K s)) = augmentation K (simplex K s) := by
  rw [mapChains_simplex K L f hs, augmentation_simplex K hs]
  by_cases hcard : (s.image f).card = s.card
  · rw [mapSimplex, ite_eq_left hcard, augmentation_simplex L (hf s hs), hcard]
  · have hne : s.card ≠ 1 := by
      intro hc
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
      simp at hcard
    simp [mapSimplex, hcard, hne]

omit [DecidableEq V] in
lemma mapChains_augmentation (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) :
    (augmentation L).comp (mapChains K L f) = augmentation K := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := mapChains_augmentation_simplex K L f hf s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs]

end Maps

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Equivariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]
section Equivariance
variable (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K)

noncomputable def faceEquiv : {s : Finset V // s ∈ K} ≃ {s : Finset V // s ∈ K} where
  toFun s := ⟨s.val.image e, (he s.val).mp s.property⟩
  invFun s := ⟨s.val.image e.symm, (he _).mpr (by simp [Finset.image_image, s.property])⟩
  left_inv s := Subtype.ext (by simp [Finset.image_image])
  right_inv s := Subtype.ext (by simp [Finset.image_image])

lemma faceEquiv_involutive (hi : Function.Involutive e) :
    Function.Involutive (faceEquiv K e he) := by
  intro s
  apply Subtype.ext
  change (s.val.image e).image e = s.val
  rw [Finset.image_image]
  have h : e ∘ e = id := funext hi
  rw [h, Finset.image_id]

lemma faceEquiv_free (hf : ∀ s ∈ K, s.image e ≠ s) :
    ∀ s, faceEquiv K e he s ≠ s := by
  intro s hh
  exact hf s.val s.property (congrArg Subtype.val hh)

lemma mapChains_equiv :
    mapChains K K e = (Finsupp.domLCongr (faceEquiv K e he)).toLinearMap := by
  apply Finsupp.lhom_ext
  intro s r
  have hc : (s.val.image e).card = s.val.card := Finset.card_image_iff.mpr e.injective.injOn
  simp only [mapChains, Finsupp.linearCombination_single, mapSimplex, ite_eq_left hc,
    simplex_of_mem K ((he s.val).mp s.property), LinearEquiv.coe_toLinearMap,
    Finsupp.domLCongr_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

end Equivariance

section Cone

noncomputable def cone (K : PreAbstractSimplicialComplex V) (a : V) : Chain K →ₗ[F₂] Chain K :=
  Finsupp.linearCombination F₂ (fun s => if a ∈ s.val then 0 else simplex K (insert a s.val))

end Cone

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SmithTheory_Involution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SmithTheory
variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]
section Involution
variable {ι : Type*}

noncomputable def involutionNorm (τ : ι ≃ ι) :
    (ι →₀ ZMod 2) →ₗ[ZMod 2] (ι →₀ ZMod 2) :=
  LinearMap.id + (Finsupp.domLCongr τ).toLinearMap

lemma involutionNorm_apply (τ : ι ≃ ι) (c : ι →₀ ZMod 2) (a : ι) :
    involutionNorm τ c a = c a + c (τ.symm a) := by
  simp [involutionNorm, Finsupp.domCongr, Finsupp.equivMapDomain_apply]

lemma involutionNorm_exact (τ : ι ≃ ι) (hτ : Function.Involutive τ)
    (hfree : ∀ a, τ a ≠ a) :
    LinearMap.ker (involutionNorm τ) ≤ LinearMap.range (involutionNorm τ) := by
  classical
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  intro c hc
  have ht (a : ι) : τ (τ a) = a := hτ a
  have hsymm (a : ι) : τ.symm a = τ a := by
    apply τ.injective
    rw [τ.apply_symm_apply, ht]
  have heq (a : ι) : c (τ a) = c a := by
    have h := congrArg (fun b : ι →₀ ZMod 2 => b a) hc
    simp only [involutionNorm_apply, Finsupp.zero_apply, hsymm] at h
    have hh := eq_neg_of_add_eq_zero_right h
    rwa [CharTwo.neg_eq] at hh
  refine ⟨c.filter (fun a => a < τ a), ?_⟩
  ext a
  rw [involutionNorm_apply, hsymm]
  simp only [Finsupp.filter_apply, ht]
  by_cases ha : a < τ a
  · simp [ha, not_lt_of_gt ha]
  · have hb : τ a < a := lt_of_le_of_ne (le_of_not_gt ha) (hfree a)
    simp [ha, hb, heq]

end Involution

end BorsukNine.SmithTheory

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SymmetricCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SymmetricCoordinates
variable {ν : Type*} [Fintype ν] [LinearOrder ν]

abbrev UpperTriangle (ν : Type*) [LE ν] := {p : ν × ν // p.1 ≤ p.2}

noncomputable def symmetricCoordinates :
    EuclideanSpace ℝ (UpperTriangle ν) →ₗ[ℝ] Matrix ν ν ℝ where
  toFun x i j := if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩
  map_add' x y := by
    ext i j
    change (if h : i ≤ j then (x+y) ⟨(i,j),h⟩ else (x+y) ⟨(j,i),le_of_not_ge h⟩) =
      (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩) +
      (if h : i ≤ j then y ⟨(i,j),h⟩ else y ⟨(j,i),le_of_not_ge h⟩)
    split_ifs <;> rfl
  map_smul' t x := by
    ext i j
    change (if h : i ≤ j then (t • x) ⟨(i,j),h⟩ else (t • x) ⟨(j,i),le_of_not_ge h⟩) =
      t * (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩)
    split_ifs <;> rfl

end SymmetricCoordinates

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine

open scoped RealInnerProductSpace ContDiff

@[simp] theorem projector_apply (u : Vector4) (i j : Fin 4) :
    projector u (i, j) = u i * u j := rfl

@[simp] theorem projector_neg (u : Vector4) : projector (-u) = projector u := by
  ext ⟨i, j⟩
  simp [projector]

structure Admissible {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] (f : V → ι → ℝ) : Prop where
  smooth : ∀ i, ContDiff ℝ ∞ (fun u => f u i)
  antipodal : ∀ u i, f (-u) i = f u i
  nonneg : ∀ u, ‖u‖ = 1 → ∀ i, 0 ≤ f u i
  sum_one : ∀ u, ‖u‖ = 1 → ∑ i, f u i = 1
  orthogonal : ∀ u v, ‖u‖ = 1 → ‖v‖ = 1 → ⟪u, v⟫ = 0 →
    ∀ i, ¬ (0 < f u i ∧ 0 < f v i)

open scoped Manifold

noncomputable def positiveSupport {ι : Type*} [Fintype ι]
    {V : Type*} (f : V → ι → ℝ) (u : V) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => 0 < f u i)

@[simp] theorem mem_positiveSupport {ι : Type*} [Fintype ι]
    {V : Type*} (f : V → ι → ℝ) (u : V) (i : ι) :
    i ∈ positiveSupport f u ↔ 0 < f u i := by
  classical
  simp [positiveSupport]

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_HomogeneousLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
section HomogeneousLift
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*}

noncomputable def homogeneousLift (f : V → ι → ℝ) (v : V) : ι → ℝ :=
  fun i => ‖v‖ ^ 2 * f ((‖v‖⁻¹ : ℝ) • v) i

@[simp] lemma homogeneousLift_zero (f : V → ι → ℝ) : homogeneousLift f 0 = 0 := by
  ext i
  simp [homogeneousLift]

end HomogeneousLift

open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_SphereMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereMeasure
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

abbrev UnitSphere := Metric.sphere (0 : V) 1

noncomputable def sphereProbability : Measure (UnitSphere V) :=
  ((volume : Measure V).toSphere Set.univ)⁻¹ • volume.toSphere

instance sphereMeasure_neZero : NeZero ((volume : Measure V).toSphere) := by
  constructor
  exact (Measure.toSphere_eq_zero_iff_finrank volume).not.mpr
    (ne_of_gt (Module.finrank_pos (R := ℝ) (M := V)))

instance sphereProbability_isProbability : IsProbabilityMeasure (sphereProbability V) := by
  unfold sphereProbability
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance sphereProbability_openPos : (sphereProbability V).IsOpenPosMeasure := by
  unfold sphereProbability
  exact Measure.isOpenPosMeasure_smul volume.toSphere (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

variable {V}

noncomputable def sphereRotation (e : V ≃ₗᵢ[ℝ] V) : UnitSphere V ≃ₜ UnitSphere V :=
  e.toHomeomorph.subtype (fun x => by simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph, e.norm_map])

end SphereMeasure

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_IntegralLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section IntegralLift
variable {ν ι : Type*} [Fintype ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

noncomputable def integralLift (f : E → ι → ℝ) (T : E →L[ℝ] E) : ι → ℝ :=
  fun i => (Fintype.card ν : ℝ) *
    ∫ x : UnitSphere E, homogeneousLift f (T x) i ∂sphereProbability E

end IntegralLift

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix

section PositiveExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

noncomputable def positiveExtension (f : E → ι → ℝ) (Q : Matrix ν ν ℝ) : ι → ℝ :=
  integralLift f (op (CFC.sqrt Q))

end PositiveExtension

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SignedExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SignedExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

noncomputable def signedExtension (f : E → ι → ℝ) (A : Matrix ν ν ℝ) : ι → ℝ :=
  positiveExtension f A⁺ - positiveExtension f A⁻

end SignedExtension

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_SphereExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

noncomputable def normalizedSignedExtension (f : E → ι → ℝ) (A : Matrix ν ν ℝ) :
    EuclideanSpace ℝ ι :=
  ‖WithLp.toLp 2 (signedExtension f A)‖⁻¹ • WithLp.toLp 2 (signedExtension f A)

end SphereExtension

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_OddSphereMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section OddSphereMap
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

noncomputable def sphereExtension (f : E → ι → ℝ)
    (x : EuclideanSpace ℝ (UpperTriangle ν)) : EuclideanSpace ℝ ι :=
  normalizedSignedExtension f (symmetricCoordinates x)

end OddSphereMap

end BorsukNine

namespace BorsukNine.SmithTheory

variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

lemma exists_factor_of_ker_le (N : P →ₗ[K] P) (φ : P →ₗ[K] Q)
    (h : LinearMap.ker N ≤ LinearMap.ker φ) : ∃ ψ : P →ₗ[K] Q, ψ.comp N = φ := by
  let ψ₀ : LinearMap.range N →ₗ[K] Q :=
    (N.ker.liftQ φ h).comp N.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ, hψ⟩ := ψ₀.exists_extend
  refine ⟨ψ, ?_⟩
  ext x
  have he := LinearMap.congr_fun hψ ⟨N x, LinearMap.mem_range_self N x⟩
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, ψ₀,
    LinearEquiv.coe_toLinearMap, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply] using he

lemma exists_factor_of_vanish_norm (N : P →ₗ[K] P)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : P →ₗ[K] Q)
    (hφ : φ.comp N = 0) : ∃ ψ : P →ₗ[K] Q, ψ.comp N = φ := by
  apply exists_factor_of_ker_le N φ
  intro x hx
  obtain ⟨y, rfl⟩ := hexact hx
  exact LinearMap.congr_fun hφ y

end BorsukNine.SmithTheory

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_NormMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

noncomputable def normMap (K : PreAbstractSimplicialComplex V) (e : V ≃ V) :
    Chain K →ₗ[F₂] Chain K := LinearMap.id + mapChains K K e

lemma normMap_eq (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) :
    normMap K e = SmithTheory.involutionNorm (faceEquiv K e he) := by
  unfold normMap SmithTheory.involutionNorm
  rw [mapChains_equiv K e he]

lemma boundary_normMap (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) :
    (boundary K).comp (normMap K e) = (normMap K e).comp (boundary K) := by
  unfold normMap
  rw [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_id, LinearMap.id_comp,
    mapChains_boundary K K e he]

lemma augmentation_normMap (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) :
    (augmentation K).comp (normMap K e) = 0 := by
  unfold normMap
  rw [LinearMap.comp_add, LinearMap.comp_id, mapChains_augmentation K K e he]
  ext c
  exact CharTwo.add_self_eq_zero _

noncomputable def degreeChains (K : PreAbstractSimplicialComplex V) (d : ℕ) :
    Submodule F₂ (Chain K) := Finsupp.supported F₂ F₂ {s | s.val.card = d}

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SubdivSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

noncomputable def subdivSimplex (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    (s : Finset V) : Chain L :=
  if _hs : s.Nonempty then
    if s.card = 1 then simplex L {b s}
    else cone L (b s) (∑ a ∈ s.attach, subdivSimplex L b (s.erase a.val))
  else 0
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem a.property

@[simp] lemma subdivSimplex_empty (L : PreAbstractSimplicialComplex W) (b : Finset V → W) :
    subdivSimplex L b ∅ = 0 := by rw [subdivSimplex]; simp

def vertexCarrier (b : Finset V → W) (s : Finset V) : Set W :=
  {w | ∃ t : Finset V, t.Nonempty ∧ t ⊆ s ∧ b t = w}

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SimplexMemDegreeAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def SubdivisionCarrier (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (b : Finset V → W) : Prop :=
  ∀ s ∈ K, ∀ t : Finset W, t.Nonempty → ↑t ⊆ vertexCarrier b s → t ∈ L

noncomputable def subdivMap (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) : Chain K →ₗ[F₂] Chain L :=
  Finsupp.linearCombination F₂ (fun s => subdivSimplex L b s.val)

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SignedVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

abbrev SignedVertex := ℕ × Bool

def flip : SignedVertex ≃ SignedVertex :=
  Equiv.prodCongr (Equiv.refl ℕ) Equiv.boolNot

@[simp] lemma flip_apply (v : SignedVertex) : flip v = (v.1, !v.2) := rfl

lemma flip_involutive : Function.Involutive flip := by
  intro v
  simp

lemma flip_ne (v : SignedVertex) : flip v ≠ v := by
  intro equality
  exact Bool.not_ne_self v.2 (congrArg Prod.snd equality)

def cross (n : ℕ) : PreAbstractSimplicialComplex SignedVertex where
  faces := {s | s.Nonempty ∧ (∀ v ∈ s, v.1 < n) ∧ Set.InjOn Prod.fst (s : Set SignedVertex)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, fun v hv => hs.2.1 v (hts hv), hs.2.2.mono hts⟩

lemma cross_flip_forward (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) :
    s.image flip ∈ cross n := by
  refine ⟨hs.1.image _, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact hs.2.1 w hw
  · intro v hv w hw he
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    exact congrArg flip (hs.2.2 hv' hw' he)

lemma cross_flip (n : ℕ) (s : Finset SignedVertex) :
    s ∈ cross n ↔ s.image flip ∈ cross n := by
  refine ⟨cross_flip_forward n s, ?_⟩
  intro hs
  have h := cross_flip_forward n _ hs
  rw [Finset.image_image] at h
  have hh : flip ∘ flip = id := funext flip_involutive
  simpa only [hh, Finset.image_id] using h

lemma cross_free (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) :
    s.image flip ≠ s := by
  intro he
  obtain ⟨v, hv⟩ := hs.1
  have hv' : flip v ∈ s := he ▸ Finset.mem_image_of_mem flip hv
  exact flip_ne v (hs.2.2 hv' hv rfl)

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

noncomputable def crossTower (n : ℕ) : ℕ → Chain (cross n)
  | 0 => simplex (cross n) {(0,false)}
  | i+1 => cone (cross n) (i+1,false) (normMap (cross n) flip (crossTower n i))

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_CrossChainDimensionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def barycenter (s : Finset E) : E := (s.card : ℝ)⁻¹ • ∑ x ∈ s, x

def hemisphereComplex (R : ℝ) : PreAbstractSimplicialComplex E where
  faces := {s | s.Nonempty ∧ ∃ w : E, ‖w‖ ≤ R ∧ ∀ x ∈ s, ‖x‖ ≤ 1 ∧ ⟪w,x⟫ = 1}
  isRelLowerSet_faces := by
    rintro s ⟨hs, w, hw, hs'⟩
    refine ⟨hs, ?_⟩
    intro t hts ht
    exact ⟨ht, w, hw, fun x hx => hs' x (hts hx)⟩

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_CrossEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

noncomputable def crossEmbedding (n : ℕ) (v : SignedVertex) : EuclideanSpace ℝ (Fin n) :=
  if h : v.1 < n then (if v.2 then (-1:ℝ) else 1) • EuclideanSpace.single ⟨v.1,h⟩ 1 else 0

noncomputable def crossGeometricMap (n : ℕ) :
    Chain (cross n) →ₗ[F₂] Chain (hemisphereComplex (n:ℝ) :
      PreAbstractSimplicialComplex (EuclideanSpace ℝ (Fin n))) :=
  mapChains (cross n) (hemisphereComplex (n:ℝ)) (crossEmbedding n)

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_MaxIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

noncomputable def maxIndex {m : ℕ} [NeZero m] (g : Fin m → ℝ) : Fin m :=
  (Finset.exists_max_image Finset.univ g Finset.univ_nonempty).choose

noncomputable def peakIndex {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) : Fin m :=
  maxIndex (fun i => |y i|)

noncomputable def sphereLabel {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) : SignedVertex :=
  ((peakIndex y).val, decide (y (peakIndex y) < 0))

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq E]

noncomputable def refinement (R : ℝ) : ℕ →
    Chain (hemisphereComplex R : PreAbstractSimplicialComplex E) →ₗ[F₂]
      Chain (hemisphereComplex R : PreAbstractSimplicialComplex E)
  | 0 => LinearMap.id
  | r+1 => (subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter).comp
      (refinement R r)

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_FineCrossMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

noncomputable def fineCrossMap (n r : ℕ) :
    Chain (cross n) →ₗ[F₂] Chain (hemisphereComplex (n:ℝ) :
      PreAbstractSimplicialComplex (EuclideanSpace ℝ (Fin n))) :=
  (refinement (n:ℝ) r).comp (crossGeometricMap n)

def annulus (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (1:ℝ)/n ≤ ‖x‖ ∧ ‖x‖ ≤ 1}

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_UnitRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

noncomputable def unitRadial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) : E :=
  ‖x‖⁻¹ • x

noncomputable def dropLast (n : ℕ) :
    EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => x i.castSucc)
  map_add' x y := by ext i; rfl
  map_smul' a x := by ext i; rfl

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_HemisphereChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
open SimplicialChains
section HemisphereChart
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (w : E) (e : W →ₗᵢ[ℝ] E)
noncomputable def hemisphereChart (v : W) : E := unitRadial (w + e v)
noncomputable def hemisphereInverse (u : E) : W := ⟪w,u⟫⁻¹ • e.toContinuousLinearMap.adjoint u

end HemisphereChart
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_NegativeQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace Topology
open Filter Set
section NegativeQuadratic
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
def NegativeQuadratic (B : E →L[ℝ] E) : Prop := ∀ v, v ≠ 0 → ⟪v,B v⟫ < 0
end NegativeQuadratic
end BorsukNine

namespace BorsukNine
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixBlocks
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
local notation "W" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (𝕜 := ℝ)

noncomputable def blockScalar (c : E) (A : M) : ℝ := ⟪c,op A c⟫
noncomputable def blockOff (c : E) (e : W →ₗᵢ[ℝ] E) (A : M) : W := e.toContinuousLinearMap.adjoint (op A c)
noncomputable def blockCorner (e : W →ₗᵢ[ℝ] E) (A : M) : M := matrixEmbed e (matrixCompress e A)

end MatrixBlocks
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_FacetTangent
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped BigOperators
section FacetTangent
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "W" => EuclideanSpace ℝ (Fin k)
noncomputable def facetTangent {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : W →ₗ[ℝ] (ι → ℝ) where
  toFun v i := if hi : i ∈ I then Fin.cases (-∑ j, v j) (fun j => v j) (a.symm ⟨i,hi⟩) else 0
  map_add' x y := by
    ext i
    dsimp
    split_ifs with hi
    · generalize a.symm ⟨i,hi⟩ = j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [Finset.sum_add_distrib]; ring
      · rfl
    · simp
  map_smul' t x := by
    ext i
    dsimp
    split_ifs with hi
    · generalize a.symm ⟨i,hi⟩ = j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [Finset.mul_sum]
      · rfl
    · simp

end FacetTangent
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_LocalModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section LocalModel
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "M" => Matrix ν ν ℝ

noncomputable def localBlockModel (f : E → ι → ℝ) (c : E) (e : W →ₗᵢ[ℝ] E)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : W ≃L[ℝ] W) (A : M) : ι → ℝ :=
  blockScalar c A • f c + facetTangent a (D (blockOff c e A)) + signedExtension f (blockCorner e A)

end LocalModel
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SymmetricEntries
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section SymmetricEntries
variable {ν : Type*} [Fintype ν] [LinearOrder ν]

noncomputable def symmetricEntries : Matrix ν ν ℝ →ₗ[ℝ] EuclideanSpace ℝ (UpperTriangle ν) where
  toFun Q := WithLp.toLp 2 (fun p => Q p.val.1 p.val.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end SymmetricEntries
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_SimplexPoint
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set
noncomputable def simplexPoint {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) : Fin (n+1) → ℝ :=
  Fin.cases (1 - ∑ i, z i) (fun i => z i)

def simplexInterior (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | (∀ i, 0 < z i) ∧ ∑ i, z i < 1}

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_PositiveSlice
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
section PositiveSlice
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "M" => Matrix ν ν ℝ

noncomputable def unflattenMatrix : EuclideanSpace ℝ (ν × ν) →ₗ[ℝ] M where
  toFun x i j := x (i,j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def flatGram (x : EuclideanSpace ℝ (ν × ν)) : M :=
  unflattenMatrix x * (unflattenMatrix x)ᴴ

end PositiveSlice
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_Rank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section RankOne
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

noncomputable def rankOne (u : E) : Matrix ν ν ℝ := fun i j => u i * u j

omit [Nonempty ν] in
lemma rankOne_action (u x : E) : op (rankOne u) x = ⟪u, x⟫ • u := by
  ext i
  change ∑ j, (u i * u j) * x j = ⟪u, x⟫ * u i
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  simp only [mul_comm]

omit [DecidableEq ν] [Nonempty ν] in
lemma rankOne_nonneg (u : E) : 0 ≤ rankOne u := by
  apply Matrix.nonneg_iff_posSemidef.mpr
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp [rankOne, Matrix.conjTranspose_apply, mul_comm]
  · intro x
    have he : star x ⬝ᵥ (rankOne u) *ᵥ x = (∑ i, u i * x i) ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, rankOne, Pi.star_apply, star_trivial]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      simp_rw [← mul_assoc, mul_comm (x _) (u _)]
      rw [← Finset.sum_mul, pow_two]
    rw [he]
    exact sq_nonneg _

omit [DecidableEq ν] [Nonempty ν] in
lemma rankOne_trace (u : E) : Matrix.trace (rankOne u) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [Matrix.trace, Matrix.diag, rankOne, pow_two]

end RankOne

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixFibre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section MatrixFibre
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma rankOne_mul_of_kernel {Q : M} (hQ : IsSelfAdjoint Q) {u : E}
    (hu : op Q u = 0) : rankOne u * Q = 0 := by
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op (rankOne u * Q) = op 0
  rw [map_mul,map_zero]
  apply ContinuousLinearMap.ext
  intro v
  change op (rankOne u) (op Q v) = 0
  rw [rankOne_action]
  have hi : ⟪u,op Q v⟫ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint,← map_star,hQ.star_eq,hu,inner_zero_left]
  rw [hi,zero_smul]

lemma rankOne_split_parts {Q : M} (hQ : 0 ≤ Q) {u : E} (hu : op Q u = 0)
    {lam mu : ℝ} (hl : 0 ≤ lam) (hm : 0 ≤ mu) :
    (lam • rankOne u - mu • Q)⁺ = lam • rankOne u ∧
    (lam • rankOne u - mu • Q)⁻ = mu • Q := by
  apply CFC.posPart_negPart_unique rfl _ (smul_nonneg hl (rankOne_nonneg u)) (smul_nonneg hm hQ)
  rw [Matrix.smul_mul,Matrix.mul_smul,rankOne_mul_of_kernel hQ.isSelfAdjoint hu,smul_zero,smul_zero]

noncomputable def matrixFibre (u : E) : Set M :=
  {Q | 0 ≤ Q ∧ Matrix.trace Q = 1 ∧ op Q u = 0}

end MatrixFibre
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_TraceSphere
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
section TraceSphere
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "M" => Matrix ν ν ℝ

noncomputable def traceSphere (ν : Type*) [Fintype ν] [DecidableEq ν] : Set (Matrix ν ν ℝ) :=
  {A | IsSelfAdjoint A ∧ Matrix.trace (CFC.abs A) = 1}

noncomputable def traceRadial (A : M) : M := (Matrix.trace (CFC.abs A))⁻¹ • A

end TraceSphere
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_ActiveChambers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section ActiveChambers
variable {E W ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]

def activeVectors (f : E → ι → ℝ) (I : Finset ι) : Set E :=
  {z | ∃ i ∈ I, 0 < homogeneousLift f z i}

def commonPositiveCone (f : E → ι → ℝ) (I : Finset ι) : Set E :=
  {z | ∀ i ∈ I, 0 < homogeneousLift f z i}

end ActiveChambers
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_PurityGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section PurityGeometry
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

noncomputable def orientedLevel (f : E → ι → ℝ) (w : E) (r : ι → ℝ) : Set E :=
  {u | ‖u‖ = 1 ∧ f u = r ∧ 0 ≤ ⟪w,u⟫}

noncomputable def levelFibre (f : E → ι → ℝ) (w : E) (r : ι → ℝ) : Set (E × M) :=
  {p | p.1 ∈ orientedLevel f w r ∧ 0 ≤ p.2 ∧ Matrix.trace p.2 = 1 ∧ op p.2 p.1 = 0}

omit [Nonempty ν] in
lemma balancedFibre_mem {u : E} (hu : ‖u‖ = 1) {Q : M}
    (hQ : 0 ≤ Q) (htr : Matrix.trace Q = 1) (hQu : op Q u = 0) :
    ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) ∈ traceSphere ν := by
  have hSA : IsSelfAdjoint ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) :=
    ((IsSelfAdjoint.all (_:ℝ)).smul (rankOne_nonneg u).isSelfAdjoint).sub
      ((IsSelfAdjoint.all (_:ℝ)).smul hQ.isSelfAdjoint)
  refine ⟨hSA,?_⟩
  obtain ⟨hp,hn⟩ := rankOne_split_parts hQ hQu (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num)
  rw [← CFC.posPart_add_negPart _ hSA,hp,hn,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,
    rankOne_trace,hu,one_pow,htr]
  norm_num

end PurityGeometry
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_RegularBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set
open scoped RealInnerProductSpace
section RegularBase
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
noncomputable def baseCoordinates (f : E → ι → ℝ) (w : E) (e : W →ₗᵢ[ℝ] E)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : W → W :=
  fun v => WithLp.toLp 2 (fun j => f (hemisphereChart w e v) (a j.succ).val)

noncomputable def facetPoint {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : W) : ι → ℝ :=
  fun i => if hi : i ∈ I then simplexPoint z (a.symm ⟨i,hi⟩) else 0

end RegularBase
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SpectralChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
section SpectralChart
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "M" => Matrix ν ν ℝ

noncomputable def positiveProjection (A : M) : M := Ring.inverse A * A⁺

end SpectralChart
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_LineRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
section LineRepresentative
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

noncomputable def lineRepresentative (w : E) (A : M) : E :=
  ‖op A⁺ w‖⁻¹ • op A⁺ w

def HasPositiveLine (A : M) : Prop :=
  ∃ u : E, ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u

end LineRepresentative
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_RegularPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section RegularPatch
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "op" => Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ)
noncomputable def regularPatch (f : E → ι → ℝ) (I : Finset ι) (w c : E)
    (e : W →ₗᵢ[ℝ] E) (δ : ℝ) : Set (traceSphere (Fin (k+1))) :=
  {A | IsUnit A.val ∧ HasPositiveLine A.val ∧ op A.val⁺ w ≠ 0 ∧
    (∀ i ∈ I, 0 < f (lineRepresentative w A.val) i) ∧
    0 < ⟪c,lineRepresentative w A.val⟫ ∧
    ‖hemisphereInverse c e (lineRepresentative w A.val)‖ < δ ∧
    0 < blockScalar c A.val ∧
    NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A.val))}

end RegularPatch

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_SphereBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
section SphereBlock
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
noncomputable def sphereBlock (s : ℝ) (v : W) : E := WithLp.toLp 2 (Fin.cases s (fun i => v i))
noncomputable def sphereBlockModel (c : E) (e : W →ₗᵢ[ℝ] E) (D : W ≃L[ℝ] W) (u : E) : E :=
  sphereBlock ⟪c,u⟫ (D (e.toContinuousLinearMap.adjoint u))
end SphereBlock
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_NegativeFibre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section NegativeFibre
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "M" => Matrix ν ν ℝ

noncomputable def negativeFibre (A : M) : M := (Matrix.trace A⁻)⁻¹ • A⁻

end NegativeFibre
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_LocalMix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section LocalMix
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "M" => Matrix ν ν ℝ

noncomputable def localBlockMix (f : E → ι → ℝ) (c : E) (e : W →ₗᵢ[ℝ] E)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : W ≃L[ℝ] W) (t : ℝ) (A : M) : ι → ℝ :=
  (1-t) • signedExtension f A + t • localBlockModel f c e a D A

noncomputable def facetTail {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : (ι → ℝ) →ₗ[ℝ] W where
  toFun r := WithLp.toLp 2 (fun j => r (a j.succ).val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LocalMix
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_FinitePatch
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Finset
open scoped RealInnerProductSpace
section FinitePatch
variable {X E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype A]

noncomputable def finitePatch (f : X → E) (g : A → X → E) (q : A → X → ℝ)
    (t : ℝ) (x : X) : E := f x + ∑ a, (t * q a x) • (g a x - f x)

end FinitePatch

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SmithTheory_CharacteristicCochains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SmithTheory

section CharacteristicCochains
variable {P : Type*} [AddCommGroup P] [Module (ZMod 2) P]
variable (d N : P →ₗ[ZMod 2] P)

def SmithCocycle : Submodule (ZMod 2) (P →ₗ[ZMod 2] ZMod 2) where
  carrier := {φ | φ.comp N = 0 ∧ φ.comp d = 0}
  zero_mem' := by simp
  add_mem' := by intro φ ψ hφ hψ; simp [LinearMap.add_comp, hφ.1, hφ.2, hψ.1, hψ.2]
  smul_mem' := by intro a φ hφ; simp [LinearMap.smul_comp, hφ.1, hφ.2]

noncomputable def smithLift (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (φ : SmithCocycle d N) : P →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose (exists_factor_of_vanish_norm N hexact φ.val φ.property.1)

lemma smithLift_comp_norm (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (φ : SmithCocycle d N) : (smithLift d N hexact φ).comp N = φ.val :=
  Classical.choose_spec (exists_factor_of_vanish_norm N hexact φ.val φ.property.1)

noncomputable def smithNext (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) :
    SmithCocycle d N :=
  ⟨(smithLift d N hexact φ).comp d, by
    constructor
    · rw [LinearMap.comp_assoc, hcomm, ← LinearMap.comp_assoc,
        smithLift_comp_norm, φ.property.2]
    · rw [LinearMap.comp_assoc, hd, LinearMap.comp_zero]⟩

noncomputable def smithCochain (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) :
    ℕ → SmithCocycle d N
  | 0 => φ
  | n+1 => smithNext d N hd hcomm hexact (smithCochain hd hcomm hexact φ n)

noncomputable def smithDegree (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) (n : ℕ) :
    P →ₗ[ZMod 2] ZMod 2 :=
  smithLift d N hexact (smithCochain d N hd hcomm hexact φ n)

end CharacteristicCochains
end BorsukNine.SmithTheory

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_CharacteristicDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open BorsukNine.SmithTheory

section CharacteristicDegree
variable {V : Type*} [DecidableEq V]
variable (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
variable (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
variable (hfree : ∀ s ∈ K, s.image e ≠ s)

noncomputable def characteristicAugmentation : SmithCocycle (boundary K) (normMap K e) :=
  ⟨augmentation K, augmentation_normMap K e (fun s hs => (he s).mp hs),
    augmentation_boundary K⟩

include he hi hfree in
lemma normMap_exact : LinearMap.ker (normMap K e) ≤ LinearMap.range (normMap K e) := by
  rw [normMap_eq K e he]
  exact involutionNorm_exact _ (faceEquiv_involutive K e he hi)
    (faceEquiv_free K e he hfree)

noncomputable def characteristicDegree (n : ℕ) : Chain K →ₗ[F₂] F₂ :=
  smithDegree (boundary K) (normMap K e) (boundary_sq K)
    (boundary_normMap K e (fun s hs => (he s).mp hs)) (normMap_exact K e he hi hfree)
    (characteristicAugmentation K e he) n

end CharacteristicDegree

end BorsukNine.SimplicialChains

namespace BorsukNine.SimplicialChains
open Finset BorsukNine.SmithTheory

noncomputable def crossFundamental (n : ℕ) : Chain (cross n) :=
  normMap (cross n) flip (crossTower n (n-1))

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

noncomputable def crossFacet (n : ℕ) (b : Fin n → Bool) : Finset SignedVertex :=
  Finset.univ.image (fun i : Fin n => (i.val,b i))

lemma mem_crossFacet (n : ℕ) (b : Fin n → Bool) (v : SignedVertex) :
    v ∈ crossFacet n b ↔ ∃ i : Fin n, v = (i.val,b i) := by
  classical
  simp only [crossFacet, Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_congr (fun _ => eq_comm)

lemma crossFacet_card (n : ℕ) (b : Fin n → Bool) : (crossFacet n b).card = n := by
  classical
  rw [crossFacet, Finset.card_image_iff.mpr, Finset.card_univ, Fintype.card_fin]
  intro i _ j _ hij
  exact Fin.ext (congrArg Prod.fst hij)

lemma crossFacet_mem (n : ℕ) (hn : 0 < n) (b : Fin n → Bool) : crossFacet n b ∈ cross n := by
  classical
  refine ⟨?_,?_,?_⟩
  · exact Finset.card_pos.mp (by rw [crossFacet_card]; exact hn)
  · intro v hv
    obtain ⟨i,rfl⟩ := (mem_crossFacet n b v).mp hv
    exact i.isLt
  · intro v hv w hw he
    obtain ⟨i,rfl⟩ := (mem_crossFacet n b v).mp hv
    obtain ⟨j,rfl⟩ := (mem_crossFacet n b w).mp hw
    have hij : i = j := Fin.ext he
    rw [hij]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

noncomputable def flipAt {n : ℕ} (b : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update b i (! b i)

noncomputable def crossRidge (n : ℕ) (b : Fin n → Bool) (i : Fin n) : Finset SignedVertex :=
  (crossFacet n b).erase (i.val,b i)

lemma crossRidge_card (n : ℕ) (b : Fin n → Bool) (i : Fin n) :
    (crossRidge n b i).card = n-1 := by
  rw [crossRidge, Finset.card_erase_of_mem ((mem_crossFacet n b _).mpr ⟨i,rfl⟩),
    crossFacet_card]

lemma crossRidge_mem (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) (i : Fin n) :
    crossRidge n b i ∈ cross n := by
  apply ((cross n).isRelLowerSet_faces (crossFacet_mem n (by omega) b)).2
    (Finset.erase_subset _ _)
  apply Finset.card_pos.mp
  change 0 < (crossRidge n b i).card
  rw [crossRidge_card]
  omega

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_DoubleEraseSumFun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

noncomputable def contigSimplex (L : PreAbstractSimplicialComplex W) (f g : V → W)
    (s : Finset V) : Chain L :=
  if hs : s.Nonempty then
    cone L (f hs.choose) (mapSimplex L f s + mapSimplex L g s +
      ∑ a ∈ s.attach, contigSimplex L f g (s.erase a.val))
  else 0
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem a.property

@[simp] lemma contigSimplex_empty (L : PreAbstractSimplicialComplex W) (f g : V → W) :
    contigSimplex L f g ∅ = 0 := by rw [contigSimplex]; simp

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_ContigSimplexBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

noncomputable def contigMap (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f g : V → W) : Chain K →ₗ[F₂] Chain L :=
  Finsupp.linearCombination F₂ (fun s => contigSimplex L f g s.val)

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

noncomputable def approximation (n m r : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → SignedVertex) : Chain (cross n) →ₗ[F₂] Chain (cross m) :=
  (mapChains (hemisphereComplex (n:ℝ)) (cross m) f).comp (fineCrossMap n r)

def IsFineLabel (n m r : ℕ) (f : EuclideanSpace ℝ (Fin n) → SignedVertex) : Prop :=
  ∀ (s : Finset SignedVertex), s ∈ cross n →
    ∀ (t : {s : Finset (EuclideanSpace ℝ (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}),
      t ∈ (fineCrossMap n r (simplex (cross n) s)).support → t.val.image f ∈ cross m

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_LabelRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

noncomputable def labelRegion {m : ℕ} (i : Fin m) (b : Bool) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {y | (∀ j, |y j| ≤ |y i|) ∧ if b then y i ≤ 0 else 0 ≤ y i}

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SignVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

noncomputable def signVector (m : ℕ) (b : Fin m → Bool) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => if b i then (-1:ℝ) else 1)

@[simp] lemma signVector_apply (m : ℕ) (b : Fin m → Bool) (i : Fin m) :
    signVector m b i = if b i then (-1:ℝ) else 1 := rfl

noncomputable def facetCenter (m : ℕ) (b : Fin m → Bool) : EuclideanSpace ℝ (Fin m) :=
  (Real.sqrt m)⁻¹ • signVector m b

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_NormSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
noncomputable def normSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {u | ‖u‖ = 1}
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_SphereParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
open scoped RealInnerProductSpace
section SphereParity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)

noncomputable def sphereRegularPatch (w c : E) (d : W →ₗᵢ[ℝ] E) (δ : ℝ) : Set (normSphere (k+1)) :=
  {u | 0 < ⟪w,u.val⟫ ∧ 0 < ⟪c,u.val⟫ ∧ ‖hemisphereInverse c d u.val‖ < δ}
end SphereParity
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_BlockVector
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped BigOperators
section BlockVector
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def blockVector (I : Finset ι) (lam : ℝ) (r : ι → ℝ) (mu : ℝ)
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => if hi : i ∈ I then lam * r i else -mu * z ⟨i,Finset.mem_compl.mpr hi⟩)

end BlockVector
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixTransport
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

noncomputable def matrixConjugate (e : E ≃ₗᵢ[ℝ] E) : M ≃⋆ₐ[ℝ] M :=
  (op).trans (e.conjStarAlgEquiv.trans (op).symm)

end MatrixTransport
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_ReflectionTransport
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section ReflectionTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def householder (c x : E) : E ≃ₗᵢ[ℝ] E :=
  (Submodule.span ℝ {c+x}).reflection

end ReflectionTransport
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixReflection
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

noncomputable def reflectionMatrix (c u : E) : M :=
  (2 / ‖c+u‖^2) • rankOne (c+u) - 1

end MatrixReflection
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_FibreTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section FibreTransport
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

noncomputable def fibreTransport (c u v : E) (Q : M) : M :=
  matrixConjugate (householder c v) (matrixConjugate (householder c u) Q)

end FibreTransport
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_ChamberPath
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section ChamberPath
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def chamberPath (c u : E) (t : ℝ) : E :=
  ‖(1-t) • u + t • c‖⁻¹ • ((1-t) • u + t • c)

end ChamberPath
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_FibreHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section FibreHomotopy
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

noncomputable def negativeCoordinates (f : E → ι → ℝ) (I : Finset ι) (Q : M) :
    EuclideanSpace ℝ ↥(Iᶜ : Finset ι) :=
  WithLp.toLp 2 (fun i => positiveExtension f Q i.val)

noncomputable def transportedFibre (c : E) (t : ℝ) (u : E) (Q : M) : M :=
  fibreTransport c u (chamberPath c u t) Q

noncomputable def centeredFibre (c u : E) (Q : M) : M :=
  matrixConjugate (householder c u) Q

noncomputable def fibreHomotopy (f : E → ι → ℝ) (I : Finset ι) (c : E)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (t : ℝ) (u : E) (Q : M) :=
  negativeCoordinates f I (transportedFibre c t u Q) +
    t • (g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q))

end FibreHomotopy
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_FiniteOpenGlue
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped BigOperators Topology

noncomputable def finiteOpenGlue {κ X Y : Type*} [Fintype κ] [AddCommMonoid Y]
    (S : κ → Set X) (f : κ → X → Y) : X → Y :=
  by classical exact fun x => ∑ i, if x ∈ S i then f i x else 0

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_CompactTargetHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section LevelModel
variable {ν ι κ : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

noncomputable def balancedModel {f : E → ι → ℝ} {w : E} {r : ι → ℝ}
    (p : levelFibre f w r) : traceSphere ν :=
  ⟨(1/2:ℝ) • rankOne p.val.1 - (1/2:ℝ) • p.val.2,
    balancedFibre_mem p.property.1.1 p.property.2.1 p.property.2.2.1 p.property.2.2.2⟩

noncomputable def modelChambers (f : E → ι → ℝ) (I : Finset ι) (w : E) (r : ι → ℝ)
    (c : κ → E) (j : κ) : Set (levelFibre f w r) :=
  {p | p.val.1 ∈ interior (signChamber (activeVectors f I) (c j))}

noncomputable def levelHomotopy (f : E → ι → ℝ) (I : Finset ι) (w : E) (r : ι → ℝ)
    (c : κ → E) (g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) :
    ℝ × levelFibre f w r → EuclideanSpace ℝ ↥(Iᶜ : Finset ι) :=
  finiteOpenGlue (fun j => {p | p.2 ∈ modelChambers f I w r c j})
    (fun j p => fibreHomotopy f I (c j) (g j) p.1 p.2.val.1 p.2.val.2)

end LevelModel
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_CoordinateSum
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped BigOperators

noncomputable def coordinateSum {ι : Type*} [Fintype ι] : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ∑ i, x i
      map_add' := by intro x y; simp only [PiLp.add_apply,Finset.sum_add_distrib]
      map_smul' := by intro t x; simp only [PiLp.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply] }

noncomputable def uniformVector (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun _ => (Fintype.card ι : ℝ)⁻¹)

noncomputable def zeroSumProjection (ι : Type*) [Fintype ι] :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  ContinuousLinearMap.id ℝ _ - coordinateSum.smulRight (uniformVector ι)

noncomputable def simplexProjection {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :=
  zeroSumProjection ι x + uniformVector ι

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_NullImage
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open Set MeasureTheory
open scoped Topology

noncomputable def initialProjection (n m : ℕ) (h : n ≤ m) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => x (Fin.castLE h i))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_PurityChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
open Set
section PurityChart
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

noncomputable def purityChart (f : E → ι → ℝ) (I : Finset ι) (w c : E) : Set M :=
  {A | IsUnit A ∧ HasPositiveLine A ∧ op A⁺ w ≠ 0 ∧ 0 < Matrix.trace A⁻ ∧
    lineRepresentative w A ∈ commonPositiveCone f I ∧
    lineRepresentative w A ∈ interior (signChamber (activeVectors f I) c)}

end PurityChart
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_RaySet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
noncomputable def raySet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E) : Set E :=
  {v | v = (‖v‖ / ‖y‖) • y}
end BorsukNine

namespace BorsukNine
open Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section MatrixFibres
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "T" => traceSphere (Fin (k+1))
local notation "Y" => EuclideanSpace ℝ ι
noncomputable def matrixRayFibre (F : T → Y) (y : Y) (c : E) : Set T :=
  {A | F A ∈ raySet y ∧ A.val⁺ = Matrix.trace A.val⁺ • rankOne c}
end MatrixFibres
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_MixedHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section MixedHomotopy
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "Y" => EuclideanSpace ℝ ι

noncomputable def mixedHomotopy (f : E → ι → ℝ) (I : Finset ι) (w c : E)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (t : ℝ) (A : M) : Y :=
  blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
    (fibreHomotopy f I c g t (lineRepresentative w A) (negativeFibre A))

end MixedHomotopy
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_SupportIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
section SupportIncidence
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
def SupportFace (f : V → ι → ℝ) (S : Finset ι) : Prop :=
  ∃ u : V, ‖u‖ = 1 ∧ S ⊆ positiveSupport f u
end SupportIncidence

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_AllPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory

namespace BorsukNine.SixCounting

variable {α : Type*} [DecidableEq α]
noncomputable local instance instDecidablePred_solutions : DecidablePred (fun p : Prop => p) := Classical.propDecidable

noncomputable def triangles (C : Finset α) (T : Finset α → Prop) : Finset (Finset α) :=
  (C.powersetCard 3).filter T

omit [DecidableEq α] in
@[simp] lemma mem_triangles {C U : Finset α} {T : Finset α → Prop} :
    U ∈ triangles C T ↔ U ⊆ C ∧ U.card = 3 ∧ T U := by
  simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

end BorsukNine.SixCounting

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_Within
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
attribute [local instance] Classical.propDecidable
section Within
variable {α : Type*} [DecidableEq α]
noncomputable def withinLabels (C U : Finset α) : Finset C := U.subtype (· ∈ C)
@[simp] lemma mem_withinLabels {C U : Finset α} {i : C} :
    i ∈ withinLabels C U ↔ i.val ∈ U := Finset.mem_subtype
end Within

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_TenLabels_Labels
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction

abbrev Labels := Fin 10
abbrev Family := Finset Labels → Prop

attribute [local instance] Classical.propDecidable

structure TenSystem (T Q : Family) : Prop where
  tetra_card : ∀ S, Q S → S.card = 4
  down : ∀ S U, Q S → U ⊆ S → U.card = 3 → T U
  pure : ∀ U, T U → ∃ S, Q S ∧ U ⊆ S
  no_boundary : ∀ S U, Q S → U ⊆ S → U.card = 3 →
    ∃ S', Q S' ∧ U ⊆ S' ∧ S' ≠ S
  complementary : ∀ S U, Q S → U ⊆ Sᶜ → U.card = 3 →
    (T U ↔ ¬ T (Sᶜ \ U))
  pair_count : ∀ S P, Q S → P ⊆ Sᶜ → P.card = 2 →
    ((Sᶜ \ P).filter (fun w => T (insert w P))).card = 2

variable {T Q : Family}

@[simp] lemma map_compl (e : Equiv.Perm Labels) (S : Finset Labels) :
    Sᶜ.map e.toEmbedding = (S.map e.toEmbedding)ᶜ := by
  ext x
  simp

@[simp] lemma map_symm_map (e : Equiv.Perm Labels) (S : Finset Labels) :
    (S.map e.symm.toEmbedding).map e.toEmbedding = S := by
  ext x
  simp

@[simp] lemma symm_map_map (e : Equiv.Perm Labels) (S : Finset Labels) :
    (S.map e.toEmbedding).map e.symm.toEmbedding = S := by
  ext x
  simp

end BorsukNine.FiniteObstruction

end OAI
end


