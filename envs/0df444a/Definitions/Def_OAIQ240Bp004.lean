-- Prove2me | Definitions.Def_OAIQ240Bp004
-- name    : OAIQ240Bp004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:41:17.863582+00:00
-- url     : https://prove2.me/theorems/f20ac36c-e7f2-487b-9920-eb1fbd481caf
-- title:
--   Definitions bundle OAIQ240Bp004 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 149 declarations of OpenAI's Lean: 58 definitions, 1 inductive type or structure, 8 instances and 82 theorems. The definitions and types are `OAI.PackingSufficiencySupport.Hamiltonian.HasSmoothSurfaceBoundary`, `OAI.PackingSufficiencySupport.Hamiltonian.IntervalPlacements`, `OAI.PackingSufficiencySupport.Hamiltonian.RoundedMargins`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothCircleAction`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothCircleAction.slice`, `OAI.PackingSufficiencySupport.Hamiltonian.StrictNestedStarts`, `OAI.PackingSufficiencySupport.Hamiltonian.areaRadius`, `OAI.PackingSufficiencySupport.Hamiltonian.baseFiberInner`, `OAI.PackingSufficiencySupport.Hamiltonian.baseFiberMoment`, `OAI.PackingSufficiencySupport.Hamiltonian.baseFiberOuter`, `OAI.PackingSufficiencySupport.Hamiltonian.chartField`, `OAI.PackingSufficiencySupport.Hamiltonian.complexAffineTangent`, `OAI.PackingSufficiencySupport.Hamiltonian.complexLeftBlock`, `OAI.PackingSufficiencySupport.Hamiltonian.complexLeftBlockCLM`, `OAI.PackingSufficiencySupport.Hamiltonian.complexMiddleBlock`, `OAI.PackingSufficiencySupport.Hamiltonian.complexMiddleBlockCLM`, `OAI.PackingSufficiencySupport.Hamiltonian.complexPair`, `OAI.PackingSufficiencySupport.Hamiltonian.complexPairing`, `OAI.PackingSufficiencySupport.Hamiltonian.diskChartRadius`, `OAI.PackingSufficiencySupport.Hamiltonian.familySpatialExterior`, `OAI.PackingSufficiencySupport.Hamiltonian.fiberField`, `OAI.PackingSufficiencySupport.Hamiltonian.infinitySign`, `OAI.PackingSufficiencySupport.Hamiltonian.localNormalJet`, `OAI.PackingSufficiencySupport.Hamiltonian.logarithmicError`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldPotentialChart`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldSpatialDifferential`, `OAI.PackingSufficiencySupport.Hamiltonian.maximalChartLinearEquiv`, `OAI.PackingSufficiencySupport.Hamiltonian.nonautonomousSlice`, `OAI.PackingSufficiencySupport.Hamiltonian.parameterField`, `OAI.PackingSufficiencySupport.Hamiltonian.pathTimePrimitive`, `OAI.PackingSufficiencySupport.Hamiltonian.periodicPrimitive`, `OAI.PackingSufficiencySupport.Hamiltonian.planarMarginal`, `OAI.PackingSufficiencySupport.Hamiltonian.planarPrimitiveX`, `OAI.PackingSufficiencySupport.Hamiltonian.planarPrimitiveY`, `OAI.PackingSufficiencySupport.Hamiltonian.preferredDifferential`, `OAI.PackingSufficiencySupport.Hamiltonian.primitiveLineBump`, `OAI.PackingSufficiencySupport.Hamiltonian.radialOneFormPotential`, `OAI.PackingSufficiencySupport.Hamiltonian.reparametrizedTimeField`, `OAI.PackingSufficiencySupport.Hamiltonian.smoothBlowup`, `OAI.PackingSufficiencySupport.Hamiltonian.smoothUpperPositivePart` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `BallPacking_BallMaps_CubicBubbleSeparated`, `BallPacking_BallMaps_QuadricLargeAmbientPacking`, `BallPacking_BallMaps_SphereCartesianDescent`, `BallPacking_DiskMaps_CompactEmbeddingIsotopy`, `BallPacking_DiskMaps_FlatIsotopy`, `BallPacking_DiskMaps_SmoothConvexSelection`, `BallPacking_Flows_FlowSmoothExtension`, `BallPacking_Flows_ManifoldFormTransport`, `BallPacking_Flows_NonautonomousManifoldFlow`, `BallPacking_Flows_TimeSteps`, `BallPacking_Forms_HorizontalCoupling`, `BallPacking_Forms_QuadricInfinityPrimitive`, `BallPacking_Forms_SpatialOneForm`, `BallPacking_Hopf_AffineHopfRestriction`, `BallPacking_Models_CubicPhysicalLocality`, `BallPacking_Models_DisjointClocks`, `BallPacking_Models_EqualNormalModelConvergence`, `BallPacking_Models_LiouvilleRadialCalculus`, `BallPacking_Models_RationalSlack`, `BallPacking_Moments_PolytopeSlices`, `BallPacking_Moser_AnnularFinalPacking`, `BallPacking_Moser_ManifoldExteriorNaturality`, `BallPacking_Moser_ManifoldMoserField`, `BallPacking_Moser_ParametricMoser`, `BallPacking_Moser_PlanarCorrection`, `BallPacking_Moser_PlanarCovectorPrimitive`, `BallPacking_Moser_SmoothManifoldIntegral`, `BallPacking_Normal_MovingPrimitiveNaturality`, `BallPacking_RelativeJets_SymplecticProjectionNaturality`, `BallPacking_SurfaceArea_BoundedPlanarResidue`, `BallPacking_SurfaceArea_QuadricEndAnnuli`, `BallPacking_SurfaceArea_QuadricEndResidueMass`, `BallPacking_Toric_RestrictedMassIndependence`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ240Bp007`; the proof of `OAI_HigherDimensionalBallPacking_Rigidity_packing_two_line_reduction`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ240_BP.Compat
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
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_TimeSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology NNReal
open scoped ContDiff Topology
open Set Metric
open scoped ContDiff Topology
open Set Metric

namespace PackingSufficiencySupport.Hamiltonian

def planarMarginal (A : ℝ) (f : ℝ × ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in -A..A, f (x,t)

def planarPrimitiveX (A : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -ρ p.1 * ∫ t in -A..p.2, planarMarginal A f t

def planarPrimitiveY (A : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ x in -A..p.1, f (x,p.2) - ρ x * planarMarginal A f p.2

open MeasureTheory Function

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Metric
open MeasureTheory Function
open scoped Classical

theorem smoothTransition_deriv_compact : HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 1))
  intro t ht
  have hor : t < 0 ∨ 1 < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases hor with ht | ht
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    exact ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he).deriv
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact Real.smoothTransition.one_of_one_le hs.le
    exact ((hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq he).deriv

def periodicPrimitive (a : ℝ → ℝ) (t : ℝ) := ∫ s in -Real.pi..t, a s

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCovectorPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def symplecticProjection (Ω : E →L[ℝ] E →L[ℝ] ℝ) (i : F →L[ℝ] E) : E →L[ℝ] F :=
  (Ω.bilinearComp i i).inverse.comp (Ω.bilinearComp (ContinuousLinearMap.id ℝ E) i)

def symplecticNormalJet (Ω : E →L[ℝ] E →L[ℝ] ℝ) (i : F →L[ℝ] E)
    (α : E →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  α.comp (i.comp (symplecticProjection Ω i)) - α


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def preferredDifferential (f : M → M) (x : M) : E →L[ℝ] E :=
  mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldMoserField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped NNReal
open MeasureTheory

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def parameterField (X : C(ℝ × (P × E),E)) : C(ℝ × (P × E),P × E) :=
  ⟨fun p => (0,X p),continuous_const.prodMk X.continuous⟩

def fiberField (X : C(ℝ × (P × E),E)) (y : P) : C(ℝ × E,E) :=
  ⟨fun p => X (p.1,(y,p.2)),X.continuous.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))⟩

omit [NormedSpace ℝ P] [CompleteSpace P] [NormedSpace ℝ E] [CompleteSpace E] in
theorem parameterField_lipschitz {L : ℝ≥0} (X : C(ℝ × (P × E),E))
    (hX : LipschitzWith L X) : LipschitzWith L (parameterField X) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [parameterField,ContinuousMap.coe_mk,Prod.dist_eq,dist_self,
    max_eq_right dist_nonneg] using hX.dist_le_mul p q

omit [NormedSpace ℝ P] [CompleteSpace P] [NormedSpace ℝ E] [CompleteSpace E] in
theorem fiberField_lipschitz {L : ℝ≥0} (X : C(ℝ × (P × E),E))
    (hX : LipschitzWith L X) (y : P) : LipschitzWith L (fiberField X y) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [fiberField,ContinuousMap.coe_mk,Prod.dist_eq,dist_self,
    max_eq_right dist_nonneg] using hX.dist_le_mul (p.1,(y,p.2)) (q.1,(y,q.2))

omit [CompleteSpace P] [CompleteSpace E] in
theorem parameterField_smooth (X : C(ℝ × (P × E),E)) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (parameterField X) := contDiff_const.prodMk hX

omit [CompleteSpace P] [CompleteSpace E] in
theorem fiberField_smooth (X : C(ℝ × (P × E),E)) (hX : ContDiff ℝ ∞ X) (y : P) :
    ContDiff ℝ ∞ (fiberField X y) :=
  hX.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ParametricMoser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory

def diskChartRadius (R r : ℝ) : ℝ := r / Real.sqrt (R^2-r^2)

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_SpatialOneForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def manifoldSpatialDifferential (f : ℝ × M → ℝ) (t : ℝ) (x : M) : E →L[ℝ] ℝ :=
  mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun z => f (t,z)) x

def manifoldPotentialChart (f : ℝ × M → ℝ) (c : M) (p : ℝ × E) : ℝ :=
  f (p.1,(extChartAt 𝓘(ℝ,E) c).symm p.2)


end

open scoped ContDiff Manifold Topology
open MeasureTheory Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_FlatIsotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
open scoped ComplexConjugate
section

universe u
variable {P E F : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def smoothBlowup (f : E → F) (p : ℝ × E) : F :=
  ∫ s in (0:ℝ)..1, fderiv ℝ f ((s*p.1) • p.2) p.2

end

def complexPair (a b : ℂ) : ℂ →L[ℝ] ℂ :=
  a • ContinuousLinearMap.id ℝ ℂ + b • Complex.conjCLE.toContinuousLinearMap

@[simp] theorem complexPair_apply (a b z : ℂ) : complexPair a b z = a*z+b*conj z := rfl

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_QuadricInfinityPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {ι : Type*} [Fintype ι]

 def complexPairing (z v : ι → ℂ) : ℂ := ∑ i,star (z i)*v i

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_HorizontalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pathTimePrimitive (Γ : ℝ × E → E →L[ℝ] ℝ) (p : ℝ × E) : E →L[ℝ] ℝ :=
  fderiv ℝ Γ p (1,0)


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open scoped BigOperators
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def familySpatialExterior (Γ : P × E → E →L[ℝ] ℝ) (p : P × E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (fderiv ℝ Γ p).comp (ContinuousLinearMap.inr ℝ P E) -
    ((fderiv ℝ Γ p).comp (ContinuousLinearMap.inr ℝ P E)).flip

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricEndAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

def primitiveLineBump (A : ℝ) (hA : 0<A) : ℝ → ℝ :=
  (⟨A/2,A,by positivity,by linarith⟩ : ContDiffBump (0:ℝ)).normed volume

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricEndResidueMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology ENNReal NNReal
open Set Function Manifold MeasureTheory

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × ℝ) M]
  [IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M]

 def HasSmoothSurfaceBoundary (D : Set M) : Prop :=
  ∀ x∈frontier D,∃ e : PartialDiffeomorph 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℝ × ℝ) M (ℝ × ℝ) ∞,
    x∈e.source ∧ ∀ y∈e.source,(y∈D ↔ 0≤(e y).2)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_BoundedPlanarResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open Set Filter
open scoped Topology

 def logarithmicError (C R : ℝ) (n : ℕ) : ℝ := C/(-Real.log (R/((n:ℝ)+1)))

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_SmoothConvexSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function

variable {n : ℕ}

def StrictNestedStarts (L c : Fin n → ℝ) : Prop :=
  ∀ ⦃i j : Fin n⦄, i < j → c j < c i ∧ c i+L i < c j+L j

def IntervalPlacements (L : Fin n → ℝ) (V : Fin n → Set ℝ) : Set (Fin n → ℝ) :=
  {c | (∀ i, c i ∈ V i ∧ c i+L i ∈ V i) ∧ StrictNestedStarts L c}


end

section
open scoped ContDiff Topology
open Set Function
variable {P : Type*} [TopologicalSpace P]

def RoundedMargins {n : ℕ} (C : P → Fin n → ℝ) (L w : Fin n → ℝ)
    (V : P → Fin n → Set ℝ) (q s : ℝ) (y : P) : Prop :=
  0 < s ∧
  (∀ i, C y i-s*L i/2 ∈ V y i ∧ C y i+s*L i/2 ∈ V y i) ∧
  ∀ ⦃i j⦄, i < j →
    C y j-q*s*L j/2 < C y i-s*L i/2 ∧
    C y i+s*L i/2 < C y j+q*s*L j/2 ∧ w i < q*w j


end

open scoped ContDiff Topology
open Set Function MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CompactEmbeddingIsotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory

def areaRadius (a : ℝ) : ℝ := Real.sqrt (a/Real.pi)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_PolytopeSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical
namespace PackingSufficiencySupport.MomentPolytope
variable {m N : ℕ}

theorem weighted_affine {ι : Type*} [Fintype ι] (B y z : ι → ℝ) (a d : ℝ) :
    ∑ i, B i * (a * y i + d * z i) = a * ∑ i, B i * y i + d * ∑ i, B i * z i := by
  calc
    _ = ∑ i, (a * (B i * y i) + d * (B i * z i)) := by congr 1; funext i; ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

end PackingSufficiencySupport.MomentPolytope

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_ManifoldFormTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def chartField (v : (x : M) → TangentSpace 𝓘(ℝ,E) x) (x : M) (y : E) : E :=
  let z := (extChartAt 𝓘(ℝ,E) x).symm y
  tangentCoordChange 𝓘(ℝ,E) z x z (v z)


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_FlowSmoothExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def timeLiftField (χ : ℝ → ℝ) (V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2)
    (p : ℝ × M) : TangentSpace ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) p :=
  χ p.1 • ((1:ℝ),V p)


end

open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_NonautonomousManifoldFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def nonautonomousSlice (Φ Ψ : ℝ × M → M)
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    (hΨ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ)
    (t : ℝ) (hinv : ∀ x, Ψ (t,Φ (t,x)) = x ∧ Φ (t,Ψ (t,x)) = x) :
    M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ M where
  toFun x := Φ (t,x)
  invFun x := Ψ (t,x)
  left_inv x := (hinv x).1
  right_inv x := (hinv x).2
  contMDiff_toFun := hΦ.comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := hΨ.comp (contMDiff_const.prodMk contMDiff_id)

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_AnnularFinalPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {M V ι : Type*}

def baseFiberMoment (χ : M → ℝ) (μ : ι → V → ℝ) : Option ι → M × V → ℝ := fun i =>
  match i with | none => fun z => -χ z.1 | some i => fun z => μ i z.2

def baseFiberInner (a : ι → ℝ) : Option ι → ℝ :=
  fun i => match i with | none => -3/4 | some i => a i

def baseFiberOuter (c : ι → ℝ) : Option ι → ℝ :=
  fun i => match i with | none => -1/2 | some i => c i

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_SmoothManifoldIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable (E : Type) (M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

structure SmoothCircleAction where
  toFun : ℝ × M → M
  smooth : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ toFun
  zero : ∀ x, toFun (0,x) = x
  add : ∀ s t x, toFun (s+t,x) = toFun (s,toFun (t,x))
  period : ∀ s x, toFun (s+1,x) = toFun (s,x)

variable {E M}
namespace SmoothCircleAction
variable (A : SmoothCircleAction E M)

def slice (s : ℝ) (x : M) : M := A.toFun (s,x)

end SmoothCircleAction

end

section
open scoped ContDiff Topology
open Set Function
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def timePullbackOneForm (α : ℝ × E → E →L[ℝ] ℝ) (g : F → E)
    (p : ℝ × F) : F →L[ℝ] ℝ := (α (p.1,g p.2)).comp (fderiv ℝ g p.2)

def timePullbackTwoForm (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (g : F → E)
    (p : ℝ × F) : F →L[ℝ] F →L[ℝ] ℝ :=
  (Ω (p.1,g p.2)).bilinearComp (fderiv ℝ g p.2) (fderiv ℝ g p.2)


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_RelativeJets_SymplecticProjectionNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open Set Function
open scoped ContDiff Topology
open scoped Manifold
open Manifold IsManifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def localNormalJet (β : E → E →L[ℝ] ℝ) (r : E → E) (x : E) : ℝ := β x (x-r x)

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem maximalChart_inverse_differential {c : OpenPartialHomeomorph M E}
    (hc : c ∈ maximalAtlas 𝓘(ℝ,E) ∞ M) {x : M} (hx : x ∈ c.source) :
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c.symm (c x)).comp (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c x) =
      ContinuousLinearMap.id ℝ E ∧
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c x).comp (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c.symm (c x)) =
      ContinuousLinearMap.id ℝ E := by
  have hd := (contMDiffAt_of_mem_maximalAtlas hc hx).mdifferentiableAt (by simp)
  have hi := (contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hx)).mdifferentiableAt (by simp)
  constructor
  · have hf := (hi.hasMFDerivAt.comp x hd.hasMFDerivAt).mfderiv
    have he : (c.symm ∘ c : M → M) =ᶠ[𝓝 x] id := by
      filter_upwards [c.open_source.mem_nhds hx] with z hz
      exact c.left_inv hz
    rw [he.mfderiv_eq] at hf
    convert! hf.symm using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mfderiv_id]
    rfl
  · have hid := hi.hasMFDerivAt
    have hd' : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,E) c (c.symm (c x))
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c x) := by
      rw [c.left_inv hx]
      exact hd.hasMFDerivAt
    have hf := (hd'.comp (c x) hid).mfderiv
    have he : (c ∘ c.symm : E → E) =ᶠ[𝓝 (c x)] id := by
      filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with z hz
      exact c.right_inv hz
    rw [he.mfderiv_eq] at hf
    convert! hf.symm using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mfderiv_id]
    rfl

def maximalChartLinearEquiv {c : OpenPartialHomeomorph M E}
    (hc : c ∈ maximalAtlas 𝓘(ℝ,E) ∞ M) {x : M} (hx : x ∈ c.source) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse' (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c x)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c.symm (c x))
    (maximalChart_inverse_differential hc hx).2 (maximalChart_inverse_differential hc hx).1

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_MovingPrimitiveNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.NormalLift
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

abbrev zeroFibre (f : E → F) := {z : E // f z=0}
abbrev tubeDomain (f : E → F) (W : Set (E×F)) :=
  {p : zeroFibre f × F // ((p.1 : E),p.2)∈W}
def tubeSlice (Φ : ℝ × (E×F) → E×F) (t : ℝ) (f : E → F) (W : Set (E×F))
    (p : tubeDomain f W) : E := (Φ (t,((p.val.1 : E),p.val.2))).1

end PackingSufficiencySupport.NormalLift

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_EqualNormalModelConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped BigOperators
open Set MeasureTheory

def momentSimplex (m : ℕ) (h : ℝ) : Set (Fin m → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i ≤ h}

def smallModelMean (m : ℕ) (h : ℝ) : ℝ :=
  (2:ℝ)^m*h^m/(m.factorial : ℝ)*(1-2*m*h/(m+1))

def cappedAffine {m : ℕ} {ι : Type*} [Fintype ι]
    (A : ℝ) (B : Fin m → ℝ) (r w : ι → ℝ) (p : Fin m → ℝ) : ℝ :=
  A-(∑ j, B j*p j)-∑ i,w i*max (r i-∑ j,p j) 0

end PackingSufficiencySupport
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_DisjointClocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function

def smoothUpperPositivePart (δ x : ℝ) : ℝ := (x+Real.sqrt (x^2+δ^2))/2

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_RationalSlack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped BigOperators
open Set
open scoped Pointwise
open MeasureTheory

def smallModelGap {m : ℕ} {ι : Type*} [Fintype ι] (r : ι → ℝ) (p : Fin m → ℝ) : ℝ :=
  (2:ℝ)^m*(1-2*∑ j,p j)-∑ i,max (r i-∑ j,p j) 0

end PackingSufficiencySupport

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_CubicPhysicalLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped BigOperators
open MeasureTheory Set
open scoped Pointwise
open MomentPolytope

def truncatedSimplex (q : ℕ) (h b : ℝ) : Set (ℝ × (Fin q → ℝ)) :=
  {x | x.1 ∈ Icc 0 h ∧ x.2 ∈ momentSimplex q (b-x.1)}

def sixModelMean (s b h₁ h₂ : ℝ) : ℝ :=
  (3/2)*(b^3-(b-h₁)^3) -(9/2)*h₁*(b-h₂)^2 -(1/3)*(s^3-(s-h₁)^3)

def momentHeadTail (q : ℕ) : (Fin (q+1) → ℝ) ≃ᵐ (ℝ×(Fin q → ℝ)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q+1) => ℝ) 0

@[simp] theorem momentHeadTail_apply (q : ℕ) (p : Fin (q+1) → ℝ) :
    momentHeadTail q p=(p 0,fun i => p i.succ) := by
  rfl

@[simp] theorem momentHeadTail_symm_apply (q : ℕ) (x : ℝ×(Fin q → ℝ)) :
    (momentHeadTail q).symm x=Fin.cons x.1 x.2 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [momentHeadTail,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]

end PackingSufficiencySupport

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_AffineHopfRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
section
variable {ι : Type*} [Fintype ι]

def complexAffineTangent : (ι → ℂ) →L[ℝ] (Option ι → ℂ) :=
  ContinuousLinearMap.pi fun i => match i with
  | none => 0
  | some i => ContinuousLinearMap.proj i

omit [Fintype ι] in
@[simp] theorem complexAffineTangent_none (z : ι → ℂ) : complexAffineTangent z none=0 := rfl
omit [Fintype ι] in
@[simp] theorem complexAffineTangent_some (z : ι → ℂ) (i : ι) : complexAffineTangent z (some i)=z i := rfl

end

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open scoped BigOperators
section

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

 def complexMiddleBlock (z : κ → ℂ) : (ι ⊕ (κ ⊕ ν)) → ℂ :=
   Sum.elim 0 (Sum.elim z 0)

 def complexMiddleBlockCLM : (κ → ℂ) →L[ℝ] ((ι ⊕ (κ ⊕ ν)) → ℂ) :=
   ContinuousLinearMap.pi fun i => match i with
     | Sum.inl _ => 0
     | Sum.inr (Sum.inl k) => ContinuousLinearMap.proj k
     | Sum.inr (Sum.inr _) => 0

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldExteriorNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def reparametrizedTimeField (τ : ℝ → ℝ)
    (V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2)
    (p : ℝ × M) : TangentSpace 𝓘(ℝ,E) p.2 := deriv τ p.1 • V (τ p.1,p.2)

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_SphereCartesianDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]
 def complexLeftBlock (z : κ → ℂ) : (κ ⊕ (ι ⊕ ν)) → ℂ :=
   Sum.elim z (0 : (ι ⊕ ν) → ℂ)

 def complexLeftBlockCLM : (κ → ℂ) →L[ℝ] ((κ ⊕ (ι ⊕ ν)) → ℂ) :=
   ContinuousLinearMap.pi fun i => match i with
     | Sum.inl k => ContinuousLinearMap.proj k
     | Sum.inr (Sum.inl _) => 0
     | Sum.inr (Sum.inr _) => 0

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_CubicBubbleSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open scoped Topology
open Set Function MeasureTheory
open scoped Manifold
open Manifold
section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 def radialOneFormPotential (α : E → E →L[ℝ] ℝ) (x : E) : ℝ :=
  ∫ t in (0:ℝ)..1,α (t • x) x

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_LiouvilleRadialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped BigOperators
open MeasureTheory Set
open scoped Pointwise
open MomentPolytope

def largeMomentDomain (q : ℕ) (h₁ h₂ : ℝ) : Set (ℝ × (Fin q → ℝ)) :=
  {x | x.1 ∈ Icc 0 h₁ ∧ x.2 ∈ momentSimplex q (h₂*(1-x.1))}

def largeModelMean (q : ℕ) (h₁ h₂ : ℝ) : ℝ :=
  smallModelMean q h₂ * (1-(1-h₁)^(q+2))/(q+2)

end PackingSufficiencySupport

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_QuadricLargeAmbientPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators

variable {ι : Type*} [Fintype ι]

def infinitySign : Option ι → ℂ
  | none => -1
  | some _ => 1

omit [Fintype ι] in
theorem infinitySign_unit (i : Option ι) : Complex.normSq (infinitySign i)=1 := by
  cases i <;> norm_num [infinitySign]

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end


