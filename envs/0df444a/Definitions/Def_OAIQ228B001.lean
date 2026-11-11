-- Prove2me | Definitions.Def_OAIQ228B001
-- name    : OAIQ228B001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:15:20.648913+00:00
-- url     : https://prove2.me/theorems/2c9ee681-cad0-4c3a-9834-3bd8ee19fae3
-- title:
--   Definitions bundle OAIQ228B001 of the split of OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 358 declarations of OpenAI's Lean: 189 definitions, 6 inductive types or structures, 15 instances and 148 theorems. The definitions and types are `OAI.CriticalPercolation.Corridor.ScaleChoice.contour`, `OAI.CriticalPercolation.Corridor.ScaleChoice.delta`, `OAI.CriticalPercolation.Corridor.ScaleChoice.epsilon`, `OAI.CriticalPercolation.CosetGrowth.ball`, `OAI.CriticalPercolation.DiskWinding.increment`, `OAI.CriticalPercolation.EuclideanEllipse.boundaryError`, `OAI.CriticalPercolation.EuclideanEllipse.diagonal`, `OAI.CriticalPercolation.EuclideanEllipse.expand`, `OAI.CriticalPercolation.EuclideanEllipse.gridPoint`, `OAI.CriticalPercolation.EuclideanEllipse.lineAngle`, `OAI.CriticalPercolation.EuclideanEllipse.normalize`, `OAI.CriticalPercolation.EuclideanEllipse.parameterDisk`, `OAI.CriticalPercolation.FiniteClusters.coefficient`, `OAI.CriticalPercolation.FiniteCyclicConstruction`, `OAI.CriticalPercolation.FiniteEntropy.binaryDivergence`, `OAI.CriticalPercolation.FiniteEntropy.binaryRemainder`, `OAI.CriticalPercolation.FiniteEntropy.divergence`, `OAI.CriticalPercolation.FiniteEntropy.endpointKernel`, `OAI.CriticalPercolation.FiniteEntropy.fiberValue`, `OAI.CriticalPercolation.FiniteMarkov.Associated`, `OAI.CriticalPercolation.FiniteMarkov.avg`, `OAI.CriticalPercolation.FiniteMarkov.compose`, `OAI.CriticalPercolation.FiniteMarkov.remainder`, `OAI.CriticalPercolation.FiniteMarkov.step`, `OAI.CriticalPercolation.FiniteProduct.closedThin`, `OAI.CriticalPercolation.FiniteProduct.exposureLaw`, `OAI.CriticalPercolation.FiniteProduct.forceClosed`, `OAI.CriticalPercolation.FiniteProduct.freeze`, `OAI.CriticalPercolation.GraphTopology.HasCompactOpenVirtuallyNilpotentQuotient`, `OAI.CriticalPercolation.GraphTopology.HasUniformCompactApproximatePowers`, `OAI.CriticalPercolation.GraphTopology.autTopology`, `OAI.CriticalPercolation.GraphTopology.coordinates`, `OAI.CriticalPercolation.GraphTopology.displacement`, `OAI.CriticalPercolation.GraphTopology.instTopologicalSpaceIso_solutions`, `OAI.CriticalPercolation.GraphTopology.instTopologicalSpaceIso_solutions_1`, `OAI.CriticalPercolation.GraphTopology.reachBall`, `OAI.CriticalPercolation.GraphTopology.stabilizerCosetEmbedding`, `OAI.CriticalPercolation.GraphTopology.vertexStabilizer`, `OAI.CriticalPercolation.HarmonicAnalysis.RegularHilbert`, `OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry` and 155 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `CriticalPercolation_Criticality_BandScale`, `CriticalPercolation_Criticality_ClassTwoRankOne`, `CriticalPercolation_Criticality_DiskWinding`, `CriticalPercolation_Criticality_IntegerBoxes`, `CriticalPercolation_Criticality_InterpolationUniform`, `CriticalPercolation_Criticality_NormalClosureGrowth`, `CriticalPercolation_Criticality_Weight`, `CriticalPercolation_Entropy_Divergence`, `CriticalPercolation_Entropy_EndpointKernel`, `CriticalPercolation_Entropy_FiberValue`, `CriticalPercolation_Entropy_FreshSet`, `CriticalPercolation_Entropy_Uniform01`, `CriticalPercolation_Exploration_ClosedFresh`, `CriticalPercolation_Exploration_IncidenceIdentity`, `CriticalPercolation_Exploration_IncidenceSearch`, `CriticalPercolation_Exploration_Score`, `CriticalPercolation_Exploration_Select`, `CriticalPercolation_Exploration_SequentialExposure`, `CriticalPercolation_Exploration_Tagged`, `CriticalPercolation_Exploration_Visits`, `CriticalPercolation_Gluing_CorridorScaleChoice`, `CriticalPercolation_Gluing_HonestChoice`, `CriticalPercolation_Gluing_RelayGeometry`, `CriticalPercolation_GraphGeometry_EllipseAngles`, `CriticalPercolation_GraphGeometry_EllipseGrid`, `CriticalPercolation_GraphGeometry_EllipseMesh`, `CriticalPercolation_GraphGeometry_EuclideanEllipse`, `CriticalPercolation_GraphGeometry_FiniteActionAverage`, `CriticalPercolation_GraphGeometry_GraphApproximateNeighborhoods`, `CriticalPercolation_GraphGeometry_Link`, `CriticalPercolation_GraphGeometry_Link2`, `CriticalPercolation_GraphTopology_GraphAutomorphismTopology`, `CriticalPercolation_GraphTopology_GraphNeighborhoodCompact`, `CriticalPercolation_GraphTopology_LocalProjectiveTopology`, `CriticalPercolation_GraphTopology_TopologicalClassificationBoundary`, `CriticalPercolation_Growth_CosetBallIndex`, `CriticalPercolation_Growth_CosetBounded`, `CriticalPercolation_Growth_CosetGeometry`, `CriticalPercolation_Growth_CosetNormalClosure`, `CriticalPercolation_Growth_CosetSparseGrowth`, `CriticalPercolation_Growth_CosetTransfer`, `CriticalPercolation_Growth_GraphRelativeGrowth`, `CriticalPercolation_Growth_HomogeneousAverage`, `CriticalPercolation_Growth_HomogeneousGeometry`, `CriticalPercolation_Growth_HomogeneousGrowth`, `CriticalPercolation_Growth_HomogeneousPolynomialSpace`, `CriticalPercolation_Growth_PolynomialGrowthDescent`, `CriticalPercolation_Growth_WordBallPacking`, `CriticalPercolation_Growth_WordLengthGeometry`, `CriticalPercolation_Harmonic_CayleyCaccioppoli`, `CriticalPercolation_Harmonic_CayleyPoincare`, `CriticalPercolation_Harmonic_FiniteHilbert`, `CriticalPercolation_Harmonic_FunctionGramMatrix`, `CriticalPercolation_Harmonic_GeneralizedGramSpectrum`, `CriticalPercolation_Harmonic_GraphHarmonicLinear`, `CriticalPercolation_Harmonic_GraphProjectedFunctions`, `CriticalPercolation_Harmonic_GraphWalkOperator`, `CriticalPercolation_Harmonic_GraphWalkProbability`, `CriticalPercolation_Harmonic_HarmonicFunctionSpace`, `CriticalPercolation_Harmonic_HarmonicLinearQuotient`, `CriticalPercolation_Harmonic_LazyWalkHilbert`, `CriticalPercolation_Harmonic_LazyWalkProbability`, `CriticalPercolation_Harmonic_PolynomialHarmonicSpace`, `CriticalPercolation_Harmonic_ProjectedWalkFunctions`, `CriticalPercolation_LinearGroups_AbsoluteMatrixSpan`, `CriticalPercolation_LinearGroups_ConjugationMatrixGrowth`, `CriticalPercolation_LinearGroups_FgMatrixRing`, `CriticalPercolation_LinearGroups_FiniteSubspaceOrbit`, `CriticalPercolation_LinearGroups_FullSpanAlternative`, `CriticalPercolation_LinearGroups_InvariantBlockSolvability`, `CriticalPercolation_LinearGroups_LocalFurstenbergBound`, `CriticalPercolation_LinearGroups_LocalProjectiveAction`, `CriticalPercolation_LinearGroups_ProjectivePeriodicity`, `CriticalPercolation_LinearGroups_ProjectivelyPeriodicSchur`, `CriticalPercolation_Modular_CappedDiscrepancy`, `CriticalPercolation_Modular_ClusterMassInfinite`, `CriticalPercolation_Modular_InputMass`, `CriticalPercolation_Modular_OrderMass`, `CriticalPercolation_Modular_WeightedIncidenceSearch`, `CriticalPercolation_Nilpotent_CharacteristicNilpotentCore`, `CriticalPercolation_Nilpotent_FiniteCyclicConstruction`, `CriticalPercolation_Nilpotent_LowerCentralFG`, `CriticalPercolation_ProductMeasure_Associated`, `CriticalPercolation_ProductMeasure_ClosedThin`, `CriticalPercolation_ProductMeasure_CompactInvariantMeasure`, `CriticalPercolation_ProductMeasure_ExposureLaw`, `CriticalPercolation_ProductMeasure_FiniteMarkovAvg`, `CriticalPercolation_ProductMeasure_ForceClosed`, `CriticalPercolation_ProductMeasure_LayerExpectation`, `CriticalPercolation_ProductMeasure_LevelContactMeasurability`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ228B002`; the statements `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient`, `OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure`, `OAI.CriticalPercolation.LinearGrowth.virtually_solvable_real_linear_general`, `OAI.CriticalPercolation.RelativeGrowth.virtually_indicable` and `OAI.CriticalPercolation.SparseGrowth.HasPolynomialDegree.linear_virtually_indicable`; the proofs of `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.incoming_finite_ae`, `OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae`, `OAI.CriticalPercolation.BondGraph.atMostOneInfinite_ae`, `OAI.CriticalPercolation.BondGraph.critical_strip_null`, `OAI.CriticalPercolation.BondGraph.expected_discrepancyTail_bound`, `OAI.CriticalPercolation.BondGraph.expected_weighted_peakRatio`, `OAI.CriticalPercolation.BondGraph.fresh_collar_transfer`, `OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport_incoming_ae`, `OAI.CriticalPercolation.BondGraph.light_zero_or_infinitely_many_ae`, `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial`, `OAI.CriticalPercolation.BondGraph.root_corridor_miss`, `OAI.CriticalPercolation.BondGraph.source_hit_probability`, `OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn`, `OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law`, `OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks`, `OAI.CriticalPercolation.LinearGrowth.virtually_solvable_real_linear_general` and `OAI.CriticalPercolation.SparseGrowth.HasPolynomialDegree.linear_virtually_indicable`.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib

section
-- module Solutions.Q228_CP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h

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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteMarkovAvg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteMarkov
variable {X : Type*} [Fintype X]

noncomputable def avg (μ : X → ℝ) (f : X → ℝ) : ℝ := ∑ x, μ x * f x

noncomputable def step (K : X → X → ℝ) (f : X → ℝ) (x : X) : ℝ := avg (K x) f

noncomputable def remainder (K : X → X → ℝ) (a : ℝ) (z x y : X) : ℝ := by
  classical
  exact K x y - if y = z then a else 0

end CriticalPercolation.FiniteMarkov

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_BandScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation

def bandScale (L j : ℕ) : ℕ := L ^ (2 ^ j)

end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_ClassTwoRankOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G A : Type*} [Group G] [Group A]

def centralCommHom (hc : commutator G≤Subgroup.center G) (a : G) :
    G →* commutator G where
  toFun b := ⟨⁅a,b⁆,Subgroup.commutator_mem_commutator (by trivial) (by trivial)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' b d := by
    apply Subtype.ext
    change ⁅a,b*d⁆=⁅a,b⁆*⁅a,d⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hd := hc (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G))
      (H₂ := ⊤) (by trivial) (by trivial) : ⁅a,d⁆∈commutator G)
    calc
      ⁅a,b⁆*b*⁅a,d⁆*b⁻¹ = ⁅a,b⁆*(b*⁅a,d⁆)*b⁻¹ := by group
      _ = ⁅a,b⁆*(⁅a,d⁆*b)*b⁻¹ := by rw [Subgroup.mem_center_iff.mp hd b]
      _ = _ := by group

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_DiskWinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation.DiskWinding

def increment (a b : Real.Angle) : ℝ := (b-a).toReal

end CriticalPercolation.DiskWinding
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_IntegerBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

def integerPairBox (k : ℕ) : Set (Multiplicative (ℤ×ℤ)) :=
  {t | |(t.toAdd.1 : ℝ)|≤(k:ℝ) ∧ |(t.toAdd.2 : ℝ)|≤(k:ℝ)}

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_InterpolationUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation

def interpolationConstant (c ε : ℝ) : ℝ :=
  (4*(16/(2*ε*ε))+6)*(1+Real.log 8+max 0 (Real.log (1/c))) +
    (2*(16/(2*ε*ε))+5)*Real.log 4

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_PolynomialGrowthDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

def HasDegree (S : Finset A) (d : ℕ) : Prop :=
  ∃ C : ℕ, ∀ R : ℕ, ∃ n ≥ R, (S ^ n).card ≤ C * n ^ d

lemma exists_mem_pow (S : Finset A) (hsym : S⁻¹=S)
    {a : A} (ha : a ∈ Subgroup.closure (S : Set A)) : ∃ n : ℕ, a ∈ S^n := by
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact ⟨1,by simpa using hx⟩
  | one => exact ⟨0,by simp⟩
  | mul x y hx hy ix iy =>
    obtain ⟨m,hm⟩ := ix
    obtain ⟨n,hn⟩ := iy
    refine ⟨m+n,?_⟩
    rw [pow_add]
    exact Finset.mul_mem_mul hm hn
  | inv x hx ih =>
    obtain ⟨n,hn⟩ := ih
    refine ⟨n,?_⟩
    have hh : x⁻¹ ∈ (S^n)⁻¹ := Finset.inv_mem_inv hn
    simpa only [← inv_pow,hsym] using hh

def HasPolynomialDegree (A : Type*) [Group A] (d : ℕ) : Prop :=
  ∃ S : Set A, S.Finite ∧ (1 : A)∈S ∧ S⁻¹=S ∧ Subgroup.closure S=⊤ ∧
    ∃ C : ℕ, ∀ R : ℕ, ∃ n≥R, (S^n).ncard ≤ C*n^d

universe u

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_NormalClosureGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter Topology
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

def binaryProducts (g : ℕ → A) : ℕ → Finset A
  | 0 => {1}
  | n+1 => binaryProducts g n ∪ (binaryProducts g n).image (fun x => g n*x)

def boundedConjugates (S F : Finset A) (n : ℕ) : Finset A :=
  (S^n).biUnion (fun g => F.image (MulAut.conj g))

def conjugateStage (S F : Finset A) (n : ℕ) : Subgroup A :=
  Subgroup.closure (boundedConjugates S F n : Set A)

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_Weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule0

noncomputable section
open Set
open scoped BigOperators Classical

namespace CriticalPercolation.Sharpness

variable {E A : Type*} [Fintype E]

def weight (p : ℝ) (b : Prop) : ℝ := if b then p else 1 - p

def closedPivot (F : Set E → Prop) (e : E) (ω : E → Prop) : Prop :=
  ¬ω e ∧ ¬F ω ∧ F (Function.update ω e True)

def pivotal (F : Set E → Prop) (e : E) (ω : Set E) : Prop :=
  F (Function.update ω e True) ∧ ¬ F (Function.update ω e False)

end CriticalPercolation.Sharpness
end
end CurrentModule0

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_Divergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real

namespace CriticalPercolation.FiniteEntropy
variable {X : Type*} [Fintype X]

noncomputable def divergence (P R : X → ℝ) : ℝ :=
  ∑ x, P x * Real.log (P x / R x)

end CriticalPercolation.FiniteEntropy

open Set Real
open scoped Topology

namespace CriticalPercolation.FiniteEntropy

noncomputable def binaryDivergence (r p : ℝ) : ℝ :=
  r * Real.log (r / p) + (1-r) * Real.log ((1-r)/(1-p))

noncomputable def binaryRemainder (p r : ℝ) : ℝ :=
  r * Real.log r + (1-r) * Real.log (1-r) -
    r * Real.log p - (1-r)*Real.log (1-p) - 2*(r-p)^2

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_EndpointKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.FiniteEntropy

def endpointKernel (t : ℝ) : ℝ := 16 - 120*t + 240*t^2 - 140*t^3

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_FiberValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y : Type*}

noncomputable def fiberValue (f : X → Y) (g : X → ℝ) (y : Y) : ℝ :=
  if h : ∃ x, f x = y then g h.choose else 0

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_Uniform01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.Priority

variable {I : Type*} [Fintype I]

noncomputable def split (i : I) : (I → ℝ) ≃ᵐ (ℝ × ({j : I // j ≠ i} → ℝ)) where
  toEquiv := Equiv.funSplitAt i ℝ
  measurable_toFun := (measurable_pi_apply i).prodMk
    (Measurable.of_eval (fun coordinate => measurable_pi_apply coordinate.val))
  measurable_invFun := by
    apply Measurable.of_eval
    intro j
    by_cases h : j = i
    · subst j
      simpa [Equiv.funSplitAt, Equiv.piSplitAt] using measurable_fst
    · simpa [Equiv.funSplitAt, Equiv.piSplitAt, h, Function.comp_def] using
        (measurable_pi_apply (⟨j,h⟩ : {j : I // j ≠ i})).comp measurable_snd

end CriticalPercolation.Priority
open Set MeasureTheory Real
open scoped Interval

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_FreshSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.Priority
variable {I : Type*} [Fintype I]

def freshSet (i : I) (S : Finset {j : I // j ≠ i}) : Set (I → ℝ) :=
  {u | ∀ j ∈ S, u i < u j.val}

end CriticalPercolation.Priority

namespace CriticalPercolation.Priority
variable {I : Type*} [Fintype I]

noncomputable def enumeration : List I := Finset.univ.toList

abbrev Order (I : Type*) [Fintype I] := {l : List I // l.Perm (enumeration (I := I))}

noncomputable instance instFintypeOrder : Fintype (Order I) :=
  Fintype.subtype ((enumeration (I := I)).permutations.toFinset) (by
    intro l
    simp [List.mem_permutations])

lemma order_nodup (o : Order I) : o.val.Nodup := by
  exact o.property.nodup_iff.mpr (Finset.nodup_toList _)

lemma mem_order (o : Order I) (i : I) : i ∈ o.val := by
  rw [o.property.mem_iff]
  simp [enumeration]

def cell (o : Order I) : Set (I → ℝ) :=
  {u | o.val.Pairwise fun i j => u i < u j}

lemma order_split (o : Order I) (i : I) :
    ∃ pre post : List I, o.val = pre++i::post ∧ i ∉ pre ∧ i ∉ post := by
  obtain ⟨pre,post,he⟩ := List.mem_iff_append.mp (mem_order o i)
  refine ⟨pre,post,he,?_,?_⟩
  all_goals
    have hn := order_nodup o
    rw [he, List.nodup_append, List.nodup_cons] at hn
  · exact fun hi => hn.2.2 i hi i (by simp) rfl
  · exact hn.2.1.1

end CriticalPercolation.Priority

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Associated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteMarkov
open Filter
open scoped Topology

variable {X : Type*} [Fintype X] [Preorder X]

def Associated (μ : X → ℝ) : Prop :=
  ∀ f g : X → ℝ, Monotone f → Monotone g →
    avg μ f * avg μ g ≤ avg μ (fun x => f x * g x)

noncomputable def compose (K L : X → X → ℝ) (x z : X) : ℝ :=
  ∑ y, K x y * L y z

end CriticalPercolation.FiniteMarkov

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ClosedThin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

noncomputable def closedThin (w : E → Prop → ℝ) (t : ℝ) (e : E) (b : Prop) : ℝ :=
  (1-t)*w e b + if b then 0 else t

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_Link
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation
namespace Wiring
variable {V : Type*} (H : SimpleGraph V)

def link (s b u v : V) : Prop :=
  H.Reachable u v ∨ (H.Reachable u s ∧ H.Reachable b v) ∨
    (H.Reachable u b ∧ H.Reachable s v)

end Wiring
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Score
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

def Fresh (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) : Prop :=
  ∀ e ∉ read, w e False = 1-p ∧ w e True = p

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_ClosedFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

def ClosedFresh (r : E → Prop → ℝ) (p : ℝ) (C : Set E) (used : Finset E) : Prop :=
  ∀ e ∉ used, r e False = (if e ∈ C then 1 else 1-p) ∧
    r e True = (if e ∈ C then 0 else p)

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_IncidenceSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch

structure State (E : Type*) where
  opened : Finset E
  read : Finset E

variable {V E : Type*} [DecidableEq E]

 def State.closed (st : State E) (e : E) : State E := ⟨st.opened,insert e st.read⟩
 def State.open (st : State E) (e : E) : State E := ⟨insert e st.opened,insert e st.read⟩

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_IncidenceIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

 def readSum (p : ℝ) (ω : Set E) (st : State E) : ℝ :=
  ∑ e ∈ st.read, if e∈ω then 1-p else -p

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Visits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation
universe u v w

inductive MarkedTree (E : Type u) (A : Type v) : Type (max u v) where
  | stop : MarkedTree E A
  | ask (e : E) (tag : A) (left right : MarkedTree E A) : MarkedTree E A

namespace MarkedTree
variable {E : Type u} {A : Type v} {B : Type w}

def trace : MarkedTree E A → (E → Bool) → List (E × A)
  | .stop, _ => []
  | .ask e a l r, ω => (e,a) :: if ω e then r.trace ω else l.trace ω

def append : MarkedTree E A → MarkedTree E A → MarkedTree E A
  | .stop, s => s
  | .ask e a l r, s => .ask e a (l.append s) (r.append s)

def sequence : List (MarkedTree E A) → MarkedTree E A
  | [] => .stop
  | t :: ts => t.append (sequence ts)

variable [DecidableEq E]

abbrev Cache (E : Type u) := E → Option Bool

def Compatible (σ : Cache E) (ω : E → Bool) : Prop :=
  ∀ e b, σ e = some b → ω e = b

def cached : MarkedTree E A → Cache E → MarkedTree E A
  | .stop, _ => .stop
  | .ask e a l r, σ =>
    match σ e with
    | some false => l.cached σ
    | some true => r.cached σ
    | none => .ask e a
        (l.cached (Function.update σ e (some false)))
        (r.cached (Function.update σ e (some true)))

def fresh (ω : E → Bool) : Cache E → List (E × A) → List (E × A)
  | _, [] => []
  | σ, x :: xs =>
    let rest := fresh ω (Function.update σ x.1 (some (ω x.1))) xs
    if (σ x.1).isNone then x :: rest else rest

variable [Fintype E]

noncomputable def domain (σ : Cache E) : Finset E :=
  Finset.univ.filter (fun e => (σ e).isSome)

end MarkedTree
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Select
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.MarkedTree
variable {E A : Type*} [DecidableEq E] [Fintype E]

def select : Finset E → List (E × A) → List (E × A)
  | _, [] => []
  | S, x :: xs =>
      if x.1 ∈ S then select S xs else x :: select (insert x.1 S) xs

end CriticalPercolation.MarkedTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ExposureLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

noncomputable def exposureLaw (w : E → A → ℝ) (D : Set E) (σ : E → A)
    (e : E) (b : A) : ℝ := if e ∈ D then (if b = σ e then 1 else 0) else w e b

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ForceClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*}

noncomputable def forceClosed (w : E → Prop → ℝ) (C : Set E) (e : E) (b : Prop) : ℝ :=
  if e ∈ C then (if b then 0 else 1) else w e b

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_SequentialExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A B : Type*} [Fintype E] [Fintype A] [Fintype B]

noncomputable def freeze (D : Set E) (σ ω : E → A) : E → A :=
  fun e => if e ∈ D then σ e else ω e

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Tagged
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.MarkedTree

variable {E A : Type*}

def Tagged (coord : A → E) : MarkedTree E A → Prop
  | .stop => True
  | .ask e a l r => e = coord a ∧ l.Tagged coord ∧ r.Tagged coord

end CriticalPercolation.MarkedTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorScaleChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Classical

namespace CriticalPercolation.Corridor.ScaleChoice

def contour : ℝ := 1/16
def epsilon : ℝ := contour^4
def delta : ℝ := epsilon/4

end CriticalPercolation.Corridor.ScaleChoice
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_HonestChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory
open scoped Classical

namespace CriticalPercolation
variable {Ω I : Type*} [MeasurableSpace Ω]

def firstTest (P : ℕ → Ω → Prop) (ω : Ω) : ℕ :=
  if h : ∃ n, P n ω then Nat.find h else 0

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_RelayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.Relay

def selectedSign (u : ℝ) : ℝ := if 0 ≤ u then -1 else 1

end CriticalPercolation.Relay
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_LevelContactMeasurability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

def finiteSetChoice {E : Type*} (S : Set E) : Finset E :=
  if h : S.Finite then h.toFinset else ∅

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EuclideanEllipse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology

namespace CriticalPercolation.EuclideanEllipse

def diagonal (a b : ℝ) (z : ℂ) : ℂ := ⟨a*z.re,b*z.im⟩

def normalize (R W : ℝ) (c : Circle) (z : ℂ) : ℂ :=
  (c : ℂ)*diagonal (1/R) (1/W) ((c : ℂ)⁻¹*z)

def expand (R W : ℝ) (c : Circle) (z : ℂ) : ℂ :=
  (c : ℂ)*diagonal R W ((c : ℂ)⁻¹*z)

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Topology

namespace CriticalPercolation.EuclideanEllipse

def parameterDisk : Set (ℝ×ℝ) := Set.Icc (0,0) (1,Real.pi)

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseAngles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function

namespace CriticalPercolation.EuclideanEllipse

def lineAngle (c : Circle) : Real.Angle := ((2*(c : ℂ).arg : ℝ) : Real.Angle)

def boundaryError (phi : ℝ) (c : Circle) : ℝ :=
  (lineAngle c-((2*phi+Real.pi : ℝ) : Real.Angle)).toReal

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function

namespace CriticalPercolation.EuclideanEllipse

def gridPoint (N K i k : ℕ) : ℝ×ℝ := ((i : ℝ)/N,(k : ℝ)*Real.pi/K)

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FiniteActionAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
universe u v
variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

def restrictedPermutation (B : Set X) (hB : ∀ g : G, ∀ x∈B, g • x∈B) (g : G) : Equiv.Perm B where
  toFun x := ⟨g • x.val,hB g x.val x.property⟩
  invFun x := ⟨g⁻¹ • x.val,hB g⁻¹ x.val x.property⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.val)
  right_inv x := Subtype.ext (smul_inv_smul g x.val)

def restrictionHom (B : Set X) (hB : ∀ g : G, ∀ x∈B, g • x∈B) : G →* Equiv.Perm B where
  toFun := restrictedPermutation B hB
  map_one' := by ext x; exact one_smul G x.val
  map_mul' g h := by ext x; exact mul_smul g h x.val

end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_GraphAutomorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X]

variable (Γ : SimpleGraph X)

def coordinates (g : Γ ≃g Γ) : (X → X) × (X → X) := (g,g.symm)

@[instance_reducible] def autTopology : TopologicalSpace (Γ ≃g Γ) :=
  TopologicalSpace.induced (coordinates Γ) inferInstance

local instance instTopologicalSpaceIso_solutions : TopologicalSpace (Γ ≃g Γ) := autTopology Γ

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_GraphNeighborhoodCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def reachBall (o : X) (r : ℕ) : Set X :=
  {x | ∃ p : Γ.Walk o x, p.length ≤ r}

lemma reachBall_add {o x y : X} {r s : ℕ} (hx : x∈reachBall Γ o r)
    (hy : y∈reachBall Γ x s) : y∈reachBall Γ o (r+s) := by
  obtain ⟨p,hp⟩ := hx
  obtain ⟨q,hq⟩ := hy
  exact ⟨p.append q,by simpa using Nat.add_le_add hp hq⟩

lemma reachBall_finite (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) (r : ℕ) :
    (reachBall Γ o r).Finite := by
  induction r generalizing o with
  | zero =>
    apply (Set.finite_singleton o).subset
    rintro x ⟨p,hp⟩
    cases p with
    | nil => exact Set.mem_singleton o
    | cons h p => simp at hp
  | succ r ih =>
    apply ((Set.finite_singleton o).union ((hl o).biUnion fun x _ => ih x)).subset
    rintro x ⟨p,hp⟩
    cases p with
    | nil => exact Or.inl rfl
    | @cons a b c h p =>
      right
      exact Set.mem_iUnion₂.mpr ⟨b,h,p,by simpa using hp⟩

lemma iso_reachBall (g : Γ ≃g Γ) {o x : X} {r : ℕ}
    (h : x∈reachBall Γ o r) : g x∈reachBall Γ (g o) r := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.map g.toHom,by simpa using hp⟩

variable [TopologicalSpace X] [DiscreteTopology X]
local instance instTopologicalSpaceIso_solutions_1 : TopologicalSpace (Γ ≃g Γ) := autTopology Γ

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_GraphApproximateNeighborhoods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def displacement (o : X) (r : ℕ) : Set (Γ ≃g Γ) :=
  {g | g o∈reachBall Γ o r}

lemma reachBall_mono (o : X) : Monotone (reachBall Γ o) := by
  intro r s hrs x hx
  obtain ⟨p,hp⟩ := hx
  exact ⟨p,hp.trans hrs⟩

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_Link2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule1
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
namespace Wiring
variable {V : Type*} (H : SimpleGraph V)

def link (s b u v : V) : Prop :=
  H.Reachable u v ∨ (H.Reachable u s ∧ H.Reachable b v) ∨
    (H.Reachable u b ∧ H.Reachable s v)

end Wiring

end CriticalPercolation.Sharpness
end
end CurrentModule1

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_LocalProjectiveTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory Module Metric TopologicalSpace
open scoped Classical Topology

namespace CriticalPercolation.LocalProjective
variable (K V : Type*) [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

abbrev NZ := {v : V // v≠0}

instance nzMulAction : MulAction Kˣ (NZ V) where
  smul a v := ⟨(a:K) • (v:V),smul_ne_zero a.ne_zero v.property⟩
  one_smul v := Subtype.ext (one_smul K (v:V))
  mul_smul a b v := Subtype.ext (mul_smul (a:K) (b:K) (v:V))

instance nzContinuousConstSMul : ContinuousConstSMul Kˣ (NZ V) :=
  ⟨fun _ => (continuous_const.smul continuous_subtype_val).subtype_mk _⟩

abbrev Space := Quotient (MulAction.orbitRel Kˣ (NZ V))
def point (v : NZ V) : Space K V := Quotient.mk _ v

lemma point_surjective : Surjective (point K V) := Quotient.mk_surjective

variable {K V}

variable (K V)

instance spaceSecondCountable [ProperSpace K] [FiniteDimensional K V] :
    SecondCountableTopology (Space K V) := by
  let : ProperSpace V := FiniteDimensional.proper K V
  exact ContinuousConstSMul.secondCountableTopology

end CriticalPercolation.LocalProjective
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_OrderMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.Priority
open FiniteEntropy

variable {I : Type*} [Fintype I]

noncomputable def priorList (o : Order I) (i : I) : List I := (order_split o i).choose
noncomputable def suffix (o : Order I) (i : I) : List I := (order_split o i).choose_spec.choose

def First (o : Order I) (i : I) (S : Finset {j : I // j ≠ i}) : Prop :=
  ∀ j ∈ S, j.val ∉ priorList o i

end CriticalPercolation.Priority

open scoped Classical

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_InputMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.QueryTree
open FiniteEntropy

variable {E : Type*} [Fintype E]

noncomputable def bitValue (ω : E → Bool) (e : E) : ℝ := if ω e then 1 else 0

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_CappedDiscrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

def cappedMass (s m : ℕ) : ℝ := min ((m:ℝ)/s) 1

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterMassInfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*}

def coefficient (p : ℝ) (ω : Set E) (e : E) : ℝ := if e ∈ ω then -(1-p)/p else 1

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedIncidenceSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

def weightedRead (a : E → ℝ) (p : ℝ) (ω : Set E) (st : State E) : ℝ :=
  ∑ e∈st.read, if e∈ω then a e*(1-p) else -a e*p

def quadraticRead (a : E → ℝ) (st : State E) : ℝ := ∑ e∈st.read, (a e)^2

end CriticalPercolation.IncidenceSearch
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_LayerExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation

def vertexCount {V : Type*} (S : Set V) : ℝ≥0∞ := ∑' x : V, if x∈S then 1 else 0

end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_FiniteCyclicConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

section
section
noncomputable section
open Set Function
open scoped Classical DirectSum

namespace CriticalPercolation

inductive FiniteCyclicConstruction : (G : Type u) → [Group G] → ℕ → Prop
  | finite (G : Type u) [Group G] [Finite G] : FiniteCyclicConstruction G 0
  | cyclic (G : Type u) [Group G] (e : G ≃* Multiplicative ℤ) :
      FiniteCyclicConstruction G 1
  | extension {G Q : Type u} [Group G] [Group Q] (f : G →* Q)
      (hf : Surjective f) {n m : ℕ}
      (hker : FiniteCyclicConstruction f.ker n)
      (hquot : FiniteCyclicConstruction Q m) : FiniteCyclicConstruction G (n+m)

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_LowerCentralFG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable (G : Type*) [Group G]

def lowerFactor (n : ℕ) : Subgroup (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (n+1)) :=
  ((⊤ : Subgroup G).lowerCentralSeries n).map
    (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1)))

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_TopologicalClassificationBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function MeasureTheory Topology
open scoped Classical ENNReal Pointwise

namespace CriticalPercolation
namespace GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def HasCompactOpenVirtuallyNilpotentQuotient : Prop :=
  let _ : TopologicalSpace X := ⊥
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  ∃ H : Subgroup (Γ ≃g Γ), ∃ hn : H.Normal,
    let _ := hn
    IsCompact (H : Set (Γ ≃g Γ)) ∧ IsOpen (H : Set (Γ ≃g Γ)) ∧
      ∃ N : Subgroup ((Γ ≃g Γ) ⧸ H), Group.IsNilpotent N ∧ N.index≠0

def HasUniformCompactApproximatePowers (K : ℝ) : Prop :=
  let _ : TopologicalSpace X := ⊥
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  ∃ S : Set (Γ ≃g Γ), IsCompact S ∧ IsOpen S ∧ (1 : Γ ≃g Γ)∈S ∧
    S⁻¹=S ∧ Subgroup.closure S=⊤ ∧
    ∀ R : ℕ, ∃ n≥R, IsCompact (S^n) ∧ IsOpen (S^n) ∧
      IsApproximateSubgroup K (S^n)

end GraphTopology
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetBallIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Pointwise

namespace CriticalPercolation.CosetGrowth
variable {A : Type*} [Group A]

def ball (S : Set A) (L : Subgroup A) (n : ℕ) : Set (A ⧸ L) :=
  (QuotientGroup.mk : A → A ⧸ L) '' (S^n)

end CriticalPercolation.CosetGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetSparseGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter Topology
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

def ball (K : Subgroup A) (S : Set A) (n : ℕ) : Set (A ⧸ K) :=
  (QuotientGroup.mk : A → A ⧸ K) '' S^n

def HasDegree (K : Subgroup A) (S : Set A) (d : ℕ) : Prop :=
  (∀ n, (ball K S n).Finite) ∧ ∃ C : ℕ, ∀ R : ℕ, ∃ n≥R, (ball K S n).ncard≤C*n^d

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

def Bounded (S T : Set A) : Prop := ∃ n : ℕ, T⊆S^n

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
structure Geometry (X : Type*) where
  graph : SimpleGraph X
  connected : graph.Connected
  locallyFinite : ∀ x, (graph.neighborSet x).Finite
  transitive : ∀ x y, ∃ g : graph ≃g graph, g x=y
  root : X

namespace Geometry
variable {X : Type*} (W : Geometry X)
abbrev Aut := W.graph ≃g W.graph

def around (x : X) (r : ℕ) : Finset X := (GraphTopology.reachBall_finite W.graph W.locallyFinite x r).toFinset
abbrev ball (r : ℕ) := W.around W.root r

@[simp] lemma mem_around {x y : X} {r : ℕ} :
    y∈W.around x r ↔ y∈GraphTopology.reachBall W.graph x r := (GraphTopology.reachBall_finite W.graph W.locallyFinite x r).mem_toFinset

lemma around_mono (x : X) : Monotone (W.around x) := by
  intro r s h y hy
  exact W.mem_around.mpr (GraphTopology.reachBall_mono W.graph x h (W.mem_around.mp hy))
lemma ball_mono : Monotone W.ball := W.around_mono W.root

lemma mem_around_add {x y z : X} {r s : ℕ} (hy : y∈W.around x r) (hz : z∈W.around y s) :
    z∈W.around x (r+s) :=
  W.mem_around.mpr (GraphTopology.reachBall_add W.graph (W.mem_around.mp hy) (W.mem_around.mp hz))

lemma aut_around_image (g : W.Aut) (x : X) (r : ℕ) :
    (W.around x r).image g=W.around (g x) r := by
  ext y
  constructor
  · intro hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    exact W.mem_around.mpr (GraphTopology.iso_reachBall W.graph g (W.mem_around.mp hz))
  · intro hy
    refine Finset.mem_image.mpr ⟨g.symm y,?_,g.apply_symm_apply y⟩
    apply W.mem_around.mpr
    simpa using GraphTopology.iso_reachBall W.graph g.symm (W.mem_around.mp hy)

def length (x : X) : ℕ := W.graph.dist W.root x
lemma mem_ball_length (x : X) : x∈W.ball (W.length x) := by
  obtain ⟨p,_,hp⟩ := W.connected.exists_path_of_dist W.root x
  exact W.mem_around.mpr ⟨p,hp.le⟩
lemma length_le_iff {x : X} {n : ℕ} : W.length x≤n ↔ x∈W.ball n := by
  constructor
  · intro h; exact W.ball_mono h (W.mem_ball_length x)
  · intro h
    obtain ⟨p,hp⟩ := W.mem_around.mp h
    exact (SimpleGraph.dist_le p).trans hp

lemma aut_length_le (g : W.Aut) (x : X) : W.length (g x)≤W.length (g W.root)+W.length x := by
  apply W.length_le_iff.mpr
  apply W.mem_around_add (W.mem_ball_length (g W.root))
  rw [←W.aut_around_image]
  exact Finset.mem_image.mpr ⟨x,W.mem_ball_length x,rfl⟩

def neighbors (x : X) : Finset X := (W.locallyFinite x).toFinset
@[simp] lemma mem_neighbors {x y : X} : y∈W.neighbors x ↔ W.graph.Adj x y := (W.locallyFinite x).mem_toFinset
lemma neighbors_image (g : W.Aut) (x : X) : (W.neighbors x).image g=W.neighbors (g x) := by
  ext y
  simp only [Finset.mem_image,W.mem_neighbors]
  constructor
  · rintro ⟨z,hz,rfl⟩; exact g.map_adj_iff.mpr hz
  · intro h; exact ⟨g.symm y,by simpa using g.symm.map_adj_iff.mpr h,g.apply_symm_apply y⟩
abbrev degree := (W.neighbors W.root).card

def energy (F : Finset X) (u : X → ℝ) := ∑ x∈F, ∑ y∈W.neighbors x, (u y-u x)^2

def IsHarmonic (u : X → ℝ) : Prop := ∀ x, (∑ y∈W.neighbors x, (u x-u y))=0

def cutoff (R : ℕ) (x : X) : ℝ := max 0 (2*(R:ℝ)-(W.length x:ℝ))

end Geometry
end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry

variable {X : Type*} (W : Geometry X)

abbrev Stab := MulAction.stabilizer W.Aut W.root

def frame (x : X) : W.Aut := (W.transitive W.root x).choose
lemma action_transitive : ∀ x y : X, ∃ g : W.Aut, g • x=y := W.transitive

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry

variable {X : Type*} (W : Geometry X)

def HasDegree (d : ℕ) : Prop := ∃ C : ℕ, ∀ R : ℕ, ∃ n≥R, (W.ball n).card≤C*n^d

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

structure Presentation (A : Type*) [Group A] where
  K : Subgroup A
  S : Set A
  one_mem : (1:A)∈S
  inv_eq : S⁻¹=S
  generates : Subgroup.closure S=⊤
  left_stable : (K:Set A)*S⊆S

namespace Presentation
variable (P : Presentation A)
abbrev X := A ⧸ P.K
abbrev projection (a : A) : P.X := QuotientGroup.mk a
abbrev root : P.X := P.projection 1

def graph : SimpleGraph P.X where
  Adj x y := x≠y ∧ ∃ g : A, ∃ s∈P.S, P.projection g=x ∧ P.projection (g*s)=y
  symm := ⟨by
    rintro x y ⟨hne,g,s,hs,rfl,rfl⟩
    refine ⟨hne.symm,g*s,s⁻¹,?_,rfl,?_⟩
    · rw [←P.inv_eq]; exact Set.inv_mem_inv.mpr hs
    · simp⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

lemma adj_mk_iff (g : A) (y : P.X) :
    P.graph.Adj (P.projection g) y ↔ P.projection g≠y ∧ ∃ s∈P.S, P.projection (g*s)=y := by
  constructor
  · rintro ⟨hne,h,s,hs,hh,he⟩
    have hk : g⁻¹*h∈P.K := QuotientGroup.eq.mp hh.symm
    refine ⟨hne,(g⁻¹*h)*s,P.left_stable (Set.mul_mem_mul hk hs),?_⟩
    simpa only [mul_assoc,mul_inv_cancel_left] using he
  · rintro ⟨hne,s,hs,he⟩; exact ⟨hne,g,s,hs,rfl,he⟩

lemma smul_adj_iff (a : A) (x y : P.X) :
    P.graph.Adj (a • x) (a • y) ↔ P.graph.Adj x y := by
  have hf (b : A) {x y : P.X} (h : P.graph.Adj x y) :
      P.graph.Adj (b • x) (b • y) := by
    obtain ⟨hne,g,s,hs,rfl,rfl⟩ := h
    refine ⟨fun he => hne (smul_left_cancel b he),b*g,s,hs,rfl,?_⟩
    change P.projection ((b*g)*s)=P.projection (b*(g*s))
    rw [mul_assoc]
  constructor
  · intro h; simpa using hf a⁻¹ h
  · exact hf a

def actionAut (a : A) : P.graph ≃g P.graph where
  toEquiv := MulAction.toPerm a
  map_rel_iff' := P.smul_adj_iff a _ _
def actionHom : A →* (P.graph ≃g P.graph) where
  toFun := P.actionAut
  map_one' := by ext x; exact one_smul A x
  map_mul' a b := by ext x; exact mul_smul a b x
@[simp] lemma actionAut_mk (a b : A) : P.actionAut a (P.projection b)=P.projection (a*b) := rfl

lemma reachable_mk (a : A) : P.graph.Reachable P.root (P.projection a) := by
  have ha : a∈Subgroup.closure P.S := P.generates.symm ▸ Subgroup.mem_top a
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    by_cases he : P.root=P.projection a
    · rw [←he]
    · apply SimpleGraph.Adj.reachable
      exact ⟨he,1,a,ha,rfl,by simp⟩
  | one => exact .refl _
  | mul a b _ _ ha hb =>
    have hh := hb.map (P.actionAut a).toHom
    change P.graph.Reachable (P.projection (a*1)) (P.projection (a*b)) at hh
    simp only [mul_one] at hh
    exact ha.trans hh
  | inv a _ ha =>
    have hh := ha.symm.map (P.actionAut a⁻¹).toHom
    change P.graph.Reachable (P.projection (a⁻¹*a)) (P.projection (a⁻¹*1)) at hh
    simpa using hh
lemma connected : P.graph.Connected := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
        exact (P.reachable_mk a).symm.trans (P.reachable_mk b)

lemma neighbors_subset (a : A) : P.graph.neighborSet (P.projection a)⊆
    (fun x : P.X => a • x) '' ball P.K P.S 1 := by
  intro y hy
  obtain ⟨hne,s,hs,rfl⟩ := (P.adj_mk_iff a y).mp hy
  exact ⟨P.projection s,⟨s,by simpa using hs,rfl⟩,rfl⟩
lemma locallyFinite (hf : (ball P.K P.S 1).Finite) : ∀ x, (P.graph.neighborSet x).Finite := by
  intro x
  induction x using Quotient.inductionOn with | _ a =>
    exact (hf.image (fun x : P.X => a • x)).subset (P.neighbors_subset a)
lemma transitive (x y : P.X) : ∃ g : P.graph ≃g P.graph, g x=y := by
  induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
      exact ⟨P.actionAut (b*a⁻¹),by simp⟩
def geometry (hf : (ball P.K P.S 1).Finite) : HomogeneousAnalysis.Geometry P.X :=
  ⟨P.graph,P.connected,P.locallyFinite hf,P.transitive,P.root⟩

end Presentation
end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetNormalClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

def boundedConjugates (S F : Set A) (n : ℕ) : Set A :=
  {x | ∃ g∈S^n, ∃ f∈F, g*f*g⁻¹=x}

def conjugateStage (S F : Set A) (n : ℕ) : Subgroup A :=
  Subgroup.closure (boundedConjugates S F n : Set A)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

def subgroupCosetEmbedding (K H : Subgroup A) : H ⧸ K.subgroupOf H ↪ A ⧸ K where
  toFun := Quotient.map' Subtype.val (by
    intro a b h
    simpa only [QuotientGroup.leftRel_apply,Subgroup.mem_subgroupOf,Subgroup.coe_mul,Subgroup.coe_inv] using h)
  inj' := Quotient.ind₂' (by
    intro a b h
    change (QuotientGroup.mk a.val : A ⧸ K)=QuotientGroup.mk b.val at h
    apply QuotientGroup.eq.mpr
    change a.val⁻¹*b.val∈K
    exact QuotientGroup.eq.mp h)
@[simp] lemma subgroupCosetEmbedding_mk (K H : Subgroup A) (h : H) :
    subgroupCosetEmbedding K H (QuotientGroup.mk h)=QuotientGroup.mk h.val := rfl

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_GraphRelativeGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def vertexStabilizer (o : X) : Subgroup (Γ ≃g Γ) where
  carrier := {g | g o=o}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a (b o)=o; rw [hb,ha]
  inv_mem' := by
    intro a ha
    change a.symm o=o
    calc
      a.symm o = a.symm (a o) := congrArg a.symm ha.symm
      _ = o := a.symm_apply_apply o

@[simp] lemma mem_vertexStabilizer (o : X) (a : Γ ≃g Γ) : a∈vertexStabilizer Γ o ↔ a o=o := Iff.rfl

def stabilizerCosetEmbedding (o : X) : ((Γ ≃g Γ) ⧸ vertexStabilizer Γ o) ↪ X where
  toFun := Quotient.lift (s:=QuotientGroup.leftRel (vertexStabilizer Γ o)) (fun g : Γ ≃g Γ => g o) (by
    intro a b hab
    have hab' : a⁻¹*b ∈ vertexStabilizer Γ o := (QuotientGroup.leftRel_apply).mp hab
    change a.symm (b o)=o at hab'
    have hh := congrArg a hab'
    simpa using hh.symm)
  inj' := Quotient.ind₂' (by
    intro a b h
    apply QuotientGroup.eq.mpr
    change a.symm (b o)=o
    change a o=b o at h
    rw [←h]
    exact a.symm_apply_apply o)
@[simp] lemma stabilizerCosetEmbedding_mk (o : X) (g : Γ ≃g Γ) :
    stabilizerCosetEmbedding Γ o (QuotientGroup.mk g)=g o := rfl

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousPolynomialSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
variable {A : Type*} (W : Geometry A)

def harmonicSpace : Submodule ℝ (A → ℝ) where
  carrier := {u | W.IsHarmonic u}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro u v hu hv x
    change (∑ s∈W.neighbors x, ((u x+v x)-(u s+v s)))=0
    simp_rw [show ∀ s:A, (u x+v x)-(u s+v s)=(u x-u s)+(v x-v s) by intro s; ring]
    rw [Finset.sum_add_distrib,hu x,hv x,add_zero]
  smul_mem' := by
    intro c u hu x
    change (∑ s∈W.neighbors x, (c*u x-c*u s))=0
    simp_rw [←mul_sub]
    rw [←Finset.mul_sum,hu x,mul_zero]

def HasPolynomialGrowth (k : ℕ) (u : A → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ x∈W.ball n, |u x| ≤ C*((n:ℝ)+1)^k

def polynomialGrowthSpace (k : ℕ) : Submodule ℝ (A → ℝ) where
  carrier := {u | W.HasPolynomialGrowth k u}
  zero_mem' := ⟨0,le_rfl,by simp⟩
  add_mem' := by
    rintro u v ⟨C,hC,hu⟩ ⟨D,hD,hv⟩
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro n x hx
    change |u x+v x| ≤ _
    calc
      _ ≤ |u x|+|v x| := abs_add_le _ _
      _ ≤ C*((n:ℝ)+1)^k+D*((n:ℝ)+1)^k := add_le_add (hu n x hx) (hv n x hx)
      _ = _ := by ring
  smul_mem' := by
    rintro c u ⟨C,hC,hu⟩
    refine ⟨|c| * C,mul_nonneg (abs_nonneg _) hC,?_⟩
    intro n x hx
    change |c*u x| ≤ _
    rw [abs_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (hu n x hx) (abs_nonneg _)

def polynomialHarmonicSpace (k : ℕ) : Submodule ℝ (A → ℝ) :=
  W.harmonicSpace ⊓ W.polynomialGrowthSpace k

lemma polynomial_growth_iff_length (k : ℕ) (u : A → ℝ) :
    W.HasPolynomialGrowth k u ↔ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, |u x| ≤ C*((W.length x:ℝ)+1)^k := by
  constructor
  · rintro ⟨C,hC,hu⟩
    exact ⟨C,hC,fun x => hu _ _ (W.mem_ball_length x)⟩
  · rintro ⟨C,hC,hu⟩
    refine ⟨C,hC,?_⟩
    intro n x hx
    apply (hu x).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right (W.length_le_iff.mpr hx) 1

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_WordLengthGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]

structure WordGeometry (A : Type*) [Group A] where
  generators : Finset A
  one_mem : (1:A)∈generators
  inv_eq : generators⁻¹=generators
  generates : Subgroup.closure (generators:Set A)=⊤

namespace WordGeometry
variable (W : WordGeometry A)
abbrev ball (n : ℕ) := W.generators^n

lemma exists_mem_ball (a : A) : ∃ n, a∈W.ball n :=
  SparseGrowth.exists_mem_pow W.generators W.inv_eq (by rw [W.generates]; trivial)

def length (a : A) : ℕ := Nat.find (W.exists_mem_ball a)

lemma mem_ball_length (a : A) : a∈W.ball (W.length a) := Nat.find_spec (W.exists_mem_ball a)

lemma length_le_iff {a : A} {n : ℕ} : W.length a≤n ↔ a∈W.ball n := by
  constructor
  · intro h
    exact Finset.pow_subset_pow_right W.one_mem h (W.mem_ball_length a)
  · intro h; exact Nat.find_min' (W.exists_mem_ball a) h

lemma length_mul_le (a b : A) : W.length (a*b)≤W.length a+W.length b := by
  apply W.length_le_iff.mpr
  rw [ball,pow_add]
  exact Finset.mem_mul.mpr ⟨a,W.mem_ball_length a,b,W.mem_ball_length b,rfl⟩

lemma length_inv (a : A) : W.length a⁻¹=W.length a := by
  have hl (b : A) : W.length b⁻¹≤W.length b := by
    apply W.length_le_iff.mpr
    have hh := Finset.inv_mem_inv (W.mem_ball_length b)
    simpa [ball,←inv_pow,W.inv_eq] using hh
  exact le_antisymm (hl a) (by simpa using hl a⁻¹)

def cutoff (R : ℕ) (a : A) : ℝ := max 0 (2*(R:ℝ)-(W.length a:ℝ))

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_WordBallPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

def around (a : A) (r : ℕ) : Finset A := (W.ball r).image (fun x => a*x)

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_CayleyPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A] [DecidableEq A]

def energy (S F : Finset A) (u : A → ℝ) : ℝ :=
  ∑ x∈F, ∑ s∈S, (u (x*s)-u x)^2

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_HarmonicFunctionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {X : Type*}

def vanishingSubspace (D : Submodule ℝ (X → ℝ)) (F : Set X) : Submodule ℝ D where
  carrier := {u | ∀ x∈F, (u:X → ℝ) x=0}
  zero_mem' := by intro x hx; rfl
  add_mem' := by intro u v hu hv x hx; change u.val x+v.val x=0; rw [hu x hx,hv x hx,add_zero]
  smul_mem' := by intro a u hu x hx; change a*u.val x=0; rw [hu x hx,mul_zero]

def squareMass (F : Finset X) (u : X → ℝ) : ℝ := ∑ x∈F, (u x)^2

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_CayleyCaccioppoli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]

namespace WordGeometry
variable (W : WordGeometry A)

def IsHarmonic (u : A → ℝ) : Prop := ∀ x, (∑ s∈W.generators, (u x-u (x*s)))=0

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_LazyWalkHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]
abbrev RegularHilbert (A : Type*) := lp (fun _ : A => ℝ) 2

lemma translate_mem (a : A) (f : RegularHilbert A) :
    Memℓp (fun x => f (a*x)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)).mpr
  have hf : Summable (fun x : A => ‖f x‖ ^ (2:ENNReal).toReal) :=
    (lp.memℓp f).summable (by norm_num)
  exact (Equiv.mulLeft a).summable_iff.mpr hf

def translateVector (a : A) (f : RegularHilbert A) : RegularHilbert A :=
  ⟨fun x => f (a*x), translate_mem a f⟩

def regularLinearEquiv (a : A) : RegularHilbert A ≃ₗ[ℝ] RegularHilbert A where
  toFun := translateVector a⁻¹
  invFun := translateVector a
  left_inv f := by
    apply Subtype.ext
    funext x
    change f (a⁻¹*(a*x))=f x
    rw [inv_mul_cancel_left]
  right_inv f := by
    apply Subtype.ext
    funext x
    change f (a*(a⁻¹*x))=f x
    rw [mul_inv_cancel_left]
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' c f := by apply Subtype.ext; rfl

def regular (a : A) : RegularHilbert A ≃ₗᵢ[ℝ] RegularHilbert A :=
  (regularLinearEquiv a).isometryOfInner (by
    intro f g
    change (∑' x, inner ℝ (f (a⁻¹*x)) (g (a⁻¹*x))) = ∑' x, inner ℝ (f x) (g x)
    exact (Equiv.mulLeft a⁻¹).tsum_eq (fun x : A => inner ℝ (f x) (g x)))

@[simp] lemma regular_apply (a : A) (f : RegularHilbert A) (x : A) :
    regular a f x=f (a⁻¹*x) := rfl
@[simp] lemma regular_one (f : RegularHilbert A) : regular 1 f=f := by ext x; simp
@[simp] lemma regular_mul (a b : A) (f : RegularHilbert A) :
    regular (a*b) f=regular a (regular b f) := by ext x; simp [mul_assoc]

namespace WordGeometry
variable (W : WordGeometry A)
def walkAverage : RegularHilbert A →ₗ[ℝ] RegularHilbert A :=
  (W.generators.card:ℝ)⁻¹ • ∑ s∈W.generators, (regular s).toLinearEquiv.toLinearMap

def lazyWalk : RegularHilbert A →ₗ[ℝ] RegularHilbert A :=
  (1/2:ℝ) • (LinearMap.id+W.walkAverage)

def walkEnergy (f : RegularHilbert A) : ℝ := inner ℝ f (f-W.lazyWalk f)

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_FiniteHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
open HarmonicAnalysis

variable {X : Type*}

def finiteHilbert : Submodule ℝ (RegularHilbert X) where
  carrier := {f | (Function.support (fun x => f x)).Finite}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    apply (hf.union hg).subset
    intro x hx
    by_contra hn
    have hx' : f x+g x≠0 := hx
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hx' (by rw [hn.1,hn.2]; ring)
  smul_mem' := by
    intro c f hf
    apply hf.subset
    intro x hx
    by_contra hn
    have hx' : c*f x≠0 := hx
    simp only [Function.mem_support,not_not] at hn
    exact hx' (by rw [hn,mul_zero])

abbrev FH (X : Type*) := ↥(finiteHilbert (X:=X))
namespace FH
instance instCoeFunForallReal : CoeFun (FH X) (fun _ => X → ℝ) := ⟨fun f => (f.val : X → ℝ)⟩
@[ext] lemma ext {f g : FH X} (h : ∀ x, f x=g x) : f=g :=
  Subtype.ext (by ext x; exact h x)

@[simp] lemma zero_apply (x : X) : (0 : FH X) x=0 := rfl
@[simp] lemma add_apply (f g : FH X) (x : X) : (f+g) x=f x+g x := rfl
@[simp] lemma sub_apply (f g : FH X) (x : X) : (f-g) x=f x-g x := rfl
@[simp] lemma smul_apply (c : ℝ) (f : FH X) (x : X) : (c • f) x=c*f x := rfl

def support (f : FH X) : Finset X := f.property.toFinset
@[simp] lemma mem_support (f : FH X) (x : X) : x∈f.support ↔ f x≠0 :=
  f.property.mem_toFinset

def ofFunction (f : X → ℝ) (hf : (Function.support f).Finite) : FH X :=
  ⟨⟨f,(memℓp_zero_iff.mpr hf).of_exponent_ge (by norm_num)⟩,hf⟩
@[simp] lemma ofFunction_apply (f : X → ℝ) (hf : (Function.support f).Finite) (x : X) :
    ofFunction f hf x=f x := rfl

def delta (x : X) : FH X :=
  ofFunction (Pi.single x 1) ((Set.finite_singleton x).subset (by
    intro y hy
    by_contra hn
    simp only [Set.mem_singleton_iff] at hn
    exact hy (by simp [hn])))
@[simp] lemma delta_apply (x y : X) : delta x y=if y=x then 1 else 0 := by
  simp [delta,Pi.single_apply,eq_comm]

def transportLinear (g : Equiv.Perm X) : FH X ≃ₗ[ℝ] FH X where
  toFun f := ofFunction (fun x => f (g.symm x)) (by
    have he : Function.support (fun x => f (g.symm x))=g '' Function.support (fun x => f x) := by
      ext x; simp [Function.mem_support]
    rw [he]; exact f.property.image g)
  invFun f := ofFunction (fun x => f (g x)) (by
    have he : Function.support (fun x => f (g x))=g.symm '' Function.support (fun x => f x) := by
      ext x; simp [Function.mem_support]
    rw [he]; exact f.property.image g.symm)
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f h := by ext x; rfl
  map_smul' c f := by ext x; rfl

def transport (g : Equiv.Perm X) : FH X ≃ₗᵢ[ℝ] FH X :=
  (transportLinear g).isometryOfInner (by
    intro f h
    change (∑' x, inner ℝ (f (g.symm x)) (h (g.symm x)))=∑' x, inner ℝ (f x) (h x)
    exact g.symm.tsum_eq (fun x => inner ℝ (f x) (h x)))
@[simp] lemma transport_apply (g : Equiv.Perm X) (f : FH X) (x : X) :
    transport g f x=f (g.symm x) := rfl
@[simp] lemma transport_one (f : FH X) : transport 1 f=f := by ext x; rfl
@[simp] lemma transport_mul (a b : Equiv.Perm X) (f : FH X) :
    transport (a*b) f=transport a (transport b f) := by ext x; rfl
@[simp] lemma transport_delta (g : Equiv.Perm X) (x : X) :
    transport g (delta x)=delta (g x) := by
  ext y
  simp only [transport_apply,delta_apply]
  congr 1
  exact propext g.symm_apply_eq

lemma summable (f : FH X) : Summable (fun x => f x) := summable_of_hasFiniteSupport f.property

def mass : FH X →ₗ[ℝ] ℝ where
  toFun f := ∑' x, f x
  map_add' f g := by simp only [add_apply]; exact Summable.tsum_add f.summable g.summable
  map_smul' c f := by simp only [smul_apply,RingHom.id_apply,smul_eq_mul,tsum_mul_left]
@[simp] lemma mass_delta (x : X) : mass (delta x)=1 := by
  change (∑' y, delta x y)=1
  simp only [delta_apply]
  exact tsum_ite_eq _ _

end FH
end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GeneralizedGramSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix InnerProductSpace

namespace CriticalPercolation.HarmonicAnalysis
variable {ι : Type*} [Fintype ι]

def matrixQuadratic (M : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ M *ᵥ v

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_FunctionGramMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix

namespace CriticalPercolation.HarmonicAnalysis
variable {ι X : Type*} [Fintype ι]

def functionGram (F : Finset X) (v : ι → X → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ x∈F, v i x*v j x

def functionCombination (v : ι → X → ℝ) (a : ι → ℝ) : X → ℝ :=
  fun x => ∑ i, a i*v i x

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_PolynomialHarmonicSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

def harmonicSpace : Submodule ℝ (A → ℝ) where
  carrier := {u | W.IsHarmonic u}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro u v hu hv x
    change (∑ s∈W.generators, ((u x+v x)-(u (x*s)+v (x*s))))=0
    simp_rw [show ∀ s:A, (u x+v x)-(u (x*s)+v (x*s))=(u x-u (x*s))+(v x-v (x*s)) by intro s; ring]
    rw [Finset.sum_add_distrib,hu x,hv x,add_zero]
  smul_mem' := by
    intro c u hu x
    change (∑ s∈W.generators, (c*u x-c*u (x*s)))=0
    simp_rw [←mul_sub]
    rw [←Finset.mul_sum,hu x,mul_zero]

def HasPolynomialGrowth (k : ℕ) (u : A → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ x∈W.ball n, |u x| ≤ C*((n:ℝ)+1)^k

def polynomialGrowthSpace (k : ℕ) : Submodule ℝ (A → ℝ) where
  carrier := {u | W.HasPolynomialGrowth k u}
  zero_mem' := ⟨0,le_rfl,by simp⟩
  add_mem' := by
    rintro u v ⟨C,hC,hu⟩ ⟨D,hD,hv⟩
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro n x hx
    change |u x+v x| ≤ _
    calc
      _ ≤ |u x|+|v x| := abs_add_le _ _
      _ ≤ C*((n:ℝ)+1)^k+D*((n:ℝ)+1)^k := add_le_add (hu n x hx) (hv n x hx)
      _ = _ := by ring
  smul_mem' := by
    rintro c u ⟨C,hC,hu⟩
    refine ⟨|c| * C,mul_nonneg (abs_nonneg _) hC,?_⟩
    intro n x hx
    change |c*u x| ≤ _
    rw [abs_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (hu n x hx) (abs_nonneg _)

def polynomialHarmonicSpace (k : ℕ) : Submodule ℝ (A → ℝ) :=
  W.harmonicSpace ⊓ W.polynomialGrowthSpace k

lemma polynomial_growth_iff_length (k : ℕ) (u : A → ℝ) :
    W.HasPolynomialGrowth k u ↔ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, |u x| ≤ C*((W.length x:ℝ)+1)^k := by
  constructor
  · rintro ⟨C,hC,hu⟩
    exact ⟨C,hC,fun x => hu _ _ (W.mem_ball_length x)⟩
  · rintro ⟨C,hC,hu⟩
    refine ⟨C,hC,?_⟩
    intro n x hx
    apply (hu x).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right (W.length_le_iff.mpr hx) 1

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GraphWalkOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma inverse_neighbor_sum (f : FH X) :
    (Function.support (fun y => (W.degree:ℝ)⁻¹*∑ z∈W.neighbors y, f z)).Finite := by
  apply (f.support.biUnion W.neighbors).finite_toSet.subset
  intro y hy
  have hz : (∑ z∈W.neighbors y, f z)≠0 := by
    intro h; apply hy; change (W.degree:ℝ)⁻¹*(∑ z∈W.neighbors y, f z)=0; rw [h,mul_zero]
  obtain ⟨z,hz,hfz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  exact Finset.mem_biUnion.mpr ⟨z,(f.mem_support z).mpr hfz,
    W.mem_neighbors.mpr (W.mem_neighbors.mp hz).symm⟩

def averaging : FH X →ₗ[ℝ] FH X where
  toFun f := FH.ofFunction (fun x => (W.degree:ℝ)⁻¹*∑ y∈W.neighbors x, f y)
    (W.inverse_neighbor_sum f)
  map_add' f g := by
    ext x
    simp only [FH.ofFunction_apply,FH.add_apply,Finset.sum_add_distrib,mul_add]
  map_smul' c f := by
    ext x
    simp only [FH.ofFunction_apply,FH.smul_apply,←Finset.mul_sum,RingHom.id_apply]
    ring

def lazyWalk : FH X →ₗ[ℝ] FH X := (1/2:ℝ) • (LinearMap.id+W.averaging)
def walkEnergy (f : FH X) : ℝ := inner ℝ f (f-W.lazyWalk f)

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GraphWalkProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

def walkFeature (n : ℕ) (x : X) : FH X := (W.lazyWalk^n) (FH.delta x)
abbrev walkState (n : ℕ) := W.walkFeature n W.root
@[simp] lemma walkFeature_zero (x : X) : W.walkFeature 0 x=FH.delta x := rfl

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GraphProjectedFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

def projectedFunction (n : ℕ) (t x : X) : ℝ :=
  inner ℝ (W.walkFeature n x-W.walkState n) (W.walkFeature n t-W.walkState n) /
    (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n))
end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_GraphHarmonicLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

def translateFunction (a : W.Aut) (u : X → ℝ) : X → ℝ := fun x => u (a.symm x)
lemma translate_harmonic (a : W.Aut) {u : X → ℝ} (hu : W.IsHarmonic u) :
    W.IsHarmonic (W.translateFunction a u) := by
  intro x
  have h := hu (a.symm x)
  rw [←W.neighbors_image a.symm x,Finset.sum_image] at h
  · exact h
  · exact fun b hb c hc he => a.symm.injective he
lemma translate_polynomial_growth (a : W.Aut) (k : ℕ) {u : X → ℝ}
    (hu : W.HasPolynomialGrowth k u) : W.HasPolynomialGrowth k (W.translateFunction a u) := by
  obtain ⟨C,hC,hu⟩ := (W.polynomial_growth_iff_length k u).mp hu
  apply (W.polynomial_growth_iff_length k _).mpr
  refine ⟨C*((W.length (a.symm W.root):ℝ)+1)^k,by positivity,?_⟩
  intro x
  have hl := W.aut_length_le a.symm x
  have hl' : (W.length (a.symm x):ℝ)≤(W.length (a.symm W.root):ℝ)+(W.length x:ℝ) := by exact_mod_cast hl
  change |u (a.symm x)|≤_
  calc
    _ ≤ C*((W.length (a.symm x):ℝ)+1)^k := hu _
    _ ≤ C*(((W.length (a.symm W.root):ℝ)+1)*((W.length x:ℝ)+1))^k := by
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) (W.length (a.symm W.root)),Nat.cast_nonneg (α:=ℝ) (W.length x)]
    _ = _ := by rw [mul_pow]; ring

def harmonicTranslation (k : ℕ) (a : W.Aut) :
    W.polynomialHarmonicSpace k ≃ₗ[ℝ] W.polynomialHarmonicSpace k where
  toFun u := ⟨W.translateFunction a u,W.translate_harmonic a u.property.1,
    W.translate_polynomial_growth a k u.property.2⟩
  invFun u := ⟨W.translateFunction a.symm u,W.translate_harmonic a.symm u.property.1,
    W.translate_polynomial_growth a.symm k u.property.2⟩
  left_inv u := by apply Subtype.ext; funext x; simp [translateFunction]
  right_inv u := by apply Subtype.ext; funext x; simp [translateFunction]
  map_add' u v := rfl
  map_smul' c u := rfl
@[simp] lemma harmonicTranslation_apply (k : ℕ) (a : W.Aut) (u : W.polynomialHarmonicSpace k) (x : X) :
    (W.harmonicTranslation k a u:X → ℝ) x=(u:X → ℝ) (a.symm x) := rfl

def harmonicRepresentation (k : ℕ) : W.Aut →*
    (W.polynomialHarmonicSpace k ≃ₗ[ℝ] W.polynomialHarmonicSpace k) where
  toFun := W.harmonicTranslation k
  map_one' := by ext u x; rfl
  map_mul' a b := by ext u x; rfl

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_LazyWalkProbability
attribute [-simp] _root_.OAI.CriticalPercolation.HomogeneousAnalysis.FH.add_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.FH.delta_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.FH.mass_delta _root_.OAI.CriticalPercolation.HomogeneousAnalysis.FH.mem_support _root_.OAI.CriticalPercolation.HomogeneousAnalysis.FH.ofFunction_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.FH.smul_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.FH.sub_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.FH.transport_apply _root_.OAI.CriticalPercolation.HomogeneousAnalysis.FH.transport_delta _root_.OAI.CriticalPercolation.HomogeneousAnalysis.FH.transport_mul _root_.OAI.CriticalPercolation.HomogeneousAnalysis.FH.transport_one _root_.OAI.CriticalPercolation.HomogeneousAnalysis.FH.zero_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

def walkState (n : ℕ) : RegularHilbert A :=
  (W.lazyWalk^n) (lp.single 2 (1:A) (1:ℝ))

@[simp] lemma walkState_zero : W.walkState 0=lp.single 2 (1:A) (1:ℝ) := rfl

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_ProjectedWalkFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

def projectedFunction (f : RegularHilbert A) (t : A) (x : A) : ℝ :=
  inner ℝ (regular x f-f) (regular t f-f) / (4*(W.generators.card:ℝ)*W.walkEnergy f)

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_HarmonicLinearQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
universe u
variable {A : Type u} [Group A] (W : WordGeometry A)

def translateFunction (a : A) (u : A → ℝ) : A → ℝ := fun x => u (a⁻¹*x)

lemma translate_harmonic (a : A) {u : A → ℝ} (hu : W.IsHarmonic u) :
    W.IsHarmonic (translateFunction a u) := by
  intro x
  simpa only [translateFunction,mul_assoc] using hu (a⁻¹*x)

lemma translate_polynomial_growth (a : A) (k : ℕ) {u : A → ℝ}
    (hu : W.HasPolynomialGrowth k u) : W.HasPolynomialGrowth k (translateFunction a u) := by
  obtain ⟨C,hC,hu⟩ := (W.polynomial_growth_iff_length k u).mp hu
  apply (W.polynomial_growth_iff_length k _).mpr
  refine ⟨C*((W.length a:ℝ)+1)^k,by positivity,?_⟩
  intro x
  have hl := W.length_mul_le a⁻¹ x
  rw [W.length_inv] at hl
  have hl' : (W.length (a⁻¹*x):ℝ)≤(W.length a:ℝ)+(W.length x:ℝ) := by exact_mod_cast hl
  change |u (a⁻¹*x)|≤_
  calc
    _ ≤ C*((W.length (a⁻¹*x):ℝ)+1)^k := hu _
    _ ≤ C*(((W.length a:ℝ)+1)*((W.length x:ℝ)+1))^k := by
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) (W.length a),Nat.cast_nonneg (α:=ℝ) (W.length x)]
    _ = _ := by rw [mul_pow]; ring

def harmonicTranslation (k : ℕ) (a : A) :
    W.polynomialHarmonicSpace k ≃ₗ[ℝ] W.polynomialHarmonicSpace k where
  toFun u := ⟨translateFunction a u, W.translate_harmonic a u.property.1,
    W.translate_polynomial_growth a k u.property.2⟩
  invFun u := ⟨translateFunction a⁻¹ u, W.translate_harmonic a⁻¹ u.property.1,
    W.translate_polynomial_growth a⁻¹ k u.property.2⟩
  left_inv u := by apply Subtype.ext; funext x; simp [translateFunction]
  right_inv u := by apply Subtype.ext; funext x; simp [translateFunction]
  map_add' u v := rfl
  map_smul' c u := rfl

@[simp] lemma harmonicTranslation_apply (k : ℕ) (a : A) (u : W.polynomialHarmonicSpace k) (x : A) :
    (W.harmonicTranslation k a u:A → ℝ) x=(u:A → ℝ) (a⁻¹*x) := rfl

def harmonicRepresentation (k : ℕ) : A →*
    (W.polynomialHarmonicSpace k ≃ₗ[ℝ] W.polynomialHarmonicSpace k) where
  toFun := W.harmonicTranslation k
  map_one' := by ext u x; simp
  map_mul' a b := by ext u x; simp [mul_assoc]

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_FiniteSubspaceOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

@[instance_reducible] def subspaceAction (ρ : G →* (V ≃ₗ[K] V)) : MulAction G (Submodule K V) where
  smul g W := W.map (ρ g).toLinearMap
  one_smul W := by
    change W.map (ρ 1).toLinearMap=W
    rw [map_one]
    exact W.map_id
  mul_smul g h W := by
    change W.map (ρ (g*h)).toLinearMap=(W.map (ρ h).toLinearMap).map (ρ g).toLinearMap
    rw [map_mul]
    exact (Submodule.map_comp _ _ W)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_CompactInvariantMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter Finset MeasureTheory
open scoped Classical Topology BigOperators Pointwise ENNReal NNReal BoundedContinuousFunction

namespace CriticalPercolation.SparseGrowth
variable {G X : Type*} [Group G] [DecidableEq G]
variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MulAction G X] [ContinuousConstSMul G X]

lemma orbit_wordBall_nonempty (S : Finset G) (h1 : (1:G)∈S) (n : ℕ) : (S^n).Nonempty :=
  ⟨1,Finset.one_mem_pow h1⟩

def orbitAverage (T : Finset G) (hT : T.Nonempty) (x : X) : ProbabilityMeasure X :=
  ⟨((T.card:ℝ≥0∞)⁻¹) • ∑ g∈T, Measure.dirac (g • x), by
    constructor
    simp only [Measure.smul_apply,Measure.finsetSum_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),
      Finset.sum_const,nsmul_eq_mul,smul_eq_mul,mul_one]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast (Finset.card_ne_zero.mpr hT)) (by simp)⟩

end CriticalPercolation.SparseGrowth

namespace CriticalPercolation.SparseGrowth
variable {G X : Type*} [Group G] [DecidableEq G]
variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MulAction G X] [ContinuousConstSMul G X]

def integralInvariantSubgroup (μ : ProbabilityMeasure X) : Subgroup G where
  carrier := {g | ∀ f : X →ᵇ ℝ, (∫ y, f (g • y) ∂(μ:Measure X))=∫ y, f y ∂(μ:Measure X)}
  one_mem' := by intro f; simp
  mul_mem' := by
    intro a b ha hb f
    let fa : X →ᵇ ℝ := f.compContinuous ⟨fun y => a • y,continuous_const_smul a⟩
    calc
      _ = ∫ y, fa (b • y) ∂(μ:Measure X) := by simp only [fa,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,mul_smul]
      _ = ∫ y, fa y ∂(μ:Measure X) := hb fa
      _ = ∫ y, f y ∂(μ:Measure X) := ha f
  inv_mem' := by
    intro a ha f
    let fi : X →ᵇ ℝ := f.compContinuous ⟨fun y => a⁻¹ • y,continuous_const_smul _⟩
    have hh := ha fi
    simpa only [fi,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,inv_smul_smul] using hh.symm

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_LocalProjectiveAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory Module Metric TopologicalSpace
open scoped Classical Topology

namespace CriticalPercolation.LocalProjective
variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

def nzImage (a : V ≃L[K] V) (v : NZ V) : NZ V :=
  ⟨a v,fun he => v.property (a.injective (he.trans a.map_zero.symm))⟩

def action (a : V ≃L[K] V) : Space K V → Space K V :=
  Quotient.map (nzImage a) (by
    intro v w h
    obtain ⟨c,hc⟩ := h
    refine ⟨c,Subtype.ext ?_⟩
    change (c:K) • a (w:V)=a (v:V)
    rw [←map_smul]
    exact congrArg a (congrArg Subtype.val hc))

@[simp] lemma action_point (a : V ≃L[K] V) (v : NZ V) :
    action a (point K V v)=point K V (nzImage a v) := rfl

@[simp] lemma action_one (q : Space K V) : action (1:V ≃L[K] V) q=q := by
  obtain ⟨v,rfl⟩ := point_surjective K V q
  rfl

lemma action_mul (a b : V ≃L[K] V) (q : Space K V) :
    action (a*b) q=action a (action b q) := by
  obtain ⟨v,rfl⟩ := point_surjective K V q
  rfl

variable {G : Type*} [Group G]
@[instance_reducible]
def mulAction (ρ : G →* (V ≃L[K] V)) : MulAction G (Space K V) where
  smul g q := action (ρ g) q
  one_smul q := by change action (ρ 1) q=q; rw [map_one,action_one]
  mul_smul g h q := by change action (ρ (g*h)) q=action (ρ g) (action (ρ h) q); rw [map_mul,action_mul]

instance spaceMeasurable : MeasurableSpace (Space K V) := borel _
instance spaceBorel : BorelSpace (Space K V) := ⟨rfl⟩

def subspace (W : Submodule K V) : Set (Space K V) :=
  point K V '' {v : NZ V | (v:V)∈W}

end CriticalPercolation.LocalProjective
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_LocalFurstenbergBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory NormedSpace Module Metric TopologicalSpace
open scoped Classical Topology ENNReal

namespace CriticalPercolation.LocalProjective
variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

lemma equiv_operator_ne_zero [Nontrivial V] (a : V ≃L[K] V) :
    a.toContinuousLinearMap≠0 := by
  intro he
  obtain ⟨x,hx⟩ := exists_ne (0:V)
  apply hx
  apply a.injective
  have hh := congrArg (fun f : V →L[K] V => f x) he
  exact hh.trans a.map_zero.symm

variable (t : K) (ht : 1<‖t‖)
include ht
lemma exists_shell_scalar {U : Type*} [NormedAddCommGroup U] [NormedSpace K U]
    (x : U) (hx : x≠0) : ∃ c : K, c≠0 ∧ 1/‖t‖≤‖c • x‖ ∧ ‖c • x‖≤1 := by
  obtain ⟨c,hc,hlt,hle,_⟩ := rescale_to_shell ht zero_lt_one hx
  exact ⟨c,hc,hle,hlt.le⟩

noncomputable def shellScalar {U : Type*} [NormedAddCommGroup U] [NormedSpace K U]
    (x : U) (hx : x≠0) : K := Classical.choose (exists_shell_scalar t ht x hx)

variable [Nontrivial V]
def normalized (a : V ≃L[K] V) : V →L[K] V :=
  shellScalar t ht a.toContinuousLinearMap (equiv_operator_ne_zero a) • a.toContinuousLinearMap

def shell (U : Type*) [NormedAddCommGroup U] : Set U := {x | 1/‖t‖≤‖x‖ ∧ ‖x‖≤1}

end CriticalPercolation.LocalProjective
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_FullSpanAlternative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

def FullSpan (ρ : G →* (V ≃ₗ[K] V)) : Prop :=
  Submodule.span K (Set.range (fun g => (ρ g).toLinearMap))=⊤

def StrongFullSpan (ρ : G →* (V ≃ₗ[K] V)) : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex → FullSpan (ρ.comp H.subtype)

end CriticalPercolation.LinearGrowth
namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V]
variable [NormedSpace K V] [ProperSpace K] [FiniteDimensional K V] [Group G]

def continuousRepresentation (ρ : G →* (V ≃ₗ[K] V)) : G →* (V ≃L[K] V) where
  toFun g := (ρ g).toContinuousLinearEquiv
  map_one' := by ext x; change ρ 1 x=x; rw [map_one]; rfl
  map_mul' g h := by ext x; change ρ (g*h) x=ρ g (ρ h x); rw [map_mul]; rfl

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_AbsoluteMatrixSpan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K L T G n : Type*} [Field K] [Field L] [Field T] [Group G]
variable [Fintype n] [DecidableEq n]

def matrixRepresentation (ρ : G →* GL n K) : G →* ((n → K) ≃ₗ[K] (n → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

@[simp] lemma matrixRepresentation_apply (ρ : G →* GL n K) (g : G) (v : n → K) :
    matrixRepresentation ρ g v=(ρ g).val.mulVec v := rfl

def matrixFlatten : Matrix n n K ≃ₗ[K] (n × n → K) where
  toFun M p := M p.1 p.2
  invFun f i j := f (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def FullMatrixSpan (ρ : G →* GL n K) : Prop :=
  Submodule.span K (Set.range (fun g (p : n×n) => ρ g p.1 p.2))=⊤

def StrongFullMatrixSpan (ρ : G →* GL n K) : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex → FullMatrixSpan (ρ.comp H.subtype)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_ConjugationMatrixGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Matrix

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def latticeCharacter (w : ι → ℂ) : Multiplicative (ι → ℤ) →* Multiplicative ℂ where
  toFun x := Multiplicative.ofAdd (w ⬝ᵥ fun i => ((Multiplicative.toAdd x i : ℤ) : ℂ))
  map_one' := by change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0; congr 1; simp
  map_mul' x y := by
    change Multiplicative.ofAdd (w ⬝ᵥ fun i => (((Multiplicative.toAdd x i +
      Multiplicative.toAdd y i) : ℤ) : ℂ)) = Multiplicative.ofAdd (_+_)
    congr 1
    simp [dotProduct,Finset.sum_add_distrib,mul_add]

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_FgMatrixRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.LinearGrowth
variable {G R : Type*} [Group G] [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

variable (ρ : G →* GL n R) (D : Subalgebra ℤ R) (hD : ∀ g i j, ρ g i j∈D)

def liftMatrix (g : G) : Matrix n n D := fun i j => ⟨ρ g i j,hD g i j⟩

@[simp] lemma liftMatrix_map (g : G) :
    (D.val.toRingHom.mapMatrix) (liftMatrix ρ D hD g)=(ρ g).val := rfl

lemma liftMatrix_one : liftMatrix ρ D hD 1=1 := by
  apply Matrix.map_injective (f := D.val) Subtype.val_injective
  change D.val.toRingHom.mapMatrix (liftMatrix ρ D hD 1)=D.val.toRingHom.mapMatrix 1
  rw [map_one]
  change (ρ 1).val=1
  rw [map_one]
  rfl

lemma liftMatrix_mul (g h : G) : liftMatrix ρ D hD (g*h)=liftMatrix ρ D hD g*liftMatrix ρ D hD h := by
  apply Matrix.map_injective (f := D.val) Subtype.val_injective
  change D.val.toRingHom.mapMatrix (liftMatrix ρ D hD (g*h))=D.val.toRingHom.mapMatrix _
  rw [map_mul]
  change (ρ (g*h)).val=(ρ g).val*(ρ h).val
  rw [map_mul]
  rfl

def liftMatrixGroup : G →* GL n D where
  toFun g := ⟨liftMatrix ρ D hD g,liftMatrix ρ D hD g⁻¹,
    by rw [←liftMatrix_mul,mul_inv_cancel,liftMatrix_one],
    by rw [←liftMatrix_mul,inv_mul_cancel,liftMatrix_one]⟩
  map_one' := Units.ext (liftMatrix_one ρ D hD)
  map_mul' g h := Units.ext (liftMatrix_mul ρ D hD g h)

@[simp] lemma liftMatrixGroup_map (g : G) :
    Matrix.GeneralLinearGroup.map D.val.toRingHom (liftMatrixGroup ρ D hD g)=ρ g := by
  apply Units.ext
  rfl

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_InvariantBlockSolvability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Module Function

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

def subspaceRepresentation (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g, W.map (ρ g).toLinearMap=W) : G →* (W ≃ₗ[K] W) where
  toFun g := (ρ g).ofSubmodules W W (hW g)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

def quotientRepresentation (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g, W.map (ρ g).toLinearMap=W) : G →* ((V ⧸ W) ≃ₗ[K] (V ⧸ W)) where
  toFun g := Submodule.Quotient.equiv W W (ρ g) (hW g)
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp
  map_mul' g h := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp

@[simp] lemma subspaceRepresentation_apply (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g, W.map (ρ g).toLinearMap=W) (g : G) (w : W) :
    (subspaceRepresentation ρ W hW g w : V)=ρ g w := rfl

@[simp] lemma quotientRepresentation_apply (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g, W.map (ρ g).toLinearMap=W) (g : G) (v : V) :
    quotientRepresentation ρ W hW g (Submodule.Quotient.mk v)=Submodule.Quotient.mk (ρ g v) := rfl

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_ProjectivePeriodicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Module

namespace CriticalPercolation.LinearGrowth
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def continuousEndAlgEquiv : End ℂ V ≃ₐ[ℂ] (V →L[ℂ] V) :=
  AlgEquiv.ofLinearEquiv LinearMap.toContinuousLinearMap rfl (fun _ _ => rfl)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_ProjectivelyPeriodicSchur
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Group G]

def linearMatrixEquiv : (V ≃ₗ[K] V) ≃* GL (Fin (finrank K V)) K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis K V)).toMulEquiv)

def conjugationRepresentation (ρ : G →* (V ≃ₗ[K] V)) : G →* (End K V ≃ₗ[K] End K V) where
  toFun g := (ρ g).conj
  map_one' := by ext f x; simp only [map_one]; rfl
  map_mul' g h := by ext f x; simp only [map_mul]; rfl

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_CharacteristicNilpotentCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise IsMulCommutative

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

omit [DecidableEq A] [DecidableEq B] in

def powerSubgroup (A : Type*) [Group A] (k : ℕ) : Subgroup A :=
  Subgroup.closure (Set.range (fun x : A => x^k))

omit [DecidableEq A] [DecidableEq B] in
instance powerSubgroup_characteristic (k : ℕ) : (powerSubgroup A k).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro f
  rw [powerSubgroup,MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
  exact ⟨f x,map_pow f x k |>.symm⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
end


