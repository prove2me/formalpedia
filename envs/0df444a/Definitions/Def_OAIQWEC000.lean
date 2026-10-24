-- Prove2me | Definitions.Def_OAIQWEC000
-- name    : OAIQWEC000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T23:10:47.977711+00:00
-- url     : https://prove2.me/theorems/b6d1e06d-9390-46c6-9eda-931792c673a2
-- title:
--   OpenAI C¹ entropy conjecture counterexample split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof that the general $C^1$ self-map form of Shub's entropy conjecture fails (`OAI.Problem340.exists_C1_entropy_counterexample`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below (OpenAI, *A $C^1$ Counterexample to the Entropy Conjecture*, OpenAI Math Release, September 25, 2026, result family 151, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are the clock, cutoffs, saturation and gain profiles and the model map on $\mathbb R/100\mathbb Z \times \Sigma \times \Sigma^3$ (`SphereData`, `concreteData`, `rawMap`), its realization on the published manifold (`modelHomeomorph`, `realizedMap`), and the singular-chain machinery of the homology computation (affine simplices, barycentric subdivision, good covers). The bundle also contains the lemmas those definitions use in their bodies.
--
--   The port's compatibility layer `OAI.SStd` is here too: OpenAI's code was written against a newer Mathlib, whose topological simplex is the structure `Convexity.StdSimplex`; this Mathlib uses the subtype `stdSimplex`, and `OAI.SStd R X` is that subtype, with the part of the newer API OpenAI uses (`SStd.weights`, `SStd.single`, `SStd.map`, which is `stdSimplex.map`, `SStd.barycenter` and their lemmas). It is not OpenAI's code.
--
--   The definitions of the published statement (`CounterexampleManifold`, `IsC1SelfMap`, `RealSingularHomology`, `realHomologyMap`, `totalRealHomologySpectralRadius` and the rest) are not repeated: the bundle imports them from the published bundle `Def_C1EntropyCounterexample`. It imports no other bundle of this split.
--
--   Modules: `ActualSingularSubdivision`, `ActualSingularSubdivisionMap`, `AffineSimplexCone`, `AffineSimplexGeometry`, `AffineSingularRealization`, `AmbientPrediction`, `AmbientRetraction`, `BarycentricSubdivision`, `C1Coordinates`, `CircleClockDoubling`, `CircleDoublingChains`, `CircleWindingCocycle`, `Clock`, `ClockAtInfinity`, `ClockCharts`, `ClockLift`, `ClockLocalExtension`, `ClockModel`, `ClockOrbit`, `ClockPeriodization`, `ClockProfiles`, `ClockQuotient`, `ClockQuotientC1`, `ClockRotation`, `ConcreteInputRegularity`, `Conjugacy`, `CoordinateGoodCover`, `EntropyCoding`, `FiniteGoodCoverHomology`, `GainLocalExtension`, `GainProfile`, `HomologyConjugacy`, `HomologyConstant`, `HomologyCycle`, `HomologyHomotopyEquiv`, `HomologyNaturality`, `HomologyTransfer`, `HomologyZero`, `IteratedSubdivision`, `Map`, `MapClockComponent`, `MapContinuity`, `MapData`, `MapHomology`, `MapOrbitAlternatives`, `MapOrbitLift`, `MapPassage`, `MapPassagePhase`, `MapQuotientContinuity`, `MapReadout`, `MapRealizedHomology`, `MapRegisterRegularity`, `MapSignal`, `MapSignals`, `MapTerminalEntropy`, `MonotoneItineraries`, `NormalizedPrediction`, `OrderedIntervalLabels`, `PassagePhase`, `PolarProductEntropy`, `PolynomialSpectralBound`, `PredictionInput`, `PredictionModelBridge`, `PredictionSeries`, `RadialRegisterEntropy`, `RawBaseGoodCover`, `RawInvariantInfinity`, `RawInvariantSets`, `RawSpectrumFactor`, `ReadoutCover`, `ReadoutLocalExtension`, `RealizedConstruction`, `RecursiveSubdivisionMesh`, `RegisterLinearity`, `Saturation`, `SaturationEntropy`, `Simplex`, `SimplexCoordinates`, `SimplexSingularRealization`, `SimplexSubdivisionMesh`, `SimplicialMayerVietoris`, `SingularAcyclicModels`, `SingularChainsFinsupp`, `SingularChainsFinsuppBoundary`, `SingularCoverChains`, `SingularCoverNaturality`, `SingularSimplexCircleLift`, `SingularSmallChains`, `SingularSmallNaturality`, `SingularSubdivision`, `SingularSubdivisionIterateRealization`, `SingularSupportNaturality`, `SingularUniversalChainMap`, `SingularUniversalFinsupp`, `SingularUniversalOperator`, `SkewProduct`, `SkewProductHomology`, `SmallCoverMayerVietoris`, `SmallCoverNaturality`, `SparseVisits`, `SpectralRadius`, `SphereAngularInput`, `SphereCharts`, `SphereCompactSupport`, `SphereCoverGeometry`, `SphereCutoffs`, `SphereCutoffsAffine`, `SphereDoubling`, `SphereDoublingCharts`, `SphereInfinityChart`, `SphereMainUpdate`, `SphereMayerVietorisEigen`, `SphereOverlapDoubling`, `SpherePerturbation`, `SphereSquareEquator`, `SphereTranslation`, `StandardRegisterUpdate`, `StandardSaturation`, `StdSimplexShim`, `SubdivisionQuasiIso`, `SubdivisionSupportMesh`.
--
--   The theorems of the development that the definitions do not need are proved in the two solutions of this split: one proves the paper's Proposition 4.3 (`OAI.Problem340.Construction.coverEntropy_realizedMap_eq_zero`), and the other proves `OAI.Problem340.exists_C1_entropy_counterexample` from it. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A C^1 Counterexample to the Entropy Conjecture, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 151; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-C1-Counterexample-to-the-Entropy-Conjecture-September-25-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Dynamics/EntropyCounterexample, lean/OAI/Geometry/SingularHomology and lean/OAI/Combinatorics/PerfectMatching at commit adc7f12

import Mathlib
import Definitions.Def_C1EntropyCounterexample

section
-- module Solutions.OAIQW_Problem340.StdSimplexShim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
Port shim (not OpenAI's code). OpenAI's Mathlib takes the topological simplex of
`SimplexCategory.toTop` to be the structure `Convexity.StdSimplex ℝ (Fin (n+1))`; this Mathlib
takes it to be the subtype `stdSimplex ℝ (Fin (n+1))`. The port replaces OpenAI's
`Convexity.StdSimplex` by `OAI.SStd`, the subtype `stdSimplex R X` on a finite type, and this file
provides the part of the newer API that OpenAI's modules use, with `SStd.map` equal to
`stdSimplex.map`, so that `TopCat.toSSetObjEquiv` and its naturality apply unchanged.
-/

namespace OAI

/-- The standard simplex on a finite type, as the subtype `stdSimplex R X`. -/
abbrev SStd (R : Type*) [Semiring R] [PartialOrder R] (X : Type*) [Fintype X] : Type _ :=
  ↥(stdSimplex R X)

namespace SStd

section Semiring

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- The weights as a finitely supported function. -/
noncomputable def weights (s : SStd R X) : X →₀ R := Finsupp.equivFunOnFinite.symm s.1

lemma weights_apply (s : SStd R X) (x : X) : s.weights x = s.1 x := rfl

lemma coe_weights (s : SStd R X) : ⇑s.weights = s.1 := rfl

lemma weights_nonneg (s : SStd R X) (x : X) : 0 ≤ s.weights x := s.2.1 x

lemma total_of_fintype (s : SStd R X) : ∑ x, s.weights x = 1 := s.2.2

lemma ext {s t : SStd R X} (h : s.weights = t.weights) : s = t :=
  Subtype.ext (congrArg (fun f : X →₀ R => (f : X → R)) h)

@[simp] lemma weights_inj {s t : SStd R X} : s.weights = t.weights ↔ s = t :=
  ⟨ext, fun h => h ▸ rfl⟩

end Semiring

section OrderedRing

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Push a simplex point forward along a map of index types (this Mathlib's `stdSimplex.map`). -/
noncomputable def map (g : X → Y) (s : SStd R X) : SStd R Y := stdSimplex.map g s

lemma map_val_apply [DecidableEq Y] (g : X → Y) (s : SStd R X) (y : Y) :
    (map g s).1 y = ∑ x ∈ Finset.univ.filter (fun x => g x = y), s.1 x := by
  change (FunOnFinite.linearMap R R g s.1) y = _
  rw [FunOnFinite.linearMap_apply_apply]

@[simp] lemma weights_map (g : X → Y) (s : SStd R X) :
    (map g s).weights = s.weights.mapDomain g := by
  classical
  ext y
  rw [weights_apply, map_val_apply, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
    Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, Finset.sum_filter, weights_apply]

@[simp] lemma map_id (s : SStd R X) : map id s = s := stdSimplex.map_id_apply s

/-- The vertex (point mass) at `x`. -/
noncomputable def single (x : X) : SStd R X := by
  classical
  exact ⟨Pi.single x 1, single_mem_stdSimplex R x⟩

@[simp] lemma weights_single (x : X) : (single (R := R) x).weights = Finsupp.single x 1 := by
  classical
  ext y
  simp only [weights_apply, single, Finsupp.single_apply, Pi.single_apply, eq_comm]

@[simp] lemma single_val_apply [DecidableEq X] (x y : X) :
    (single (R := R) x).1 y = if x = y then 1 else 0 := by
  classical
  simp only [single, Pi.single_apply, eq_comm]

@[simp] lemma single_coe_apply [DecidableEq X] (x y : X) :
    DFunLike.coe (F := stdSimplex R X) (single (R := R) x) y = if x = y then 1 else 0 :=
  single_val_apply x y

@[simp] lemma map_single (x : X) (f : X → Y) : map f (single (R := R) x) = single (f x) := by
  classical
  apply ext
  rw [weights_map, weights_single, weights_single, Finsupp.mapDomain_single]

end OrderedRing

section Field

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type*} [Fintype X]

/-- The barycenter, with every weight `(card X)⁻¹`. -/
noncomputable def barycenter [Nonempty X] : SStd 𝕜 X := stdSimplex.barycenter

@[simp] lemma barycenter_val_apply [Nonempty X] (x : X) :
    (barycenter : SStd 𝕜 X).1 x = (Fintype.card X : 𝕜)⁻¹ := rfl

@[simp] lemma barycenter_coe_apply [Nonempty X] (x : X) :
    DFunLike.coe (F := stdSimplex 𝕜 X) (barycenter : SStd 𝕜 X) x = (Fintype.card X : 𝕜)⁻¹ := rfl

end Field

section Topology

variable (R : Type*) [Ring R] [PartialOrder R] [IsOrderedRing R] [TopologicalSpace R]
  [IsTopologicalRing R]

lemma continuous_map {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y) :
    Continuous (map (R := R) f) := stdSimplex.continuous_map f

lemma continuous_weights_apply {X : Type*} [Fintype X] (x : X) :
    Continuous (fun s : SStd R X => s.weights x) :=
  (continuous_apply x).comp continuous_subtype_val

variable (M : Type*) [Fintype M]

lemma isEmbedding_toFun_comp_weights :
    Topology.IsEmbedding (fun t ↦ t.weights : SStd R M → M → R) :=
  Topology.IsEmbedding.subtypeVal

lemma range_toFun_comp_weights :
    Set.range (fun t ↦ t.weights : SStd R M → (M → R)) =
      (⋂ (i : M), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext f
  simp only [Set.mem_range, coe_weights, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.2.1, s.2.2⟩
  · intro hf
    exact ⟨⟨f, hf⟩, rfl⟩

end Topology

end SStd

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Simplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Probability vectors on finite types, with their convexity and compactness properties.
The function-space simplex is the range of the weights of `SStd`.
-/

noncomputable section

open scoped BigOperators

namespace MatchingEntropy

/-- Nonnegative real weights with total mass one. -/
def probabilitySimplex (Index : Type*) [Fintype Index] : Set (Index → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

theorem convex_probabilitySimplex (Index : Type*) [Fintype Index] :
    Convex ℝ (probabilitySimplex Index) := by
  intro leftWeights leftMem rightWeights rightMem leftScale rightScale
    leftNonneg rightNonneg total
  constructor
  · intro index
    exact add_nonneg (mul_nonneg leftNonneg (leftMem.1 index))
      (mul_nonneg rightNonneg (rightMem.1 index))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, leftMem.2, rightMem.2, mul_one, total]

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SimplexCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.RealSimplex

variable {Index : Type*} [Fintype Index]

instance coordinatesFun : CoeFun (SStd ℝ Index) (fun _ => Index → ℝ) :=
  ⟨fun point => point.weights⟩

def coordinates (point : SStd ℝ Index) : Index → ℝ := point.weights

@[simp] lemma single_apply [DecidableEq Index] (vertex index : Index) :
    SStd.single (R := ℝ) vertex index = if vertex = index then 1 else 0 := by
  change (SStd.single vertex).weights index = _
  simp [Finsupp.single_apply]

lemma map_apply {Target : Type*} [Fintype Target] [DecidableEq Target]
    (mapping : Index → Target) (point : SStd ℝ Index) (index : Target) :
    point.map mapping index =
      ∑ source ∈ Finset.univ.filter (fun source => mapping source = index), point source := by
  classical
  change (point.map mapping).weights index = _
  rw [SStd.weights_apply, SStd.map_val_apply]
  rfl

lemma coordinates_injective : Function.Injective (coordinates (Index := Index)) :=
  (SStd.isEmbedding_toFun_comp_weights ℝ Index).injective

def coordinateSet (Index : Type*) [Fintype Index] : Set (Index → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

lemma mem_coordinateSet (point : SStd ℝ Index) :
    coordinates point ∈ coordinateSet Index :=
  ⟨point.weights_nonneg, point.total_of_fintype⟩

lemma convex_coordinateSet : Convex ℝ (coordinateSet Index) :=
  MatchingEntropy.convex_probabilitySimplex Index

def coordinateHomeomorph : SStd ℝ Index ≃ₜ coordinateSet Index :=
  (SStd.isEmbedding_toFun_comp_weights ℝ Index).toHomeomorph.trans
    (Homeomorph.setCongr (by
      rw [SStd.range_toFun_comp_weights]
      ext weights
      simp [coordinateSet]))

@[simp] lemma coordinateHomeomorph_apply (point : SStd ℝ Index) :
    (coordinateHomeomorph point : Index → ℝ) = coordinates point := rfl

@[simp] lemma coordinateHomeomorph_symm_apply (point : coordinateSet Index) :
    coordinates (coordinateHomeomorph.symm point) = point :=
  congrArg Subtype.val (coordinateHomeomorph.apply_symm_apply point)

@[simp] lemma coordinateHomeomorph_symm_apply_at (point : coordinateSet Index) (index : Index) :
    coordinateHomeomorph.symm point index = point.val index :=
  congrFun (coordinateHomeomorph_symm_apply point) index

lemma contractible [Nonempty Index] : ContractibleSpace (SStd ℝ Index) := by
  have : ContractibleSpace (coordinateSet Index) :=
    convex_coordinateSet.contractibleSpace
      ⟨coordinates (SStd.single (Classical.arbitrary Index)), mem_coordinateSet _⟩
  exact (coordinateHomeomorph (Index := Index)).contractibleSpace

lemma locallyPathConnected : LocallyPathConnectedSpace (SStd ℝ Index) := by
  have : LocallyPathConnectedSpace (coordinateSet Index) :=
    convex_coordinateSet.locallyPathConnectedSpace
  exact (coordinateHomeomorph (Index := Index)).isOpenEmbedding.locallyPathConnectedSpace

end Problem340.RealSimplex

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.AffineSimplexGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.AffineSimplex

variable {E : Type*} {n : ℕ}

section Realization

variable [AddCommGroup E] [Module ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def realize (v : ι → E) (p : SStd ℝ ι) : E :=
  ∑ i, p i • v i

@[simp] lemma realize_vertex (v : ι → E) [DecidableEq ι] (i : ι) :
    realize v (SStd.single i) = v i := by
  simp [realize, Finsupp.single_apply]

lemma realize_comp_map (f : ι → κ) (v : κ → E) (p : SStd ℝ ι) :
    realize v (SStd.map f p) = realize (v ∘ f) p := by
  classical
  unfold realize
  simp only [RealSimplex.map_apply, Finset.sum_smul]
  calc
    (∑ y : κ, ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x • v y) =
        ∑ y : κ, ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x • v (f x) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x : ι, p x • (v ∘ f) x := by
      exact Finset.sum_fiberwise Finset.univ f (fun x => p x • v (f x))

lemma realize_mem {s : Set E} (hs : Convex ℝ s) (v : ι → E)
    (hv : ∀ i, v i ∈ s) (p : SStd ℝ ι) : realize v p ∈ s := by
  exact hs.sum_mem (fun i _ => p.weights_nonneg i) p.total_of_fintype
    (fun i _ => hv i)

def barycenter [Nonempty ι] (v : ι → E) : E := realize v SStd.barycenter

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

lemma continuous_realize (v : ι → E) : Continuous (realize v) := by
  unfold realize
  exact continuous_finsetSum _ (fun i _ =>
    (SStd.continuous_weights_apply ℝ i).smul continuous_const)

def realizeIn (s : Set E) (hs : Convex ℝ s) (v : ι → E) (hv : ∀ i, v i ∈ s) :
    C(SStd ℝ ι, s) :=
  ⟨fun p => ⟨realize v p, realize_mem hs v hv p⟩,
    (continuous_realize v).subtype_mk _⟩

@[simp] lemma realizeIn_coe (s : Set E) (hs : Convex ℝ s)
    (v : ι → E) (hv : ∀ i, v i ∈ s) (p : SStd ℝ ι) :
    (realizeIn s hs v hv p : E) = realize v p := rfl

end Topology

end Realization

section SimplexTarget

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

def simplexRealizeMap (v : ι → SStd ℝ κ) :
    C(SStd ℝ ι, SStd ℝ κ) :=
  (⟨RealSimplex.coordinateHomeomorph.symm,
    RealSimplex.coordinateHomeomorph.symm.continuous⟩ :
      C(RealSimplex.coordinateSet κ, SStd ℝ κ)).comp
    (realizeIn (RealSimplex.coordinateSet κ) RealSimplex.convex_coordinateSet
      (fun i => (v i : κ → ℝ)) (fun i => RealSimplex.mem_coordinateSet (v i)))

@[simp] lemma simplexRealizeMap_coe (v : ι → SStd ℝ κ) (p : SStd ℝ ι) :
    (simplexRealizeMap v p : κ → ℝ) = realize (fun i => (v i : κ → ℝ)) p :=
  RealSimplex.coordinateHomeomorph_symm_apply _

lemma simplexRealizeMap_apply (v : ι → SStd ℝ κ) (p : SStd ℝ ι) (j : κ) :
    simplexRealizeMap v p j = ∑ i, p i * v i j := by
  rw [simplexRealizeMap_coe]
  simp [realize, Finset.sum_apply]

@[simp] lemma simplexRealizeMap_vertex (v : ι → SStd ℝ κ)
    [DecidableEq ι] (i : ι) : simplexRealizeMap v (SStd.single i) = v i := by
  apply RealSimplex.coordinates_injective
  exact (simplexRealizeMap_coe v _).trans (realize_vertex (fun j => (v j : κ → ℝ)) i)

lemma simplexRealizeMap_comp_map (f : ι → κ) (v : κ → SStd ℝ τ) :
    (simplexRealizeMap v).comp ⟨SStd.map f, SStd.continuous_map ℝ f⟩ =
      simplexRealizeMap (v ∘ f) := by
  ext p : 1
  apply RealSimplex.coordinates_injective
  change (simplexRealizeMap v (SStd.map f p) : τ → ℝ) =
    (simplexRealizeMap (v ∘ f) p : τ → ℝ)
  simp only [simplexRealizeMap_coe]
  exact realize_comp_map f (fun i => (v i : τ → ℝ)) p

lemma map_simplexRealizeMap (f : κ → τ) (v : ι → SStd ℝ κ)
    (p : SStd ℝ ι) :
    SStd.map f (simplexRealizeMap v p) =
      simplexRealizeMap (fun i => SStd.map f (v i)) p := by
  classical
  apply RealSimplex.coordinates_injective
  funext index
  change SStd.map f (simplexRealizeMap v p) index =
    simplexRealizeMap (fun i => SStd.map f (v i)) p index
  simp_rw [RealSimplex.map_apply, simplexRealizeMap_apply, RealSimplex.map_apply,
    Finset.mul_sum]
  exact Finset.sum_comm

def simplexBarycenter [Nonempty ι] (v : ι → SStd ℝ κ) : SStd ℝ κ :=
  simplexRealizeMap v SStd.barycenter

@[simp] lemma simplexBarycenter_coe [Nonempty ι] (v : ι → SStd ℝ κ) :
    (simplexBarycenter v : κ → ℝ) = barycenter (fun i => (v i : κ → ℝ)) :=
  simplexRealizeMap_coe v _

lemma map_simplexBarycenter [Nonempty ι] (f : κ → τ) (v : ι → SStd ℝ κ) :
    SStd.map f (simplexBarycenter v) =
      simplexBarycenter (fun i => SStd.map f (v i)) :=
  map_simplexRealizeMap f v SStd.barycenter

end SimplexTarget

end Problem340.AffineSimplex

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.AffineSimplexCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.AffineSimplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section SimplexValued

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

abbrev simplexRealize (v : ι → SStd ℝ κ) (p : SStd ℝ ι) :
    SStd ℝ κ := simplexRealizeMap v p

abbrev simplexRealization (v : ι → SStd ℝ κ) := simplexRealizeMap v

@[simp] theorem simplexRealize_apply (v : ι → SStd ℝ κ)
    (p : SStd ℝ ι) (j : κ) :
    simplexRealize v p j = ∑ i, p i * v i j := simplexRealizeMap_apply v p j

@[simp] theorem simplexRealize_vertex [DecidableEq ι]
    (v : ι → SStd ℝ κ) (i : ι) :
    simplexRealize v (SStd.single i) = v i := simplexRealizeMap_vertex v i

theorem simplexRealize_map (v : κ → SStd ℝ τ) (f : ι → κ)
    (p : SStd ℝ ι) :
    simplexRealize v (SStd.map f p) = simplexRealize (v ∘ f) p :=
  DFunLike.congr_fun (simplexRealizeMap_comp_map f v) p

@[simp] theorem simplexRealize_vertices [DecidableEq ι] (p : SStd ℝ ι) :
    simplexRealize (SStd.single (R := ℝ) (X := ι)) p = p := by
  apply SStd.ext
  ext j
  simp [simplexRealize_apply, Finsupp.single_apply]

end SimplexValued

end Problem340.AffineSimplex

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologyCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

section ModuleCycles

variable {R : Type*} [Ring R]

def moduleHomologyClass (S : ShortComplex (ModuleCat R))
    (z : S.X₂) (hz : S.g.hom z = 0) : S.homology :=
  S.moduleCatHomologyIso.toLinearEquiv.symm
    (Submodule.Quotient.mk (⟨z, LinearMap.mem_ker.mpr hz⟩ : LinearMap.ker S.g.hom))

end ModuleCycles

abbrev realSingularChainComplex (X : Type) [TopologicalSpace X] :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℝ)).obj
    (ModuleCat.of ℝ ℝ)).obj (TopCat.of X)

abbrev realSingularChainMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    realSingularChainComplex X ⟶ realSingularChainComplex Y :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℝ)).obj
    (ModuleCat.of ℝ ℝ)).map (TopCat.ofHom (continuousMapOf f hf))

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularChainsFinsupp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340

abbrev RealSingularSimplex (X : Type) [TopologicalSpace X] (n : ℕ) :=
  C(SStd ℝ (Fin (n + 1)), X)

abbrev RealSingularChains (X : Type) [TopologicalSpace X] (n : ℕ) :=
  RealSingularSimplex X n →₀ ℝ

def simplicialChainsFinsuppEquiv (S : SSet) (n : ℕ) :
    (S _⦋n⦌ →₀ ℝ) ≃ₗ[ℝ] (S.chainComplex (ModuleCat.of ℝ ℝ)).X n :=
  ((ModuleCat.finsuppCoconeIsColimit ℝ ℝ (S _⦋n⦌)).coconePointUniqueUpToIso
    (S.isColimitChainComplexXCofan (ModuleCat.of ℝ ℝ) n)).toLinearEquiv

@[simp]
theorem simplicialChainsFinsuppEquiv_single (S : SSet) (n : ℕ)
    (σ : S _⦋n⦌) (r : ℝ) :
    simplicialChainsFinsuppEquiv S n (Finsupp.single σ r) =
      (S.ιChainComplex (R := ModuleCat.of ℝ ℝ) σ).hom r := by
  have h := (ModuleCat.finsuppCoconeIsColimit ℝ ℝ (S _⦋n⦌)).comp_coconePointUniqueUpToIso_hom
    (S.isColimitChainComplexXCofan (ModuleCat.of ℝ ℝ) n) (Discrete.mk σ)
  exact congrArg (fun f : ModuleCat.of ℝ ℝ ⟶ (S.chainComplex (ModuleCat.of ℝ ℝ)).X n =>
    f.hom r) h

def singularChainsFinsuppEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    RealSingularChains X n ≃ₗ[ℝ] (realSingularChainComplex X).X n :=
  (Finsupp.domLCongr (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm).trans
    (simplicialChainsFinsuppEquiv (TopCat.toSSet.obj (TopCat.of X)) n)

def realSingularGenerator {X : Type} [TopologicalSpace X] {n : ℕ}
    (σ : RealSingularSimplex X n) : ℝ →ₗ[ℝ] (realSingularChainComplex X).X n :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℝ ℝ)
    ((TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ)).hom

@[simp]
theorem singularChainsFinsuppEquiv_single (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : RealSingularSimplex X n) (r : ℝ) :
    singularChainsFinsuppEquiv X n (Finsupp.single σ r) = realSingularGenerator σ r := by
  unfold singularChainsFinsuppEquiv realSingularGenerator
  erw [LinearEquiv.trans_apply, Finsupp.domLCongr_single]
  exact simplicialChainsFinsuppEquiv_single (TopCat.toSSet.obj (TopCat.of X)) n _ r

@[simp]
theorem singularChainsFinsuppEquiv_symm_generator (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : RealSingularSimplex X n) (r : ℝ) :
    (singularChainsFinsuppEquiv X n).symm (realSingularGenerator σ r) = Finsupp.single σ r := by
  rw [← singularChainsFinsuppEquiv_single X n σ r, LinearEquiv.symm_apply_apply]

@[elab_as_elim]
theorem realSingularChain_induction {X : Type} [TopologicalSpace X] {n : ℕ}
    {P : (realSingularChainComplex X).X n → Prop}
    (hzero : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b))
    (hgen : ∀ (σ : RealSingularSimplex X n) (r : ℝ), P (realSingularGenerator σ r))
    (z : (realSingularChainComplex X).X n) : P z := by
  obtain ⟨c, rfl⟩ := (singularChainsFinsuppEquiv X n).surjective z
  induction c using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using hzero
  | add c d hc hd => simpa only [map_add] using hadd _ _ hc hd
  | single σ r => simpa only [singularChainsFinsuppEquiv_single] using hgen σ r

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SingularSubdivision

variable {V : Type*}

abbrev Chains (V : Type*) (n : ℕ) := (Fin n → V) →₀ ℝ

def generator {n : ℕ} (p : Fin n → V) : Chains V n := Finsupp.single p 1

def face {n : ℕ} (i : Fin (n + 1)) (p : Fin (n + 1) → V) : Fin n → V :=
  p ∘ i.succAbove

def boundary (n : ℕ) : Chains V (n + 1) →ₗ[ℝ] Chains V n :=
  Finsupp.linearCombination ℝ (fun p =>
    ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val • generator (face i p))

def cone (v : V) (n : ℕ) : Chains V n →ₗ[ℝ] Chains V (n + 1) :=
  Finsupp.linearCombination ℝ (fun p => generator (Fin.cons v p))

@[simp] theorem boundary_generator {n : ℕ} (p : Fin (n + 1) → V) :
    boundary n (generator p) =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val • generator (face i p) := by
  simp [boundary, generator]

@[simp] theorem cone_generator (v : V) {n : ℕ} (p : Fin n → V) :
    cone v n (generator p) = generator (Fin.cons v p) := by
  simp [cone, generator]

@[simp] theorem face_cons_zero {n : ℕ} (v : V) (p : Fin n → V) :
    face 0 (Fin.cons v p) = p := by
  funext i
  simp [face]

@[simp] theorem face_cons_succ {n : ℕ} (v : V)
    (p : Fin (n + 1) → V) (i : Fin (n + 1)) :
    face i.succ (Fin.cons v p) = Fin.cons v (face i p) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [face, Fin.succAbove_ne_zero_zero]
  · simp [face, Fin.succ_succAbove_succ]

theorem boundary_cone_generator (v : V) {n : ℕ} (p : Fin (n + 1) → V) :
    boundary (n + 1) (cone v (n + 1) (generator p)) =
      generator p - cone v n (boundary n (generator p)) := by
  rw [cone_generator, boundary_generator, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, face_cons_zero, face_cons_succ,
    boundary_generator, map_sum, map_smul, cone_generator, Fin.val_succ,
    pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem linearMap_ext {n : ℕ} {M : Type*} [AddCommMonoid M] [Module ℝ M]
    {f g : Chains V n →ₗ[ℝ] M}
    (h : ∀ p, f (generator p) = g (generator p)) : f = g := by
  apply Finsupp.lhom_ext
  intro p r
  have hr : Finsupp.single p r = r • generator p := by simp [generator]
  rw [hr, map_smul, map_smul, h]

theorem boundary_cone (v : V) (n : ℕ) (c : Chains V (n + 1)) :
    boundary (n + 1) (cone v (n + 1) c) = c - cone v n (boundary n c) := by
  have h : (boundary (n + 1)).comp (cone v (n + 1)) =
      LinearMap.id - (cone v n).comp (boundary n) := by
    apply linearMap_ext
    exact boundary_cone_generator v
  exact LinearMap.congr_fun h c

theorem boundary_cone_zero (v : V) (c : Chains V 0) :
    boundary 0 (cone v 0 c) = c := by
  have h : (boundary 0).comp (cone v 0) = LinearMap.id := by
    apply linearMap_ext
    intro p
    simp
  exact LinearMap.congr_fun h c

theorem boundary_boundary (n : ℕ) (c : Chains V (n + 2)) :
    boundary n (boundary (n + 1) c) = 0 := by
  induction n with
  | zero =>
      have h : (boundary (V := V) 0).comp (boundary 1) = 0 := by
        apply linearMap_ext
        intro p
        change boundary 0 (boundary 1 (generator p)) = 0
        conv_lhs => rw [← Fin.cons_self_tail p, ← cone_generator]
        rw [boundary_cone, map_sub, boundary_cone_zero, sub_self]
      exact LinearMap.congr_fun h c
  | succ n ih =>
      have h : (boundary (V := V) (n + 1)).comp (boundary (n + 2)) = 0 := by
        apply linearMap_ext
        intro p
        change boundary (n + 1) (boundary (n + 2) (generator p)) = 0
        conv_lhs => rw [← Fin.cons_self_tail p, ← cone_generator]
        rw [boundary_cone, map_sub, boundary_cone, ih, map_zero, sub_zero, sub_self]
      exact LinearMap.congr_fun h c

abbrev Centers (V : Type*) := ∀ n : ℕ, (Fin (n + 1) → V) → V

def subdivision (center : Centers V) : (n : ℕ) → Chains V n →ₗ[ℝ] Chains V n
  | 0 => LinearMap.id
  | n + 1 => Finsupp.linearCombination ℝ (fun p =>
      cone (center n p) n (subdivision center n (boundary n (generator p))))

@[simp] theorem subdivision_zero (center : Centers V) (c : Chains V 0) :
    subdivision center 0 c = c := rfl

@[simp] theorem subdivision_generator (center : Centers V) (n : ℕ)
    (p : Fin (n + 1) → V) :
    subdivision center (n + 1) (generator p) =
      cone (center n p) n (subdivision center n (boundary n (generator p))) := by
  simp [subdivision, generator]

theorem boundary_subdivision (center : Centers V) (n : ℕ) (c : Chains V (n + 1)) :
    boundary n (subdivision center (n + 1) c) =
      subdivision center n (boundary n c) := by
  induction n with
  | zero =>
      have h : (boundary 0).comp (subdivision center 1) =
          (subdivision center 0).comp (boundary 0) := by
        apply linearMap_ext
        intro p
        change boundary 0 (subdivision center 1 (generator p)) = _
        rw [subdivision_generator, boundary_cone_zero]
        rfl
      exact LinearMap.congr_fun h c
  | succ n ih =>
      have h : (boundary (n + 1)).comp (subdivision center (n + 2)) =
          (subdivision center (n + 1)).comp (boundary (n + 1)) := by
        apply linearMap_ext
        intro p
        change boundary (n + 1) (subdivision center (n + 2) (generator p)) = _
        rw [subdivision_generator, boundary_cone, ih, boundary_boundary,
          map_zero, map_zero, sub_zero]
        rfl
      exact LinearMap.congr_fun h c

section Naturality

variable {W : Type*}

def mapVertices (f : V → W) (n : ℕ) : Chains V n →ₗ[ℝ] Chains W n :=
  Finsupp.linearCombination ℝ (fun p => generator (f ∘ p))

@[simp] theorem mapVertices_generator (f : V → W) {n : ℕ} (p : Fin n → V) :
    mapVertices f n (generator p) = generator (f ∘ p) := by
  simp [mapVertices, generator]

theorem mapVertices_cone (f : V → W) (v : V) (n : ℕ) (c : Chains V n) :
    mapVertices f (n + 1) (cone v n c) = cone (f v) n (mapVertices f n c) := by
  have h : (mapVertices f (n + 1)).comp (cone v n) =
      (cone (f v) n).comp (mapVertices f n) := by
    apply linearMap_ext
    intro p
    simp only [LinearMap.comp_apply, cone_generator, mapVertices_generator]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  exact LinearMap.congr_fun h c

theorem mapVertices_boundary (f : V → W) (n : ℕ) (c : Chains V (n + 1)) :
    mapVertices f n (boundary n c) = boundary n (mapVertices f (n + 1) c) := by
  have h : (mapVertices f n).comp (boundary n) =
      (boundary n).comp (mapVertices f (n + 1)) := by
    apply linearMap_ext
    intro p
    simp only [LinearMap.comp_apply, boundary_generator, mapVertices_generator,
      map_sum, map_smul]
    rfl
  exact LinearMap.congr_fun h c

theorem mapVertices_subdivision (f : V → W) (cv : Centers V) (cw : Centers W)
    (hf : ∀ n p, f (cv n p) = cw n (f ∘ p))
    (n : ℕ) (c : Chains V n) :
    mapVertices f n (subdivision cv n c) = subdivision cw n (mapVertices f n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : (mapVertices f (n + 1)).comp (subdivision cv (n + 1)) =
          (subdivision cw (n + 1)).comp (mapVertices f (n + 1)) := by
        apply linearMap_ext
        intro p
        simp only [LinearMap.comp_apply, subdivision_generator, mapVertices_generator]
        rw [mapVertices_cone, ih, mapVertices_boundary, mapVertices_generator, hf]
      exact LinearMap.congr_fun h c

end Naturality

end Problem340.SingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.AffineSingularRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory Simplicial Opposite

namespace Problem340.AffineSingularRealization

variable {E : Type} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

section SimplexTarget

abbrev Simplex (k : ℕ) := SStd ℝ (Fin (k + 1))

def realizeInSimplex (k n : ℕ) : SingularSubdivision.Chains (Simplex k) (n + 1) →ₗ[ℝ]
    (realSingularChainComplex (Simplex k)).X n :=
  (singularChainsFinsuppEquiv (Simplex k) n).toLinearMap.comp
    (Finsupp.lmapDomain ℝ ℝ (fun v => AffineSimplex.simplexRealization v))

@[simp]
theorem realizeInSimplex_single {k n : ℕ} (v : Fin (n + 1) → Simplex k) (r : ℝ) :
    realizeInSimplex k n (Finsupp.single v r) =
      realSingularGenerator (AffineSimplex.simplexRealization v) r := by
  simp only [realizeInSimplex, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, singularChainsFinsuppEquiv_single]

@[simp]
theorem realizeInSimplex_generator {k n : ℕ} (v : Fin (n + 1) → Simplex k) :
    realizeInSimplex k n (SingularSubdivision.generator v) =
      realSingularGenerator (AffineSimplex.simplexRealization v) 1 :=
  realizeInSimplex_single v 1

theorem singular_simplex_face {k n : ℕ} (v : Fin (n + 2) → Simplex k)
    (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of (Simplex k))).δ i
        ((TopCat.toSSetObjEquiv (TopCat.of (Simplex k)) (op ⦋n + 1⦌)).symm
          (AffineSimplex.simplexRealization v)) =
      (TopCat.toSSetObjEquiv (TopCat.of (Simplex k)) (op ⦋n⦌)).symm
        (AffineSimplex.simplexRealization (SingularSubdivision.face i v)) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (Simplex k)) (op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro p
  simp only [Equiv.apply_symm_apply]
  exact AffineSimplex.simplexRealize_map v i.succAbove p

theorem boundary_realizeInSimplex_single {k n : ℕ} (v : Fin (n + 2) → Simplex k)
    (r : ℝ) :
    ((realSingularChainComplex (Simplex k)).d (n + 1) n).hom
        (realizeInSimplex k (n + 1) (Finsupp.single v r)) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val •
        realizeInSimplex k n (Finsupp.single (SingularSubdivision.face i v) r) := by
  simp only [realizeInSimplex_single]
  let S := TopCat.toSSet.obj (TopCat.of (Simplex k))
  let σ := (TopCat.toSSetObjEquiv (TopCat.of (Simplex k)) (op ⦋n + 1⦌)).symm
    (AffineSimplex.simplexRealization v)
  have h := congrArg
    (fun f : ModuleCat.of ℝ ℝ ⟶ (S.chainComplex (ModuleCat.of ℝ ℝ)).X n => f.hom r)
    (S.ιChainComplex_d (ModuleCat.of ℝ ℝ) σ)
  have hface (i : Fin (n + 2)) : S.δ i σ =
      (TopCat.toSSetObjEquiv (TopCat.of (Simplex k)) (op ⦋n⦌)).symm
        (AffineSimplex.simplexRealization (SingularSubdivision.face i v)) :=
    singular_simplex_face v i
  simp only [hface, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
    LinearMap.sum_apply,
    ← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one] at h
  exact h

theorem realizeInSimplex_boundary {k n : ℕ}
    (c : SingularSubdivision.Chains (Simplex k) (n + 2)) :
    realizeInSimplex k n (SingularSubdivision.boundary (n + 1) c) =
      ((realSingularChainComplex (Simplex k)).d (n + 1) n).hom
        (realizeInSimplex k (n + 1) c) := by
  have h : (realizeInSimplex k n).comp (SingularSubdivision.boundary (n + 1)) =
      ((realSingularChainComplex (Simplex k)).d (n + 1) n).hom.comp
        (realizeInSimplex k (n + 1)) := by
    apply SingularSubdivision.linearMap_ext
    intro v
    simp only [LinearMap.comp_apply, SingularSubdivision.boundary_generator, map_sum, map_smul]
    exact (boundary_realizeInSimplex_single v 1).symm
  exact LinearMap.congr_fun h c

end SimplexTarget

end Problem340.AffineSingularRealization

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.BarycentricSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SingularSubdivision

abbrev StandardSimplex (n : ℕ) := SStd ℝ (Fin (n + 1))

def simplexCenters (k : ℕ) : Centers (StandardSimplex k) :=
  fun _ p => AffineSimplex.simplexBarycenter p

def standardVertices (n : ℕ) : Fin (n + 1) → StandardSimplex n := SStd.single

def universalSubdivision (n : ℕ) : Chains (StandardSimplex n) (n + 1) :=
  subdivision (simplexCenters n) (n + 1) (generator (standardVertices n))

lemma map_centers {k l : ℕ} (f : Fin (k + 1) → Fin (l + 1))
    (n : ℕ) (p : Fin (n + 1) → StandardSimplex k) :
    SStd.map f (simplexCenters k n p) =
      simplexCenters l n (SStd.map f ∘ p) :=
  AffineSimplex.map_simplexBarycenter f p

lemma standardVertices_face (n : ℕ) (i : Fin (n + 2)) :
    face i (standardVertices (n + 1)) =
      SStd.map i.succAbove ∘ standardVertices n := by
  funext j
  simp [face, standardVertices]

theorem universalSubdivision_boundary (n : ℕ) :
    boundary (n + 1) (universalSubdivision (n + 1)) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val •
        mapVertices (SStd.map i.succAbove) (n + 1) (universalSubdivision n) := by
  unfold universalSubdivision
  rw [boundary_subdivision, boundary_generator, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, standardVertices_face,
    ← mapVertices_generator (SStd.map i.succAbove)]
  rw [mapVertices_subdivision _ _ _ (map_centers i.succAbove)]

lemma simplexCenters_zero (k : ℕ) (p : Fin 1 → StandardSimplex k) :
    simplexCenters k 0 p = p 0 := by
  change AffineSimplex.simplexRealizeMap p SStd.barycenter = p 0
  rw [show (SStd.barycenter : SStd ℝ (Fin 1)) =
    SStd.single 0 from Subsingleton.elim _ _]
  exact AffineSimplex.simplexRealizeMap_vertex p 0

theorem subdivision_one (k : ℕ) (c : Chains (StandardSimplex k) 1) :
    subdivision (simplexCenters k) 1 c = c := by
  have h : subdivision (simplexCenters k) 1 = LinearMap.id := by
    apply linearMap_ext
    intro p
    have ht : Fin.cons (p 0) (face 0 p) = p := by
      funext i
      fin_cases i
      simp
    simp [simplexCenters_zero, ht]
  exact LinearMap.congr_fun h c

@[simp] theorem universalSubdivision_zero :
    universalSubdivision 0 = generator (standardVertices 0) :=
  subdivision_one 0 _

end Problem340.SingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularChainsFinsuppBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularChainFormulas

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def simplexChain {n : ℕ} (σ : C(SStd ℝ (Fin (n + 1)), X)) :
    (realSingularChainComplex X).X n :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℝ ℝ)
    ((TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ)).hom (1 : ℝ)

def face {n : ℕ} (σ : C(SStd ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    C(SStd ℝ (Fin (n + 1)), X) :=
  σ.comp ⟨SStd.map i.succAbove, SStd.continuous_map ℝ i.succAbove⟩

lemma simplexChain_boundary {n : ℕ} (σ : C(SStd ℝ (Fin (n + 2)), X)) :
    ((realSingularChainComplex X).d (n + 1) n).hom (simplexChain σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • simplexChain (face σ i) := by
  let S := TopCat.toSSet.obj (TopCat.of X)
  let s := (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n + 1⦌)).symm σ
  have h := congrArg (fun k : ModuleCat.of ℝ ℝ ⟶ (S.chainComplex
      (ModuleCat.of ℝ ℝ)).X n => k.hom (1 : ℝ)) (S.ιChainComplex_d (ModuleCat.of ℝ ℝ) s)
  have hsface (i : Fin (n + 2)) : S.δ i s =
      (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm (face σ i) := by
    apply (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).injective
    ext p
    rfl
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply, hsface, S, s, SSet.chainComplex] at h
  convert h using 1 <;> rfl

lemma simplexChain_boundary_real {n : ℕ}
    (σ : C(SStd ℝ (Fin (n + 2)), X)) :
    ((realSingularChainComplex X).d (n + 1) n).hom (simplexChain σ) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val • simplexChain (face σ i) := by
  simpa only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one]
    using simplexChain_boundary σ

lemma simplexChain_map (f : C(X, Y)) {n : ℕ}
    (σ : C(SStd ℝ (Fin (n + 1)), X)) :
    ((realSingularChainMap f f.continuous).f n).hom (simplexChain σ) =
      simplexChain (f.comp σ) := by
  let S := TopCat.toSSet.obj (TopCat.of X)
  let T := TopCat.toSSet.obj (TopCat.of Y)
  let s := (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ
  let φ := TopCat.toSSet.map (TopCat.ofHom f)
  have h := congrArg (fun k : ModuleCat.of ℝ ℝ ⟶ (T.chainComplex
      (ModuleCat.of ℝ ℝ)).X n => k.hom (1 : ℝ))
    (SSet.ι_chainComplexMap_f S T φ (ModuleCat.of ℝ ℝ) s)
  exact h

end Problem340.SingularChainFormulas

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SimplexSingularRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SimplexSingularRealization

open SingularSubdivision

abbrev Simplex (k : ℕ) := SStd ℝ (Fin (k + 1))

def realize (k n : ℕ) :
    Chains (Simplex k) (n + 1) →ₗ[ℝ] (realSingularChainComplex (Simplex k)).X n :=
  Finsupp.linearCombination ℝ (fun v =>
    SingularChainFormulas.simplexChain (AffineSimplex.simplexRealizeMap v))

@[simp] theorem realize_generator (k n : ℕ) (v : Fin (n + 1) → Simplex k) :
    realize k n (generator v) =
      SingularChainFormulas.simplexChain (AffineSimplex.simplexRealizeMap v) := by
  simp [realize, generator]

theorem map_realize (k l n : ℕ) (f : Fin (k + 1) → Fin (l + 1))
    (c : Chains (Simplex k) (n + 1)) :
    ((realSingularChainMap (SStd.map f) (SStd.continuous_map ℝ f)).f n).hom
      (realize k n c) =
      realize l n (mapVertices (SStd.map f) (n + 1) c) := by
  let F : C(Simplex k, Simplex l) := ⟨SStd.map f, SStd.continuous_map ℝ f⟩
  have h : ((realSingularChainMap F F.continuous).f n).hom.comp (realize k n) =
      (realize l n).comp (mapVertices (SStd.map f) (n + 1)) := by
    apply linearMap_ext
    intro v
    change ((realSingularChainMap F F.continuous).f n).hom
      (realize k n (generator v)) = _
    rw [realize_generator, SingularChainFormulas.simplexChain_map]
    have he : F.comp (AffineSimplex.simplexRealizeMap v) =
        AffineSimplex.simplexRealizeMap (SStd.map f ∘ v) := by
      ext p : 1
      exact AffineSimplex.map_simplexRealizeMap f v p
    simp only [LinearMap.comp_apply, mapVertices_generator, realize_generator]
    rw [he]
  exact LinearMap.congr_fun h c

@[simp] theorem simplexRealizeMap_standardVertices (n : ℕ) :
    AffineSimplex.simplexRealizeMap (standardVertices n) = ContinuousMap.id (Simplex n) := by
  ext p : 1
  apply RealSimplex.coordinates_injective
  funext j
  change AffineSimplex.simplexRealizeMap (standardVertices n) p j = p j
  rw [AffineSimplex.simplexRealizeMap_apply]
  simp [standardVertices, Finsupp.single_apply]

@[simp] theorem realize_standardVertices (n : ℕ) :
    realize n n (generator (standardVertices n)) =
      SingularChainFormulas.simplexChain (ContinuousMap.id (Simplex n)) := by
  rw [realize_generator, simplexRealizeMap_standardVertices]

end Problem340.SimplexSingularRealization

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularUniversalOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularUniversalOperator

abbrev chainsFunctor (n : ℕ) : TopCat ⥤ ModuleCat ℝ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℝ)).obj
    (ModuleCat.of ℝ ℝ)) ⋙ HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n

abbrev simplex (n : ℕ) : TopCat := TopCat.of (SStd ℝ (Fin (n + 1)))

def simplexMap {X : TopCat} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) : simplex n ⟶ X :=
  TopCat.ofHom (TopCat.toSSetObjEquiv X (op ⦋n⦌) σ)

@[simp]
theorem simplexMap_naturality {X Y : TopCat} (g : X ⟶ Y) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    simplexMap ((TopCat.toSSet.map g).app (op ⦋n⦌) σ) = simplexMap σ ≫ g := by
  rfl

@[reassoc (attr := simp)]
theorem generator_map {X Y : TopCat} (g : X ⟶ Y) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ ≫
      (chainsFunctor n).map g =
    (TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℝ ℝ)
      ((TopCat.toSSet.map g).app (op ⦋n⦌) σ) :=
  SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
    (TopCat.toSSet.map g) (ModuleCat.of ℝ ℝ) σ

def operator (n m : ℕ) (u : (chainsFunctor m).obj (simplex n)) :
    chainsFunctor n ⟶ chainsFunctor m where
  app X := Sigma.desc (fun σ : (TopCat.toSSet.obj X) _⦋n⦌ =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ _ u) ≫
      (chainsFunctor m).map (simplexMap σ))
  naturality {X Y} g := by
    apply SSet.chainComplex_hom_ext
    intro σ
    erw [generator_map_assoc]
    dsimp only [SSet.ιChainComplex]
    erw [Sigma.ι_desc, simplexMap_naturality, Functor.map_comp]
    erw [Sigma.ι_desc_assoc]
    rfl

@[reassoc (attr := simp)]
theorem generator_operator {n m : ℕ} (u : (chainsFunctor m).obj (simplex n))
    (X : TopCat) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ ≫ (operator n m u).app X =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ _ u) ≫
        (chainsFunctor m).map (simplexMap σ) := by
  exact Sigma.ι_desc _ _

@[simp]
theorem operator_generator_apply {n m : ℕ} (u : (chainsFunctor m).obj (simplex n))
    (X : TopCat) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ((operator n m u).app X).hom
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ).hom 1) =
      ((chainsFunctor m).map (simplexMap σ)).hom u := by
  have h := congrArg (fun k : ModuleCat.of ℝ ℝ ⟶ (chainsFunctor m).obj X => k.hom 1)
    (generator_operator u X σ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using! h

def identitySimplex (n : ℕ) : (TopCat.toSSet.obj (simplex n)) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv (simplex n) (op ⦋n⦌)).symm (ContinuousMap.id _)

@[simp]
theorem simplexMap_identity (n : ℕ) : simplexMap (identitySimplex n) = 𝟙 (simplex n) := by
  rfl

def identityGenerator (n : ℕ) : ModuleCat.of ℝ ℝ ⟶ (chainsFunctor n).obj (simplex n) :=
  (TopCat.toSSet.obj (simplex n)).ιChainComplex (identitySimplex n)

@[simp]
theorem map_identitySimplex {X : TopCat} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.map (simplexMap σ)).app (op ⦋n⦌) (identitySimplex n) = σ := by
  apply (TopCat.toSSetObjEquiv X (op ⦋n⦌)).injective
  ext p
  rfl

@[reassoc (attr := simp)]
theorem identityGenerator_map {X : TopCat} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    identityGenerator n ≫ (chainsFunctor n).map (simplexMap σ) =
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ := by
  unfold identityGenerator
  erw [generator_map, map_identitySimplex]

theorem natTrans_ext {n : ℕ} {F : TopCat ⥤ ModuleCat ℝ}
    {α β : chainsFunctor n ⟶ F}
    (h : identityGenerator n ≫ α.app (simplex n) =
      identityGenerator n ≫ β.app (simplex n)) : α = β := by
  apply NatTrans.ext
  funext X
  apply SSet.chainComplex_hom_ext
  intro σ
  erw [← identityGenerator_map σ, Category.assoc, Category.assoc,
    α.naturality, β.naturality]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ F.map (simplexMap σ)) h).trans (Category.assoc _ _ _))

@[reassoc (attr := simp)]
theorem identityGenerator_operator {n m : ℕ} (u : (chainsFunctor m).obj (simplex n)) :
    identityGenerator n ≫ (operator n m u).app (simplex n) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ _ u) := by
  unfold identityGenerator
  erw [generator_operator, simplexMap_identity, CategoryTheory.Functor.map_id, Category.comp_id]

theorem natTrans_ext_apply {n : ℕ} {F : TopCat ⥤ ModuleCat ℝ}
    {α β : chainsFunctor n ⟶ F}
    (h : (α.app (simplex n)).hom ((identityGenerator n).hom 1) =
      (β.app (simplex n)).hom ((identityGenerator n).hom 1)) : α = β := by
  apply natTrans_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact h

end Problem340.SingularUniversalOperator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ActualSingularSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory Simplicial Opposite

namespace Problem340.ActualSingularSubdivision

open SingularSubdivision AffineSingularRealization

def identityChain (n : ℕ) :
    (realSingularChainComplex (StandardSimplex n)).X n :=
  (SingularUniversalOperator.identityGenerator n).hom 1

def subdivisionChain (n : ℕ) :
    (realSingularChainComplex (StandardSimplex n)).X n :=
  realizeInSimplex n n (universalSubdivision n)

def subdivision (n : ℕ) : SingularUniversalOperator.chainsFunctor n ⟶
    SingularUniversalOperator.chainsFunctor n :=
  SingularUniversalOperator.operator n n (subdivisionChain n)

lemma realize_standardVertices (n : ℕ) :
    realizeInSimplex n n (generator (standardVertices n)) =
      identityChain n := by
  rw [realizeInSimplex_generator]
  have h : AffineSimplex.simplexRealization (standardVertices n) =
      ContinuousMap.id (StandardSimplex n) := by
    ext p : 1
    exact AffineSimplex.simplexRealize_vertices p
  rw [h]
  rfl

@[simp] theorem subdivisionChain_zero :
    subdivisionChain 0 = identityChain 0 := by
  rw [subdivisionChain, universalSubdivision_zero, realize_standardVertices]

theorem subdivisionChain_boundary_affine (n : ℕ) :
    ((realSingularChainComplex (StandardSimplex (n + 1))).d (n + 1) n).hom
        (subdivisionChain (n + 1)) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val •
        realizeInSimplex (n + 1) n
          (mapVertices (SStd.map i.succAbove) (n + 1) (universalSubdivision n)) := by
  rw [subdivisionChain, ← realizeInSimplex_boundary, universalSubdivision_boundary, map_sum]
  simp only [map_smul]

lemma realize_eq_aux (k n : ℕ) :
    realizeInSimplex k n = SimplexSingularRealization.realize k n := by
  apply linearMap_ext
  intro p
  rw [realizeInSimplex_generator, SimplexSingularRealization.realize_generator]
  rfl

lemma realizeInSimplex_map (k l n : ℕ) (f : Fin (k + 1) → Fin (l + 1))
    (c : Chains (StandardSimplex k) (n + 1)) :
    ((realSingularChainMap (SStd.map f) (SStd.continuous_map ℝ f)).f n).hom
        (realizeInSimplex k n c) =
      realizeInSimplex l n (mapVertices (SStd.map f) (n + 1) c) := by
  rw [realize_eq_aux, realize_eq_aux]
  exact SimplexSingularRealization.map_realize k l n f c

theorem subdivisionChain_boundary (n : ℕ) :
    ((realSingularChainComplex (StandardSimplex (n + 1))).d (n + 1) n).hom
        (subdivisionChain (n + 1)) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val •
        ((realSingularChainMap (SStd.map i.succAbove)
          (SStd.continuous_map ℝ i.succAbove)).f n).hom (subdivisionChain n) := by
  rw [subdivisionChain_boundary_affine]
  apply Finset.sum_congr rfl
  intro i _
  rw [← realizeInSimplex_map]
  rfl

end Problem340.ActualSingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologyNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

theorem realHomologyMap_eq_of_homotopy {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) {f g : X → Y} (hf : Continuous f) (hg : Continuous g)
    (H : ContinuousMap.Homotopy (continuousMapOf f hf) (continuousMapOf g hg)) :
    realHomologyMap n f hf = realHomologyMap n g hg := by
  have h := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (C := ModuleCat ℝ) (f := TopCat.ofHom (continuousMapOf f hf))
    (g := TopCat.ofHom (continuousMapOf g hg)) H (ModuleCat.of ℝ ℝ) n
  exact congrArg (fun k => k.hom) h

theorem realHomologyMap_eq_of_homotopic {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) {f g : X → Y} (hf : Continuous f) (hg : Continuous g)
    (H : ContinuousMap.Homotopic (continuousMapOf f hf) (continuousMapOf g hg)) :
    realHomologyMap n f hf = realHomologyMap n g hg := by
  obtain ⟨H⟩ := H
  exact realHomologyMap_eq_of_homotopy n hf hg H

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologyConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

theorem realHomologyMap_const
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (hn : n ≠ 0) (y : Y) :
    realHomologyMap n (fun _ : X => y) continuous_const = 0 := by
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)
  let a : TopCat.of X ⟶ TopCat.of PUnit :=
    TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let b : TopCat.of PUnit ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨fun _ => y, continuous_const⟩
  have hz : CategoryTheory.Limits.IsZero (H.obj (TopCat.of PUnit)) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℝ) n (ModuleCat.of ℝ ℝ) (TopCat.of PUnit) hn
  have hb : H.map b = 0 := hz.eq_zero_of_src (H.map b)
  change (H.map (a ≫ b)).hom = 0
  rw [Functor.map_comp, hb, Limits.comp_zero, ModuleCat.hom_zero]

theorem realHomologyMap_eq_zero_of_nullhomotopic
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (hn : n ≠ 0) (f : X → Y) (hf : Continuous f)
    (h : (continuousMapOf f hf).Nullhomotopic) : realHomologyMap n f hf = 0 := by
  obtain ⟨y, hy⟩ := h
  exact (realHomologyMap_eq_of_homotopic n hf continuous_const hy).trans
    (realHomologyMap_const n hn y)

theorem realSingularHomology_subsingleton_of_contractible
    (n : ℕ) (hn : n ≠ 0) (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] : Subsingleton (RealSingularHomology n X) := by
  have hz : realHomologyMap n (id : X → X) continuous_id = 0 :=
    realHomologyMap_eq_zero_of_nullhomotopic n hn id continuous_id (id_nullhomotopic X)
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)
  have hid : realHomologyMap n (id : X → X) continuous_id = LinearMap.id :=
    congrArg (fun k => k.hom) (H.map_id (TopCat.of X))
  have hid0 : (LinearMap.id : RealSingularHomology n X →ₗ[ℝ]
      RealSingularHomology n X) = 0 := hid.symm.trans hz
  constructor
  intro x y
  have hx := LinearMap.congr_fun hid0 x
  have hy := LinearMap.congr_fun hid0 y
  exact hx.trans hy.symm

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularAcyclicModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

namespace Problem340.SingularAcyclicModels

abbrev singularFunctor : TopCat.{0} ⥤ ChainComplex (ModuleCat ℝ) ℕ :=
  (singularChainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ)

abbrev degree (n : ℕ) : TopCat.{0} ⥤ ModuleCat ℝ :=
  ((Functor.postcompose₂.obj
    (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n)).obj
      (singularChainComplexFunctor (ModuleCat ℝ))).obj (ModuleCat.of ℝ ℝ)

abbrev complex : ChainComplex (TopCat.{0} ⥤ ModuleCat ℝ) ℕ where
  X := degree
  d i j :=
    { app X := (singularFunctor.obj X).d i j
      naturality X Y f := (singularFunctor.map f).comm i j }
  shape i j hij := by
    apply NatTrans.ext
    funext X
    exact (singularFunctor.obj X).shape i j hij
  d_comp_d' i j k hij hjk := by
    apply NatTrans.ext
    funext X
    exact (singularFunctor.obj X).d_comp_d i j k

abbrev model (n : ℕ) : TopCat.{0} := SimplexCategory.toTop.obj ⦋n⦌

instance contractible_model (n : ℕ) : ContractibleSpace (model n) := by
  let : ContractibleSpace (SStd ℝ (Fin (n + 1))) :=
    RealSimplex.contractible
  change ContractibleSpace (ULift (SStd ℝ (Fin (n + 1))))
  exact Homeomorph.ulift.contractibleSpace

lemma model_exact (n k : ℕ) : (singularFunctor.obj (model n)).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact realSingularHomology_subsingleton_of_contractible (k + 1) (by omega) (model n)

def liftCycle (n k : ℕ) (φ : complex.X n ⟶ complex.X (k + 1))
    (hφ : φ ≫ complex.d (k + 1) k = 0) :
    complex.X n ⟶ complex.X (k + 2) := by
  let adj := singularChainComplexFunctorAdjunction (ModuleCat ℝ) n
  let a := (adj.homEquiv (ModuleCat.of ℝ ℝ) (degree (k + 1))) φ
  have ha : a ≫ (singularFunctor.obj (model n)).d (k + 1) k = 0 := by
    have h := congrArg (adj.homEquiv (ModuleCat.of ℝ ℝ) (degree k)) hφ
    rw [adj.homEquiv_naturality_right, adj.homAddEquiv_zero] at h
    exact h
  have hs : ((singularFunctor.obj (model n)).sc' (k + 2) (k + 1) k).Exact := by
    apply ((singularFunctor.obj (model n)).exactAt_iff' (k + 2) (k + 1) k
      (ChainComplex.prev ℕ (k + 1)) (ChainComplex.next_nat_succ k)).mp
    exact model_exact n k
  exact (adj.homEquiv (ModuleCat.of ℝ ℝ) (degree (k + 2))).symm
    (hs.liftFromProjective a ha)

lemma liftCycle_comp (n k : ℕ) (φ : complex.X n ⟶ complex.X (k + 1))
    (hφ : φ ≫ complex.d (k + 1) k = 0) :
    liftCycle n k φ hφ ≫ complex.d (k + 2) (k + 1) = φ := by
  let adj := singularChainComplexFunctorAdjunction (ModuleCat ℝ) n
  apply (adj.homEquiv (ModuleCat.of ℝ ℝ) (degree (k + 1))).injective
  rw [adj.homEquiv_naturality_right]
  unfold liftCycle
  dsimp only [adj]
  erw [Equiv.apply_symm_apply]
  exact ShortComplex.Exact.liftFromProjective_comp _ _ _

def homotopyZero (e : complex ⟶ complex) (he : e.f 0 = 0) : Homotopy e 0 := by
  have h1 : e.f 1 ≫ complex.d 1 0 = 0 := by
    rw [e.comm, he, comp_zero]
  refine Homotopy.mkInductive e 0 ?_ (liftCycle 1 0 (e.f 1) h1) ?_ ?_
  · simpa only [zero_comp] using he
  · simp only [comp_zero, zero_add]
    exact (liftCycle_comp 1 0 (e.f 1) h1).symm
  · intro n p
    rcases p with ⟨a, b, hab⟩
    let φ := e.f (n + 2) - complex.d (n + 2) (n + 1) ≫ b
    have hφ : φ ≫ complex.d (n + 2) (n + 1) = 0 := by
      dsimp [φ]
      rw [Preadditive.sub_comp, Category.assoc, e.comm, hab,
        Preadditive.comp_add, ← Category.assoc,
        complex.d_comp_d, zero_comp, zero_add]
      exact sub_self _
    refine ⟨liftCycle (n + 2) (n + 1) φ hφ, ?_⟩
    rw [liftCycle_comp]
    dsimp [φ]
    abel

def homotopyOfDegreeZero (f g : complex ⟶ complex) (h : f.f 0 = g.f 0) :
    Homotopy f g :=
  Homotopy.equivSubZero.symm (homotopyZero (f - g) (by simp [h]))

def transpose (f : singularFunctor ⟶ singularFunctor) : complex ⟶ complex where
  f n :=
    { app X := (f.app X).f n
      naturality X Y g := congrArg (fun k => k.f n) (f.naturality g) }
  comm' i j hij := by
    apply NatTrans.ext
    funext X
    exact (f.app X).comm i j

def naturalHomotopy (f g : singularFunctor ⟶ singularFunctor)
    (h : ∀ X, (f.app X).f 0 = (g.app X).f 0) :
    Homotopy (transpose f) (transpose g) :=
  homotopyOfDegreeZero (transpose f) (transpose g) (by
    apply NatTrans.ext
    funext Y
    exact h Y)

def homotopyApp (f g : singularFunctor ⟶ singularFunctor)
    (h : ∀ X, (f.app X).f 0 = (g.app X).f 0) (X : TopCat.{0}) :
    Homotopy (f.app X) (g.app X) where
  hom i j := ((naturalHomotopy f g h).hom i j).app X
  zero i j hij := congrArg (fun k => k.app X) ((naturalHomotopy f g h).zero i j hij)
  comm i := congrArg (fun k => k.app X) ((naturalHomotopy f g h).comm i)

def operator (s : ∀ n, degree n ⟶ degree n)
    (hs : ∀ n, s (n + 1) ≫ complex.d (n + 1) n =
      complex.d (n + 1) n ≫ s n) : singularFunctor ⟶ singularFunctor where
  app X :=
    { f n := (s n).app X
      comm' i j hij := by
        obtain rfl : j + 1 = i := hij
        exact congrArg (fun k => k.app X) (hs j) }
  naturality X Y u := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (s n).naturality u

end Problem340.SingularAcyclicModels

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularUniversalFinsupp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory Simplicial Opposite

namespace Problem340.SingularUniversalOperator

theorem operator_realSingularGenerator {n m : ℕ}
    (u : (chainsFunctor m).obj (simplex n))
    {X : Type} [TopologicalSpace X] (σ : RealSingularSimplex X n) (r : ℝ) :
    ((operator n m u).app (TopCat.of X)).hom (realSingularGenerator σ r) =
      r • ((realSingularChainMap σ σ.continuous).f m).hom u := by
  have h := congrArg (fun k : ModuleCat.of ℝ ℝ ⟶ (chainsFunctor m).obj (TopCat.of X) =>
    k.hom r) (generator_operator u (TopCat.of X)
      ((TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, map_smul, simplexMap, Equiv.apply_symm_apply,
    realSingularGenerator] using! h

@[simp]
theorem operator_finsupp_single {n m : ℕ}
    (u : (chainsFunctor m).obj (simplex n))
    {X : Type} [TopologicalSpace X] (σ : RealSingularSimplex X n) (r : ℝ) :
    ((operator n m u).app (TopCat.of X)).hom
      (singularChainsFinsuppEquiv X n (Finsupp.single σ r)) =
      r • ((realSingularChainMap σ σ.continuous).f m).hom u := by
  rw [singularChainsFinsuppEquiv_single, operator_realSingularGenerator]

end Problem340.SingularUniversalOperator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularUniversalChainMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory Simplicial Opposite

namespace Problem340.SingularUniversalOperator

def faceMap (n : ℕ) (i : Fin (n + 2)) : simplex n ⟶ simplex (n + 1) :=
  TopCat.ofHom ⟨SStd.map i.succAbove, SStd.continuous_map ℝ i.succAbove⟩

def faceSum (n : ℕ) (u : (chainsFunctor n).obj (simplex n)) :
    (chainsFunctor n).obj (simplex (n + 1)) :=
  ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val • ((chainsFunctor n).map (faceMap n i)).hom u

@[simp]
theorem operator_identity_apply {n m : ℕ} (u : (chainsFunctor m).obj (simplex n)) (r : ℝ) :
    ((operator n m u).app (simplex n)).hom ((identityGenerator n).hom r) = r • u := by
  have h := congrArg (fun k : ModuleCat.of ℝ ℝ ⟶ (chainsFunctor m).obj (simplex n) =>
    k.hom r) (identityGenerator_operator u)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply] using! h

theorem operator_identity_boundary (n : ℕ) (u : (chainsFunctor n).obj (simplex n)) :
    ((operator n n u).app (simplex (n + 1))).hom
      (((realSingularChainComplex (simplex (n + 1))).d (n + 1) n).hom
        ((identityGenerator (n + 1)).hom 1)) = faceSum n u := by
  change ((operator n n u).app (simplex (n + 1))).hom
    (((realSingularChainComplex (simplex (n + 1))).d (n + 1) n).hom
      (SingularChainFormulas.simplexChain (ContinuousMap.id _))) = _
  rw [SingularChainFormulas.simplexChain_boundary_real]
  erw [map_sum]
  simp only [map_smul, faceSum]
  apply Finset.sum_congr rfl
  intro i _
  erw [map_smul]
  congr 1
  change ((operator n n u).app (simplex (n + 1))).hom
    (realSingularGenerator (SingularChainFormulas.face (ContinuousMap.id _) i) 1) = _
  rw [operator_realSingularGenerator, one_smul]
  rfl

def BoundaryCompatible (u : ∀ n, (chainsFunctor n).obj (simplex n)) : Prop :=
  ∀ n, ((realSingularChainComplex (simplex (n + 1))).d (n + 1) n).hom (u (n + 1)) =
    faceSum n (u n)

theorem operator_comm (u : ∀ n, (chainsFunctor n).obj (simplex n))
    (hu : BoundaryCompatible u) (n : ℕ) :
    operator (n + 1) (n + 1) (u (n + 1)) ≫ SingularAcyclicModels.complex.d (n + 1) n =
      SingularAcyclicModels.complex.d (n + 1) n ≫ operator n n (u n) := by
  apply natTrans_ext_apply
  change ((realSingularChainComplex (simplex (n + 1))).d (n + 1) n).hom
      (((operator (n + 1) (n + 1) (u (n + 1))).app (simplex (n + 1))).hom
        ((identityGenerator (n + 1)).hom 1)) =
    ((operator n n (u n)).app (simplex (n + 1))).hom
      (((realSingularChainComplex (simplex (n + 1))).d (n + 1) n).hom
        ((identityGenerator (n + 1)).hom 1))
  rw [operator_identity_apply, one_smul, operator_identity_boundary]
  exact hu n

def chainMap (u : ∀ n, (chainsFunctor n).obj (simplex n)) (hu : BoundaryCompatible u) :
    SingularAcyclicModels.singularFunctor ⟶ SingularAcyclicModels.singularFunctor :=
  SingularAcyclicModels.operator (fun n => operator n n (u n)) (operator_comm u hu)

@[simp]
theorem chainMap_app_f (u : ∀ n, (chainsFunctor n).obj (simplex n))
    (hu : BoundaryCompatible u) (X : TopCat) (n : ℕ) :
    ((chainMap u hu).app X).f n = (operator n n (u n)).app X := rfl

theorem chainMap_zero (u : ∀ n, (chainsFunctor n).obj (simplex n))
    (hu : BoundaryCompatible u) (hzero : u 0 = (identityGenerator 0).hom 1) (X : TopCat) :
    ((chainMap u hu).app X).f 0 = 𝟙 ((SingularAcyclicModels.singularFunctor.obj X).X 0) := by
  have h : operator 0 0 (u 0) = 𝟙 (chainsFunctor 0) := by
    apply natTrans_ext_apply
    rw [operator_identity_apply, one_smul, hzero]
    rfl
  exact congrArg (fun k => k.app X) h

end Problem340.SingularUniversalOperator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ActualSingularSubdivisionMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.ActualSingularSubdivision

theorem subdivisionChain_boundaryCompatible :
    SingularUniversalOperator.BoundaryCompatible subdivisionChain := by
  intro n
  exact subdivisionChain_boundary n

def subdivisionChainMap :
    SingularAcyclicModels.singularFunctor ⟶ SingularAcyclicModels.singularFunctor :=
  SingularUniversalOperator.chainMap subdivisionChain subdivisionChain_boundaryCompatible

@[simp]
theorem subdivisionChainMap_f (X : TopCat) (n : ℕ) :
    (subdivisionChainMap.app X).f n = (subdivision n).app X := rfl

@[simp]
theorem subdivisionChainMap_zero (X : TopCat) :
    (subdivisionChainMap.app X).f 0 =
      𝟙 ((SingularAcyclicModels.singularFunctor.obj X).X 0) :=
  SingularUniversalOperator.chainMap_zero subdivisionChain subdivisionChain_boundaryCompatible
    subdivisionChain_zero X

abbrev chainMap := subdivisionChainMap

end Problem340.ActualSingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Clock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Clock

def profileCutoff : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 36 / 25
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoff (x : ℝ) : ℝ := profileCutoff (x ^ 2)

lemma cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x := profileCutoff.nonneg

lemma cutoff_le_one (x : ℝ) : cutoff x ≤ 1 := profileCutoff.le_one

lemma cutoff_neg (x : ℝ) : cutoff (-x) = cutoff x := by simp [cutoff]

lemma contDiff_cutoff {n : ℕ∞} : ContDiff ℝ n cutoff :=
  profileCutoff.contDiff.comp (contDiff_id.pow 2)

def profile (s : ℝ) : ℝ := profileCutoff s * s / 4 + 1 - profileCutoff s

def localBarrier (x : ℝ) : ℝ := cutoff x * x ^ 2 / 4 + 1 - cutoff x

lemma localBarrier_neg (x : ℝ) : localBarrier (-x) = localBarrier x := by
  simp [localBarrier, cutoff_neg]

lemma contDiff_localBarrier {n : ℕ∞} : ContDiff ℝ n localBarrier := by
  unfold localBarrier
  exact (((contDiff_cutoff.mul (contDiff_id.pow 2)).div_const 4).add contDiff_const).sub
    contDiff_cutoff

def coordinate (t : ℝ) : ℝ := 30 * Real.sin (Real.pi * (t - 50) / 100)

lemma contDiff_coordinate {n : ℕ∞} : ContDiff ℝ n coordinate := by
  unfold coordinate
  fun_prop

lemma coordinate_add_period (t : ℝ) : coordinate (t + 100) = -coordinate t := by
  unfold coordinate
  have heq : Real.pi * (t + 100 - 50) / 100 =
      Real.pi * (t - 50) / 100 + Real.pi := by ring
  rw [heq, Real.sin_add_pi]
  ring

def barrier (t : ℝ) : ℝ := localBarrier (coordinate t)

lemma contDiff_barrier {n : ℕ∞} : ContDiff ℝ n barrier :=
  contDiff_localBarrier.comp contDiff_coordinate

lemma barrier_periodic : Function.Periodic barrier 100 := by
  intro t
  simp only [barrier, coordinate_add_period, localBarrier_neg]

def ambientBarrier (x : EuclideanSpace ℝ (Fin 2)) : ℝ := profile (450 * (1 + x 0))

def increment (t e : ℝ) : ℝ := barrier t + (1 - barrier t) * e

@[simp] lemma increment_zero (t : ℝ) : increment t 0 = barrier t := by
  simp [increment]

@[simp] lemma increment_one (t : ℝ) : increment t 1 = 1 := by
  simp [increment]

lemma increment_periodic (e : ℝ) : Function.Periodic (fun t => increment t e) 100 := by
  intro t
  simp only [increment, barrier_periodic t]

end Problem340.Clock

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SphereCutoffs

def clockGateAmbient (x : SphereAmbient) : ℝ :=
  Real.smoothTransition ((25 * x 2 + 15) / 8)

def preparationCutoffAmbient (x : SphereAmbient) : ℝ :=
  Real.smoothTransition (5 * x 2 + 4) *
    Real.smoothTransition (1 - 2 * x 2)

def clockGate (x : StandardSphere2) : ℝ := clockGateAmbient x.1

@[fun_prop]
theorem contDiff_clockGateAmbient {n : ℕ∞} : ContDiff ℝ n clockGateAmbient := by
  have hh : ContDiff ℝ n (fun x : SphereAmbient => x 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul hh).add contDiff_const).div_const 8)

@[fun_prop]
theorem contDiff_preparationCutoffAmbient {n : ℕ∞} :
    ContDiff ℝ n preparationCutoffAmbient := by
  have hh : ContDiff ℝ n (fun x : SphereAmbient => x 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff
  exact (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul hh).add contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp
      (contDiff_const.sub (contDiff_const.mul hh)))

@[continuity, fun_prop]
theorem continuous_clockGate : Continuous clockGate :=
  (@contDiff_clockGateAmbient 0).continuous.comp continuous_subtype_val

end Problem340.SphereCutoffs

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereDoubling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SphereDoubling

abbrev Ambient := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := Metric.sphere (0 : Ambient) (1 : ℝ)

def ambientMap (x : Ambient) : Ambient :=
  !₂[(x 0 ^ 2 - x 1 ^ 2) / (1 + x 2 ^ 2),
     (2 * x 0 * x 1) / (1 + x 2 ^ 2),
     (2 * x 2) / (1 + x 2 ^ 2)]

lemma denominator_pos (x : Ambient) : 0 < 1 + x 2 ^ 2 := by positivity

lemma contDiff_ambientMap (n : WithTop ℕ∞) : ContDiff ℝ n ambientMap := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ n (fun x : Ambient => (x 0 ^ 2 - x 1 ^ 2) / (1 + x 2 ^ 2))
    fun_prop (disch := intro x; exact ne_of_gt (denominator_pos x))
  · change ContDiff ℝ n (fun x : Ambient => (2 * x 0 * x 1) / (1 + x 2 ^ 2))
    fun_prop (disch := intro x; exact ne_of_gt (denominator_pos x))
  · change ContDiff ℝ n (fun x : Ambient => (2 * x 2) / (1 + x 2 ^ 2))
    fun_prop (disch := intro x; exact ne_of_gt (denominator_pos x))

lemma sphere_equation (x : Sphere) :
    (x.val 0) ^ 2 + (x.val 1) ^ 2 + (x.val 2) ^ 2 = 1 := by
  have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hn := EuclideanSpace.real_norm_sq_eq x.val
  simpa [hx, Fin.sum_univ_succ, add_assoc] using hn.symm

lemma ambientMap_mem_sphere (x : Sphere) : ambientMap x.val ∈ Metric.sphere (0 : Ambient) 1 := by
  have hx := sphere_equation x
  have hd := ne_of_gt (denominator_pos x.val)
  have hn : ‖ambientMap x.val‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ, ambientMap]
    field_simp
    have hsq := congrArg (fun t : ℝ => t ^ 2) hx
    nlinarith
  have hnorm : ‖ambientMap x.val‖ = 1 := by nlinarith [norm_nonneg (ambientMap x.val)]
  simpa using hnorm

def sphereMap (x : Sphere) : Sphere := ⟨ambientMap x.val, ambientMap_mem_sphere x⟩

lemma continuous_sphereMap : Continuous sphereMap := by
  exact ((contDiff_ambientMap 1).continuous.comp continuous_subtype_val).subtype_mk _

def stereoCoordinate (x : Ambient) : ℂ :=
  ((x 0 : ℂ) + Complex.I * (x 1 : ℂ)) / (1 - (x 2 : ℂ))

lemma ambientMap_third_ne_one {x : Ambient} (hx : x 2 ≠ 1) :
    ambientMap x 2 ≠ 1 := by
  intro h
  change (2 * x 2) / (1 + x 2 ^ 2) = 1 at h
  have h' := (div_eq_one_iff_eq (ne_of_gt (denominator_pos x))).mp h
  apply hx
  nlinarith [sq_nonneg (x 2 - 1)]

def north : Sphere := ⟨!₂[0, 0, 1], by
  norm_num [Metric.mem_sphere, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

def south : Sphere := ⟨!₂[0, 0, -1], by
  norm_num [Metric.mem_sphere, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

@[simp] lemma sphereMap_north : sphereMap north = north := by
  apply Subtype.ext
  ext i
  fin_cases i <;> norm_num [sphereMap, ambientMap, north, Matrix.cons_val_two]

@[simp] lemma sphereMap_south : sphereMap south = south := by
  apply Subtype.ext
  ext i
  fin_cases i <;> norm_num [sphereMap, ambientMap, south, Matrix.cons_val_two]

lemma eq_north_iff (x : Sphere) : x = north ↔ x.val 2 = 1 := by
  constructor
  · intro h
    simp [h, north, Matrix.cons_val_two]
  · intro h
    have he := sphere_equation x
    have h0 : x.val 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x.val 1)]
    have h1 : x.val 1 ^ 2 = 0 := by nlinarith [sq_nonneg (x.val 0)]
    have h0' := sq_eq_zero_iff.mp h0
    have h1' := sq_eq_zero_iff.mp h1
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [north, h0', h1', h, Matrix.cons_val_two]

@[simp] lemma sphereMap_eq_north_iff (x : Sphere) : sphereMap x = north ↔ x = north := by
  constructor
  · intro h
    apply (eq_north_iff x).mpr
    by_contra hx
    apply ambientMap_third_ne_one hx
    exact (eq_north_iff (sphereMap x)).mp h
  · intro h
    simp [h]

@[simp] lemma iterate_sphereMap_eq_north_iff (n : ℕ) (x : Sphere) :
    (sphereMap^[n]) x = north ↔ x = north := by
  induction n with
  | zero => simp
  | succ n ih => simpa [Function.iterate_succ_apply'] using ih

end Problem340.SphereDoubling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.AmbientPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.AmbientPrediction

abbrev Ambient := ℝ × SphereAmbient

def predictor (x : Ambient) : Ambient :=
  (x.1 + Clock.increment x.1 (SphereCutoffs.clockGateAmbient x.2),
    SphereDoubling.ambientMap x.2)

def cylinder : Set Ambient := Set.univ ×ˢ Metric.sphere (0 : SphereAmbient) 1

def clockPrediction (m : ℕ) (x : Ambient) : ℝ := (predictor^[m] x).1

end Problem340.AmbientPrediction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.AmbientRetraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContDiff

namespace Problem340.AmbientRetraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalize (x : E) : E := ‖x‖⁻¹ • x

@[simp]
theorem norm_smul_normalize (x : E) : ‖x‖ • normalize x = x := by
  by_cases hx : x = 0
  · simp [hx, normalize]
  · rw [normalize, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

def cylinder (x : ℝ × E) : ℝ × E := (x.1, normalize x.2)

def cylinderDomain : Set (ℝ × E) := {x | (1 / 2 : ℝ) < ‖x.2‖}

end Problem340.AmbientRetraction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.C1Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

def HasLocalC1Extension {X E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : X → E) (f : X → F) : Prop :=
  ∀ x, ∃ U : Set E, IsOpen U ∧ e x ∈ U ∧
    ∃ F : E → F, ContDiffOn ℝ 1 F U ∧ ∀ y, e y ∈ U → f y = F (e y)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace Problem340

def complexClockLinearIsometry : ℂ ≃ₗᵢ[ℝ] ClockAmbient :=
  Complex.orthonormalBasisOneI.repr

@[simp]
theorem complexClockLinearIsometry_apply (z : ℂ) :
    complexClockLinearIsometry z = ![z.re, z.im] := rfl

def circleClockHomeomorph : Circle ≃ₜ StandardClock :=
  complexClockLinearIsometry.toHomeomorph.subtype fun z => by
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔
      complexClockLinearIsometry z ∈ Metric.sphere (0 : ClockAmbient) 1
    simp only [Metric.mem_sphere, dist_zero_right,
      complexClockLinearIsometry.norm_map]

@[simp]
theorem circleClockHomeomorph_coe (z : Circle) :
    (circleClockHomeomorph z).1 = complexClockLinearIsometry (z : ℂ) := rfl

def clockHomeomorph : AddCircle (100 : ℝ) ≃ₜ StandardClock :=
  (AddCircle.homeomorphCircle (by norm_num : (100 : ℝ) ≠ 0)).trans
    circleClockHomeomorph

@[simp]
theorem clockHomeomorph_apply (t : AddCircle (100 : ℝ)) :
    clockHomeomorph t = circleClockHomeomorph (AddCircle.toCircle t) := by
  simp only [clockHomeomorph, Homeomorph.trans_apply, AddCircle.homeomorphCircle_apply]

def clockParam (t : ℝ) : ClockAmbient :=
  complexClockLinearIsometry (Complex.exp ((2 * Real.pi / 100 * t : ℝ) * Complex.I))

@[simp]
theorem clockHomeomorph_coe (t : ℝ) :
    (clockHomeomorph (t : AddCircle (100 : ℝ))).1 = clockParam t := by
  simp only [clockHomeomorph_apply, circleClockHomeomorph_coe,
    AddCircle.toCircle_apply_mk, Circle.coe_exp, clockParam]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Conjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

def conjugateMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (f : X → X) : Y → Y := fun y => e (f (e.symm y))

@[simp] theorem conjugateMap_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (f : X → X) (x : X) :
    conjugateMap e f (e x) = e (f x) := by
  simp [conjugateMap]

@[simp] theorem conjugateMap_symm {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (f : X → X) :
    conjugateMap e.symm (conjugateMap e f) = f := by
  funext x
  simp [conjugateMap]

theorem continuous_conjugateMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {f : X → X} (hf : Continuous f) : Continuous (conjugateMap e f) :=
  e.continuous.comp (hf.comp e.symm.continuous)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologyTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[simp] theorem realHomologyMap_id (n : ℕ) :
    realHomologyMap n (id : X → X) continuous_id = LinearMap.id := by
  change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)).map (𝟙 (TopCat.of X))).hom = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem realHomologyMap_comp (n : ℕ) (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g) :
    realHomologyMap n (g ∘ f) (hg.comp hf) =
      (realHomologyMap n g hg).comp (realHomologyMap n f hf) := by
  change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)).map
      (TopCat.ofHom (continuousMapOf f hf) ≫ TopCat.ofHom (continuousMapOf g hg))).hom = _
  rw [Functor.map_comp]
  rfl

theorem realHomologyMap_surjective_of_section (n : ℕ)
    (p : X → Y) (s : Y → X) (hp : Continuous p) (hs : Continuous s)
    (hps : Function.LeftInverse p s) :
    Function.Surjective (realHomologyMap n p hp) := by
  intro v
  refine ⟨realHomologyMap n s hs v, ?_⟩
  have hcomp : p ∘ s = id := funext hps
  have hmap := realHomologyMap_comp n s p hs hp
  simp only [hcomp, realHomologyMap_id] at hmap
  exact congrArg (fun k => k v) hmap.symm

theorem realHomologyMap_injective_of_retraction (n : ℕ)
    (s : Y → X) (p : X → Y) (hs : Continuous s) (hp : Continuous p)
    (hps : Function.LeftInverse p s) :
    Function.Injective (realHomologyMap n s hs) := by
  have hcomp : p ∘ s = id := funext hps
  have hmap := realHomologyMap_comp n s p hs hp
  simp only [hcomp, realHomologyMap_id] at hmap
  apply Function.LeftInverse.injective (g := realHomologyMap n p hp)
  intro v
  exact congrArg (fun k => k v) hmap.symm

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologyConjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def realHomologyEquiv (n : ℕ) (e : X ≃ₜ Y) :
    RealSingularHomology n X ≃ₗ[ℝ] RealSingularHomology n Y :=
  LinearEquiv.ofBijective (realHomologyMap n e e.continuous)
    ⟨realHomologyMap_injective_of_retraction n e e.symm e.continuous
      e.symm.continuous (fun x => e.symm_apply_apply x),
    realHomologyMap_surjective_of_section n e e.symm e.continuous
      e.symm.continuous (fun y => e.apply_symm_apply y)⟩

@[simp] theorem realHomologyEquiv_apply (n : ℕ) (e : X ≃ₜ Y)
    (v : RealSingularHomology n X) :
    realHomologyEquiv n e v = realHomologyMap n e e.continuous v := rfl

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.CircleClockDoubling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.CircleClockDoubling

abbrev AngularCircle := AddCircle (1 : ℝ)

def homeomorph : AngularCircle ≃ₜ StandardClock :=
  (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).trans
    circleClockHomeomorph

@[simp] theorem homeomorph_apply (t : AngularCircle) :
    homeomorph t = circleClockHomeomorph (AddCircle.toCircle t) := by
  simp only [homeomorph, Homeomorph.trans_apply, AddCircle.homeomorphCircle_apply]

def angularDouble (t : AngularCircle) : AngularCircle := t + t

theorem continuous_angularDouble : Continuous angularDouble :=
  continuous_id.add continuous_id

def clockDouble (x : StandardClock) : StandardClock :=
  circleClockHomeomorph ((circleClockHomeomorph.symm x) ^ 2)

theorem continuous_clockDouble : Continuous clockDouble :=
  circleClockHomeomorph.continuous.comp (circleClockHomeomorph.symm.continuous.pow 2)

@[simp] theorem homeomorph_angularDouble (t : AngularCircle) :
    homeomorph (angularDouble t) = clockDouble (homeomorph t) := by
  simp only [homeomorph_apply, angularDouble, AddCircle.toCircle_add,
    clockDouble, Homeomorph.symm_apply_apply, pow_two]

@[simp] theorem clockDouble_coe (x : StandardClock) :
    (clockDouble x).1 = complexClockLinearIsometry
      ((complexClockLinearIsometry.symm x.1) ^ 2) := by
  change complexClockLinearIsometry (((circleClockHomeomorph.symm x : Circle) ^ 2 : Circle) : ℂ) = _
  simp only [Circle.coe_pow]
  rfl

def homologyEquiv (n : ℕ) :
    RealSingularHomology n AngularCircle ≃ₗ[ℝ] RealSingularHomology n StandardClock :=
  realHomologyEquiv n homeomorph

@[simp] theorem homologyEquiv_apply (n : ℕ) (v : RealSingularHomology n AngularCircle) :
    homologyEquiv n v = realHomologyMap n homeomorph homeomorph.continuous v := rfl

end Problem340.CircleClockDoubling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.CircleDoublingChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.CircleDoublingChains

abbrev Circle := AddCircle (1 : ℝ)
abbrev singularSet := TopCat.toSSet.obj (TopCat.of Circle)
abbrev coefficients := ModuleCat.of ℝ ℝ
abbrev chains := realSingularChainComplex Circle

def loopMap : C(SStd ℝ (Fin 2), Circle) :=
  ⟨fun p => (p 1 : Circle),
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      (SStd.continuous_weights_apply ℝ 1)⟩

def triangleMap : C(SStd ℝ (Fin 3), Circle) :=
  ⟨fun p => (p 1 + 2 * p 2 : ℝ),
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((SStd.continuous_weights_apply ℝ 1).add
        (continuous_const.mul (SStd.continuous_weights_apply ℝ 2)))⟩

def doubling : Circle → Circle := fun x => x + x

lemma continuous_doubling : Continuous doubling := by
  exact continuous_id.add continuous_id

def doublingMap : C(Circle, Circle) := ⟨doubling, continuous_doubling⟩

def loopSimplex : singularSet _⦋1⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) _).symm loopMap

def triangleSimplex : singularSet _⦋2⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) _).symm triangleMap

def doubledLoopSimplex : singularSet _⦋1⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) _).symm (doublingMap.comp loopMap)

lemma loop_endpoints : singularSet.δ 0 loopSimplex = singularSet.δ 1 loopSimplex := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) _).injective
  ext p
  change SStd ℝ (Fin 1) at p
  change ((SStd.map (0 : Fin 2).succAbove p) 1 : Circle) =
    ((SStd.map (1 : Fin 2).succAbove p) 1 : Circle)
  have h0 : (SStd.map (0 : Fin 2).succAbove p) 1 = 1 := by
    have hf : (Finset.univ.filter fun x : Fin 1 =>
        (0 : Fin 2).succAbove x = (1 : Fin 2)) = {0} := by decide
    rw [RealSimplex.map_apply, hf, Finset.sum_singleton]
    simpa only [Fin.sum_univ_one] using p.total_of_fintype
  have h1 : (SStd.map (1 : Fin 2).succAbove p) 1 = 0 := by
    have hf : (Finset.univ.filter fun x : Fin 1 =>
        (1 : Fin 2).succAbove x = (1 : Fin 2)) = ∅ := by decide
    rw [RealSimplex.map_apply, hf, Finset.sum_empty]
  rw [h0, h1, AddCircle.coe_period, AddCircle.coe_zero]

def loopChain : coefficients ⟶ chains.X 1 := singularSet.ιChainComplex loopSimplex

def triangleChain : coefficients ⟶ chains.X 2 := singularSet.ιChainComplex triangleSimplex

def doubledLoopChain : coefficients ⟶ chains.X 1 :=
  singularSet.ιChainComplex doubledLoopSimplex

lemma loopChain_boundary : loopChain ≫ chains.d 1 0 = 0 := by
  change singularSet.ιChainComplex loopSimplex ≫
    (singularSet.chainComplex coefficients).d 1 0 = 0
  rw [SSet.ιChainComplex_d]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val • singularSet.ιChainComplex (singularSet.δ i loopSimplex)) = 0
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_smul, loop_endpoints, add_neg_cancel]

def loop : chains.X 1 := loopChain.hom 1

def triangle : chains.X 2 := triangleChain.hom 1

lemma loop_boundary : (chains.d 1 0).hom loop = 0 := by
  exact ConcreteCategory.congr_hom loopChain_boundary (1 : ℝ)

lemma loop_cycle_sc : (chains.sc 1).g.hom loop = 0 := by
  change (chains.d 1 ((ComplexShape.down ℕ).next 1)).hom loop = 0
  rw [ChainComplex.next_nat_succ 0]
  exact loop_boundary

def loopClass : RealSingularHomology 1 Circle :=
  moduleHomologyClass (chains.sc 1) loop loop_cycle_sc

end Problem340.CircleDoublingChains

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSimplexCircleLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SingularSimplexCircleLift

abbrev Circle := AddCircle (1 : ℝ)
abbrev Simplex (n : ℕ) := SStd ℝ (Fin (n + 1))

theorem exists_lift (n : ℕ) (σ : C(Simplex n, Circle)) :
    ∃ F : C(Simplex n, ℝ), ∀ x, (F x : Circle) = σ x := by
  let : ContractibleSpace (Simplex n) :=
    RealSimplex.contractible
  let : LocallyPathConnectedSpace (Simplex n) :=
    RealSimplex.locallyPathConnected
  let x : Simplex n := SStd.single 0
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (σ x)
  obtain ⟨F, hF, -⟩ := (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
    σ x y hy
  exact ⟨F, fun z => congrFun hF.2 z⟩

def lift {n : ℕ} (σ : C(Simplex n, Circle)) : C(Simplex n, ℝ) :=
  Classical.choose (exists_lift n σ)

@[simp] theorem coe_lift {n : ℕ} (σ : C(Simplex n, Circle)) (x : Simplex n) :
    (lift σ x : Circle) = σ x :=
  Classical.choose_spec (exists_lift n σ) x

def increment {n : ℕ} (σ : C(Simplex n, Circle)) (x y : Simplex n) : ℝ :=
  lift σ y - lift σ x

@[simp] theorem increment_self {n : ℕ} (σ : C(Simplex n, Circle)) (x : Simplex n) :
    increment σ x x = 0 := sub_self _

end Problem340.SingularSimplexCircleLift

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.CircleWindingCocycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.CircleWinding

abbrev CircleSpace := AddCircle (1 : ℝ)
abbrev singularSet := TopCat.toSSet.obj (TopCat.of CircleSpace)
abbrev coefficients := ModuleCat.of ℝ ℝ
abbrev chains := singularSet.chainComplex coefficients

def cochainOfIncrement (w : singularSet _⦋1⦌ → ℝ) : chains.X 1 ⟶ coefficients :=
  Sigma.desc (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ ℝ (w σ)))

@[simp] theorem generator_cochainOfIncrement (w : singularSet _⦋1⦌ → ℝ)
    (σ : singularSet _⦋1⦌) :
    singularSet.ιChainComplex σ ≫ cochainOfIncrement w =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ ℝ (w σ)) := by
  exact Sigma.ι_desc _ _

def simplexIncrement (σ : singularSet _⦋1⦌) : ℝ :=
  SingularSimplexCircleLift.increment
    ((TopCat.of CircleSpace).toSSetObjEquiv _ σ)
    (SStd.single 0) (SStd.single 1)

def windingCochain : chains.X 1 ⟶ coefficients :=
  cochainOfIncrement simplexIncrement

end Problem340.CircleWinding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockAtInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340
namespace ClockAtInfinity

abbrev Clock := AddCircle (100 : ℝ)

def step (t : Clock) : Clock := t + ((1 : ℝ) : Clock)

@[continuity, fun_prop]
theorem continuous_step : Continuous step :=
  continuous_id.add continuous_const

end ClockAtInfinity
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

def orbitClockLift {X : Type*} (f : X → X) (h : X → ℝ)
    (x : X) (t₀ : ℝ) (n : ℕ) : ℝ :=
  t₀ + ∑ i ∈ Finset.range n, h (f^[i] x)

@[simp] theorem orbitClockLift_zero {X : Type*} (f : X → X) (h : X → ℝ)
    (x : X) (t₀ : ℝ) : orbitClockLift f h x t₀ 0 = t₀ := by
  simp [orbitClockLift]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockLocalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContDiff

namespace Problem340

def clockLocalLift (t₀ : ℝ) (x : ClockAmbient) : ℝ :=
  t₀ + (100 / (2 * Real.pi)) *
    Complex.arg (complexClockLinearIsometry.symm x /
      Complex.exp ((2 * Real.pi / 100 * t₀ : ℝ) * Complex.I))

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.ClockModel

def circleHomeomorph : Circle ≃ₜ StandardClock :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype (by
    intro z
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔
      Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere (0 : ClockAmbient) 1
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map])

@[simp] theorem circleHomeomorph_val (z : Circle) :
    (circleHomeomorph z).val = Complex.orthonormalBasisOneI.repr (z : ℂ) := rfl

@[simp] theorem circleHomeomorph_coord_zero (z : Circle) :
    (circleHomeomorph z).val 0 = (z : ℂ).re := by
  simp [circleHomeomorph_val, Complex.orthonormalBasisOneI_repr_apply]

@[simp] theorem circleHomeomorph_coord_one (z : Circle) :
    (circleHomeomorph z).val 1 = (z : ℂ).im := by
  simp [circleHomeomorph_val, Complex.orthonormalBasisOneI_repr_apply]

def clockHomeomorph : AddCircle (100 : ℝ) ≃ₜ StandardClock :=
  (AddCircle.homeomorphCircle (T := (100 : ℝ)) (by norm_num)).trans circleHomeomorph

def prependHomeomorph (q : ℕ) (S : Type*) [TopologicalSpace S] :
    S × (Fin q → S) ≃ₜ (Fin (q + 1) → S) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, fun i => x i.succ)
  left_inv p := by cases p; rfl
  right_inv x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd
  continuous_invFun :=
    (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)

@[simp] theorem prependHomeomorph_zero (q : ℕ) {S : Type*} [TopologicalSpace S]
    (p : S × (Fin q → S)) : prependHomeomorph q S p 0 = p.1 := rfl

@[simp] theorem prependHomeomorph_succ (q : ℕ) {S : Type*} [TopologicalSpace S]
    (p : S × (Fin q → S)) (i : Fin q) :
    prependHomeomorph q S p i.succ = p.2 i := rfl

def productHomeomorph (q : ℕ) {S : Type*} [TopologicalSpace S]
    (eSphere : S ≃ₜ StandardSphere2) :
    (AddCircle (100 : ℝ) × (S × (Fin q → S))) ≃ₜ CounterexampleManifold q :=
  clockHomeomorph.prodCongr
    ((prependHomeomorph q S).trans (Homeomorph.piCongrRight fun _ => eSphere))

@[simp] theorem productHomeomorph_clock (q : ℕ) {S : Type*} [TopologicalSpace S]
    (eSphere : S ≃ₜ StandardSphere2)
    (x : AddCircle (100 : ℝ) × (S × (Fin q → S))) :
    (productHomeomorph q eSphere x).1 = clockHomeomorph x.1 := rfl

@[simp] theorem productHomeomorph_main (q : ℕ) {S : Type*} [TopologicalSpace S]
    (eSphere : S ≃ₜ StandardSphere2)
    (x : AddCircle (100 : ℝ) × (S × (Fin q → S))) :
    (productHomeomorph q eSphere x).2 0 = eSphere x.2.1 := rfl

@[simp] theorem productHomeomorph_register (q : ℕ) {S : Type*} [TopologicalSpace S]
    (eSphere : S ≃ₜ StandardSphere2)
    (x : AddCircle (100 : ℝ) × (S × (Fin q → S))) (i : Fin q) :
    (productHomeomorph q eSphere x).2 i.succ = eSphere (x.2.2 i) := rfl

end Problem340.ClockModel

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Set
open scoped Topology OnePoint

namespace Problem340.Clock

structure LiftedOrbit (t e : ℕ → ℝ) : Prop where
  cutoff_nonneg : ∀ n, 0 ≤ e n
  cutoff_le_one : ∀ n, e n ≤ 1
  update : ∀ n, t (n + 1) = t n + increment (t n) (e n)

end Problem340.Clock

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockPeriodization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace Problem340.ClockPeriodization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def periodize (P : ℝ) (f : ℝ × E → F) (x : ℝ × E) : F :=
  ∑' k : ℤ, f (x.1 - (k : ℝ) * P, x.2)

theorem locallyFinite_clockIntervals {P : ℝ} (hP : 0 < P) (a b : ℝ) :
    LocallyFinite (fun k : ℤ => Icc ((k : ℝ) * P + a) ((k : ℝ) * P + b)) := by
  apply locallyFinite_Icc_of_tendsto
  · exact (tendsto_intCast_atTop_atTop.atTop_mul_const hP).atTop_add tendsto_const_nhds
  · exact ((tendsto_intCast_atBot_iff.mpr tendsto_id).atBot_mul_const hP).atBot_add
      tendsto_const_nhds

end Problem340.ClockPeriodization

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.GainProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

def gainBump : ContDiffBump (51 : ℝ) where
  rIn := 44
  rOut := 89 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def gainProfile (L : ℝ) (t : ℝ) : ℝ := L * gainBump t

lemma gainProfile_contDiff (L : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (gainProfile L) :=
  contDiff_const.mul gainBump.contDiff

lemma gainProfile_zero_outside {L t : ℝ} (ht : t ∉ Set.Ioo (6 : ℝ) 96) :
    gainProfile L t = 0 := by
  have hb : gainBump t = 0 := by
    apply gainBump.zero_of_le_dist
    rw [Real.dist_eq]
    change (89 / 2 : ℝ) ≤ |t - 51|
    simp only [Set.mem_Ioo, not_and_or, not_lt] at ht
    rcases ht with ht | ht
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  simp [gainProfile, hb]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

def periodicGain (L : ℝ) (t : ℝ) : ℝ :=
  ClockPeriodization.periodize 100 (fun x : ℝ × ℝ => gainProfile L x.1) (t, 0)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Function
open scoped Topology

namespace Problem340
namespace ClockQuotient

variable {E F : Type*}

def periodize [AddCommMonoid F] (P : ℝ) (f : ℝ × E → F) (x : ℝ × E) : F :=
  ∑ᶠ k : ℤ, f (x.1 - (k : ℝ) * P, x.2)

lemma periodic_periodize [AddCommMonoid F] (P : ℝ) (f : ℝ × E → F) (z : E) :
    Periodic (fun t => periodize P f (t, z)) P := by
  intro t
  unfold periodize
  refine finsum_eq_of_bijective (fun k : ℤ => k - 1) ?_ ?_
  · constructor
    · intro a b h
      dsimp at h
      omega
    · intro a
      exact ⟨a + 1, by simp⟩
  · intro k
    apply congrArg f
    apply Prod.ext
    · simp only [Int.cast_sub, Int.cast_one]
      ring
    · rfl

lemma locallyFinite_translated_strips [TopologicalSpace E]
    {P : ℝ} (hP : 0 < P) (a b : ℝ) :
    LocallyFinite (fun k : ℤ =>
      {x : ℝ × E | x.1 - (k : ℝ) * P ∈ Icc a b}) := by
  have hl := (ClockPeriodization.locallyFinite_clockIntervals hP a b).preimage_continuous
    (continuous_fst : Continuous (Prod.fst : ℝ × E → ℝ))
  refine hl.subset ?_
  intro k x hx
  change (k : ℝ) * P + a ≤ x.1 ∧ x.1 ≤ (k : ℝ) * P + b
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma locallyFinite_translated_supports [TopologicalSpace E] [Zero F]
    {P a b : ℝ} {f : ℝ × E → F} (hP : 0 < P)
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    LocallyFinite (fun k : ℤ => support (fun x : ℝ × E =>
      f (x.1 - (k : ℝ) * P, x.2))) := by
  refine (locallyFinite_translated_strips hP a b).subset ?_
  intro k x hx
  exact hsupp _ hx

lemma continuous_periodize [TopologicalSpace E]
    [AddCommMonoid F] [TopologicalSpace F] [ContinuousAdd F]
    {P a b : ℝ} {f : ℝ × E → F}
    (hP : 0 < P) (hf : Continuous f)
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    Continuous (periodize P f) := by
  exact continuous_finsum
    (fun k => hf.comp ((continuous_fst.sub continuous_const).prodMk continuous_snd))
    (locallyFinite_translated_supports hP hsupp)

lemma periodize_eq_on_fundamental_strip [AddCommMonoid F]
    {P : ℝ} {f : ℝ × E → F} (hP : 0 < P)
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 P)
    {t : ℝ} (ht : t ∈ Icc 0 P) (z : E) :
    periodize P f (t, z) = f (t, z) := by
  unfold periodize
  have hzero : ∀ k : ℤ, k ≠ 0 → f (t - (k : ℝ) * P, z) = 0 := by
    intro k hk
    by_contra hne
    have hi := hsupp (t - (k : ℝ) * P, z) hne
    rcases lt_or_gt_of_ne hk with hkneg | hkpos
    · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have hmul := mul_le_mul_of_nonneg_right hk1 hP.le
      linarith [hi.2, ht.1]
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hmul := mul_le_mul_of_nonneg_right hk1 hP.le
      linarith [hi.1, ht.2]
  simpa using finsum_eq_single (fun k : ℤ => f (t - (k : ℝ) * P, z)) 0 hzero

def liftPeriodic {P : ℝ} (f : ℝ × E → F)
    (hf : ∀ z, Periodic (fun t => f (t, z)) P) (x : AddCircle P × E) : F :=
  (hf x.2).lift x.1

@[simp] lemma liftPeriodic_coe {P : ℝ} (f : ℝ × E → F)
    (hf : ∀ z, Periodic (fun t => f (t, z)) P) (t : ℝ) (z : E) :
    liftPeriodic f hf ((t : AddCircle P), z) = f (t, z) :=
  (hf z).lift_coe t

lemma continuous_liftPeriodic [TopologicalSpace E] [TopologicalSpace F]
    {P : ℝ} {f : ℝ × E → F}
    (hf : ∀ z, Periodic (fun t => f (t, z)) P) (hc : Continuous f) :
    Continuous (liftPeriodic f hf) := by
  have hq : IsOpenQuotientMap
      (fun x : ℝ × E => ((x.1 : AddCircle P), x.2)) :=
    QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id
  rw [← hq.continuous_comp_iff]
  simpa only [Function.comp_def, liftPeriodic_coe] using hc

lemma liftPeriodic_eq_liftIco {P : ℝ} [Fact (0 < P)] (f : ℝ × E → F)
    (hf : ∀ z, Periodic (fun t => f (t, z)) P) (x : AddCircle P × E) :
    liftPeriodic f hf x = AddCircle.liftIco P 0 (fun t => f (t, x.2)) x.1 := by
  let r := AddCircle.equivIco P 0 x.1
  have he : ((r : ℝ) : AddCircle P) = x.1 := AddCircle.coe_equivIco
  calc
    liftPeriodic f hf x = liftPeriodic f hf (((r : ℝ) : AddCircle P), x.2) := by rw [he]
    _ = f ((r : ℝ), x.2) := liftPeriodic_coe f hf _ _
    _ = AddCircle.liftIco P 0 (fun t => f (t, x.2)) x.1 := rfl

lemma continuous_liftIco_of_periodic [TopologicalSpace E] [TopologicalSpace F]
    {P : ℝ} [Fact (0 < P)] {f : ℝ × E → F}
    (hf : ∀ z, Periodic (fun t => f (t, z)) P) (hc : Continuous f) :
    Continuous (fun x : AddCircle P × E =>
      AddCircle.liftIco P 0 (fun t => f (t, x.2)) x.1) :=
  (continuous_liftPeriodic hf hc).congr (liftPeriodic_eq_liftIco f hf)

def liftPeriodize [AddCommMonoid F] (P : ℝ) (f : ℝ × E → F) : AddCircle P × E → F :=
  liftPeriodic (periodize P f) (periodic_periodize P f)

@[simp] lemma liftPeriodize_coe [AddCommMonoid F]
    (P : ℝ) (f : ℝ × E → F) (t : ℝ) (z : E) :
    liftPeriodize P f ((t : AddCircle P), z) = periodize P f (t, z) :=
  liftPeriodic_coe _ _ _ _

lemma continuous_liftPeriodize [TopologicalSpace E]
    [AddCommMonoid F] [TopologicalSpace F] [ContinuousAdd F]
    {P a b : ℝ} {f : ℝ × E → F}
    (hP : 0 < P) (hf : Continuous f)
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    Continuous (liftPeriodize P f) :=
  continuous_liftPeriodic _ (continuous_periodize hP hf hsupp)

lemma liftPeriodize_eq_liftIco [AddCommMonoid F]
    {P : ℝ} [Fact (0 < P)] {f : ℝ × E → F}
    (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 P) (x : AddCircle P × E) :
    liftPeriodize P f x = AddCircle.liftIco P 0 (fun t => f (t, x.2)) x.1 := by
  let r := AddCircle.equivIco P 0 x.1
  have hr : (r : ℝ) ∈ Icc 0 P := by
    have h := r.property
    simp only [zero_add] at h
    exact ⟨h.1, h.2.le⟩
  have he : ((r : ℝ) : AddCircle P) = x.1 := AddCircle.coe_equivIco
  calc
    liftPeriodize P f x = liftPeriodize P f (((r : ℝ) : AddCircle P), x.2) := by
      rw [he]
    _ = f ((r : ℝ), x.2) := by
      rw [liftPeriodize_coe]
      exact periodize_eq_on_fundamental_strip Fact.out hsupp hr x.2
    _ = AddCircle.liftIco P 0 (fun t => f (t, x.2)) x.1 := rfl

lemma continuous_liftIco_of_strip_support [TopologicalSpace E]
    [AddCommMonoid F] [TopologicalSpace F] [ContinuousAdd F]
    {P : ℝ} [Fact (0 < P)] {f : ℝ × E → F}
    (hf : Continuous f) (hsupp : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 P) :
    Continuous (fun x : AddCircle P × E =>
      AddCircle.liftIco P 0 (fun t => f (t, x.2)) x.1) := by
  have hsupp' : ∀ x, f x ≠ 0 → x.1 ∈ Icc 0 P :=
    fun x hx => ⟨(hsupp x hx).1.le, (hsupp x hx).2.le⟩
  exact (continuous_liftPeriodize Fact.out hf hsupp').congr
    (liftPeriodize_eq_liftIco hsupp)

end ClockQuotient
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockQuotientC1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace Problem340.ClockQuotient
local instance instFactLtRealOfNat_solutions : Fact (0 < (100 : ℝ)) := ⟨by norm_num⟩

end Problem340.ClockQuotient

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Clock

def rotate (x : ClockAmbient) (a : ℝ) : ClockAmbient :=
  WithLp.toLp 2 ![x 0 * Real.cos a - x 1 * Real.sin a,
    x 0 * Real.sin a + x 1 * Real.cos a]

@[simp] lemma rotate_zero_apply (x : ClockAmbient) (a : ℝ) :
    rotate x a 0 = x 0 * Real.cos a - x 1 * Real.sin a := rfl

@[simp] lemma rotate_one_apply (x : ClockAmbient) (a : ℝ) :
    rotate x a 1 = x 0 * Real.sin a + x 1 * Real.cos a := rfl

lemma norm_rotate (x : ClockAmbient) (a : ℝ) : ‖rotate x a‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, rotate_zero_apply, rotate_one_apply]
  have hc := Real.sin_sq_add_cos_sq a
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

def parametrization (t : ℝ) : ClockAmbient :=
  WithLp.toLp 2 ![Real.cos (2 * Real.pi * t / 100), Real.sin (2 * Real.pi * t / 100)]

@[simp] lemma parametrization_zero (t : ℝ) :
    parametrization t 0 = Real.cos (2 * Real.pi * t / 100) := rfl

@[simp] lemma parametrization_one (t : ℝ) :
    parametrization t 1 = Real.sin (2 * Real.pi * t / 100) := rfl

def ambientIncrement (x : ClockAmbient) (e : ℝ) : ℝ :=
  ambientBarrier x + (1 - ambientBarrier x) * e

@[simp] lemma ambientIncrement_one (x : ClockAmbient) : ambientIncrement x 1 = 1 := by
  simp [ambientIncrement]

@[simp] lemma ambientIncrement_zero (x : ClockAmbient) : ambientIncrement x 0 = ambientBarrier x := by
  simp [ambientIncrement]

def ambientUpdate (x : ClockAmbient) (e : ℝ) : ClockAmbient :=
  rotate x (2 * Real.pi * ambientIncrement x e / 100)

lemma norm_ambientUpdate (x : ClockAmbient) (e : ℝ) : ‖ambientUpdate x e‖ = ‖x‖ :=
  norm_rotate _ _

def update (x : StandardClock) (e : ℝ) : StandardClock :=
  ⟨ambientUpdate x.1 e, by
    rw [Metric.mem_sphere, dist_zero_right, norm_ambientUpdate]
    simp⟩

end Problem340.Clock

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PredictionSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

def predictionMajorant (C B L : ℝ) (n : ℕ) : ℝ :=
  C * (L⁻¹) ^ n * (1 + B ^ (n + 1) + 2 ^ (n + 2))

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PredictionInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

def predictionSummand
    {E F : Type*} [SMul ℝ F]
    (α : E → ℝ) (β : ℝ → ℝ) (T : ℕ → E → ℝ) (Φ : ℕ → E → F)
    (L : ℝ) (n : ℕ) (x : E) : F :=
  ((L⁻¹) ^ n / 10) • (α x • (β (T n x) • Φ n x))

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.NormalizedPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContDiff

namespace Problem340.NormalizedPrediction

open AmbientRetraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {G : ℝ × E → ℝ × E}

def clock (G : ℝ × E → ℝ × E) (m : ℕ) (x : ℝ × E) : ℝ :=
  ((G ∘ cylinder)^[m] x).1

end Problem340.NormalizedPrediction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ReadoutCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem340

def readoutCenter (i : Fin 3) : ℝ := 76 + (i : ℝ) / 2

def readoutBump (i : Fin 3) : ContDiffBump (readoutCenter i) :=
  ⟨1 / 4, 2 / 5, by norm_num, by norm_num⟩

def readoutCoeff (i : Fin 3) (t : ℝ) : ℝ := readoutBump i t

def readoutInterval (i : Fin 3) : Set ℝ :=
  Set.Ioo (readoutCenter i - 2 / 5) (readoutCenter i + 2 / 5)

theorem readoutCoeff_contDiff (i : Fin 3) {n : ℕ∞} :
    ContDiff ℝ n (readoutCoeff i) := (readoutBump i).contDiff

theorem readoutCoeff_nonneg (i : Fin 3) (t : ℝ) : 0 ≤ readoutCoeff i t :=
  (readoutBump i).nonneg

theorem readoutCoeff_le_one (i : Fin 3) (t : ℝ) : readoutCoeff i t ≤ 1 :=
  (readoutBump i).le_one

theorem readoutCoeff_support (i : Fin 3) :
    Function.support (readoutCoeff i) = readoutInterval i := by
  change Function.support (readoutBump i) = _
  rw [(readoutBump i).support_eq]
  ext t
  simp only [Metric.mem_ball, Real.dist_eq, readoutBump, readoutInterval,
    Set.mem_Ioo, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem readoutCenter_bounds (i : Fin 3) :
    76 ≤ readoutCenter i ∧ readoutCenter i ≤ 77 := by
  have hi : (i : ℕ) ≤ 2 := by omega
  have hi' : (i : ℝ) ≤ 2 := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := by positivity
  dsimp [readoutCenter]
  constructor <;> linarith

theorem readoutInterval_subset (i : Fin 3) :
    readoutInterval i ⊆ Set.Ioo 74 80 := by
  intro t ht
  obtain ⟨hc0, hc1⟩ := readoutCenter_bounds i
  change readoutCenter i - 2 / 5 < t ∧ t < readoutCenter i + 2 / 5 at ht
  constructor <;> linarith [ht.1, ht.2]

def preparationBump : ContDiffBump (10 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def preparationCoeff (t : ℝ) : ℝ := preparationBump t

theorem preparationCoeff_contDiff {n : ℕ∞} : ContDiff ℝ n preparationCoeff :=
  preparationBump.contDiff

theorem preparationCoeff_support :
    Function.support preparationCoeff = Set.Ioo 8 12 := by
  change Function.support preparationBump = _
  rw [preparationBump.support_eq]
  ext t
  simp only [Metric.mem_ball, Real.dist_eq, preparationBump, Set.mem_Ioo, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SpherePerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped OnePoint

namespace Problem340

def perturbedSquare (c : ℂ) : OnePoint ℂ → OnePoint ℂ :=
  OnePoint.map (fun z : ℂ => z ^ 2 + c)

@[simp] theorem perturbedSquare_infty (c : ℂ) :
    perturbedSquare c ∞ = ∞ := rfl

@[simp] theorem perturbedSquare_coe (c z : ℂ) :
    perturbedSquare c (z : OnePoint ℂ) = ((z ^ 2 + c : ℂ) : OnePoint ℂ) := rfl

theorem tendsto_norm_perturbedSquare (c : ℂ) :
    Tendsto (fun p : ℂ × ℂ => ‖p.2 ^ 2 + p.1‖)
      (𝓝 c ×ˢ cocompact ℂ) atTop := by
  have hz : Tendsto (fun p : ℂ × ℂ => ‖p.2‖)
      (𝓝 c ×ˢ cocompact ℂ) atTop :=
    tendsto_norm_cocompact_atTop.comp tendsto_snd
  have hp := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hz
  have hc : Tendsto (fun p : ℂ × ℂ => -‖p.1‖)
      (𝓝 c ×ˢ cocompact ℂ) (𝓝 (-‖c‖)) := tendsto_fst.norm.neg
  apply tendsto_atTop_mono (f := fun p : ℂ × ℂ => ‖p.2‖ ^ 2 + -‖p.1‖)
  · intro p
    have h := norm_sub_norm_le (p.2 ^ 2) (-p.1)
    rw [norm_pow] at h
    simpa only [norm_neg, sub_neg_eq_add, sub_eq_add_neg, neg_neg] using h
  · exact hp.atTop_add hc

theorem continuous_perturbedSquare :
    Continuous (fun p : ℂ × OnePoint ℂ => perturbedSquare p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨c, z⟩
  induction z using OnePoint.rec with
  | infty =>
      change Tendsto _ (𝓝 (c, (∞ : OnePoint ℂ))) (𝓝 ∞)
      conv => arg 2; rw [nhds_prod_eq, OnePoint.nhds_infty_eq, prod_sup]
      rw [tendsto_sup]
      constructor
      · rw [prod_map_right, tendsto_map'_iff]
        have hproper : Tendsto (fun p : ℂ × ℂ => p.2 ^ 2 + p.1)
            (𝓝 c ×ˢ cocompact ℂ) (cocompact ℂ) := by
          simpa only [Metric.cobounded_eq_cocompact] using
            (tendsto_norm_atTop_iff_cobounded.mp (tendsto_norm_perturbedSquare c))
        change Tendsto (fun p : ℂ × ℂ => ((p.2 ^ 2 + p.1 : ℂ) : OnePoint ℂ))
          (𝓝 c ×ˢ coclosedCompact ℂ) (𝓝 ∞)
        simpa only [Function.comp_def, coclosedCompact_eq_cocompact] using
          (OnePoint.tendsto_coe_infty (X := ℂ)).comp
            (by simpa only [coclosedCompact_eq_cocompact] using hproper)
      · rw [prod_pure, tendsto_map'_iff]
        change Tendsto (fun _ : ℂ => (∞ : OnePoint ℂ)) (𝓝 c) (𝓝 ∞)
        exact tendsto_const_nhds
  | coe z =>
      change Tendsto _ (𝓝 (c, (z : OnePoint ℂ))) (𝓝 ((z ^ 2 + c : ℂ) : OnePoint ℂ))
      rw [nhds_prod_eq, OnePoint.nhds_coe_eq, prod_map_right, tendsto_map'_iff]
      have hpoly : Continuous (fun p : ℂ × ℂ => p.2 ^ 2 + p.1) := by fun_prop
      change Tendsto (fun p : ℂ × ℂ => ((p.2 ^ 2 + p.1 : ℂ) : OnePoint ℂ))
        (𝓝 c ×ˢ 𝓝 z) (𝓝 ((z ^ 2 + c : ℂ) : OnePoint ℂ))
      rw [← nhds_prod_eq]
      exact (OnePoint.continuous_coe.comp hpoly).continuousAt

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Map
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

local instance instFactLtRealOfNat_solutions : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

abbrev Sphere := OnePoint ℂ
abbrev RawManifold := AddCircle (100 : ℝ) × (Sphere × (Fin 3 → Sphere))

structure SphereData where
  gate : Sphere → ℝ
  cutoff : Sphere → ℝ
  saturation : Sphere → ℂ
  gain : ℝ → ℝ
  L : ℝ

def phase : Sphere → ℂ := OnePoint.rec 0 (fun z : ℂ => z / (‖z‖ : ℂ))

@[simp] theorem phase_infty : phase ∞ = 0 := rfl
@[simp] theorem phase_coe (z : ℂ) : phase (z : Sphere) = z / (‖z‖ : ℂ) := rfl
@[simp] theorem phase_zero : phase ((0 : ℂ) : Sphere) = 0 := by simp

def prediction (D : SphereData) (x : ℝ × Sphere) : ℝ × Sphere :=
  (x.1 + Clock.increment x.1 (D.gate x.2), perturbedSquare 0 x.2)

def predictedClock (D : SphereData) (m : ℕ) (t : ℝ) (z : Sphere) : ℝ :=
  ((prediction D)^[m] (t, z)).1

def inputTerm (D : SphereData) (i : Fin 3) (n : ℕ) (t : ℝ) (z : Sphere) : ℂ :=
  (((D.L⁻¹) ^ n * readoutCoeff i (predictedClock D (n + 1) t z) * D.cutoff z : ℝ) : ℂ) *
    phase z ^ (2 ^ (n + 2))

def baseInput (D : SphereData) (i : Fin 3) (t : ℝ) (z : Sphere) : ℂ :=
  ((preparationCoeff t / 10 : ℝ) : ℂ) * ∑' n : ℕ, inputTerm D i n t z

def input (D : SphereData) (i : Fin 3) (t : AddCircle (100 : ℝ)) (z : Sphere) : ℂ :=
  AddCircle.liftIco 100 0 (fun s => baseInput D i s z) t

def periodicReadout (i : Fin 3) : AddCircle (100 : ℝ) → ℝ :=
  AddCircle.liftIco 100 0 (readoutCoeff i)

def periodicGain (D : SphereData) : AddCircle (100 : ℝ) → ℝ :=
  AddCircle.liftIco 100 0 D.gain

def clockIncrement (D : SphereData) (t : AddCircle (100 : ℝ)) (z : Sphere) : ℝ :=
  AddCircle.liftIco 100 0 (fun s => Clock.increment s (D.gate z)) t

def readout (D : SphereData) (t : AddCircle (100 : ℝ)) (v : Fin 3 → Sphere) : ℂ :=
  20 * ∑ i : Fin 3, (periodicReadout i t : ℂ) * D.saturation (v i)

def rawMap (D : SphereData) (x : RawManifold) : RawManifold :=
  (x.1 + (clockIncrement D x.1 x.2.1 : ℝ),
    perturbedSquare (readout D x.1 x.2.2) x.2.1,
    fun i => (((periodicGain D x.1 : ℂ) * D.saturation (x.2.2 i) +
      input D i x.1 x.2.1 : ℂ) : Sphere))

@[simp] theorem rawMap_main_infty (D : SphereData)
    (t : AddCircle (100 : ℝ)) (v : Fin 3 → Sphere) :
    (rawMap D (t, ∞, v)).2.1 = ∞ := rfl

@[simp] theorem inputTerm_infty (D : SphereData) (i : Fin 3) (n : ℕ) (t : ℝ) :
    inputTerm D i n t ∞ = 0 := by simp [inputTerm]

@[simp] theorem inputTerm_zero (D : SphereData) (i : Fin 3) (n : ℕ) (t : ℝ) :
    inputTerm D i n t ((0 : ℂ) : Sphere) = 0 := by simp [inputTerm]

@[simp] theorem baseInput_infty (D : SphereData) (i : Fin 3) (t : ℝ) :
    baseInput D i t ∞ = 0 := by simp [baseInput]

@[simp] theorem baseInput_zero (D : SphereData) (i : Fin 3) (t : ℝ) :
    baseInput D i t ((0 : ℂ) : Sphere) = 0 := by simp [baseInput]

@[simp] theorem input_infty (D : SphereData) (i : Fin 3) (t : AddCircle (100 : ℝ)) :
    input D i t ∞ = 0 := by simp [input, AddCircle.liftIco]

@[simp] theorem input_zero (D : SphereData) (i : Fin 3) (t : AddCircle (100 : ℝ)) :
    input D i t ((0 : ℂ) : Sphere) = 0 := by simp [input, AddCircle.liftIco]

theorem norm_phase_le_one (z : Sphere) : ‖phase z‖ ≤ 1 := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z =>
      by_cases hz : z = 0
      · simp [hz]
      · simp [phase_coe, Complex.norm_real, norm_ne_zero_iff.mpr hz]

theorem norm_inputTerm_le (D : SphereData) (hL : 0 ≤ D.L)
    (hχ0 : ∀ z, 0 ≤ D.cutoff z) (hχ1 : ∀ z, D.cutoff z ≤ 1)
    (i : Fin 3) (n : ℕ) (t : ℝ) (z : Sphere) :
    ‖inputTerm D i n t z‖ ≤ (D.L⁻¹) ^ n := by
  have hpow : 0 ≤ (D.L⁻¹) ^ n := pow_nonneg (inv_nonneg.mpr hL) n
  have hβ0 := readoutCoeff_nonneg i (predictedClock D (n + 1) t z)
  have hβ1 := readoutCoeff_le_one i (predictedClock D (n + 1) t z)
  have hcoef0 : 0 ≤ (D.L⁻¹) ^ n *
      readoutCoeff i (predictedClock D (n + 1) t z) * D.cutoff z :=
    mul_nonneg (mul_nonneg hpow hβ0) (hχ0 z)
  have hcoef1 : (D.L⁻¹) ^ n *
      readoutCoeff i (predictedClock D (n + 1) t z) * D.cutoff z ≤ (D.L⁻¹) ^ n := by
    calc
      _ ≤ (D.L⁻¹) ^ n * readoutCoeff i (predictedClock D (n + 1) t z) :=
        mul_le_of_le_one_right (mul_nonneg hpow hβ0) (hχ1 z)
      _ ≤ (D.L⁻¹) ^ n := mul_le_of_le_one_right hpow hβ1
  calc
    ‖inputTerm D i n t z‖ = ((D.L⁻¹) ^ n *
      readoutCoeff i (predictedClock D (n + 1) t z) * D.cutoff z) *
      ‖phase z‖ ^ (2 ^ (n + 2)) := by
        simp only [inputTerm, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hL),
          abs_of_nonneg hβ0, abs_of_nonneg (hχ0 z)]
    _ ≤ (D.L⁻¹) ^ n * readoutCoeff i (predictedClock D (n + 1) t z) * D.cutoff z :=
      mul_le_of_le_one_right hcoef0
        (pow_le_one₀ (norm_nonneg _) (norm_phase_le_one z))
    _ ≤ (D.L⁻¹) ^ n := hcoef1

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Metric Module Function Filter Topology
open scoped RealInnerProductSpace ContDiff OnePoint

namespace Problem340

def chartNorthVector : SphereAmbient := EuclideanSpace.single 2 1

@[simp] theorem norm_chartNorthVector : ‖chartNorthVector‖ = 1 := by
  simp [chartNorthVector]

def chartNorthPole : StandardSphere2 :=
  ⟨chartNorthVector, by simp⟩

theorem mem_chartEquator_iff (x : SphereAmbient) :
    x ∈ (ℝ ∙ chartNorthVector)ᗮ ↔ x 2 = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [chartNorthVector, EuclideanSpace.inner_single_left]

def chartEquatorLinearEquiv : ℂ ≃ₗ[ℝ] (ℝ ∙ chartNorthVector)ᗮ where
  toFun z := ⟨WithLp.toLp 2 ![z.re, z.im, 0], by
    rw [mem_chartEquator_iff]
    rfl⟩
  invFun w := (w.val 0 : ℂ) + (w.val 1 : ℂ) * Complex.I
  map_add' z w := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  map_smul' r z := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [Complex.real_smul]
  left_inv z := by
    apply Complex.ext <;> simp
  right_inv w := by
    apply Subtype.ext
    ext i
    have hw := (mem_chartEquator_iff w.val).mp w.property
    fin_cases i <;> simp [hw]

def chartEquatorEquiv : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ chartNorthVector)ᗮ where
  toLinearEquiv := chartEquatorLinearEquiv
  norm_map' z := by
    change ‖(WithLp.toLp 2 ![z.re, z.im, 0] : SphereAmbient)‖ = ‖z‖
    rw [EuclideanSpace.norm_eq, Complex.norm_def]
    congr 1
    simp [Fin.sum_univ_succ, Complex.normSq_apply, sq]

@[simp] theorem chartEquatorEquiv_apply (z : ℂ) :
    (chartEquatorEquiv z : SphereAmbient) = WithLp.toLp 2 ![z.re, z.im, 0] := rfl

@[simp] theorem chartEquatorEquiv_apply_zero (z : ℂ) :
    (chartEquatorEquiv z).val 0 = z.re := rfl

@[simp] theorem chartEquatorEquiv_apply_one (z : ℂ) :
    (chartEquatorEquiv z).val 1 = z.im := rfl

@[simp] theorem chartEquatorEquiv_apply_two (z : ℂ) :
    (chartEquatorEquiv z).val 2 = 0 := rfl

@[simp] theorem chartEquatorEquiv_symm_apply (w : (ℝ ∙ chartNorthVector)ᗮ) :
    chartEquatorEquiv.symm w = (w.val 0 : ℂ) + (w.val 1 : ℂ) * Complex.I := rfl

def sphereOfComplex (z : ℂ) : StandardSphere2 :=
  stereoInvFun norm_chartNorthVector (chartEquatorEquiv ((2 : ℝ) • z))

theorem sphereOfComplex_val (z : ℂ) :
    (sphereOfComplex z : SphereAmbient) =
      (‖z‖ ^ 2 + 1)⁻¹ •
        ((2 : ℝ) • (chartEquatorEquiv z : SphereAmbient) +
          (‖z‖ ^ 2 - 1) • chartNorthVector) := by
  have hn : ‖(chartEquatorEquiv z : SphereAmbient)‖ = ‖z‖ :=
    chartEquatorEquiv.norm_map z
  have hd : ‖z‖ ^ 2 + 1 ≠ 0 := by positivity
  have hd' : (2 * ‖z‖) ^ 2 + 4 ≠ 0 := by positivity
  change stereoInvFunAux chartNorthVector
    (chartEquatorEquiv ((2 : ℝ) • z) : SphereAmbient) = _
  simp only [stereoInvFunAux_apply, norm_smul, Real.norm_eq_abs, show |(2 : ℝ)| = 2 by norm_num, hn,
    map_smul, Submodule.coe_smul_of_tower, smul_add, smul_smul]
  match_scalars <;> field_simp <;> ring

@[simp] theorem sphereOfComplex_val_zero (z : ℂ) :
    (sphereOfComplex z).val 0 = 2 * z.re / (‖z‖ ^ 2 + 1) := by
  rw [sphereOfComplex_val]
  simp [chartNorthVector,
    div_eq_mul_inv, mul_comm]
  left
  change 2 * z.re = z.re * 2
  ring

@[simp] theorem sphereOfComplex_val_one (z : ℂ) :
    (sphereOfComplex z).val 1 = 2 * z.im / (‖z‖ ^ 2 + 1) := by
  rw [sphereOfComplex_val]
  simp [chartNorthVector,
    div_eq_mul_inv, mul_comm]
  left
  change 2 * z.im = z.im * 2
  ring

@[simp] theorem sphereOfComplex_val_two (z : ℂ) :
    (sphereOfComplex z).val 2 = (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1) := by
  rw [sphereOfComplex_val]
  simp [chartNorthVector,
    div_eq_mul_inv, mul_comm]
  right
  rfl

def sphereToComplex (x : StandardSphere2) : ℂ :=
  (1 / 2 : ℝ) • chartEquatorEquiv.symm (stereoToFun chartNorthVector x.val)

@[simp] theorem sphereToComplex_sphereOfComplex (z : ℂ) :
    sphereToComplex (sphereOfComplex z) = z := by
  unfold sphereToComplex sphereOfComplex
  rw [stereo_right_inv]
  simp

theorem sphereOfComplex_ne_north (z : ℂ) : sphereOfComplex z ≠ chartNorthPole := by
  exact stereoInvFun_ne_north_pole norm_chartNorthVector _

theorem sphereOfComplex_sphereToComplex {x : StandardSphere2} (hx : x ≠ chartNorthPole) :
    sphereOfComplex (sphereToComplex x) = x := by
  have hx' : (x : SphereAmbient) ≠ chartNorthVector := by
    intro h
    apply hx
    exact Subtype.ext h
  unfold sphereOfComplex sphereToComplex
  rw [smul_smul]
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact stereo_left_inv norm_chartNorthVector hx'

theorem continuous_sphereOfComplex : Continuous sphereOfComplex := by
  exact (continuous_stereoInvFun norm_chartNorthVector).comp
    (chartEquatorEquiv.continuous.comp (continuous_id.const_smul (2 : ℝ)))

theorem sphereOfComplex_injective : Function.Injective sphereOfComplex :=
  Function.LeftInverse.injective sphereToComplex_sphereOfComplex

theorem continuousOn_sphereToComplex :
    ContinuousOn sphereToComplex {chartNorthPole}ᶜ := by
  exact ((continuous_id.const_smul (1 / 2 : ℝ)).comp
    chartEquatorEquiv.symm.continuous).comp_continuousOn
      (stereographic norm_chartNorthVector).continuousOn

def scaledChartEquator : ℂ ≃ₜ (ℝ ∙ chartNorthVector)ᗮ :=
  (Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num) : ℂ ≃ₜ ℂ).trans
    chartEquatorEquiv.toHomeomorph

def complexSphereHomeomorph : OnePoint ℂ ≃ₜ StandardSphere2 :=
  scaledChartEquator.onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere norm_chartNorthVector)

@[simp] theorem complexSphereHomeomorph_coe (z : ℂ) :
    complexSphereHomeomorph (z : OnePoint ℂ) = sphereOfComplex z := by
  rfl

@[simp] theorem complexSphereHomeomorph_infty :
    complexSphereHomeomorph (∞ : OnePoint ℂ) = chartNorthPole := by
  rfl

@[simp] theorem complexSphereHomeomorph_symm_north :
    complexSphereHomeomorph.symm chartNorthPole = (∞ : OnePoint ℂ) := by
  exact complexSphereHomeomorph.symm_apply_eq.mpr complexSphereHomeomorph_infty.symm

@[simp] theorem complexSphereHomeomorph_symm_affine (z : ℂ) :
    complexSphereHomeomorph.symm (sphereOfComplex z) = (z : OnePoint ℂ) := by
  exact complexSphereHomeomorph.symm_apply_eq.mpr (complexSphereHomeomorph_coe z).symm

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereCutoffsAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology

namespace Problem340.SphereCutoffs

def affineHeight (z : ℂ) : ℝ := (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1)

def affineClockGate (z : ℂ) : ℝ :=
  Real.smoothTransition ((25 * affineHeight z + 15) / 8)

def affinePreparationCutoff (z : ℂ) : ℝ :=
  Real.smoothTransition (5 * affineHeight z + 4) *
    Real.smoothTransition (1 - 2 * affineHeight z)

@[fun_prop]
theorem contDiff_affineHeight {n : ℕ∞} : ContDiff ℝ n affineHeight := by
  exact ((contDiff_norm_sq ℝ).sub contDiff_const).div
    ((contDiff_norm_sq ℝ).add contDiff_const) (fun z => by positivity)

@[fun_prop]
theorem contDiff_affineClockGate {n : ℕ∞} : ContDiff ℝ n affineClockGate := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul contDiff_affineHeight).add contDiff_const).div_const 8)

@[fun_prop]
theorem contDiff_affinePreparationCutoff {n : ℕ∞} :
    ContDiff ℝ n affinePreparationCutoff := by
  exact (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_affineHeight).add contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp
      (contDiff_const.sub (contDiff_const.mul contDiff_affineHeight)))

theorem affinePreparationCutoff_mem_Icc (z : ℂ) :
    affinePreparationCutoff z ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)⟩

theorem affineClockGate_eq_one {z : ℂ} (h : 3 / 4 ≤ ‖z‖) :
    affineClockGate z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hh : -7 / 25 ≤ affineHeight z := by
    apply (le_div_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 1)).2
    nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 3 / 4) h]
  linarith

theorem affinePreparationCutoff_eq_zero_of_small {z : ℂ} (h : ‖z‖ ≤ 1 / 3) :
    affinePreparationCutoff z = 0 := by
  have hh : affineHeight z ≤ -4 / 5 := by
    apply (div_le_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 1)).2
    nlinarith [mul_self_le_mul_self (norm_nonneg z) h]
  unfold affinePreparationCutoff
  rw [Real.smoothTransition.zero_of_nonpos
    (by linarith : 5 * affineHeight z + 4 ≤ 0), zero_mul]

theorem affinePreparationCutoff_eq_zero_of_large {z : ℂ} (h : 3 ≤ ‖z‖ ^ 2) :
    affinePreparationCutoff z = 0 := by
  have hh : 1 / 2 ≤ affineHeight z := by
    apply (le_div_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 1)).2
    linarith
  unfold affinePreparationCutoff
  rw [Real.smoothTransition.zero_of_nonpos
    (by linarith : 1 - 2 * affineHeight z ≤ 0), mul_zero]

theorem continuous_onePointElim_of_eq_const_off_isCompact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (c : Y) (hf : Continuous f) {K : Set X}
    (hK : IsCompact K) (hclosed : IsClosed K)
    (hout : ∀ x ∉ K, f x = c) :
    Continuous (fun z : OnePoint X => z.elim c f) := by
  apply (OnePoint.continuous_iff _).2
  refine ⟨?_, hf⟩
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [hK.compl_mem_coclosedCompact_of_isClosed hclosed] with x hx
  exact (hout x hx).symm

def onePointClockGate (z : OnePoint ℂ) : ℝ := z.elim 1 affineClockGate

def onePointPreparationCutoff (z : OnePoint ℂ) : ℝ := z.elim 0 affinePreparationCutoff

@[simp] theorem onePointClockGate_coe (z : ℂ) :
    onePointClockGate (z : OnePoint ℂ) = affineClockGate z := rfl

@[simp] theorem onePointClockGate_infty : onePointClockGate OnePoint.infty = 1 := rfl

@[simp] theorem onePointPreparationCutoff_coe (z : ℂ) :
    onePointPreparationCutoff (z : OnePoint ℂ) = affinePreparationCutoff z := rfl

@[simp] theorem onePointPreparationCutoff_infty :
    onePointPreparationCutoff OnePoint.infty = 0 := rfl

@[continuity, fun_prop]
theorem continuous_onePointClockGate : Continuous onePointClockGate := by
  apply continuous_onePointElim_of_eq_const_off_isCompact _ _
    (@contDiff_affineClockGate 0).continuous (isCompact_closedBall (0 : ℂ) 1)
    Metric.isClosed_closedBall
  intro z hz
  have hz' : 1 < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  exact affineClockGate_eq_one (by linarith)

@[continuity, fun_prop]
theorem continuous_onePointPreparationCutoff : Continuous onePointPreparationCutoff := by
  apply continuous_onePointElim_of_eq_const_off_isCompact _ _
    (@contDiff_affinePreparationCutoff 0).continuous (isCompact_closedBall (0 : ℂ) 2)
    Metric.isClosed_closedBall
  intro z hz
  have hz' : 2 < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  apply affinePreparationCutoff_eq_zero_of_large
  nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) hz'.le]

theorem onePointPreparationCutoff_mem_Icc (z : OnePoint ℂ) :
    onePointPreparationCutoff z ∈ Set.Icc (0 : ℝ) 1 := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => exact affinePreparationCutoff_mem_Icc z

end Problem340.SphereCutoffs

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereDoublingCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340

lemma doubling_north_eq_chartNorthPole : SphereDoubling.north = chartNorthPole := by
  symm
  apply (SphereDoubling.eq_north_iff chartNorthPole).mpr
  simp [chartNorthPole, chartNorthVector]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PredictionModelBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped OnePoint

namespace Problem340

namespace PredictionModelBridge

def modelEmbedding (x : ℝ × OnePoint ℂ) : AmbientPrediction.Ambient :=
  (x.1, (complexSphereHomeomorph x.2).val)

end PredictionModelBridge

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereAngularInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Topology

namespace Problem340.SphereAngularInput

def horizontal (x : SphereAmbient) : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I

def phase (x : SphereAmbient) : ℂ := (‖horizontal x‖ : ℂ)⁻¹ * horizontal x

def angularAmbient (k : ℕ) (x : SphereAmbient) : ℂ :=
  (SphereCutoffs.preparationCutoffAmbient x : ℂ) * phase x ^ k

@[fun_prop]
theorem contDiff_horizontal {n : ℕ∞} : ContDiff ℝ n horizontal := by
  have h0 : ContDiff ℝ n (fun x : SphereAmbient => (x 0 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff
  have h1 : ContDiff ℝ n (fun x : SphereAmbient => (x 1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff
  exact h0.add (h1.mul contDiff_const)

def regularDomain : Set SphereAmbient :=
  {x | horizontal x ≠ 0 ∨ x 2 < -4 / 5 ∨ 1 / 2 < x 2}

end Problem340.SphereAngularInput

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ConcreteInputRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.ConcreteInputRegularity

abbrev Ambient := AmbientPrediction.Ambient

def preparation (x : Ambient) : ℝ := preparationCoeff x.1

def predictedClock (n : ℕ) : Ambient → ℝ :=
  NormalizedPrediction.clock AmbientPrediction.predictor (n + 1)

def angular (n : ℕ) (x : Ambient) : ℂ :=
  SphereAngularInput.angularAmbient (2 ^ (n + 2)) x.2

def ambientInput (L : ℝ) (i : Fin 3) (x : Ambient) : ℂ :=
  ∑' n, predictionSummand preparation (readoutCoeff i) predictedClock angular L n x

open scoped OnePoint

end Problem340.ConcreteInputRegularity

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.CoordinateGoodCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric
open scoped unitInterval

namespace Problem340
namespace CoordinateGoodCover

section Cone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sphereSlice (C : Set E) : Set (Metric.sphere (0 : E) 1) :=
  {x | (x : E) ∈ C}

theorem contractible_sphereSlice (C : Set E) (hconv : Convex ℝ C)
    (hscale : ∀ r : ℝ, 0 < r → ∀ x ∈ C, r • x ∈ C)
    (hzero : (0 : E) ∉ C) (hne : (sphereSlice C).Nonempty) :
    ContractibleSpace (sphereSlice C) := by
  obtain ⟨p, hp⟩ := hne
  let p' : sphereSlice C := ⟨p, hp⟩
  let blend : unitInterval × sphereSlice C → E :=
    fun z => (z.1 : ℝ) • (p : E) + (1 - (z.1 : ℝ)) • (z.2.1 : E)
  have hblend : Continuous blend := by
    dsimp [blend]
    fun_prop
  have hmem (z : unitInterval × sphereSlice C) : blend z ∈ C := by
    exact hconv hp z.2.property z.1.property.1
      (sub_nonneg.mpr z.1.property.2) (add_sub_cancel _ _)
  have hnezero (z : unitInterval × sphereSlice C) : blend z ≠ 0 := by
    intro hz
    exact hzero (hz ▸ hmem z)
  have hnorm (z : unitInterval × sphereSlice C) : ‖blend z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hnezero z)
  let H : unitInterval × sphereSlice C → sphereSlice C := fun z =>
    ⟨⟨‖blend z‖⁻¹ • blend z, by
      simpa [mem_sphere_zero_iff_norm] using
        (norm_smul_inv_norm (𝕜 := ℝ) (hnezero z))⟩,
      hscale _ (inv_pos.mpr (norm_pos_iff.mpr (hnezero z))) _ (hmem z)⟩
  have hH : Continuous H := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (hblend.norm.inv₀ hnorm).smul hblend
  apply (contractible_iff_id_nullhomotopic (sphereSlice C)).mpr
  refine ⟨p', ⟨⟨⟨H, hH⟩, ?_, ?_⟩⟩⟩
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    have hx : ‖(x.1 : E)‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using x.1.property
    simp [H, blend, hx]
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    have hp' : ‖(p : E)‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using p.property
    simp [H, blend, hp', p']

def positiveCone {ι : Type*} (L : ι → E →L[ℝ] ℝ) (s : Set ι) : Set E :=
  {x | ∀ i ∈ s, 0 < L i x}

theorem convex_positiveCone {ι : Type*} (L : ι → E →L[ℝ] ℝ) (s : Set ι) :
    Convex ℝ (positiveCone L s) := by
  intro x hx y hy a b ha hb hab i hi
  exact ((convex_Ioi (𝕜 := ℝ) (0 : ℝ)).linear_preimage (L i).toLinearMap)
    (hx i hi) (hy i hi) ha hb hab

theorem positiveCone_smul {ι : Type*} (L : ι → E →L[ℝ] ℝ) (s : Set ι)
    {r : ℝ} (hr : 0 < r) {x : E} (hx : x ∈ positiveCone L s) :
    r • x ∈ positiveCone L s := by
  intro i hi
  simpa only [map_smul, smul_eq_mul] using mul_pos hr (hx i hi)

theorem zero_not_mem_positiveCone {ι : Type*} (L : ι → E →L[ℝ] ℝ)
    (s : Set ι) (hs : s.Nonempty) : (0 : E) ∉ positiveCone L s := by
  obtain ⟨i, hi⟩ := hs
  intro h
  simpa only [map_zero, lt_self_iff_false] using h i hi

theorem contractible_positiveSphere {ι : Type*} (L : ι → E →L[ℝ] ℝ)
    (s : Set ι) (hs : s.Nonempty)
    (hne : (sphereSlice (positiveCone L s)).Nonempty) :
    ContractibleSpace (sphereSlice (positiveCone L s)) :=
  contractible_sphereSlice _ (convex_positiveCone L s)
    (fun _ hr _ hx => positiveCone_smul L s hr hx)
    (zero_not_mem_positiveCone L s hs) hne

end Cone

structure GoodCover (ι X : Type*) [TopologicalSpace X] where
  carrier : ι → Set X
  isOpen : ∀ i, IsOpen (carrier i)
  covers : ∀ x, ∃ i, x ∈ carrier i
  contractible : ∀ s : Finset ι, s.Nonempty →
    (⋂ i ∈ s, carrier i).Nonempty → ContractibleSpace (⋂ i ∈ s, carrier i)

def GoodCover.comap {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (U : GoodCover ι Y) (e : X ≃ₜ Y) : GoodCover ι X where
  carrier i := e ⁻¹' U.carrier i
  isOpen i := (U.isOpen i).preimage e.continuous
  covers x := U.covers (e x)
  contractible s hs hne := by
    let A := ⋂ i ∈ s, U.carrier i
    let B := ⋂ i ∈ s, e ⁻¹' U.carrier i
    have hset : B = e ⁻¹' A := by
      simp only [A, B, Set.preimage_iInter]
    have hA : A.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      refine ⟨e x, ?_⟩
      change x ∈ e ⁻¹' A
      rw [← hset]
      exact hx
    let := U.contractible s hs hA
    exact (e.sets hset).contractibleSpace

section Products

variable {ι κ X Y : Type*} [topologyX : TopologicalSpace X] [topologyY : TopologicalSpace Y]

omit topologyX topologyY in
theorem inter_prod_eq [TopologicalSpace X] [TopologicalSpace Y]
    (U : ι → Set X) (V : κ → Set Y) (s : Finset (ι × κ))
    [DecidableEq ι] [DecidableEq κ] :
    (⋂ i ∈ s, U i.1 ×ˢ V i.2) =
      (⋂ i ∈ s.image Prod.fst, U i) ×ˢ (⋂ j ∈ s.image Prod.snd, V j) := by
  ext x
  simp only [mem_iInter, mem_prod, Finset.mem_image]
  constructor
  · intro h
    constructor
    · rintro i ⟨j, hj, rfl⟩
      exact (h j hj).1
    · rintro i ⟨j, hj, rfl⟩
      exact (h j hj).2
  · rintro ⟨hU, hV⟩ i hi
    exact ⟨hU i.1 ⟨i, hi, rfl⟩, hV i.2 ⟨i, hi, rfl⟩⟩

def GoodCover.prod (U : GoodCover ι X) (V : GoodCover κ Y) :
    GoodCover (ι × κ) (X × Y) where
  carrier i := U.carrier i.1 ×ˢ V.carrier i.2
  isOpen i := (U.isOpen i.1).prod (V.isOpen i.2)
  covers x := by
    obtain ⟨i, hi⟩ := U.covers x.1
    obtain ⟨j, hj⟩ := V.covers x.2
    exact ⟨(i, j), hi, hj⟩
  contractible s hs hne := by
    classical
    rw [inter_prod_eq] at hne ⊢
    let A := ⋂ i ∈ s.image Prod.fst, U.carrier i
    let B := ⋂ j ∈ s.image Prod.snd, V.carrier j
    have hA : A.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x.1, hx.1⟩
    have hB : B.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x.2, hx.2⟩
    let := U.contractible _ (hs.image _) hA
    let := V.contractible _ (hs.image _) hB
    exact (Homeomorph.Set.prod A B).contractibleSpace

end Products

section Coordinates

variable (n : ℕ)

def signedCoordinate (i : Bool × Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  if i.1 then EuclideanSpace.proj i.2 else -EuclideanSpace.proj i.2

def hemisphere (i : Bool × Fin n) : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  {x | 0 < signedCoordinate n i (x : EuclideanSpace ℝ (Fin n))}

theorem isOpen_hemisphere (i : Bool × Fin n) : IsOpen (hemisphere n i) :=
  isOpen_lt continuous_const ((signedCoordinate n i).continuous.comp continuous_subtype_val)

theorem hemisphere_covers (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∃ i, x ∈ hemisphere n i := by
  have hx : (x : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    intro h
    have hxnorm : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using x.property
    rw [h, norm_zero] at hxnorm
    exact zero_ne_one hxnorm
  have hi : ∃ i : Fin n, (x : EuclideanSpace ℝ (Fin n)) i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (PiLp.ext h)
  obtain ⟨i, hi⟩ := hi
  rcases lt_or_gt_of_ne hi with h | h
  · exact ⟨(false, i), by simpa [hemisphere, signedCoordinate] using neg_pos.mpr h⟩
  · exact ⟨(true, i), by simpa [hemisphere, signedCoordinate] using h⟩

theorem hemisphere_inter_eq_slice (s : Finset (Bool × Fin n)) :
    (⋂ i ∈ s, hemisphere n i) =
      sphereSlice (positiveCone (signedCoordinate n) (s : Set (Bool × Fin n))) := by
  ext x
  simp [sphereSlice, positiveCone, hemisphere]

def sphereGoodCover : GoodCover (Bool × Fin n)
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) where
  carrier := hemisphere n
  isOpen := isOpen_hemisphere n
  covers := hemisphere_covers n
  contractible s hs hne := by
    rw [hemisphere_inter_eq_slice] at hne ⊢
    exact contractible_positiveSphere _ _ hs hne

end Coordinates

def clockSphereGoodCover : GoodCover ((Bool × Fin 2) × (Bool × Fin 3))
    (StandardClock × StandardSphere2) :=
  (sphereGoodCover 2).prod (sphereGoodCover 3)

end CoordinateGoodCover
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.EntropyCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem340.EntropyCoding

abbrev SparseCode (n k : ℕ) (P Q : Type*) :=
  Σ s : {s : Finset (Fin n) // s.card ≤ k}, (Fin n → P) × (s.1 → Q)

open Set SetRel Dynamics

noncomputable def center {X P Q : Type*} {r k : ℕ}
    (p : P → X) (q : Q → X) (c : SparseCode r k P Q) (i : Fin r) : X := by
  classical
  exact if h : i ∈ c.1.1 then q (c.2.2 ⟨i, h⟩) else p (c.2.1 i)

noncomputable def exceptionalBlocks {X : Type*} (T : X → X) (V : Set X)
    (m r : ℕ) (x : X) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun i : Fin r => T^[m * i.val] x ∉ V)

end Problem340.EntropyCoding

end OAI
end

section
-- module Solutions.OAIQW_Problem340.FiniteGoodCoverHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340.FiniteGoodCover

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

def FiniteHomology (C : ChainComplex (ModuleCat ℝ) ℕ) : Prop :=
  (∀ n, FiniteDimensional ℝ (C.homology n)) ∧
    ∃ N, ∀ n, N ≤ n → IsZero (C.homology n)

end Problem340.FiniteGoodCover

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.GainLocalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace Problem340

local instance instFactLtRealOfNat_solutions_1 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

def standardGain (L : ℝ) (x : StandardClock) : ℝ :=
  AddCircle.liftIco (100 : ℝ) 0 (gainProfile L) (clockHomeomorph.symm x)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologyHomotopyEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContinuousMap

namespace Problem340

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def realHomologyHomotopyEquiv (n : ℕ) (e : X ≃ₕ Y) :
    RealSingularHomology n X ≃ₗ[ℝ] RealSingularHomology n Y where
  toLinearMap := realHomologyMap n e e.continuous
  invFun := realHomologyMap n e.symm e.symm.continuous
  left_inv x := by
    have h : realHomologyMap n (e.symm ∘ e) (e.symm.continuous.comp e.continuous) =
        LinearMap.id := by
      calc
        _ = realHomologyMap n id continuous_id :=
          realHomologyMap_eq_of_homotopic n _ _ e.left_inv
        _ = LinearMap.id := realHomologyMap_id n
    rw [realHomologyMap_comp] at h
    exact congrArg (fun A => A x) h
  right_inv y := by
    have h : realHomologyMap n (e ∘ e.symm) (e.continuous.comp e.symm.continuous) =
        LinearMap.id := by
      calc
        _ = realHomologyMap n id continuous_id :=
          realHomologyMap_eq_of_homotopic n _ _ e.right_inv
        _ = LinearMap.id := realHomologyMap_id n
    rw [realHomologyMap_comp] at h
    exact congrArg (fun A => A y) h

@[simp] theorem realHomologyHomotopyEquiv_apply (n : ℕ) (e : X ≃ₕ Y)
    (x : RealSingularHomology n X) :
    realHomologyHomotopyEquiv n e x = realHomologyMap n e e.continuous x := rfl

@[simp] theorem realHomologyHomotopyEquiv_symm_apply (n : ℕ) (e : X ≃ₕ Y)
    (y : RealSingularHomology n Y) :
    (realHomologyHomotopyEquiv n e).symm y =
      realHomologyMap n e.symm e.symm.continuous y := rfl

abbrev realHomologyEquivOfHomotopyEquiv (n : ℕ) (e : X ≃ₕ Y) :=
  realHomologyHomotopyEquiv n e

@[simp] theorem realHomologyEquivOfHomotopyEquiv_apply (n : ℕ) (e : X ≃ₕ Y)
    (v : RealSingularHomology n X) :
    realHomologyEquivOfHomotopyEquiv n e v = realHomologyMap n e e.continuous v := rfl

@[simp] theorem realHomologyEquivOfHomotopyEquiv_symm_apply (n : ℕ) (e : X ≃ₕ Y)
    (v : RealSingularHomology n Y) :
    (realHomologyEquivOfHomotopyEquiv n e).symm v =
      realHomologyMap n e.symm e.symm.continuous v := rfl

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.HomologyZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

def realSingularHomologyZeroEquiv (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : RealSingularHomology 0 X ≃ₗ[ℝ] ℝ :=
  (asIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℝ ℝ))).toLinearEquiv

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.IteratedSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.IteratedSubdivision

section Linear

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

def eventuallyIn (s : Module.End R M) (P : Submodule R M) : Submodule R M where
  carrier := {x | ∃ N : ℕ, ∀ n, N ≤ n → (s ^ n) x ∈ P}
  zero_mem' := ⟨0, fun n _ => by simp⟩
  add_mem' := by
    rintro x y ⟨N, hN⟩ ⟨K, hK⟩
    refine ⟨max N K, fun n hn => ?_⟩
    simpa only [map_add] using P.add_mem
      (hN n ((le_max_left N K).trans hn))
      (hK n ((le_max_right N K).trans hn))
  smul_mem' := by
    rintro a x ⟨N, hN⟩
    exact ⟨N, fun n hn => by simpa only [map_smul] using P.smul_mem a (hN n hn)⟩

end Linear

section ChainHomotopy

variable {V : Type*} [Category V] [Preadditive V]
variable {ι : Type*} {c : ComplexShape ι} {C : HomologicalComplex V c}

def chainIterate (s : C ⟶ C) : ℕ → (C ⟶ C)
  | 0 => 𝟙 C
  | n + 1 => chainIterate s n ≫ s

end ChainHomotopy

end Problem340.IteratedSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Saturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Problem340

def saturationDerivative : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def saturationPrimitive (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..r, saturationDerivative t

theorem saturationPrimitive_hasDerivAt (r : ℝ) :
    HasDerivAt saturationPrimitive (saturationDerivative r) r := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact saturationDerivative.continuous.intervalIntegrable _ _
  · exact saturationDerivative.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact saturationDerivative.continuous.continuousAt

theorem saturationPrimitive_contDiff : ContDiff ℝ ∞ saturationPrimitive := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun r => (saturationPrimitive_hasDerivAt r).differentiableAt, ?_⟩
  have h : deriv saturationPrimitive = saturationDerivative :=
    funext fun r => (saturationPrimitive_hasDerivAt r).deriv
  rw [h]
  exact saturationDerivative.contDiff

theorem saturationPrimitive_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ saturationPrimitive r := by
  exact intervalIntegral.integral_nonneg_of_forall hr saturationDerivative.nonneg'

theorem saturationPrimitive_eq_self {r : ℝ} (hr : |r| ≤ 1) :
    saturationPrimitive r = r := by
  have h : saturationPrimitive r = ∫ t in (0 : ℝ)..r, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply saturationDerivative.one_of_mem_closedBall
    change dist t 0 ≤ (1 : ℝ)
    rw [Real.dist_eq, sub_zero]
    rcases mem_uIcc.mp ht with ht | ht
    · exact abs_le.mpr ⟨by linarith [abs_nonneg r], le_trans ht.2 (le_abs_self r |>.trans hr)⟩
    · exact abs_le.mpr ⟨le_trans (neg_abs_le r |>.trans' (neg_le_neg hr)) ht.1, by linarith⟩
  simpa [saturationPrimitive] using h

theorem saturationPrimitive_monotone : Monotone saturationPrimitive := by
  apply monotone_of_hasDerivAt_nonneg saturationPrimitive_hasDerivAt
  intro r
  exact saturationDerivative.nonneg

theorem saturationPrimitive_eq_at_two {r : ℝ} (hr : 2 ≤ r) :
    saturationPrimitive r = saturationPrimitive 2 := by
  have htail : (∫ t in (2 : ℝ)..r, saturationDerivative t) = 0 := by
    calc
      _ = ∫ t in (2 : ℝ)..r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply saturationDerivative.zero_of_le_dist
        change (2 : ℝ) ≤ dist t 0
        rw [Real.dist_eq, sub_zero, abs_of_nonneg]
        · exact ((uIcc_of_le hr) ▸ ht).1
        · have := ((uIcc_of_le hr) ▸ ht).1
          linarith
      _ = 0 := by simp
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (saturationDerivative.continuous.intervalIntegrable (μ := volume) 0 2)
    (saturationDerivative.continuous.intervalIntegrable (μ := volume) 2 r)
  simpa [saturationPrimitive, htail] using hsum.symm

theorem saturationPrimitive_le_two {r : ℝ} (_hr : 0 ≤ r) :
    saturationPrimitive r ≤ 2 := by
  have htwo : saturationPrimitive 2 ≤ 2 := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..2, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (saturationDerivative.continuous.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        intro t ht
        exact saturationDerivative.le_one
      _ = 2 := by norm_num
  rcases le_total r 2 with h | h
  · exact (saturationPrimitive_monotone h).trans htwo
  · rw [saturationPrimitive_eq_at_two h]
    exact htwo

def saturationCutoff (R : ℝ) (hR : 1 ≤ R) : ContDiffBump (0 : ℝ) :=
  ⟨R, R + 1, by linarith, by linarith⟩

def saturationProfile (R : ℝ) (hR : 1 ≤ R) (r : ℝ) : ℝ :=
  saturationCutoff R hR r * saturationPrimitive r

theorem saturationProfile_contDiff (R : ℝ) (hR : 1 ≤ R) :
    ContDiff ℝ ∞ (saturationProfile R hR) :=
  (saturationCutoff R hR).contDiff.mul saturationPrimitive_contDiff

theorem saturationProfile_nonneg (R : ℝ) (hR : 1 ≤ R) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ saturationProfile R hR r :=
  mul_nonneg (saturationCutoff R hR).nonneg (saturationPrimitive_nonneg hr)

theorem saturationProfile_le_two (R : ℝ) (hR : 1 ≤ R) {r : ℝ} (hr : 0 ≤ r) :
    saturationProfile R hR r ≤ 2 := by
  calc
    _ ≤ 1 * saturationPrimitive r := mul_le_mul_of_nonneg_right
      (saturationCutoff R hR).le_one (saturationPrimitive_nonneg hr)
    _ ≤ 2 := by simpa using saturationPrimitive_le_two hr

theorem saturationProfile_eq_primitive (R : ℝ) (hR : 1 ≤ R) {r : ℝ}
    (hr : |r| ≤ R) : saturationProfile R hR r = saturationPrimitive r := by
  unfold saturationProfile
  rw [(saturationCutoff R hR).one_of_mem_closedBall (by simpa [Real.dist_eq, saturationCutoff] using hr)]
  simp

theorem saturationProfile_eq_self (R : ℝ) (hR : 1 ≤ R) {r : ℝ}
    (hr : |r| ≤ 1) : saturationProfile R hR r = r := by
  rw [saturationProfile_eq_primitive R hR (hr.trans hR), saturationPrimitive_eq_self hr]

theorem saturationProfile_eq_zero (R : ℝ) (hR : 1 ≤ R) {r : ℝ}
    (hr : R + 1 ≤ r) : saturationProfile R hR r = 0 := by
  unfold saturationProfile
  rw [(saturationCutoff R hR).zero_of_le_dist]
  · simp
  · simpa [Real.dist_eq, saturationCutoff, abs_of_nonneg (by linarith : 0 ≤ r)] using hr

def saturation (R : ℝ) (hR : 1 ≤ R) (z : ℂ) : ℂ :=
  (saturationProfile R hR ‖z‖ / ‖z‖) • z

@[simp] theorem saturation_zero (R : ℝ) (hR : 1 ≤ R) :
    saturation R hR 0 = 0 := by
  simp [saturation]

theorem saturation_eq_self (R : ℝ) (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    saturation R hR z = z := by
  by_cases hzero : z = 0
  · subst z
    exact saturation_zero R hR
  · unfold saturation
    rw [saturationProfile_eq_self R hR (by simpa only [abs_norm] using hz),
      div_self (norm_ne_zero_iff.mpr hzero), one_smul]

theorem saturation_eq_zero (R : ℝ) (hR : 1 ≤ R) {z : ℂ}
    (hz : R + 1 ≤ ‖z‖) : saturation R hR z = 0 := by
  simp [saturation, saturationProfile_eq_zero R hR hz]

theorem saturation_contDiff (R : ℝ) (hR : 1 ≤ R) :
    ContDiff ℝ ∞ (saturation R hR) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with w hw
    have hw' : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    exact saturation_eq_self R hR hw'.le
  · have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℝ hz
    exact (((saturationProfile_contDiff R hR).contDiffAt.comp z hn).div hn
      (norm_ne_zero_iff.mpr hz)).smul contDiffAt_id

theorem saturation_hasCompactSupport (R : ℝ) (hR : 1 ≤ R) :
    HasCompactSupport (saturation R hR) := by
  apply (isCompact_closedBall (0 : ℂ) (R + 1)).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  by_contra h
  have hzR : R + 1 ≤ ‖z‖ := by
    have : ¬ ‖z‖ ≤ R + 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using h
    exact (lt_of_not_ge this).le
  exact hz (saturation_eq_zero R hR hzR)

def sphereSaturation (R : ℝ) (hR : 1 ≤ R) (z : OnePoint ℂ) : ℂ :=
  z.elim 0 (saturation R hR)

@[simp] theorem sphereSaturation_infty (R : ℝ) (hR : 1 ≤ R) :
    sphereSaturation R hR OnePoint.infty = 0 := rfl

@[simp] theorem sphereSaturation_coe (R : ℝ) (hR : 1 ≤ R) (z : ℂ) :
    sphereSaturation R hR (z : OnePoint ℂ) = saturation R hR z := rfl

theorem sphereSaturation_continuous (R : ℝ) (hR : 1 ≤ R) :
    Continuous (sphereSaturation R hR) := by
  rw [OnePoint.continuous_iff]
  refine ⟨?_, (saturation_contDiff R hR).continuous⟩
  exact tendsto_const_nhds.congr'
    (hasCompactSupport_iff_eventuallyEq.mp (saturation_hasCompactSupport R hR)).symm

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

local instance instFactLtRealOfNat_solutions_1_r38616b_1 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
def concreteData (L : ℝ) (hL : 2 < L) : SphereData where
  gate := SphereCutoffs.onePointClockGate
  cutoff := SphereCutoffs.onePointPreparationCutoff
  saturation := sphereSaturation (3 * L) (by linarith)
  gain := gainProfile L
  L := L

def concreteMap (L : ℝ) (hL : 2 < L) : RawManifold → RawManifold :=
  rawMap (concreteData L hL)

@[simp] theorem concrete_saturation_zero (L : ℝ) (hL : 2 < L) :
    (concreteData L hL).saturation ((0 : ℂ) : Sphere) = 0 := by
  simp [concreteData]

@[simp] theorem concrete_gate_infty (L : ℝ) (hL : 2 < L) :
    (concreteData L hL).gate ∞ = 1 := rfl

@[simp] theorem clockIncrement_infty (L : ℝ) (hL : 2 < L)
    (t : AddCircle (100 : ℝ)) :
    clockIncrement (concreteData L hL) t ∞ = 1 := by
  simp [clockIncrement, AddCircle.liftIco]

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapClockComponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

def concreteClockAmbient (x : CounterexampleAmbient 3) : ClockAmbient :=
  Clock.ambientUpdate x.1 (SphereCutoffs.clockGateAmbient (x.2 0))

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped OnePoint

namespace Problem340.Construction

theorem continuous_cutoff_phase_pow (D : SphereData)
    (hχ : Continuous D.cutoff)
    (hzero : ∀ᶠ z in 𝓝 (((0 : ℂ) : Sphere)), D.cutoff z = 0)
    (hinfty : ∀ᶠ z in 𝓝 (∞ : Sphere), D.cutoff z = 0) (k : ℕ) :
    Continuous (fun z : Sphere => (D.cutoff z : ℂ) * phase z ^ k) := by
  rw [continuous_iff_continuousAt]
  intro z
  induction z using OnePoint.rec with
  | infty =>
      apply (show ContinuousAt (fun _ : Sphere => (0 : ℂ)) _ from
        continuousAt_const).congr_of_eventuallyEq
      filter_upwards [hinfty] with z hz
      simp [hz]
  | coe z =>
      by_cases hz : z = 0
      · subst z
        apply (show ContinuousAt (fun _ : Sphere => (0 : ℂ)) _ from
          continuousAt_const).congr_of_eventuallyEq
        filter_upwards [hzero] with z hz
        simp [hz]
      · rw [OnePoint.continuousAt_coe]
        have hcut : Continuous (fun z : ℂ => (D.cutoff (z : Sphere) : ℂ)) :=
          Complex.continuous_ofReal.comp (hχ.comp OnePoint.continuous_coe)
        have hphase : ContinuousAt (fun w : ℂ => w / (‖w‖ : ℂ)) z :=
          continuousAt_id.div
            (Complex.continuous_ofReal.continuousAt.comp continuousAt_id.norm)
            (by simp [hz])
        exact hcut.continuousAt.mul (hphase.pow k)

theorem continuous_prediction (D : SphereData) (he : Continuous D.gate) :
    Continuous (prediction D) := by
  have hb : Continuous Clock.barrier := (Clock.contDiff_barrier (n := 1)).continuous
  have hi : Continuous (fun p : ℝ × Sphere => Clock.increment p.1 (D.gate p.2)) :=
    (hb.comp continuous_fst).add
      ((continuous_const.sub (hb.comp continuous_fst)).mul (he.comp continuous_snd))
  exact (continuous_fst.add hi).prodMk
    (continuous_perturbedSquare.comp (continuous_const.prodMk continuous_snd))

theorem continuous_predictedClock (D : SphereData) (he : Continuous D.gate) (m : ℕ) :
    Continuous (fun p : ℝ × Sphere => predictedClock D m p.1 p.2) :=
  continuous_fst.comp ((continuous_prediction D he).iterate m)

theorem continuous_inputTerm (D : SphereData) (he : Continuous D.gate)
    (hangle : ∀ k : ℕ, Continuous (fun z : Sphere => (D.cutoff z : ℂ) * phase z ^ k))
    (i : Fin 3) (n : ℕ) :
    Continuous (fun p : ℝ × Sphere => inputTerm D i n p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × Sphere =>
      (((D.L⁻¹) ^ n * readoutCoeff i (predictedClock D (n + 1) p.1 p.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.mul
      (((readoutCoeff_contDiff i (n := 1)).continuous).comp
        (continuous_predictedClock D he (n + 1))))
  convert hc.mul ((hangle (2 ^ (n + 2))).comp continuous_snd) using 1
  ext p
  simp only [inputTerm, Complex.ofReal_mul, Pi.mul_apply, Function.comp_apply, mul_assoc]

theorem continuous_baseInput (D : SphereData) (he : Continuous D.gate)
    (hangle : ∀ k : ℕ, Continuous (fun z : Sphere => (D.cutoff z : ℂ) * phase z ^ k))
    (hL : 1 < D.L) (hχ0 : ∀ z, 0 ≤ D.cutoff z) (hχ1 : ∀ z, D.cutoff z ≤ 1)
    (i : Fin 3) : Continuous (fun p : ℝ × Sphere => baseInput D i p.1 p.2) := by
  have hL0 : 0 < D.L := by linarith
  have hgeom : Summable (fun n : ℕ => (D.L⁻¹) ^ n) :=
    summable_geometric_of_lt_one (inv_nonneg.mpr hL0.le) ((inv_lt_one₀ hL0).2 hL)
  have hs : Continuous (fun p : ℝ × Sphere => ∑' n : ℕ, inputTerm D i n p.1 p.2) :=
    continuous_tsum (continuous_inputTerm D he hangle i) hgeom
      (fun n p => norm_inputTerm_le D hL0.le hχ0 hχ1 i n p.1 p.2)
  exact (Complex.continuous_ofReal.comp
    (((preparationCoeff_contDiff (n := 1)).continuous.comp continuous_fst).div_const 10)).mul hs

theorem preparationCutoff_eventually_zero_at_zero :
    ∀ᶠ z in 𝓝 (((0 : ℂ) : Sphere)), SphereCutoffs.onePointPreparationCutoff z = 0 := by
  rw [OnePoint.nhds_coe_eq]
  change ∀ᶠ z : ℂ in 𝓝 0, SphereCutoffs.onePointPreparationCutoff (z : Sphere) = 0
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 3)] with z hz
  apply SphereCutoffs.affinePreparationCutoff_eq_zero_of_small
  have h : ‖z‖ < 1 / 3 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  exact h.le

theorem preparationCutoff_eventually_zero_at_infty :
    ∀ᶠ z in 𝓝 (∞ : Sphere), SphereCutoffs.onePointPreparationCutoff z = 0 := by
  rw [OnePoint.nhds_infty_eq, Filter.eventually_sup]
  constructor
  · change ∀ᶠ z : ℂ in coclosedCompact ℂ,
      SphereCutoffs.onePointPreparationCutoff (z : Sphere) = 0
    filter_upwards [(isCompact_closedBall (0 : ℂ) 2).compl_mem_coclosedCompact_of_isClosed
      Metric.isClosed_closedBall] with z hz
    apply SphereCutoffs.affinePreparationCutoff_eq_zero_of_large
    have h : 2 < ‖z‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hz
    nlinarith [sq_nonneg (‖z‖ - 2)]
  · simp

theorem continuous_baseInput_of_standard_cutoffs (D : SphereData)
    (he : D.gate = SphereCutoffs.onePointClockGate)
    (hχ : D.cutoff = SphereCutoffs.onePointPreparationCutoff)
    (hL : 1 < D.L) (i : Fin 3) :
    Continuous (fun p : ℝ × Sphere => baseInput D i p.1 p.2) := by
  apply continuous_baseInput D
  · simpa only [he] using SphereCutoffs.continuous_onePointClockGate
  · intro k
    apply continuous_cutoff_phase_pow D
    · simpa only [hχ] using SphereCutoffs.continuous_onePointPreparationCutoff
    · simpa only [hχ] using preparationCutoff_eventually_zero_at_zero
    · simpa only [hχ] using preparationCutoff_eventually_zero_at_infty
  · exact hL
  · intro z
    simpa only [hχ] using (SphereCutoffs.onePointPreparationCutoff_mem_Icc z).1
  · intro z
    simpa only [hχ] using (SphereCutoffs.onePointPreparationCutoff_mem_Icc z).2

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapQuotientContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter
open scoped Topology OnePoint

namespace Problem340.Construction

lemma baseInput_clock_mem_of_ne_zero (D : SphereData) (i : Fin 3) (x : ℝ × Sphere)
    (hx : baseInput D i x.1 x.2 ≠ 0) : x.1 ∈ Ioo 8 12 := by
  have hα : preparationCoeff x.1 ≠ 0 := by
    intro h
    apply hx
    simp [baseInput, h]
  have hmem : x.1 ∈ Function.support preparationCoeff := hα
  rwa [preparationCoeff_support] at hmem

lemma continuous_input_of_baseInput (D : SphereData) (i : Fin 3)
    (hbase : Continuous (fun x : ℝ × Sphere => baseInput D i x.1 x.2)) :
    Continuous (fun x : AddCircle (100 : ℝ) × Sphere => input D i x.1 x.2) := by
  let : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
  apply ClockQuotient.continuous_liftIco_of_strip_support hbase
  intro x hx
  have h := baseInput_clock_mem_of_ne_zero D i x hx
  constructor <;> linarith [h.1, h.2]

lemma continuous_clockIncrement (D : SphereData) (hg : Continuous D.gate) :
    Continuous (fun x : AddCircle (100 : ℝ) × Sphere => clockIncrement D x.1 x.2) := by
  let : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
  unfold clockIncrement
  apply ClockQuotient.continuous_liftIco_of_periodic
    (f := fun x : ℝ × Sphere => Clock.increment x.1 (D.gate x.2))
    (fun z => Clock.increment_periodic (D.gate z))
  have hb : Continuous (fun x : ℝ × Sphere => Clock.barrier x.1) :=
    (Clock.contDiff_barrier (n := 1)).continuous.comp continuous_fst
  exact hb.add ((continuous_const.sub hb).mul (hg.comp continuous_snd))

lemma continuous_periodicReadout (i : Fin 3) : Continuous (periodicReadout i) := by
  let : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
  apply AddCircle.liftIco_zero_continuous
  · have hz (t : ℝ) (ht : t ∉ Ioo 74 80) : readoutCoeff i t = 0 := by
      by_contra h
      have hm : t ∈ Function.support (readoutCoeff i) := h
      rw [readoutCoeff_support] at hm
      exact ht (readoutInterval_subset i hm)
    rw [hz 0 (by norm_num), hz 100 (by norm_num)]
  · exact (readoutCoeff_contDiff i (n := 1)).continuous.continuousOn

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SkewProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

open scoped OnePoint

abbrev RawState (q : ℕ) := AddCircle (100 : ℝ) × OnePoint ℂ × (Fin q → OnePoint ℂ)

def rawQuadratic (p : ℂ × OnePoint ℂ) : OnePoint ℂ :=
  OnePoint.map (fun z : ℂ => z ^ 2 + p.1) p.2

theorem continuous_rawQuadratic : Continuous rawQuadratic :=
  continuous_perturbedSquare

def rawUpdate {q : ℕ} (h : RawState q → ℝ) (C : RawState q → ℂ)
    (R : RawState q → Fin q → ℂ) (x : RawState q) : RawState q :=
  (x.1 + (h x : AddCircle (100 : ℝ)), rawQuadratic (C x, x.2.1),
    fun i => (R x i : OnePoint ℂ))

def rawUpdateAtTime {q : ℕ} (h : RawState q → ℝ) (C : RawState q → ℂ)
    (R : RawState q → Fin q → ℂ) (s : ℝ) (x : RawState q) : RawState q :=
  rawUpdate (fun y => s * h y) (fun y => (s : ℂ) * C y)
    (fun y i => (s : ℂ) * R y i) x

def rawNormalForm {q : ℕ} (x : RawState q) : RawState q :=
  (x.1, OnePoint.map (fun z : ℂ => z ^ 2) x.2.1,
    fun _ => ((0 : ℂ) : OnePoint ℂ))

@[simp] theorem rawUpdateAtTime_zero {q : ℕ} (h : RawState q → ℝ)
    (C : RawState q → ℂ) (R : RawState q → Fin q → ℂ) (x : RawState q) :
    rawUpdateAtTime h C R 0 x = rawNormalForm x := by
  simp [rawUpdateAtTime, rawUpdate, rawQuadratic, rawNormalForm]

@[simp] theorem rawUpdateAtTime_one {q : ℕ} (h : RawState q → ℝ)
    (C : RawState q → ℂ) (R : RawState q → Fin q → ℂ) (x : RawState q) :
    rawUpdateAtTime h C R 1 x = rawUpdate h C R x := by
  simp [rawUpdateAtTime]

theorem continuous_rawUpdate {q : ℕ}
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R) :
    Continuous (rawUpdate h C R) := by
  apply Continuous.prodMk
  · exact continuous_fst.add ((AddCircle.continuous_mk' (100 : ℝ)).comp hh)
  · apply Continuous.prodMk
    · exact continuous_rawQuadratic.comp (hC.prodMk (continuous_fst.comp continuous_snd))
    · exact continuous_pi fun i => OnePoint.continuous_coe.comp
        ((continuous_apply i).comp hR)

theorem continuous_rawUpdateAtTime {q : ℕ}
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R) :
    Continuous (fun p : ℝ × RawState q => rawUpdateAtTime h C R p.1 p.2) := by
  unfold rawUpdateAtTime rawUpdate
  apply Continuous.prodMk
  · exact (continuous_fst.comp continuous_snd).add
      ((AddCircle.continuous_mk' (100 : ℝ)).comp
        (continuous_fst.mul (hh.comp continuous_snd)))
  · apply Continuous.prodMk
    · exact continuous_rawQuadratic.comp (((Complex.continuous_ofReal.comp continuous_fst).mul
        (hC.comp continuous_snd)).prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_snd)))
    · exact continuous_pi fun i => OnePoint.continuous_coe.comp
        ((Complex.continuous_ofReal.comp continuous_fst).mul
          (((continuous_apply i).comp hR).comp continuous_snd))

theorem continuous_rawNormalForm {q : ℕ} :
    Continuous (@rawNormalForm q) := by
  have H := continuous_rawUpdateAtTime (q := q)
    (h := fun _ => 0) (C := fun _ => 0) (R := fun _ _ => 0)
    continuous_const continuous_const continuous_const
  simpa [Function.comp_def] using H.comp ((continuous_const : Continuous (fun _ : RawState q => (0 : ℝ))).prodMk continuous_id)

def rawUpdateHomotopy {q : ℕ}
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R) :
    ContinuousMap.Homotopy
      ⟨rawNormalForm, continuous_rawNormalForm⟩
      ⟨rawUpdate h C R, continuous_rawUpdate hh hC hR⟩ where
  toFun p := rawUpdateAtTime h C R (p.1 : ℝ) p.2
  continuous_toFun := (continuous_rawUpdateAtTime hh hC hR).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left := rawUpdateAtTime_zero h C R
  map_one_left := rawUpdateAtTime_one h C R

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SkewProductHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

def rawSphereSection (q : ℕ) (z : OnePoint ℂ) : RawState q :=
  (0, z, fun _ => ((0 : ℂ) : OnePoint ℂ))

def rawSphereProjection {q : ℕ} (x : RawState q) : OnePoint ℂ := x.2.1

def rawSphereSquare : OnePoint ℂ → OnePoint ℂ :=
  OnePoint.map (fun z : ℂ => z ^ 2)

theorem continuous_rawSphereSquare : Continuous rawSphereSquare := by
  simpa [rawQuadratic, rawSphereSquare, Function.comp_def] using
    continuous_rawQuadratic.comp (continuous_const.prodMk continuous_id :
      Continuous (fun z : OnePoint ℂ => ((0 : ℂ), z)))

@[simp] theorem rawSphereProjection_section (q : ℕ) (z : OnePoint ℂ) :
    rawSphereProjection (rawSphereSection q z) = z := rfl

@[simp] theorem rawNormalForm_section (q : ℕ) (z : OnePoint ℂ) :
    rawNormalForm (rawSphereSection q z) = rawSphereSection q (rawSphereSquare z) := rfl

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

def rawClockFunction (D : SphereData) (x : RawManifold) : ℝ :=
  clockIncrement D x.1 x.2.1

def rawPerturbation (D : SphereData) (x : RawManifold) : ℂ :=
  readout D x.1 x.2.2

def rawRegisterFunction (D : SphereData) (x : RawManifold) (i : Fin 3) : ℂ :=
  (periodicGain D x.1 : ℂ) * D.saturation (x.2.2 i) + input D i x.1 x.2.1

theorem continuous_rawMap_of_rawCoefficients (D : SphereData)
    (hh : Continuous (rawClockFunction D)) (hC : Continuous (rawPerturbation D))
    (hR : Continuous (rawRegisterFunction D)) : Continuous (rawMap D) :=
  continuous_rawUpdate hh hC hR

def rawMapHomotopy (D : SphereData)
    (hh : Continuous (rawClockFunction D)) (hC : Continuous (rawPerturbation D))
    (hR : Continuous (rawRegisterFunction D)) :
    ContinuousMap.Homotopy
      ⟨(@rawNormalForm 3), continuous_rawNormalForm⟩
      ⟨rawMap D, continuous_rawMap_of_rawCoefficients D hh hC hR⟩ :=
  rawUpdateHomotopy hh hC hR

theorem continuous_rawCoefficients (D : SphereData)
    (hh : Continuous (fun p : AddCircle (100 : ℝ) × Sphere => clockIncrement D p.1 p.2))
    (hβ : ∀ i, Continuous (periodicReadout i))
    (ha : Continuous (periodicGain D)) (hS : Continuous D.saturation)
    (hU : ∀ i, Continuous (fun p : AddCircle (100 : ℝ) × Sphere => input D i p.1 p.2)) :
    Continuous (rawClockFunction D) ∧ Continuous (rawPerturbation D) ∧
      Continuous (rawRegisterFunction D) := by
  let p : RawManifold → AddCircle (100 : ℝ) × Sphere := fun x => (x.1, x.2.1)
  have hp : Continuous p := continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  let clock : RawManifold → AddCircle (100 : ℝ) := Prod.fst
  have ht : Continuous clock := continuous_fst
  let regs (i : Fin 3) : RawManifold → Sphere := fun x => x.2.2 i
  have hr (i : Fin 3) : Continuous (regs i) :=
    (continuous_apply i).comp (continuous_snd.comp continuous_snd)
  constructor
  · have H := hh.comp hp
    exact H
  constructor
  · unfold rawPerturbation readout
    apply continuous_const.mul
    apply continuous_finsetSum
    intro i _
    have H := (Complex.continuous_ofReal.comp ((hβ i).comp ht)).mul (hS.comp (hr i))
    exact H
  · unfold rawRegisterFunction
    apply continuous_pi
    intro i
    have H := ((Complex.continuous_ofReal.comp (ha.comp ht)).mul (hS.comp (hr i))).add
      ((hU i).comp hp)
    exact H

theorem continuous_concrete_rawCoefficients (L : ℝ) (hL : 2 < L) :
    Continuous (rawClockFunction (concreteData L hL)) ∧
      Continuous (rawPerturbation (concreteData L hL)) ∧
      Continuous (rawRegisterFunction (concreteData L hL)) := by
  let D := concreteData L hL
  have hg : Continuous D.gate := SphereCutoffs.continuous_onePointClockGate
  have hS : Continuous D.saturation := sphereSaturation_continuous (3 * L) _
  have hbase (i : Fin 3) : Continuous (fun x : ℝ × Sphere => baseInput D i x.1 x.2) :=
    continuous_baseInput_of_standard_cutoffs D rfl rfl (by change 1 < L; linarith) i
  have ha : Continuous (periodicGain D) := by
    let : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
    apply AddCircle.liftIco_zero_continuous
    · change gainProfile L 0 = gainProfile L 100
      rw [gainProfile_zero_outside (by norm_num), gainProfile_zero_outside (by norm_num)]
    · exact (gainProfile_contDiff L).continuous.continuousOn
  exact continuous_rawCoefficients D (continuous_clockIncrement D hg)
    continuous_periodicReadout ha hS (fun i => continuous_input_of_baseInput D i (hbase i))

theorem concreteMap_continuous_for_homotopy (L : ℝ) (hL : 2 < L) :
    Continuous (concreteMap L hL) := by
  obtain ⟨hh, hC, hR⟩ := continuous_concrete_rawCoefficients L hL
  exact continuous_rawMap_of_rawCoefficients (concreteData L hL) hh hC hR

def concreteMapHomotopy (L : ℝ) (hL : 2 < L) :
    ContinuousMap.Homotopy
      ⟨(@rawNormalForm 3), continuous_rawNormalForm⟩
      ⟨concreteMap L hL, concreteMap_continuous_for_homotopy L hL⟩ := by
  obtain ⟨hh, hC, hR⟩ := continuous_concrete_rawCoefficients L hL
  exact rawMapHomotopy (concreteData L hL) hh hC hR

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapOrbitLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

def rawClockLift (D : SphereData) (x : RawManifold) (t₀ : ℝ) : ℕ → ℝ :=
  orbitClockLift (rawMap D) (fun y => clockIncrement D y.1 y.2.1) x t₀

@[simp] theorem rawClockLift_zero (D : SphereData) (x : RawManifold) (t₀ : ℝ) :
    rawClockLift D x t₀ 0 = t₀ := by
  simp [rawClockLift]

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PassagePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.PassagePhase

def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

def gain {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (n : ℕ) : ℝ :=
  2 * (∑ l ∈ J, β n l ^ 2) * (∑ i ∈ I, w i)

end Problem340.PassagePhase

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapPassagePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

def passageWeight (D : SphereData) (t : ℕ → ℝ) (z : ℕ → ℂ) (i : ℕ) : ℝ :=
  preparationCoeff (t i) * D.cutoff ((z i : ℂ) : Sphere)

def orbitReadoutCoeff (x : ℕ → RawManifold) (n : ℕ) (l : Fin 3) : ℝ :=
  periodicReadout l (x n).1

def orbitSaturatedRegister (D : SphereData) (x : ℕ → RawManifold)
    (n : ℕ) (l : Fin 3) : ℂ := D.saturation ((x n).2.2 l)

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapPassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

def HasScheduledPassageAt (t : ℕ → ℝ) (k : ℤ) : Prop :=
    ∃ lo hi : ℕ,
      let s := fun n => t n - 100 * (k : ℝ)
      let I := (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (s i))
      lo < hi ∧ (0 ≤ s lo ∧ s lo < 1) ∧ (100 ≤ s hi ∧ s hi < 101) ∧
      (∀ n, lo ≤ n → n < hi → 0 ≤ s n ∧ s n < 100) ∧
      I.Nonempty ∧ I.card ≤ 5 ∧
      (∃ i ∈ I, preparationCoeff (s i) = 1) ∧
      (∃ r ∈ Finset.Ico lo hi, 2 ≤ s r ∧ s r < 3 ∧ ∀ i ∈ I, r + 1 ≤ i) ∧
      (∃ j ∈ Finset.Ico lo hi, 76 ≤ s j ∧ s j < 77 ∧
        ∃ l : Fin 3, readoutCoeff l (s j) = 1)

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapSignals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

@[simp] theorem clock_coe_add_int_period (t : ℝ) (k : ℤ) :
    ((t + 100 * (k : ℝ) : ℝ) : AddCircle (100 : ℝ)) = (t : AddCircle (100 : ℝ)) := by
  have hzero : ((100 * (k : ℝ) : ℝ) : AddCircle (100 : ℝ)) = 0 := by
    rw [mul_comm, ← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
  rw [AddCircle.coe_add, hzero, add_zero]

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapSignal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

def scheduledSignal (D : SphereData) (ℓ : Fin 3) (ti tj : ℝ)
    (z : Sphere) (delay : ℕ) : ℂ :=
  (preparationCoeff ti * readoutCoeff ℓ tj / 10) •
    ((D.cutoff z : ℂ) * phase z ^ (2 ^ (delay + 1)))

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RegisterLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340
namespace Register

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def delayedCandidate (L : ℝ) (j : ℕ) (c : ℕ → E) (n : ℕ) : E :=
  L ^ ((n : ℤ) - (j : ℤ)) • ∑ i ∈ Finset.range n, c i

@[simp] theorem delayedCandidate_zero (L : ℝ) (j : ℕ) (c : ℕ → E) :
    delayedCandidate L j c 0 = 0 := by
  simp [delayedCandidate]

@[simp] theorem delayedCandidate_readout (L : ℝ) (j : ℕ) (c : ℕ → E) :
    delayedCandidate L j c j = ∑ i ∈ Finset.range j, c i := by
  simp [delayedCandidate]

end Register
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

def passagePreparationIndices (t : ℕ → ℝ) (s j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico s j).filter (fun n => preparationCoeff (t n) ≠ 0)

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapOrbitAlternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped Topology OnePoint

namespace Problem340.Construction

local instance instFactLtRealOfNat_solutions_6_r38616b_1 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
def CompletePassageEstimates (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (z : ℕ → ℂ) : Prop :=
  ∀ k : ℤ, t₀ < 100 * (k : ℝ) →
    ∃ s hi : ℕ, 100 * (k : ℝ) ≤ rawClockLift D x t₀ s ∧
      rawClockLift D x t₀ s < 100 * (k : ℝ) + 74 ∧
      100 * (k : ℝ) + 80 ≤ rawClockLift D x t₀ hi ∧
      (∀ n, s ≤ n → n < hi → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖) ∧
      ∃ j, s ≤ j ∧ j ≤ hi ∧ 1 < ‖z j‖

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RealizedConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

local instance instFactLtRealOfNat_solutions_2 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

def modelHomeomorph : RawManifold ≃ₜ CounterexampleManifold 3 :=
  ClockModel.productHomeomorph 3 complexSphereHomeomorph

def realizedMap (L : ℝ) (hL : 2 < L) :
    CounterexampleManifold 3 → CounterexampleManifold 3 :=
  conjugateMap modelHomeomorph (concreteMap L hL)

@[simp] theorem modelHomeomorph_clock (x : RawManifold) :
    (modelHomeomorph x).1 = ClockModel.clockHomeomorph x.1 := rfl

@[simp] theorem modelHomeomorph_main (x : RawManifold) :
    (modelHomeomorph x).2 0 = complexSphereHomeomorph x.2.1 := rfl

@[simp] theorem modelHomeomorph_register (x : RawManifold) (i : Fin 3) :
    (modelHomeomorph x).2 i.succ = complexSphereHomeomorph (x.2.2 i) := rfl

@[simp] theorem realizedMap_modelHomeomorph (L : ℝ) (hL : 2 < L) (x : RawManifold) :
    realizedMap L hL (modelHomeomorph x) = modelHomeomorph (concreteMap L hL x) :=
  conjugateMap_apply _ _ _

theorem continuous_realizedMap (L : ℝ) (hL : 2 < L)
    (hf : Continuous (concreteMap L hL)) : Continuous (realizedMap L hL) :=
  continuous_conjugateMap modelHomeomorph hf

def modelEmbedding : RawManifold → CounterexampleAmbient 3 :=
  standardEmbedding 3 ∘ modelHomeomorph

@[implicit_reducible]
def modelUniformSpace : UniformSpace RawManifold := uniformSpaceOfCompactR1

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SpectralRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

def homologyEigenvalueRadii {X : Type} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) : Set ℝ :=
  {r : ℝ | ∃ n : ℕ, ∃ a b : ℝ, ∃ u v : RealSingularHomology n X,
    (u ≠ 0 ∨ v ≠ 0) ∧
    realHomologyMap n f hf u = a • u - b • v ∧
    realHomologyMap n f hf v = b • u + a • v ∧
    r = Real.sqrt (a ^ 2 + b ^ 2)}

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapRealizedHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem continuous_realizedMap_actual (L : ℝ) (hL : 2 < L) :
    Continuous (realizedMap L hL) :=
  continuous_realizedMap L hL (concreteMap_continuous_for_homotopy L hL)

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereCompactSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace Problem340
namespace SphereCompactSupport

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {v : E} (hv : ‖v‖ = 1)

def extension (F : (ℝ ∙ v)ᗮ → W) (x : sphere (0 : E) 1) : W :=
  by
  classical
  exact if (x : E) = v then 0 else F (stereoToFun v x)

omit [NormedSpace ℝ W] in
@[simp] theorem extension_pole (F : (ℝ ∙ v)ᗮ → W) :
    extension F (⟨v, by simp [hv]⟩ : sphere (0 : E) 1) = 0 := by
  simp [extension]

end SphereCompactSupport
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.StandardSaturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace Problem340

def saturationOnEquator (R : ℝ) (hR : 1 ≤ R)
    (w : (ℝ ∙ chartNorthVector)ᗮ) : ℂ :=
  saturation R hR ((1 / 2 : ℝ) • chartEquatorEquiv.symm w)

def standardSphereSaturation (R : ℝ) (hR : 1 ≤ R) : StandardSphere2 → ℂ :=
  SphereCompactSupport.extension (saturationOnEquator R hR)

@[simp] theorem standardSphereSaturation_north (R : ℝ) (hR : 1 ≤ R) :
    standardSphereSaturation R hR chartNorthPole = 0 := by
  exact SphereCompactSupport.extension_pole norm_chartNorthVector _

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.StandardRegisterUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set
open scoped ContDiff

namespace Problem340

def standardRegisterUpdate (R : ℝ) (hR : 1 ≤ R) (a : ℝ) (c : ℂ)
    (x : StandardSphere2) : StandardSphere2 :=
  sphereOfComplex (a • standardSphereSaturation R hR x + c)

@[simp] theorem standardRegisterUpdate_north (R : ℝ) (hR : 1 ≤ R)
    (a : ℝ) (c : ℂ) :
    standardRegisterUpdate R hR a c chartNorthPole = sphereOfComplex c := by
  simp [standardRegisterUpdate]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapRegisterRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

def registerInputInStandardCoordinates (L : ℝ) (hL : 2 < L) (i : Fin 3)
    (x : CounterexampleManifold 3) : ℂ :=
  input (concreteData L hL) i (clockHomeomorph.symm x.1)
    (complexSphereHomeomorph.symm (x.2 0))

def registerOutputInStandardCoordinates (L : ℝ) (hL : 2 < L) (i : Fin 3)
    (x : CounterexampleManifold 3) : StandardSphere2 :=
  standardRegisterUpdate (3 * L) (by linarith) (standardGain L x.1)
    (registerInputInStandardCoordinates L hL i x) (x.2 i.succ)

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SparseVisits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Function Set Filter
open scoped BigOperators

namespace Problem340

noncomputable def outsideVisitsCount {X : Type*} (T : X → X) (V : Set X)
    (n : ℕ) (x : X) : ℕ := by
  classical
  exact ((Finset.range n).filter (fun i => T^[i] x ∉ V)).card

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RawInvariantInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340

def rawInfinityPoint (q : ℕ) (t : ClockAtInfinity.Clock) : RawState q :=
  (t, ∞, fun _ => ((0 : ℂ) : OnePoint ℂ))

def rawInfinitySet (q : ℕ) : Set (RawState q) := Set.range (rawInfinityPoint q)

@[continuity, fun_prop]
theorem continuous_rawInfinityPoint (q : ℕ) : Continuous (rawInfinityPoint q) := by
  exact continuous_id.prodMk (continuous_const.prodMk continuous_const)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RawInvariantSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.RawInvariantSets

def zeroSlice {q : ℕ} (t₀ : AddCircle (100 : ℝ))
    (v : Fin q → OnePoint ℂ) : RawState q :=
  (t₀, ((0 : ℂ) : OnePoint ℂ), v)

def registerMap {q : ℕ} (T : OnePoint ℂ → ℂ)
    (v : Fin q → OnePoint ℂ) : Fin q → OnePoint ℂ :=
  fun i => (T (v i) : OnePoint ℂ)

@[continuity, fun_prop]
theorem continuous_zeroSlice {q : ℕ} (t₀ : AddCircle (100 : ℝ)) :
    Continuous (@zeroSlice q t₀) := by
  exact continuous_const.prodMk (continuous_const.prodMk continuous_id)

def zeroSet (q : ℕ) (t₀ : AddCircle (100 : ℝ)) : Set (RawState q) :=
  Set.range (zeroSlice t₀)

end Problem340.RawInvariantSets

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.OrderedIntervalLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

def orderedIntervalLabel (A ε : ℝ) (hε : 0 < ε) :
    Set.Icc (0 : ℝ) A → Fin (Nat.floor (A / ε) + 1) :=
  fun r => ⟨Nat.floor ((r : ℝ) / ε), Nat.lt_succ_of_le
    (Nat.floor_le_floor (div_le_div_of_nonneg_right r.property.2 hε.le))⟩

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MonotoneItineraries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem340
namespace MonotoneItineraries

open Finset

def labelSum {N H : ℕ} (v : Fin N → Fin H) : ℕ :=
  ∑ i, (v i).val

def itinerary {α : Type*} {H : ℕ} (R : α → α) (b : α → Fin H)
    (N : ℕ) (x : α) : Fin N → Fin H := fun i => b (R^[i.val] x)

end MonotoneItineraries
end Problem340

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PolarProductEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem340
namespace PolarProductEntropy

open Set Dynamics
open scoped Uniformity

def radialProduct {α S : Type*} (R : α → α) (q : ℕ)
    (x : Fin q → α × S) : Fin q → α × S :=
  fun j => (R (x j).1, (x j).2)

end PolarProductEntropy
end Problem340

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RadialRegisterEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem340
namespace RadialRegisterEntropy

open Set Dynamics

abbrev UnitComplex := Metric.sphere (0 : ℂ) (1 : ℝ)

def coordinatewise {X : Type*} (T : X → X) (q : ℕ) (x : Fin q → X) : Fin q → X :=
  fun j => T (x j)

end RadialRegisterEntropy
end Problem340

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SaturationEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340
namespace SaturationEntropy

open Set Dynamics

def radiusMap (L : ℝ) (hL : 1 ≤ L) :
    Set.Icc (0 : ℝ) (3 * L) → Set.Icc (0 : ℝ) (3 * L) :=
  fun r => ⟨L * saturationProfile (3 * L) (by linarith) r,
    mul_nonneg (by linarith) (saturationProfile_nonneg _ _ r.property.1), by
      have hp := saturationProfile_le_two (3 * L) (by linarith) r.property.1
      nlinarith⟩

section OnePoint

local instance instUniformSpaceOnePointComplex_solutions : UniformSpace (OnePoint ℂ) := uniformSpaceOfCompactR1

end OnePoint

end SaturationEntropy
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapTerminalEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction.TerminalEntropy

open RawInvariantSets

def registers (L : ℝ) (hL : 2 < L) : (Fin 3 → Sphere) → (Fin 3 → Sphere) :=
  registerMap (fun z => (L : ℂ) * (concreteData L hL).saturation z)

def terminalSet : Set RawManifold :=
  zeroSet 3 ((50 : ℝ) : AddCircle (100 : ℝ)) ∪ rawInfinitySet 3

end Problem340.Construction.TerminalEntropy

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PolynomialSpectralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.PolynomialSpectrum

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def HasPair (A : Module.End ℝ V) (z : ℂ) (u v : V) : Prop :=
  A u = z.re • u - z.im • v ∧ A v = z.im • u + z.re • v

def pairRadii (A : Module.End ℝ V) : Set ℝ :=
  {r | ∃ a b : ℝ, ∃ u v : V,
    (u ≠ 0 ∨ v ≠ 0) ∧
    A u = a • u - b • v ∧ A v = b • u + a • v ∧
    r = Real.sqrt (a ^ 2 + b ^ 2)}

end Problem340.PolynomialSpectrum

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RawSpectrumFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

open PolynomialSpectrum
open scoped OnePoint

abbrev RawBase := AddCircle (100 : ℝ) × OnePoint ℂ

def rawBaseSquare (x : RawBase) : RawBase :=
  (x.1, OnePoint.map (fun z : ℂ => z ^ 2) x.2)

def rawBaseProjection {q : ℕ} (x : RawState q) : RawBase :=
  (x.1, x.2.1)

def rawFactorInclusion {q : ℕ} (x : RawBase) : RawState q :=
  (x.1, OnePoint.map (fun z : ℂ => z ^ 2) x.2,
    fun _ => ((0 : ℂ) : OnePoint ℂ))

theorem continuous_rawBaseSquare : Continuous rawBaseSquare := by
  apply continuous_fst.prodMk
  simpa [rawQuadratic, Function.comp_def] using
    continuous_rawQuadratic.comp
      ((continuous_const : Continuous (fun _ : RawBase => (0 : ℂ))).prodMk continuous_snd)

@[simp] theorem rawNormalForm_eq_factor {q : ℕ} :
    @rawNormalForm q = rawFactorInclusion ∘ rawBaseProjection := rfl

@[simp] theorem rawProjection_factor_eq_square {q : ℕ} :
    @rawBaseProjection q ∘ rawFactorInclusion = rawBaseSquare := rfl

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RawBaseGoodCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.CoordinateGoodCover

def rawBaseGoodCover : GoodCover ((Bool × Fin 2) × (Bool × Fin 3)) RawBase :=
  clockSphereGoodCover.comap
    (ClockModel.clockHomeomorph.prodCongr complexSphereHomeomorph)

end Problem340.CoordinateGoodCover

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ReadoutLocalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContDiff

namespace Problem340

local instance instFactLtRealOfNat_solutions : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

def periodicReadoutReal (i : Fin 3) (t : ℝ) : ℝ :=
  ClockPeriodization.periodize 100 (fun x : ℝ × ℝ => readoutCoeff i x.1) (t, 0)

def standardReader (i : Fin 3) (x : StandardClock) : ℝ :=
  AddCircle.liftIco (100 : ℝ) 0 (readoutCoeff i) (clockHomeomorph.symm x)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SimplexSubdivisionMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric

namespace Problem340.SimplexSubdivision

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def faceCenter (v : ι → E) (s : Finset ι) : E :=
  s.centerMass (fun _ => (1 : ℝ)) v

end Problem340.SimplexSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RecursiveSubdivisionMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric

namespace Problem340.SimplexSubdivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def BarycentricCell : (n : ℕ) → (Fin (n + 1) → E) → (Fin (n + 1) → E) → Prop
  | 0, v, w => w = v
  | n + 1, v, w => ∃ i : Fin (n + 2), ∃ u : Fin (n + 1) → E,
      BarycentricCell n (v ∘ i.succAbove) u ∧
        w = Fin.cons (faceCenter v Finset.univ) u

end Problem340.SimplexSubdivision

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularCoverChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularCover

variable {X : Type} [TopologicalSpace X]

instance chainFunctor_preservesColimitsOfShape (J : Type) [Category J] :
    PreservesColimitsOfShape J
      ((SSet.chainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J
    ((evaluation SimplexCategoryᵒᵖ (Type _)).obj (op ⦋n⦌) ⋙
      sigmaConst.obj (ModuleCat.of ℝ ℝ))
  infer_instance

theorem union_isPushout {K : SSet} (A B : K.Subcomplex) :
    IsPushout
      (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
      (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
      (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
      (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) := by
  apply SSet.Subcomplex.BicartSq.isPushout
  exact ⟨rfl, rfl⟩

theorem chainUnion_isPushout {K : SSet} (A B : K.Subcomplex) :
    IsPushout
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) (ModuleCat.of ℝ ℝ))
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) (ModuleCat.of ℝ ℝ))
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)) (ModuleCat.of ℝ ℝ))
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) (ModuleCat.of ℝ ℝ)) :=
  (union_isPushout A B).map
    ((SSet.chainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ))

def unionShortComplex {K : SSet} (A B : K.Subcomplex) :
    ShortComplex (ChainComplex (ModuleCat ℝ) ℕ) :=
  (chainUnion_isPushout A B).shortComplex

theorem unionShortComplex_exact {K : SSet} (A B : K.Subcomplex) :
    (unionShortComplex A B).Exact :=
  (chainUnion_isPushout A B).exact_shortComplex

theorem chainMap_mono {K L : SSet} (f : K ⟶ L) [Mono f] :
    Mono (SSet.chainComplexMap f (ModuleCat.of ℝ ℝ)) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono ((sigmaConst.obj (ModuleCat.of ℝ ℝ)).map (f.app (op ⦋n⦌)))
  infer_instance

theorem unionShortComplex_shortExact {K : SSet} (A B : K.Subcomplex) :
    (unionShortComplex A B).ShortExact := by
  have : Epi (unionShortComplex A B).g :=
    (chainUnion_isPushout A B).epi_shortComplex_g
  have : Mono (unionShortComplex A B).f := by
    change Mono (biprod.lift _ _)
    exact @biprod.mono_lift_of_mono_left _ _ _ _ _ _ _ _ _ (chainMap_mono _)
  exact { exact := unionShortComplex_exact A B }

end Problem340.SingularCover

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SimplicialMayerVietoris
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SimplicialMayerVietoris

abbrev coefficients : ModuleCat ℝ := ModuleCat.of ℝ ℝ

variable {X : SSet} (A B : X.Subcomplex)

abbrev sequence := SingularCover.unionShortComplex A B

def connecting (n : ℕ) :
    (A ⊔ B : X.Subcomplex).toSSet.homology coefficients (n + 1) ⟶
      (A ⊓ B : X.Subcomplex).toSSet.homology coefficients n :=
  (SingularCover.unionShortComplex_shortExact A B).δ (n + 1) n rfl

theorem middle_homology_isZero (n : ℕ)
    (hA : IsZero (A.toSSet.homology coefficients n))
    (hB : IsZero (B.toSSet.homology coefficients n)) :
    IsZero ((sequence A B).X₂.homology n) := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts
    (HomologicalComplex.homologyFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) n)
  change IsZero ((A.toSSet.chainComplex coefficients ⊞
    B.toSSet.chainComplex coefficients).homology n)
  exact IsZero.of_iso ((biprod_isZero_iff _ _).mpr ⟨hA, hB⟩)
    ((HomologicalComplex.homologyFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) n).mapBiprod _ _)

def connectingIso (n : ℕ)
    (hA₁ : IsZero (A.toSSet.homology coefficients (n + 1)))
    (hB₁ : IsZero (B.toSSet.homology coefficients (n + 1)))
    (hA₀ : IsZero (A.toSSet.homology coefficients n))
    (hB₀ : IsZero (B.toSSet.homology coefficients n)) :
    (A ⊔ B : X.Subcomplex).toSSet.homology coefficients (n + 1) ≅
      (A ⊓ B : X.Subcomplex).toSSet.homology coefficients n :=
  (SingularCover.unionShortComplex_shortExact A B).δIso (n + 1) n rfl
    (middle_homology_isZero A B (n + 1) hA₁ hB₁)
    (middle_homology_isZero A B n hA₀ hB₀)

end Problem340.SimplicialMayerVietoris

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSmallChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularSmallChains

variable {X : Type} [TopologicalSpace X]

abbrev singularSet (X : Type) [TopologicalSpace X] : SSet :=
  TopCat.toSSet.obj (TopCat.of X)

def inSubset (s : Set X) : (singularSet X).Subcomplex where
  obj n := {σ | ∀ p, TopCat.toSSetObjEquiv (TopCat.of X) n σ p ∈ s}
  map {n m} f σ hσ := by
    intro p
    exact hσ (SStd.map f.unop p)

@[simp] theorem mem_inSubset {s : Set X} {n : SimplexCategoryᵒᵖ}
    (σ : (singularSet X).obj n) :
    σ ∈ (inSubset s).obj n ↔
      Set.range (TopCat.toSSetObjEquiv (TopCat.of X) n σ) ⊆ s := by
  simp only [inSubset, Set.mem_ofPred_eq, Set.range_subset_iff]

@[simp] theorem inSubset_univ : inSubset (Set.univ : Set X) = ⊤ := by
  ext n σ
  simp [inSubset]

@[simp] theorem inSubset_inter (s t : Set X) :
    inSubset (s ∩ t) = inSubset s ⊓ inSubset t := by
  ext n σ
  simp [inSubset, forall_and]

def small {ι : Type*} (U : ι → Set X) : (singularSet X).Subcomplex :=
  ⨆ i, inSubset (U i)

@[simp] theorem mem_small {ι : Type*} (U : ι → Set X)
    {n : SimplexCategoryᵒᵖ} (σ : (singularSet X).obj n) :
    σ ∈ (small U).obj n ↔
      ∃ i, Set.range (TopCat.toSSetObjEquiv (TopCat.of X) n σ) ⊆ U i := by
  simp [small]

abbrev chains {ι : Type*} (U : ι → Set X) :=
  (small U : SSet).chainComplex (ModuleCat.of ℝ ℝ)

def inclusion {ι : Type*} (U : ι → Set X) : chains U ⟶ realSingularChainComplex X :=
  SSet.chainComplexMap (small U).ι (ModuleCat.of ℝ ℝ)

instance inclusion_f_mono {ι : Type*} (U : ι → Set X) (n : ℕ) :
    Mono ((inclusion U).f n) := by
  change Mono ((sigmaConst.obj (ModuleCat.of ℝ ℝ)).map ((small U).ι.app (op ⦋n⦌)))
  infer_instance

def subspaceMap (s : Set X) : singularSet s ⟶ inSubset s where
  app n := TypeCat.ofHom fun σ =>
    ⟨(TopCat.toSSet.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).app n σ,
      fun p => (TopCat.toSSetObjEquiv (TopCat.of s) n σ p).property⟩
  naturality {n m} f := by
    ext σ
    apply Subtype.ext
    rfl

def subspaceInverse (s : Set X) : (inSubset s : SSet) ⟶ singularSet s where
  app n := TypeCat.ofHom fun σ =>
    (TopCat.toSSetObjEquiv (TopCat.of s) n).symm
      ⟨fun p => ⟨TopCat.toSSetObjEquiv (TopCat.of X) n σ.val p, σ.property p⟩,
        (TopCat.toSSetObjEquiv (TopCat.of X) n σ.val).continuous.subtype_mk _⟩
  naturality {n m} f := by
    ext σ
    rfl

def subspaceIso (s : Set X) : singularSet s ≅ (inSubset s : SSet) where
  hom := subspaceMap s
  inv := subspaceInverse s
  hom_inv_id := by
    ext n σ
    rfl
  inv_hom_id := by
    ext n σ
    apply Subtype.ext
    rfl

def subspaceHomologyIso (s : Set X) (n : ℕ) :
    RealSingularHomology n s ≅
      (inSubset s : SSet).homology (ModuleCat.of ℝ ℝ) n :=
  (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).mapIso (subspaceIso s)

theorem subspace_homology_subsingleton (s : Set X) [ContractibleSpace s]
    (n : ℕ) (hn : n ≠ 0) :
    Subsingleton ((inSubset s : SSet).homology (ModuleCat.of ℝ ℝ) n : ModuleCat ℝ) := by
  let := realSingularHomology_subsingleton_of_contractible n hn s
  exact (subspaceHomologyIso s n).toLinearEquiv.symm.injective.subsingleton

end Problem340.SingularSmallChains

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularCoverNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularCover

variable {X : Type} [TopologicalSpace X]

variable {K L : SSet} (f : K ⟶ L)
variable {A B : K.Subcomplex} {A' B' : L.Subcomplex}

def restrictedMap (A : K.Subcomplex) (A' : L.Subcomplex)
    (h : A ≤ A'.preimage f) : (A : SSet) ⟶ (A' : SSet) :=
  SSet.Subcomplex.homOfLE h ≫ A'.fromPreimage f

@[reassoc (attr := simp)] theorem restrictedMap_ι
    (h : A ≤ A'.preimage f) :
    restrictedMap f A A' h ≫ A'.ι = A.ι ≫ f := rfl

theorem restrictedMap_inclusion
    {C : K.Subcomplex} {C' : L.Subcomplex}
    (hA : A ≤ A'.preimage f) (hC : C ≤ C'.preimage f)
    (hAC : A ≤ C) (hAC' : A' ≤ C') :
    restrictedMap f A A' hA ≫ SSet.Subcomplex.homOfLE hAC' =
      SSet.Subcomplex.homOfLE hAC ≫ restrictedMap f C C' hC := rfl

theorem preserves_inter (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) :
    A ⊓ B ≤ (A' ⊓ B').preimage f := by
  intro n s hs
  exact ⟨hA n hs.1, hB n hs.2⟩

theorem preserves_union (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) :
    A ⊔ B ≤ (A' ⊔ B').preimage f := by
  intro n s hs
  exact hs.elim (fun h => Or.inl (hA n h)) (fun h => Or.inr (hB n h))

theorem chainRestrictedMap_inclusion
    {C : K.Subcomplex} {C' : L.Subcomplex}
    (hA : A ≤ A'.preimage f) (hC : C ≤ C'.preimage f)
    (hAC : A ≤ C) (hAC' : A' ≤ C') :
    SSet.chainComplexMap (restrictedMap f A A' hA) (ModuleCat.of ℝ ℝ) ≫
        SSet.chainComplexMap (SSet.Subcomplex.homOfLE hAC') (ModuleCat.of ℝ ℝ) =
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE hAC) (ModuleCat.of ℝ ℝ) ≫
        SSet.chainComplexMap (restrictedMap f C C' hC) (ModuleCat.of ℝ ℝ) := by
  have h := ((SSet.chainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ)).congr_map
    (restrictedMap_inclusion f hA hC hAC hAC')
  simpa only [Functor.map_comp] using h

def unionShortComplexMap
    (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) :
    unionShortComplex A B ⟶ unionShortComplex A' B' where
  τ₁ := SSet.chainComplexMap
    (restrictedMap f (A ⊓ B) (A' ⊓ B') (preserves_inter f hA hB)) (ModuleCat.of ℝ ℝ)
  τ₂ := biprod.map
    (SSet.chainComplexMap (restrictedMap f A A' hA) (ModuleCat.of ℝ ℝ))
    (SSet.chainComplexMap (restrictedMap f B B' hB) (ModuleCat.of ℝ ℝ))
  τ₃ := SSet.chainComplexMap
    (restrictedMap f (A ⊔ B) (A' ⊔ B') (preserves_union f hA hB)) (ModuleCat.of ℝ ℝ)
  comm₁₂ := by
    dsimp only [unionShortComplex, CommSq.shortComplex]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
      exact chainRestrictedMap_inclusion f (preserves_inter f hA hB) hA inf_le_left inf_le_left
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc,
        Preadditive.comp_neg, Preadditive.neg_comp]
      exact congrArg Neg.neg
        (chainRestrictedMap_inclusion f (preserves_inter f hA hB) hB inf_le_right inf_le_right)
  comm₂₃ := by
    dsimp only [unionShortComplex, CommSq.shortComplex]
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
      exact chainRestrictedMap_inclusion f hA (preserves_union f hA hB) le_sup_left le_sup_left
    · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc]
      exact chainRestrictedMap_inclusion f hB (preserves_union f hA hB) le_sup_right le_sup_right

end Problem340.SingularCover

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSmallNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularSmallChains

abbrev singularFunctor : TopCat ⥤ ChainComplex (ModuleCat ℝ) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℝ)).obj
    (ModuleCat.of ℝ ℝ)

abbrev singularDegree (n : ℕ) : TopCat ⥤ ModuleCat ℝ :=
  singularFunctor ⋙ HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n

variable {X : Type} [TopologicalSpace X]
variable {ι : Type*} (U : ι → Set X)

def memberInclusion (i : ι) : realSingularChainComplex (U i) ⟶ chains U :=
  SSet.chainComplexMap
    (subspaceMap (U i) ≫ SSet.Subcomplex.homOfLE
      (le_iSup (fun j => inSubset (U j)) i)) (ModuleCat.of ℝ ℝ)

@[reassoc] theorem memberInclusion_inclusion (i : ι) :
    memberInclusion U i ≫ inclusion U =
      realSingularChainMap (Subtype.val : U i → X) continuous_subtype_val := by
  change SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _ = _
  erw [← Functor.map_comp]
  rfl

def simplexMember {n : ℕ} (σ : (small U : SSet) _⦋n⦌) : ι :=
  Classical.choose ((mem_small U σ.val).mp σ.property)

theorem simplexMember_property {n : ℕ} (σ : (small U : SSet) _⦋n⦌) :
    ∀ p, TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌) σ.val p ∈
      U (simplexMember U σ) := by
  exact fun p => Classical.choose_spec ((mem_small U σ.val).mp σ.property) ⟨p, rfl⟩

def simplexInMember {n : ℕ} (σ : (small U : SSet) _⦋n⦌) :
    (singularSet (U (simplexMember U σ))) _⦋n⦌ :=
  (subspaceInverse (U (simplexMember U σ))).app _
    ⟨σ.val, simplexMember_property U σ⟩

theorem simplexInMember_map {n : ℕ} (σ : (small U : SSet) _⦋n⦌) :
    (singularSet (U (simplexMember U σ))).ιChainComplex (simplexInMember U σ) ≫
      (memberInclusion U (simplexMember U σ)).f n =
        (small U : SSet).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ := by
  exact SSet.ι_chainComplexMap_f _ _
    (subspaceMap (U (simplexMember U σ)) ≫ SSet.Subcomplex.homOfLE
      (le_iSup (fun j => inSubset (U j)) (simplexMember U σ)))
    (ModuleCat.of ℝ ℝ) (simplexInMember U σ)

def restrict {n m : ℕ} (T : singularDegree n ⟶ singularDegree m) :
    (chains U).X n ⟶ (chains U).X m :=
  Sigma.desc fun σ =>
    (singularSet (U (simplexMember U σ))).ιChainComplex (simplexInMember U σ) ≫
      T.app (TopCat.of (U (simplexMember U σ))) ≫
        (memberInclusion U (simplexMember U σ)).f m

theorem generator_restrict {n m : ℕ}
    (T : singularDegree n ⟶ singularDegree m) (σ : (small U : SSet) _⦋n⦌) :
    (small U : SSet).ιChainComplex σ ≫ restrict U T =
      (singularSet (U (simplexMember U σ))).ιChainComplex (simplexInMember U σ) ≫
        T.app (TopCat.of (U (simplexMember U σ))) ≫
          (memberInclusion U (simplexMember U σ)).f m := by
  exact Sigma.ι_desc _ _

@[reassoc] theorem restrict_inclusion {n m : ℕ}
    (T : singularDegree n ⟶ singularDegree m) :
    restrict U T ≫ (inclusion U).f m =
      (inclusion U).f n ≫ T.app (TopCat.of X) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, generator_restrict]
  have hnat := T.naturality
    (TopCat.ofHom ⟨(Subtype.val : U (simplexMember U σ) → X), continuous_subtype_val⟩)
  change (realSingularChainMap
      (Subtype.val : U (simplexMember U σ) → X) continuous_subtype_val).f n ≫
        T.app (TopCat.of X) =
      T.app (TopCat.of (U (simplexMember U σ))) ≫
        (realSingularChainMap
          (Subtype.val : U (simplexMember U σ) → X) continuous_subtype_val).f m at hnat
  have hm (k : ℕ) := congrArg (fun f => f.f k)
    (memberInclusion_inclusion U (simplexMember U σ))
  simp only [HomologicalComplex.comp_f] at hm
  erw [Category.assoc, Category.assoc]
  erw [hm m, ← hnat, ← hm n]
  erw [← Category.assoc, ← Category.assoc, simplexInMember_map]
  exact Category.assoc _ _ _

@[simp] theorem restrict_id (n : ℕ) :
    restrict U (𝟙 (singularDegree n)) = 𝟙 ((chains U).X n) := by
  apply (cancel_mono ((inclusion U).f n)).1
  rw [restrict_inclusion]
  simp only [NatTrans.id_app, Category.id_comp]
  exact Category.comp_id _

@[simp] theorem restrict_zero (n m : ℕ) :
    restrict U (0 : singularDegree n ⟶ singularDegree m) = 0 := by
  apply (cancel_mono ((inclusion U).f m)).1
  rw [restrict_inclusion]
  simp
  try exact Limits.comp_zero

@[simp] theorem restrict_add {n m : ℕ}
    (S T : singularDegree n ⟶ singularDegree m) :
    restrict U (S + T) = restrict U S + restrict U T := by
  apply (cancel_mono ((inclusion U).f m)).1
  rw [restrict_inclusion, Preadditive.add_comp, restrict_inclusion, restrict_inclusion]
  simp
  try exact Preadditive.comp_add _ _ _ _ _ _

@[reassoc] theorem restrict_comp {n m k : ℕ}
    (S : singularDegree n ⟶ singularDegree m)
    (T : singularDegree m ⟶ singularDegree k) :
    restrict U (S ≫ T) = restrict U S ≫ restrict U T := by
  apply (cancel_mono ((inclusion U).f k)).1
  simp only [Category.assoc, restrict_inclusion, restrict_inclusion_assoc, NatTrans.comp_app]
  erw [← Category.assoc (restrict U S), restrict_inclusion, Category.assoc]
  rfl

def restrictChainMap (S : singularFunctor ⟶ singularFunctor) : chains U ⟶ chains U where
  f n := restrict U (Functor.whiskerRight S
    (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n))
  comm' i j hij := by
    apply (cancel_mono ((inclusion U).f j)).1
    simp only [Category.assoc]
    rw [← (inclusion U).comm i j, restrict_inclusion_assoc, restrict_inclusion]
    change (inclusion U).f i ≫ (S.app (TopCat.of X)).f i ≫
      (realSingularChainComplex X).d i j =
      (chains U).d i j ≫ (inclusion U).f j ≫ (S.app (TopCat.of X)).f j
    rw [(S.app (TopCat.of X)).comm, ← Category.assoc, (inclusion U).comm]
    exact Category.assoc _ _ _

@[reassoc] theorem restrictChainMap_inclusion (S : singularFunctor ⟶ singularFunctor) :
    restrictChainMap U S ≫ inclusion U = inclusion U ≫ S.app (TopCat.of X) := by
  ext n : 1
  exact restrict_inclusion U (Functor.whiskerRight S
    (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n))

@[simp] theorem restrictChainMap_id :
    restrictChainMap U (𝟙 singularFunctor) = 𝟙 (chains U) := by
  ext n : 1
  exact restrict_id U n

@[simp] theorem restrictChainMap_comp (S T : singularFunctor ⟶ singularFunctor) :
    restrictChainMap U (S ≫ T) = restrictChainMap U S ≫ restrictChainMap U T := by
  ext n : 1
  exact restrict_comp U
    (Functor.whiskerRight S (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n))
    (Functor.whiskerRight T (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n))

def HomotopyNatural {S T : singularFunctor ⟶ singularFunctor}
    (H : ∀ Y : TopCat, Homotopy (S.app Y) (T.app Y)) : Prop :=
  ∀ (i j : ℕ) {Y Z : TopCat} (f : Y ⟶ Z),
    (singularFunctor.map f).f i ≫ (H Z).hom i j =
      (H Y).hom i j ≫ (singularFunctor.map f).f j

def homotopyOperator {S T : singularFunctor ⟶ singularFunctor}
    (H : ∀ Y : TopCat, Homotopy (S.app Y) (T.app Y))
    (hH : HomotopyNatural H) (i j : ℕ) : singularDegree i ⟶ singularDegree j where
  app Y := (H Y).hom i j
  naturality {_ _} f := hH i j f

def restrictHomotopy {S T : singularFunctor ⟶ singularFunctor}
    (H : ∀ Y : TopCat, Homotopy (S.app Y) (T.app Y))
    (hH : HomotopyNatural H) :
    Homotopy (restrictChainMap U S) (restrictChainMap U T) where
  hom i j := restrict U (homotopyOperator H hH i j)
  zero i j hij := by
    apply (cancel_mono ((inclusion U).f j)).1
    rw [restrict_inclusion, zero_comp]
    change (inclusion U).f i ≫ (H (TopCat.of X)).hom i j = 0
    rw [(H (TopCat.of X)).zero i j hij, comp_zero]
  comm i := by
    apply (cancel_mono ((inclusion U).f i)).1
    simp only [Preadditive.add_comp]
    change restrict U (Functor.whiskerRight S
        (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) i)) ≫
        (inclusion U).f i = _
    rw [restrict_inclusion]
    change (inclusion U).f i ≫ (S.app (TopCat.of X)).f i = _
    rw [(H (TopCat.of X)).comm i]
    simp only [Preadditive.comp_add]
    congr 1
    · congr 1
      · change (inclusion U).f i ≫
            ((realSingularChainComplex X).d i ((ComplexShape.down ℕ).next i) ≫
              (H (TopCat.of X)).hom ((ComplexShape.down ℕ).next i) i) =
          ((chains U).d i ((ComplexShape.down ℕ).next i) ≫
            restrict U (homotopyOperator H hH ((ComplexShape.down ℕ).next i) i)) ≫
              (inclusion U).f i
        rw [Category.assoc, restrict_inclusion, ← Category.assoc, (inclusion U).comm]
        exact Category.assoc _ _ _
      · change (inclusion U).f i ≫
            ((H (TopCat.of X)).hom i ((ComplexShape.down ℕ).prev i) ≫
              (realSingularChainComplex X).d ((ComplexShape.down ℕ).prev i) i) =
          (restrict U (homotopyOperator H hH i ((ComplexShape.down ℕ).prev i)) ≫
            (chains U).d ((ComplexShape.down ℕ).prev i) i) ≫ (inclusion U).f i
        rw [Category.assoc, ← (inclusion U).comm, restrict_inclusion_assoc]
        rfl
    · exact (restrict_inclusion U (Functor.whiskerRight T
        (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) i))).symm

@[reassoc] theorem restrictHomotopy_inclusion {S T : singularFunctor ⟶ singularFunctor}
    (H : ∀ Y : TopCat, Homotopy (S.app Y) (T.app Y))
    (hH : HomotopyNatural H) (i j : ℕ) :
    (restrictHomotopy U H hH).hom i j ≫ (inclusion U).f j =
      (inclusion U).f i ≫ (H (TopCat.of X)).hom i j :=
  restrict_inclusion U (homotopyOperator H hH i j)

end Problem340.SingularSmallChains

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSubdivisionIterateRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SingularSubdivisionIterateRealization

open SingularSubdivision SingularUniversalOperator SimplexSingularRealization

abbrev degreeOperator (n : ℕ) :=
  operator n n (realize n n (universalSubdivision n))

end Problem340.SingularSubdivisionIterateRealization

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SingularSupportNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340

namespace SingularSmallChains

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

@[reassoc] theorem subspaceIso_hom_inclusion (s : Set X) :
    (subspaceIso s).hom ≫ (inSubset s).ι =
      TopCat.toSSet.map (TopCat.ofHom
        (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) := by
  rfl

def restrictMap (f : X → Y) (hf : Continuous f) (s : Set X) (t : Set Y)
    (hst : Set.MapsTo f s t) : C(s, t) :=
  ⟨fun x => ⟨f x.val, hst x.property⟩,
    (hf.comp continuous_subtype_val).subtype_mk _⟩

def mapInSubset (f : X → Y) (hf : Continuous f) (s : Set X) (t : Set Y)
    (hst : Set.MapsTo f s t) : (inSubset s : SSet) ⟶ inSubset t where
  app n := TypeCat.ofHom fun σ =>
    ⟨(TopCat.toSSet.map (TopCat.ofHom (continuousMapOf f hf))).app n σ.val,
      fun p => hst (σ.property p)⟩
  naturality := by
    intro n m g
    ext σ
    apply Subtype.ext
    rfl

@[reassoc] theorem subspaceIso_naturality
    (f : X → Y) (hf : Continuous f) (s : Set X) (t : Set Y)
    (hst : Set.MapsTo f s t) :
    TopCat.toSSet.map (TopCat.ofHom (restrictMap f hf s t hst)) ≫
        (subspaceIso t).hom =
      (subspaceIso s).hom ≫ mapInSubset f hf s t hst := by
  rfl

@[reassoc] theorem mapInSubset_inclusion
    (f : X → Y) (hf : Continuous f) (s : Set X) (t : Set Y)
    (hst : Set.MapsTo f s t) :
    mapInSubset f hf s t hst ≫ (inSubset t).ι =
      (inSubset s).ι ≫ TopCat.toSSet.map (TopCat.ofHom (continuousMapOf f hf)) := by
  rfl

end SingularSmallChains
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SmallCoverMayerVietoris
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340

namespace SmallCoverMayerVietoris

open SingularSmallChains

variable {X : Type} [TopologicalSpace X]

def binaryCover (U V : Set X) : Bool → Set X := fun b => cond b U V

@[simp] theorem small_binaryCover (U V : Set X) :
    small (binaryCover U V) = inSubset U ⊔ inSubset V := by
  simp only [small, binaryCover, iSup_bool_eq, Bool.cond_true, Bool.cond_false]

def smallUnionHomologyIso (U V : Set X) (n : ℕ) :
    (chains (binaryCover U V)).homology n ≅
      (inSubset U ⊔ inSubset V : (singularSet X).Subcomplex).toSSet.homology
        (ModuleCat.of ℝ ℝ) n :=
  (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).mapIso
    (eqToIso (congrArg SSet.Subcomplex.toSSet (small_binaryCover U V)))

def intersectionHomologyIso (U V : Set X) (n : ℕ) :
    RealSingularHomology n ↥(U ∩ V) ≅
      (inSubset U ⊓ inSubset V : (singularSet X).Subcomplex).toSSet.homology
        (ModuleCat.of ℝ ℝ) n :=
  subspaceHomologyIso (U ∩ V) n ≪≫
    (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).mapIso
      (eqToIso (congrArg SSet.Subcomplex.toSSet (inSubset_inter U V)))

def connecting (U V : Set X) (n : ℕ) :
    (chains (binaryCover U V)).homology (n + 1) ⟶
      RealSingularHomology n ↥(U ∩ V) :=
  (smallUnionHomologyIso U V (n + 1)).hom ≫
    SimplicialMayerVietoris.connecting (inSubset U) (inSubset V) n ≫
      (intersectionHomologyIso U V n).inv

theorem member_homology_isZero (U : Set X) [ContractibleSpace U]
    (n : ℕ) (hn : n ≠ 0) :
    IsZero ((inSubset U).toSSet.homology (ModuleCat.of ℝ ℝ) n) :=
  ModuleCat.isZero_iff_subsingleton.mpr (subspace_homology_subsingleton U n hn)

def connectingIso (U V : Set X) [ContractibleSpace U] [ContractibleSpace V]
    (n : ℕ) (hn : n ≠ 0) :
    (chains (binaryCover U V)).homology (n + 1) ≅ RealSingularHomology n ↥(U ∩ V) :=
  smallUnionHomologyIso U V (n + 1) ≪≫
    SimplicialMayerVietoris.connectingIso (inSubset U) (inSubset V) n
      (member_homology_isZero U (n + 1) (Nat.succ_ne_zero n))
      (member_homology_isZero V (n + 1) (Nat.succ_ne_zero n))
      (member_homology_isZero U n hn) (member_homology_isZero V n hn) ≪≫
        (intersectionHomologyIso U V n).symm

@[simp] theorem connectingIso_hom (U V : Set X)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) (hn : n ≠ 0) :
    (connectingIso U V n hn).hom = connecting U V n := rfl

def singularConnectingIsoOfQuasiIsoAt (U V : Set X)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) (hn : n ≠ 0)
    [QuasiIsoAt (inclusion (binaryCover U V)) (n + 1)] :
    RealSingularHomology (n + 1) X ≅ RealSingularHomology n ↥(U ∩ V) :=
  (asIso (HomologicalComplex.homologyMap (inclusion (binaryCover U V)) (n + 1))).symm ≪≫
    connectingIso U V n hn

@[reassoc] theorem inclusion_singularConnectingIsoOfQuasiIsoAt
    (U V : Set X) [ContractibleSpace U] [ContractibleSpace V]
    (n : ℕ) (hn : n ≠ 0)
    [QuasiIsoAt (inclusion (binaryCover U V)) (n + 1)] :
    HomologicalComplex.homologyMap (inclusion (binaryCover U V)) (n + 1) ≫
      (singularConnectingIsoOfQuasiIsoAt U V n hn).hom = connecting U V n := by
  unfold singularConnectingIsoOfQuasiIsoAt
  erw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, IsIso.hom_inv_id,
    Category.id_comp]
  rfl

end SmallCoverMayerVietoris
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SmallCoverNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340.SmallCoverMayerVietoris

open SingularSmallChains SingularCover

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

abbrev singularMap (f : X → Y) (hf : Continuous f) : singularSet X ⟶ singularSet Y :=
  TopCat.toSSet.map (TopCat.ofHom (continuousMapOf f hf))

theorem inSubset_le_preimage (f : X → Y) (hf : Continuous f)
    (s : Set X) (t : Set Y) (h : Set.MapsTo f s t) :
    inSubset s ≤ (inSubset t).preimage (singularMap f hf) := by
  intro n σ hσ p
  exact h (hσ p)

theorem binary_le_preimage (f : X → Y) (hf : Continuous f)
    (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    small (binaryCover U V) ≤ (small (binaryCover U' V')).preimage (singularMap f hf) := by
  rw [small_binaryCover, small_binaryCover]
  exact preserves_union (singularMap f hf)
    (inSubset_le_preimage f hf U U' hU) (inSubset_le_preimage f hf V V' hV)

def binaryMap (f : X → Y) (hf : Continuous f)
    (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    (small (binaryCover U V) : SSet) ⟶ small (binaryCover U' V') :=
  restrictedMap (singularMap f hf) _ _ (binary_le_preimage f hf U V U' V' hU hV)

@[reassoc] theorem binaryMap_inclusion (f : X → Y) (hf : Continuous f)
    (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    binaryMap f hf U V U' V' hU hV ≫ (small (binaryCover U' V')).ι =
      (small (binaryCover U V)).ι ≫ singularMap f hf := rfl

@[reassoc] theorem binaryHomologyMap_inclusion (f : X → Y) (hf : Continuous f)
    (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
    SSet.homologyMap (binaryMap f hf U V U' V' hU hV) (ModuleCat.of ℝ ℝ) n ≫
        HomologicalComplex.homologyMap (inclusion (binaryCover U' V')) n =
      HomologicalComplex.homologyMap (inclusion (binaryCover U V)) n ≫
        ModuleCat.ofHom (realHomologyMap n f hf) := by
  change SSet.homologyMap (binaryMap f hf U V U' V' hU hV) (ModuleCat.of ℝ ℝ) n ≫
      SSet.homologyMap (small (binaryCover U' V')).ι (ModuleCat.of ℝ ℝ) n =
    SSet.homologyMap (small (binaryCover U V)).ι (ModuleCat.of ℝ ℝ) n ≫
      SSet.homologyMap (singularMap f hf) (ModuleCat.of ℝ ℝ) n
  rw [← SSet.homologyMap_comp, ← SSet.homologyMap_comp, binaryMap_inclusion]

def intersectionMap (f : X → Y) (hf : Continuous f)
    (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') : C(↥(U ∩ V), ↥(U' ∩ V')) :=
  restrictMap f hf (U ∩ V) (U' ∩ V') (fun _ hx => ⟨hU hx.1, hV hx.2⟩)

end Problem340.SmallCoverMayerVietoris

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereInfinityChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped RealInnerProductSpace ContDiff OnePoint

namespace Problem340

def sphereInfinityFlipLinear : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient where
  toFun x := WithLp.toLp 2 ![x 0, -x 1, -x 2]
  invFun x := WithLp.toLp 2 ![x 0, -x 1, -x 2]
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' r x := by ext i; fin_cases i <;> simp
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]

@[simp] theorem sphereInfinityFlipLinear_zero (x : SphereAmbient) :
    sphereInfinityFlipLinear x 0 = x 0 := rfl

@[simp] theorem sphereInfinityFlipLinear_one (x : SphereAmbient) :
    sphereInfinityFlipLinear x 1 = -x 1 := rfl

@[simp] theorem sphereInfinityFlipLinear_two (x : SphereAmbient) :
    sphereInfinityFlipLinear x 2 = -x 2 := rfl

@[simp] theorem sphereInfinityFlipLinear_involutive (x : SphereAmbient) :
    sphereInfinityFlipLinear (sphereInfinityFlipLinear x) = x :=
  sphereInfinityFlipLinear.left_inv x

def sphereInfinityFlip (x : StandardSphere2) : StandardSphere2 :=
  ⟨sphereInfinityFlipLinear x.val, by simp⟩

@[simp] theorem sphereInfinityFlip_involutive (x : StandardSphere2) :
    sphereInfinityFlip (sphereInfinityFlip x) = x := by
  apply Subtype.ext
  exact sphereInfinityFlipLinear_involutive x.val

def sphereAtInfinity (w : ℂ) : StandardSphere2 :=
  sphereInfinityFlip (sphereOfComplex w)

@[simp] theorem sphereAtInfinity_val_zero (w : ℂ) :
    (sphereAtInfinity w).val 0 = 2 * w.re / (‖w‖ ^ 2 + 1) := by
  change (sphereOfComplex w).val 0 = _
  exact sphereOfComplex_val_zero w

@[simp] theorem sphereAtInfinity_val_one (w : ℂ) :
    (sphereAtInfinity w).val 1 = -(2 * w.im / (‖w‖ ^ 2 + 1)) := by
  change -(sphereOfComplex w).val 1 = _
  rw [sphereOfComplex_val_one]

@[simp] theorem sphereAtInfinity_val_two (w : ℂ) :
    (sphereAtInfinity w).val 2 = -((‖w‖ ^ 2 - 1) / (‖w‖ ^ 2 + 1)) := by
  change -(sphereOfComplex w).val 2 = _
  rw [sphereOfComplex_val_two]

@[simp] theorem sphereAtInfinity_zero : sphereAtInfinity 0 = chartNorthPole := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [chartNorthPole, chartNorthVector]

def chartSouthPole : StandardSphere2 := sphereOfComplex 0

@[simp] theorem sphereInfinityFlip_south : sphereInfinityFlip chartSouthPole = chartNorthPole :=
  sphereAtInfinity_zero

@[simp] theorem sphereInfinityFlip_north : sphereInfinityFlip chartNorthPole = chartSouthPole := by
  rw [← sphereInfinityFlip_south, sphereInfinityFlip_involutive]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereCoverGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Problem340.SphereCover

def northComplement : Set StandardSphere2 := {chartNorthPole}ᶜ

def southComplement : Set StandardSphere2 := {chartSouthPole}ᶜ

def northHomeomorph : northComplement ≃ₜ ℂ where
  toFun x := sphereToComplex x.val
  invFun z := ⟨sphereOfComplex z, sphereOfComplex_ne_north z⟩
  left_inv x := Subtype.ext (sphereOfComplex_sphereToComplex x.property)
  right_inv z := sphereToComplex_sphereOfComplex z
  continuous_toFun := continuousOn_sphereToComplex.domRestrict
  continuous_invFun := continuous_sphereOfComplex.subtype_mk _

def flipHomeomorph : StandardSphere2 ≃ₜ StandardSphere2 where
  toFun := sphereInfinityFlip
  invFun := sphereInfinityFlip
  left_inv := sphereInfinityFlip_involutive
  right_inv := sphereInfinityFlip_involutive
  continuous_toFun := (sphereInfinityFlipLinear.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (sphereInfinityFlipLinear.continuous.comp continuous_subtype_val).subtype_mk _

def southToNorthHomeomorph : southComplement ≃ₜ northComplement :=
  flipHomeomorph.subtype (fun x => by
    change x ≠ chartSouthPole ↔ sphereInfinityFlip x ≠ chartNorthPole
    constructor
    · intro hx heq
      apply hx
      have h := congrArg sphereInfinityFlip heq
      simpa only [sphereInfinityFlip_involutive, sphereInfinityFlip_north] using h
    · intro hx heq
      apply hx
      rw [heq, sphereInfinityFlip_south])

def southHomeomorph : southComplement ≃ₜ ℂ :=
  southToNorthHomeomorph.trans northHomeomorph

instance north_contractible : ContractibleSpace northComplement :=
  northHomeomorph.contractibleSpace

instance south_contractible : ContractibleSpace southComplement :=
  southHomeomorph.contractibleSpace

abbrev PuncturedPlane := {z : ℂ // z ≠ 0}

def overlapHomeomorph : ↥(northComplement ∩ southComplement) ≃ₜ PuncturedPlane where
  toFun x := ⟨sphereToComplex x.val, by
    intro hz
    apply x.property.2
    change x.val = sphereOfComplex 0
    rw [← sphereOfComplex_sphereToComplex x.property.1, hz]⟩
  invFun z := ⟨sphereOfComplex z.val, sphereOfComplex_ne_north z.val, by
    intro h
    apply z.property
    exact sphereOfComplex_injective h⟩
  left_inv x := Subtype.ext (sphereOfComplex_sphereToComplex x.property.1)
  right_inv z := Subtype.ext (sphereToComplex_sphereOfComplex z.val)
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact (continuousOn_sphereToComplex.mono Set.inter_subset_left).domRestrict
  continuous_invFun := (continuous_sphereOfComplex.comp continuous_subtype_val).subtype_mk _

abbrev ComplexCircle := Metric.sphere (0 : ℂ) (1 : ℝ)

def radialRetraction : C(PuncturedPlane, ComplexCircle) where
  toFun z := ⟨‖z.val‖⁻¹ • z.val, by
    have hz : ‖z.val‖ ≠ 0 := norm_ne_zero_iff.mpr z.property
    simp [hz]⟩
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact ((continuous_norm.comp continuous_subtype_val).inv₀
      (fun z => norm_ne_zero_iff.mpr z.property)).smul continuous_subtype_val

def circleInclusion : C(ComplexCircle, PuncturedPlane) where
  toFun z := ⟨z.val, ne_zero_of_mem_unit_sphere z⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

lemma radialRetraction_circleInclusion (z : ComplexCircle) :
    radialRetraction (circleInclusion z) = z := by
  apply Subtype.ext
  change ‖z.val‖⁻¹ • z.val = z.val
  rw [norm_eq_of_mem_sphere z]
  simp

lemma radial_coefficient_pos (t : unitInterval) (z : PuncturedPlane) :
    0 < (1 - (t : ℝ)) * ‖z.val‖⁻¹ + (t : ℝ) := by
  have hr : 0 < ‖z.val‖ := norm_pos_iff.mpr z.property
  by_cases ht : 0 < (t : ℝ)
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr t.property.2) (inv_nonneg.mpr hr.le)) ht
  · have ht0 : (t : ℝ) = 0 := le_antisymm (le_of_not_gt ht) t.property.1
    simp only [ht0, sub_zero, one_mul, add_zero]
    exact inv_pos.mpr hr

def radialHomotopy : ContinuousMap.Homotopy
    (circleInclusion.comp radialRetraction) (ContinuousMap.id PuncturedPlane) where
  toFun p := ⟨((1 - (p.1 : ℝ)) * ‖p.2.val‖⁻¹ + (p.1 : ℝ)) • p.2.val,
    smul_ne_zero (ne_of_gt (radial_coefficient_pos p.1 p.2)) p.2.property⟩
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    have ht : Continuous (fun p : unitInterval × PuncturedPlane => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hz : Continuous (fun p : unitInterval × PuncturedPlane => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact (((continuous_const.sub ht).mul
      (hz.norm.inv₀ (fun p => norm_ne_zero_iff.mpr p.2.property))).add ht).smul hz
  map_zero_left z := by
    apply Subtype.ext
    change ((1 - (0 : ℝ)) * ‖z.val‖⁻¹ + 0) • z.val = ‖z.val‖⁻¹ • z.val
    simp
  map_one_left z := by
    apply Subtype.ext
    change ((1 - (1 : ℝ)) * ‖z.val‖⁻¹ + 1) • z.val = z.val
    simp

def puncturedPlaneEquivCircle : PuncturedPlane ≃ₕ ComplexCircle where
  toFun := radialRetraction
  invFun := circleInclusion
  left_inv := ⟨radialHomotopy⟩
  right_inv := by
    have h : radialRetraction.comp circleInclusion = ContinuousMap.id ComplexCircle := by
      apply ContinuousMap.ext
      intro z
      exact radialRetraction_circleInclusion z
    rw [h]

def overlapEquivCircle : ↥(northComplement ∩ southComplement) ≃ₕ ComplexCircle :=
  overlapHomeomorph.toHomotopyEquiv.trans puncturedPlaneEquivCircle

def circleHomeomorphClock : ComplexCircle ≃ₜ StandardClock :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype (fun z => by
    simp only [Metric.mem_sphere, dist_zero_right]
    change ‖z‖ = 1 ↔ ‖Complex.orthonormalBasisOneI.repr z‖ = 1
    rw [LinearIsometryEquiv.norm_map])

def overlapEquivClock : ↥(northComplement ∩ southComplement) ≃ₕ StandardClock :=
  overlapEquivCircle.trans circleHomeomorphClock.toHomotopyEquiv

def overlapHomologyEquivClock (n : ℕ) :
    RealSingularHomology n ↥(northComplement ∩ southComplement) ≃ₗ[ℝ]
      RealSingularHomology n StandardClock :=
  realHomologyEquivOfHomotopyEquiv n overlapEquivClock

end Problem340.SphereCover

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340
namespace SphereTranslation

def denom (c : ℂ) (x : SphereAmbient) : ℝ :=
  2 + 2 * c.re * x 0 + 2 * c.im * x 1 +
    (c.re ^ 2 + c.im ^ 2) * (1 - x 2)

def ambient (c : ℂ) (x : SphereAmbient) : SphereAmbient :=
  WithLp.toLp 2 ![2 * (x 0 + c.re * (1 - x 2)) / denom c x,
    2 * (x 1 + c.im * (1 - x 2)) / denom c x,
    1 - 2 * (1 - x 2) / denom c x]

lemma sphere_coordinates (x : StandardSphere2) :
    x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 = 1 := by
  have hx : ‖x.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.2
  have he := EuclideanSpace.real_norm_sq_eq x.1
  rw [hx] at he
  simpa [Fin.sum_univ_succ, add_assoc] using he.symm

lemma denom_pos (c : ℂ) (x : StandardSphere2) : 0 < denom c x.1 := by
  have hx := sphere_coordinates x
  have hz : x.1 2 ≤ 1 := by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
  by_cases htop : x.1 2 = 1
  · have hzero : x.1 0 = 0 ∧ x.1 1 = 0 := by
      rw [htop] at hx
      constructor <;> nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
    simp [denom, htop, hzero.1, hzero.2]
  · have ht : 0 < 1 - x.1 2 := sub_pos.mpr (lt_of_le_of_ne hz htop)
    have hid : denom c x.1 * (1 - x.1 2) =
        (x.1 0 + c.re * (1 - x.1 2)) ^ 2 +
        (x.1 1 + c.im * (1 - x.1 2)) ^ 2 +
        (1 - x.1 2) ^ 2 := by
      dsimp [denom]
      nlinarith [hx]
    have hp : 0 < denom c x.1 * (1 - x.1 2) := by
      rw [hid]
      positivity
    exact (mul_pos_iff_of_pos_right ht).mp hp

lemma ambient_mem_sphere (c : ℂ) (x : StandardSphere2) :
    ambient c x.1 ∈ Metric.sphere (0 : SphereAmbient) 1 := by
  have hd : denom c x.1 ≠ 0 := ne_of_gt (denom_pos c x)
  have hx := sphere_coordinates x
  have hid : ‖ambient c x.1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [Fin.sum_univ_three]
    change (2 * (x.1 0 + c.re * (1 - x.1 2)) / denom c x.1) ^ 2 +
      (2 * (x.1 1 + c.im * (1 - x.1 2)) / denom c x.1) ^ 2 +
      (1 - 2 * (1 - x.1 2) / denom c x.1) ^ 2 = 1
    field_simp [hd]
    dsimp [denom]
    nlinarith [hx]
  rw [Metric.mem_sphere, dist_zero_right]
  nlinarith [norm_nonneg (ambient c x.1)]

def translate (c : ℂ) (x : StandardSphere2) : StandardSphere2 :=
  ⟨ambient c x.1, ambient_mem_sphere c x⟩

@[simp] lemma ambient_zero (x : SphereAmbient) : ambient 0 x = x := by
  ext i
  fin_cases i <;> simp [ambient, denom]

@[simp] lemma translate_zero (x : StandardSphere2) : translate 0 x = x := by
  apply Subtype.ext
  exact ambient_zero x.1

def domain : Set (ℂ × SphereAmbient) := {p | denom p.1 p.2 ≠ 0}

@[fun_prop] lemma contDiff_complex_re (n : WithTop ℕ∞) :
    ContDiff ℝ n Complex.re := Complex.reCLM.contDiff

@[fun_prop] lemma contDiff_complex_im (n : WithTop ℕ∞) :
    ContDiff ℝ n Complex.im := Complex.imCLM.contDiff

@[fun_prop] lemma contDiff_denom (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun p : ℂ × SphereAmbient => denom p.1 p.2) := by
  unfold denom
  fun_prop

@[simp] lemma ambient_north (c : ℂ) :
    ambient c (WithLp.toLp 2 ![0, 0, 1]) = WithLp.toLp 2 ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp [ambient, denom]

def chart (x : SphereAmbient) : ℂ :=
  ⟨x 0 / (1 - x 2), x 1 / (1 - x 2)⟩

end SphereTranslation
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereMainUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SphereMainUpdate

def update (c : ℂ) (x : StandardSphere2) : StandardSphere2 :=
  SphereTranslation.translate c (SphereDoubling.sphereMap x)

def ambient (c : ℂ) (x : SphereAmbient) : SphereAmbient :=
  SphereTranslation.ambient c (SphereDoubling.ambientMap x)

@[simp] theorem coe_update (c : ℂ) (x : StandardSphere2) :
    (update c x).1 = ambient c x.1 := rfl

@[simp] theorem update_north (c : ℂ) :
    update c SphereDoubling.north = SphereDoubling.north := by
  unfold update
  rw [SphereDoubling.sphereMap_north]
  apply Subtype.ext
  exact SphereTranslation.ambient_north c

@[simp] theorem update_zero (x : StandardSphere2) : update 0 x = SphereDoubling.sphereMap x :=
  SphereTranslation.translate_zero _

end Problem340.SphereMainUpdate

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereSquareEquator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SphereDoubling

@[simp] theorem sphereMap_third_eq_zero_iff (x : Sphere) :
    (sphereMap x).val 2 = 0 ↔ x.val 2 = 0 := by
  change (2 * x.val 2) / (1 + x.val 2 ^ 2) = 0 ↔ _
  rw [div_eq_zero_iff]
  simp [ne_of_gt (denominator_pos x.val)]

@[simp] theorem sphereMap_third_pos_iff (x : Sphere) :
    0 < (sphereMap x).val 2 ↔ 0 < x.val 2 := by
  change 0 < (2 * x.val 2) / (1 + x.val 2 ^ 2) ↔ _
  rw [div_pos_iff_of_pos_right (denominator_pos x.val)]
  exact mul_pos_iff_of_pos_left (by norm_num)

@[simp] theorem sphereMap_third_neg_iff (x : Sphere) :
    (sphereMap x).val 2 < 0 ↔ x.val 2 < 0 := by
  change (2 * x.val 2) / (1 + x.val 2 ^ 2) < 0 ↔ _
  rw [div_lt_iff₀ (denominator_pos x.val)]
  constructor <;> intro h <;> nlinarith

lemma eq_south_iff (x : Sphere) : x = south ↔ x.val 2 = -1 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    have he := sphere_equation x
    have h0 : x.val 0 = 0 := by nlinarith [sq_nonneg (x.val 1), sq_nonneg (x.val 0)]
    have h1 : x.val 1 = 0 := by nlinarith [sq_nonneg (x.val 1), sq_nonneg (x.val 0)]
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [south, h0, h1, h, Matrix.cons_val_two]

@[simp] theorem sphereMap_eq_south_iff (x : Sphere) :
    sphereMap x = south ↔ x = south := by
  rw [eq_south_iff, eq_south_iff]
  change (2 * x.val 2) / (1 + x.val 2 ^ 2) = -1 ↔ _
  rw [div_eq_iff (ne_of_gt (denominator_pos x.val))]
  constructor <;> intro h <;> nlinarith

end Problem340.SphereDoubling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereOverlapDoubling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SphereOverlapDoubling

open SphereCover

abbrev Overlap := ↥(northComplement ∩ southComplement)

def puncturedSquare (z : PuncturedPlane) : PuncturedPlane :=
  ⟨z.val ^ 2, pow_ne_zero 2 z.property⟩

lemma continuous_puncturedSquare : Continuous puncturedSquare :=
  (continuous_subtype_val.pow 2).subtype_mk _

def overlapSquare (x : Overlap) : Overlap :=
  overlapHomeomorph.symm (puncturedSquare (overlapHomeomorph x))

lemma continuous_overlapSquare : Continuous overlapSquare :=
  overlapHomeomorph.symm.continuous.comp
    (continuous_puncturedSquare.comp overlapHomeomorph.continuous)

end Problem340.SphereOverlapDoubling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereMayerVietorisEigen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SphereMayerVietorisEigen

open SphereCover SingularSmallChains SmallCoverMayerVietoris

lemma doubling_south_eq_chartSouthPole : SphereDoubling.south = chartSouthPole := by
  symm
  apply (SphereDoubling.eq_south_iff chartSouthPole).mpr
  simp [chartSouthPole, sphereOfComplex_val_two]

lemma mapsTo_northComplement :
    Set.MapsTo SphereDoubling.sphereMap northComplement northComplement := by
  intro x hx
  change SphereDoubling.sphereMap x ≠ chartNorthPole
  intro h
  apply hx
  change x = chartNorthPole
  rw [← doubling_north_eq_chartNorthPole] at h ⊢
  exact (SphereDoubling.sphereMap_eq_north_iff x).mp h

lemma mapsTo_southComplement :
    Set.MapsTo SphereDoubling.sphereMap southComplement southComplement := by
  intro x hx
  change SphereDoubling.sphereMap x ≠ chartSouthPole
  intro h
  apply hx
  change x = chartSouthPole
  rw [← doubling_south_eq_chartSouthPole] at h ⊢
  exact (SphereDoubling.sphereMap_eq_south_iff x).mp h

abbrev coverFamily := binaryCover northComplement southComplement

end Problem340.SphereMayerVietorisEigen

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SubdivisionQuasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SubdivisionComparison

variable {R : Type*} [Ring R]

theorem map_cycle {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (z : S.X₂) (hz : S.g.hom z = 0) : T.g.hom (φ.τ₂.hom z) = 0 := by
  have h := congrArg (fun k : S.X₂ ⟶ T.X₃ => k.hom z) φ.comm₂₃
  change T.g.hom (φ.τ₂.hom z) = φ.τ₃.hom (S.g.hom z) at h
  simpa only [hz, map_zero] using h

end Problem340.SubdivisionComparison

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SubdivisionSupportMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.SingularSubdivision

open SimplexSubdivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def barycentricCenters : Centers E :=
  fun _ v => faceCenter v Finset.univ

@[simp] lemma barycentricCenters_zero (v : Fin 1 → E) :
    barycentricCenters 0 v = v 0 := by
  simp [barycentricCenters, faceCenter, Finset.centerMass]

@[simp] lemma subdivision_barycentric_one (v : Fin 1 → E) :
    subdivision barycentricCenters 1 (generator v) = generator v := by
  rw [subdivision_generator]
  simp only [boundary_generator, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero,
    one_smul, subdivision_zero, cone_generator, barycentricCenters_zero]
  congr 1
  ext i
  fin_cases i
  rfl

end Problem340.SingularSubdivision

end

end OAI
end


