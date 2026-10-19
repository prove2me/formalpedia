-- Prove2me | Definitions.Def_OAIE3v2B236
-- name    : OAIE3v2B236
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:41:26.811395+00:00
-- url     : https://prove2.me/theorems/3c4e5acd-6b53-4d88-b828-7b25dd47254b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 241 of 311
-- statement:
--   Definitions bundle 241 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B199`, `OAIE3v2B210`, `OAIE3v2B214`, `OAIE3v2B216`, `OAIE3v2B217` of this split.
--
--   Modules: `Dynamics/AllocatedFixedPathAnchoredNativeComparison.lean`, `Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`, `Estimates/AllocatedCutoffMaskedIdeal.lean`, `Estimates/AllocatedSlicedNormalizedNativeModel.lean`, `Geometry/AllocatedRowSlicedIdealCoordinates.lean`, `Linear/AllocatedModularRankFullProductLaw.lean`, `Linear/AllocatedShortRankWitnessWidth.lean`, `Probability/AllocatedFiberSlicedSourceLaw.lean`, `Sampling/ActualForecastModelPrecision.lean`, `Sampling/AllocatedForecastShortRawDependence.lean`, `Sampling/AllocatedFullGridChartModelMeasurable.lean`, `Sampling/ForecastActualPhysicalSourceContinuous.lean`, `Sampling/ForecastDensityPhysicalApproximation.lean`, `Sampling/ForecastLawOriginalNativeHaarJointMean.lean`, `Sampling/PreparedActualForecastSetup.lean`, `Sampling/PreparedRelativeEndpointForecastBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B210
import Definitions.Def_OAIE3v2B214
import Definitions.Def_OAIE3v2B216
import Definitions.Def_OAIE3v2B217

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFullGridChartModelMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr

noncomputable def allocatedProductFullGridPrefactor (y : EuclideanJetLayers U rowTypes) : ℂ :=
  cutoff y * (1 / (allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
    (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f y : ℂ))

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

noncomputable def allocatedProductFullGridProfile
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) (y : EuclideanJetLayers U rowTypes) : ℂ :=
  cutoff y * allocatedFullGridSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e y

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRowSlicedIdealCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace VectorPolynomial

open Module

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedRowIdealCoordinates (z : AllocatedLongJetRows B U b S rowTypes) :
    Finset α → LayerSamplerAxis I n → ℝ :=
  fun s a => realRowsSiteValue (rowSets a.1) (fun t =>
    if ha : ¬grid a then allocatedLongJetRealCoordinates B U b S z ⟨⟨a, ha⟩, t⟩ / R a.1
    else 0) s

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCutoffMaskedIdeal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

noncomputable def allocatedProductMaskedIdealSiteFactor {K : Type*}
    (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) (k : K) (s : Finset α)
    (w : MixedCoveredJetSource I (fun _ => Unit) E n d) : ℂ :=
  maskedSiteFactor
    (fun _ v => (fun j i => ((v.1 j).2 i () : ZMod period),
      fun j i => ((v.2 j () i).val : ZMod period))) label
    (fun k s v => allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (f k s) (chart v)) k s w

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankFullProductLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

noncomputable def allocatedSmoothFullSlot
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩) :
    AllocatedSmoothRankCoefficientIndex X inactive L → AllocatedFullSmoothCoefficientIndex G X I n B
  | ⟨_j,.inl x,l⟩ => .inl (some (.inl (spatial l)),x.val)
  | ⟨j,.inr i,l⟩ => .inr ⟨j,
      principalCoefficientSlot (layerSamplerDegree I n) ⟨j,.inr i.val⟩
        (block j ⟨.inr i.val,i.property⟩ l), i.val⟩

theorem allocatedSmoothFullSlot_injective
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩) :
    Function.Injective (allocatedSmoothFullSlot (X := X) inactive spatial block) := by
  rintro ⟨j,(x | i),l⟩ ⟨k,(y | a),q⟩ he
  · have hjk : j = k := Fin.ext (x.property.trans y.property.symm)
    subst k
    have hp := Sum.inl.inj he
    have hl : l = q := spatial.injective
      (Sum.inl.inj (Option.some.inj (congrArg Prod.fst hp)))
    have hxy : x = y := Subtype.ext (congrArg Prod.snd hp)
    subst q
    subst y
    rfl
  · cases he
  · cases he
  · have hh := Sum.inr.inj he
    have hjk : j = k := congrArg Sigma.fst hh
    subst k
    have hp := eq_of_heq (Sigma.mk.inj hh).2
    have hia : i = a := Subtype.ext (congrArg Prod.snd hp)
    subst a
    have hblocks := principalCoefficientSlot_injective (G := G)
      (layerSamplerDegree I n) ⟨j,.inr i.val⟩ (Nat.zero_lt_succ _) (congrArg Prod.fst hp)
    have hl : l = q := (block j ⟨.inr i.val,i.property⟩).injective hblocks
    subst q
    rfl

noncomputable def allocatedSmoothFullEmbedding
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩) :
    AllocatedSmoothRankCoefficientIndex X inactive L ↪ AllocatedFullSmoothCoefficientIndex G X I n B :=
  ⟨allocatedSmoothFullSlot inactive spatial block, allocatedSmoothFullSlot_injective inactive spatial block⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (noiseCenter noiseWidth : Fin L → X → ℝ)

noncomputable def allocatedSelectedSmoothCenter : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ
  | ⟨_j,.inl x,l⟩ => noiseCenter l x.val
  | ⟨j,.inr i,_l⟩ => allocatedPrincipalRankCenter B U basis S j i.val

noncomputable def allocatedSelectedSmoothWidth : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ
  | ⟨_j,.inl x,l⟩ => noiseWidth l x.val
  | ⟨j,.inr i,_l⟩ => allocatedPrincipalRankWidth B U basis S j i.val

include hR in
theorem allocatedSelectedSmoothWidth_pos (hnoise : ∀ l x, 0 < noiseWidth l x)
    (a : AllocatedSmoothRankCoefficientIndex X inactive L) :
    0 < allocatedSelectedSmoothWidth B U basis S inactive noiseWidth a := by
  rcases a with ⟨j,(x | i),l⟩
  · exact hnoise l x.val
  · exact allocatedPrincipalRankWidth_pos B U basis hR S j i.val

include hR in
theorem allocatedSelectedSmoothMass_pos
    (hnoise : ∀ l x, 0 < shiftedSmoothSampleSum (noiseCenter l x) (noiseWidth l x))
    (hactive : ∀ j (i : AllocatedCongruenceIntegerAxis inactive j),
      S.value ^ (j.val + 1) < basisAxisScale (basis j) i.val)
    (a : AllocatedSmoothRankCoefficientIndex X inactive L) :
    0 < shiftedSmoothSampleSum (allocatedSelectedSmoothCenter B U basis S inactive noiseCenter a)
      (allocatedSelectedSmoothWidth B U basis S inactive noiseWidth a) := by
  rcases a with ⟨j,(x | i),l⟩
  · exact hnoise l x.val
  · exact allocatedPrincipalRankMass_pos B U basis hR S j i.val (hactive j i)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable local instance shortSpatialReferenceSmoothFintype_rb45a1e_1 :
    Fintype (AllocatedFullSmoothCoefficientIndex G X I n B) := inferInstance
noncomputable local instance shortSpatialReferenceDeckFintype_rb45a1e_1 :
    Fintype (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := inferInstance
noncomputable local instance shortSpatialReferenceDeckDecidableEq_rb45a1e_1 :
    DecidableEq (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := Classical.decEq _
noncomputable def allocatedShortRankSelectedWidth {L : ℕ}
    (spatial : Fin L ↪ G) (stride : X → ℕ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) :
    AllocatedSmoothRankCoefficientIndex X (allocatedShortAxis (I := I) U basis S.value) L → ℝ :=
  allocatedSelectedSmoothWidth B U basis S (allocatedShortAxis (I := I) U basis S.value)
    (fun l x => residueProfileWidth stride V (some (.inl (spatial l)),x))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (B) {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides

noncomputable def allocatedShortPrincipalRaw (u : ShortTuple)
    (k : PrincipalTupleIndex B degree × Option Empty) : ℤ :=
  if hk : short k.1.1 then (u ⟨⟨k.1.1, hk⟩, k.1.2⟩ k.2 : ℤ) else 0

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastModelPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]
variable {Y : Type*} [PseudoMetricSpace Y]

local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

noncomputable def forecastBufferedCoveredSiteFactor
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod period) → Y × (LayerSamplerAxis I n → ℝ) → ℂ)
    (s : Y) : EuclideanJetLayers U single → ℂ :=
  restrictedComplexChartDensity chart region 1 (fun w =>
    allocatedBufferedMixedSiteFactor B U b S r hr (fun _ => 1)
      (fun j => mixedArrayRegroup _ _ _ (w.1 j) ()) *
    F (forecastBufferedFullResidue d period w)
      (s, allocatedFullMixedSiteValue (R := R) U b
        (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastActualPhysicalSourceContinuous
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

noncomputable def forecastDensityPhysicalDeckSource (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ) : ℂ := by
  exact (density ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
    forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
  (rationalInactiveForecast law active
    (forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
    Y N volume (fun a _ => (w (selected a).1).2 (selected a).2)
    (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (deck j)) output : ZMod N)) : ℂ)

local notation "deckSource" => forecastDensityPhysicalDeckSource B U basis S density selected sample x
  active Y N volume base physicalN τ

noncomputable def forecastDensityPhysicalChartSource (u : X → ℤ)
    (z : MixedCoveredJetSource I single Eout n N) : ℂ :=
  deckSource u (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())
    (fun j i => ((z.2 j () i).val : ℤ))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathAnchoredNativeComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local instance slicedNativeAtomCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastDensityPhysicalApproximation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (density : ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ) → ℝ)
variable (cap lip : ℝ≥0)
variable (hbound : ∀ y, |density y| ≤ (cap : ℝ)) (hLips : LipschitzWith lip density)

noncomputable def forecastDensityNormalizedAtom
    {A Site : Type*} [Fintype A]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    {Nmod : ℕ} [NeZero Nmod]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod Nmod) ℂ)
    (e : A → ScalarSiteExpansion Site) (k : ∀ a, (e a).Term) (site : Site)
    (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
    (u : X → ℤ) (deck : ∀ j, Eout j → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) : ℂ :=
  ((density
    ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
      forecastNormalizedActiveCoordinates short
        (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
    star (χ (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (deck j)) output : ZMod Nmod))) *
    siteFamilyFactor e k site
      (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
      (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
        basisAxisScale (basis (selected a).1) (selected a).2)) /
    (((cap : ℝ) + 1 : ℝ) : ℂ)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawOriginalNativeHaarJointMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {pw cw : ℝ} {Lw : ℝ≥0}
variable (Wtest : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
local notation "RawSource" => MixedCoveredJetSource I single Eout n N

noncomputable def forecastLawNativeRawSpatialFamily (u : X → ℤ) (z : RawSource) : ℂ :=
  chartSource u z * nativeSingleSiteCoverObservable U Wtest physicalN u N
    (mixedCoveredJetChart U o basis hb bW N z)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local instance slicedNativeSourceMeanCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedNormalizedNativeModel
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable {X : Type*} [Fintype X] (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X spatialModulus stride wholeReference x base label

noncomputable def allocatedRecenteredFiniteModelSource
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) : ℂ :=
  ∑ z : cells × window, (selectedResidueCellWeight stride cells widths z.1 : ℂ) *
    allocatedRecenteredResidueWeight (τ := τ) B U b S X spatialModulus stride wholeReference x hM selection hx
      N hW mesh base cells (physicalCubeSiteTest test) label z.1 z.2.val *
    (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
      (physicalCubeRowSample U d rows p hm (reconstruct z.1.val z.2.val)) *
    allocatedFullGridChartModel B U b S rowSets d hb o bW e
      (physicalCubeRowSample U d rows p hm (reconstruct z.1.val z.2.val)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFiberSlicedSourceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "ActiveInput" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))

variable {keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop} [DecidablePred keep]
variable {q : ℕ}
variable (slice : ResidueBoxSlice
  (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val) q)
variable (hlen : ∀ k, 0 < slice.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧
  fixed k < ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

include hlen hfixed in
theorem allocatedFiberActiveProgression_contained (j : ActiveInput) :
    integerProgressionSupport (slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      (ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q) (Sum.inr ⟨j.1.val, j.2⟩) : ℤ)
      (slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩)) ⊆
        Finset.Ico (0 : ℤ) (S.value : ℤ) := by
  apply integerProgressionSupport_subset_of_fin
  intro t
  have hi := slice.fiberPrincipalParameter_inside hlen fixed hfixed ⟨j.1.val, j.2⟩ t
  simpa only [allocatedPrincipalSides_not_short B U basis S j.1 j.2] using hi

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualForecastSetup
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem principalTupleIndex_block_sum_le_card {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (degree : D → ℕ)
    (hdegree : ∀ d, 1 ≤ degree d) :
    (∑ d, Fintype.card (B d)) ≤ Fintype.card (PrincipalTupleIndex B degree) := by
  simp only [PrincipalTupleIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  apply Finset.sum_le_sum
  intro d _
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (Fintype.card (B d)) (hdegree d)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedRelativeEndpointForecastBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedConcreteSlicedForecastPacketLog_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {r Pdim cost pRadius gainLog Qstride PF Pchart childLog E : ℝ},
      0 ≤ r →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ r →
      ((nX + m * M : ℕ) : ℝ) ≤ r →
      Pdim ∈ Set.Icc 0 r → cost ∈ Set.Icc 0 r → pRadius ∈ Set.Icc 0 r →
      gainLog ∈ Set.Icc 0 r → Qstride ∈ Set.Icc 0 r → PF ∈ Set.Icc 0 r →
      Pchart ∈ Set.Icc 0 r → childLog ∈ Set.Icc 0 r → E ∈ Set.Icc 0 r →
      preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog E ∈ Set.Icc 0 ((r + C) ^ C) ∧
      preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog E ∈ Set.Icc 0 ((r + C) ^ C) ∧
      preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog E ∈ Set.Icc 0 ((r + C) ^ C) := by
  obtain ⟨Cs, _, hsp⟩ := exists_preparedCenteredForecastSpatialLog_budget
  let Ct : ℕ := ⌈preparedSlicedForecastPrimitiveCap⌉₊
  let Ccut : ℕ := ⌈(normalizedSiteCutoffBound : ℝ)⌉₊
  let X : Polynomial ℕ := Polynomial.X
  let S := 3 * X + 9 + (X + Polynomial.C Cs) ^ Cs
  let Dp := S + Polynomial.C (layerTailDegree m + 1) + 1
  let Tp := Polynomial.C Ct + X + 1
  let Vp := S + 2 * X + 1
  let Kp := (X + Polynomial.C m) * (4 * X + 11)
  let Sp := Polynomial.C (10 * m + 30) * (S + (X + 1) * (X + 1) + 1) ^ 2
  let Bp := 2 * X ^ 2 +
    Polynomial.C (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)) + X + 11
  let Rp := 20 * X + 32 + Dp + Tp + Vp + Kp + 2 * Sp + Bp + Polynomial.C Ccut
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget
    ((forecastSlicedEarlyPolynomial m).comp Rp + X + 2)
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc r Pdim cost pRadius gainLog Qstride PF Pchart childLog E
    hr hDbase hDmod hPdim hcost hRadius hGain hStride hPF hChart hChild hE
  let spatial := 3 * r + 9 + (r + Cs) ^ Cs
  let dim := spatial + ((layerTailDegree m + 1 : ℕ) : ℝ) + 1
  let tail := (Ct : ℝ) + r + 1
  let radius := spatial + 2 * r + 1
  let jac := (r + m) * (4 * r + 11)
  let smooth := (10 * (m : ℝ) + 30) * (spatial + (r + 1) * (r + 1) + 1) ^ 2
  let bad := 2 * r ^ 2 +
    (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + r + 11
  let R := 20 * r + 32 + dim + tail + radius + jac + 2 * smooth + bad + Ccut
  have hs0 : 0 ≤ spatial := by dsimp only [spatial]; positivity
  have hd0 : 0 ≤ dim := by dsimp only [dim]; positivity
  have ht0 : 0 ≤ tail := by dsimp only [tail]; positivity
  have hv0 : 0 ≤ radius := by dsimp only [radius]; positivity
  have hk0 : 0 ≤ jac := by dsimp only [jac]; positivity
  have hsm0 : 0 ≤ smooth := by dsimp only [smooth]; positivity
  have hb0 : 0 ≤ bad := by dsimp only [bad]; positivity
  have hcc0 : (0 : ℝ) ≤ Ccut := Nat.cast_nonneg _
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hdR : dim ≤ R := by dsimp only [R]; linarith
  have htR : tail ≤ R := by dsimp only [R]; linarith
  have hvR : radius ≤ R := by dsimp only [R]; linarith
  have hksR : jac + smooth ≤ R := by dsimp only [R]; linarith
  have hsR : smooth ≤ R := by dsimp only [R]; linarith
  have hbR : bad ≤ R := by dsimp only [R]; linarith
  have hrR : r + 1 ≤ R := by dsimp only [R]; linarith
  have hspR : 2 * r + 16 ≤ R := by dsimp only [R]; linarith
  have hcoordR : 3 * r ≤ R := by dsimp only [R]; linarith
  have hcutR : 4 * r + Ccut + 1 ≤ R := by dsimp only [R]; linarith
  let Dbase := allocatedComparisonDimension m
    (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + ((layerTailDegree m + 1 : ℕ) : ℝ) + 1
  let v := P + (Dbase + pRadius + 1)
  let K := preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart
  let Sm := forecastOriginalSmoothBudget m (P + (nX + 1) * (cost + 1))
  let Bad := preparedSlicedForecastBadLog m nX Qstride gainLog
  have hDbase0 : 0 ≤ Dbase := (allocatedComparisonDimension_bounds m (Nat.cast_nonneg _)).1
  have hnX : (nX : ℝ) ≤ r :=
    (Nat.cast_le.mpr (Nat.le_add_right nX (m * M))).trans hDmod
  have hcenter : preparedCenteredForecastSpatialLog Pdim ≤ (r + Cs) ^ Cs :=
    (hsp hPdim.1).trans (pow_le_pow_left₀ (add_nonneg hPdim.1 (Nat.cast_nonneg Cs))
      (add_le_add hPdim.2 le_rfl) Cs)
  have hP0 : 0 ≤ P := by
    apply le_trans _ (le_max_left _ _)
    dsimp only [Dbase] at hDbase0
    positivity
  have hP : P ≤ spatial := by
    unfold P preparedSlicedForecastSpatialBudget
    have hpow : 0 ≤ (r + Cs) ^ Cs := by positivity
    dsimp only [spatial]
    refine max_le ?_ (max_le ?_ ?_) <;> linarith only [hDbase, hnX, hcenter, hcost.2, hr, hpow]
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hD : D ≤ R := (by dsimp only [D, dim]; linarith only [hP] : D ≤ dim).trans hdR
  have hvInput0 : 0 ≤ v := by dsimp only [v]; linarith only [hP0, hDbase0, hRadius.1]
  have hvInput : v ≤ R := (by dsimp only [v, radius]; linarith only [hP, hDbase, hRadius.2] : v ≤ radius).trans hvR
  have htail0 : 0 ≤ preparedSlicedForecastTailLog cost := preparedSlicedForecastTailLog_nonneg hcost.1
  have htail : preparedSlicedForecastTailLog cost ≤ R := by
    apply le_trans _ htR
    have hceil : preparedSlicedForecastPrimitiveCap ≤ (Ct : ℝ) := Nat.le_ceil _
    dsimp only [preparedSlicedForecastTailLog, tail]
    linarith only [hceil, hcost.2]
  have hK0 : 0 ≤ K := by
    dsimp only [K, preparedSlicedForecastJacobianLog]
    have := hRadius.1
    have := hGain.1
    have := hChart.1
    positivity
  have hK : K ≤ jac := by
    have hleft : ((nX + m + m * M : ℕ) : ℝ) ≤ r + m := by
      have hdim : (nX : ℝ) + m * M ≤ r := by simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
      simp only [Nat.cast_add, Nat.cast_mul]
      linarith only [hdim]
    have hright : pRadius + gainLog + nX + Pchart + 11 ≤ 4 * r + 11 := by
      linarith only [hRadius.2, hGain.2, hnX, hChart.2]
    exact mul_le_mul hleft hright
      (by have hn0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg _; linarith only [hRadius.1, hGain.1, hChart.1, hn0])
      (by positivity)
  have harg0 : 0 ≤ P + (nX + 1) * (cost + 1) :=
    add_nonneg hP0 (mul_nonneg (by positivity) (by linarith only [hcost.1]))
  have harg : P + (nX + 1) * (cost + 1) ≤ spatial + (r + 1) * (r + 1) :=
    add_le_add hP (mul_le_mul (add_le_add hnX le_rfl) (add_le_add hcost.2 le_rfl)
      (by linarith only [hcost.1]) (by linarith only [hr]))
  have hSm0 : 0 ≤ Sm := (forecastOriginalSmoothBudget_bounds m harg0).1
  have hSm : Sm ≤ smooth := by
    dsimp only [Sm, smooth, forecastOriginalSmoothBudget]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith only [harg0]) (add_le_add harg le_rfl) 2) (by positivity)
  have hBad0 : 0 ≤ Bad := by
    dsimp only [Bad, preparedSlicedForecastBadLog]
    have := hStride.1
    have := hGain.1
    positivity
  have hBad : Bad ≤ R := by
    apply le_trans _ hbR
    have hmul : 2 * (nX : ℝ) * Qstride ≤ 2 * r * r :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnX (by norm_num)) hStride.2 hStride.1 (by positivity)
    dsimp only [Bad, preparedSlicedForecastBadLog, bad]
    nlinarith only [hmul, hGain.2]
  have hspatial : (gainLog + nX + 8) + 8 ∈ Set.Icc 0 R := by
    have hn0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
    exact ⟨by linarith only [hGain.1, hn0], (by linarith only [hGain.2, hnX] : (gainLog + nX + 8) + 8 ≤ 2 * r + 16).trans hspR⟩
  have hcoord : pRadius + PF + Dbase ∈ Set.Icc 0 R :=
    ⟨by linarith only [hRadius.1, hPF.1, hDbase0],
      (by linarith only [hRadius.2, hPF.2, hDbase] : pRadius + PF + Dbase ≤ 3 * r).trans hcoordR⟩
  have hcut : pRadius + PF + 2 * Dbase + normalizedSiteCutoffBound + 1 ∈ Set.Icc 0 R := by
    have hc0 : (0 : ℝ) ≤ normalizedSiteCutoffBound := normalizedSiteCutoffBound.2
    have hceil : (normalizedSiteCutoffBound : ℝ) ≤ Ccut := Nat.le_ceil _
    exact ⟨by linarith only [hRadius.1, hPF.1, hDbase0, hc0],
      (by linarith only [hRadius.2, hPF.2, hDbase, hceil] :
        pRadius + PF + 2 * Dbase + normalizedSiteCutoffBound + 1 ≤ 4 * r + Ccut + 1).trans hcutR⟩
  have hdiag := forecastSlicedEarlyLogs_le_diagonal_of_dimensions m (nX + m * M) (nX + m * M + 1) hR0
    ⟨hD0, hD⟩ ⟨htail0, htail⟩ ⟨hvInput0, hvInput⟩
    ⟨hcost.1, hcost.2.trans (by linarith only [hrR])⟩
    ⟨by linarith only [hChild.1], (add_le_add hChild.2 le_rfl).trans hrR⟩
    ⟨add_nonneg hK0 hSm0, (add_le_add hK hSm).trans hksR⟩
    ⟨hSm0, hSm.trans hsR⟩ ⟨hBad0, hBad⟩
    ⟨by linarith only [hcost.1], (add_le_add hcost.2 le_rfl).trans hrR⟩
    ⟨hE.1, hE.2.trans (by linarith only [hrR])⟩ hspatial hcoord hcut
    (hDmod.trans (by linarith only [hrR]))
    (by simpa only [Nat.cast_add, Nat.cast_one] using (add_le_add hDmod le_rfl).trans hrR)
  let N := preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog E
  let Mass := preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog E
  let Cap := preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog
  let V := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog E
  have hresult : 0 ≤ N ∧ 0 ≤ Mass ∧ 0 ≤ Cap ∧
      N + Mass + Cap ≤ forecastSlicedEarlyDiagonalBudget m R := by
    simpa only [N, Mass, Cap, preparedConcreteSlicedForecastNativeLog,
      preparedConcreteSlicedForecastMassLog, preparedConcreteSlicedForecastCapLog,
      preparedConcreteSlicedForecastOutputLog, preparedConcreteSlicedForecastPeriodLog,
      preparedSlicedForecastCapLog, actualSlicedForecastModelCapLog,
      actualSlicedForecastModelPeriodLog, D, v, P, Dbase, K, Sm, Bad, add_assoc] using hdiag
  have hV : V = Cap + E + 2 := by
    dsimp only [V, Cap, preparedConcreteSlicedForecastPeriodLog,
      preparedConcreteSlicedForecastCapLog, preparedSlicedForecastCapLog,
      actualSlicedForecastModelPeriodLog, actualSlicedForecastModelCapLog]
    ring
  have hfinal : forecastSlicedEarlyDiagonalBudget m R + r + 2 ≤ (r + C) ^ C := by
    simpa [Rp, Dp, Tp, Vp, Kp, Sp, Bp, S, X, R, spatial, dim, tail, radius, jac, smooth, bad,
      Polynomial.eval₂_comp, Polynomial.eval₂_pow, forecastSlicedEarlyPolynomial_eval] using hpoly r hr
  change V ∈ Set.Icc 0 ((r + C) ^ C) ∧ N ∈ Set.Icc 0 ((r + C) ^ C) ∧ Mass ∈ Set.Icc 0 ((r + C) ^ C)
  exact ⟨⟨by linarith only [hV, hresult.2.2.1, hE.1],
      by linarith only [hV, hresult.1, hresult.2.1, hresult.2.2.2, hE.2, hfinal]⟩,
    ⟨hresult.1, by linarith only [hresult.2.1, hresult.2.2.1, hresult.2.2.2, hr, hfinal]⟩,
    ⟨hresult.2.1, by linarith only [hresult.1, hresult.2.2.1, hresult.2.2.2, hr, hfinal]⟩⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedConcreteSlicedForecastLocalModel_budget (m Cnative : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {t Pdim cost pRadius gainLog Qstride PF Pchart childLog u p budget : ℝ},
      0 ≤ t →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t →
      ((nX + m * M : ℕ) : ℝ) ≤ t →
      Pdim ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t → pRadius ∈ Set.Icc 0 t →
      gainLog ∈ Set.Icc 0 t → Qstride ∈ Set.Icc 0 t → PF ∈ Set.Icc 0 t →
      Pchart ∈ Set.Icc 0 t → childLog ∈ Set.Icc 0 t →
      u ∈ Set.Icc 0 t → p ∈ Set.Icc 0 t →
      budget ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      let Edata := 2 * u + 4 * p + 12
      let period := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog Edata
      let native := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog Edata
      let mass := preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog Edata
      let commonBudget := max budget (3 * native + 3)
      let Qmodel := max commonBudget (2 * u + 4 * p + max 0 mass + 20)
      period ∈ Set.Icc 0 ((t + C) ^ C) ∧
      native ∈ Set.Icc 0 ((t + C) ^ C) ∧
      mass ∈ Set.Icc 0 ((t + C) ^ C) ∧
      commonBudget ∈ Set.Icc 0 ((t + C) ^ C) ∧
      Qmodel ∈ Set.Icc 0 ((t + C) ^ C) ∧
      Qmodel + 2 ∈ Set.Icc 0 ((t + C) ^ C) ∧
      2 * Qmodel + 2 * u + 4 * p + 34 ∈ Set.Icc 0 ((t + C) ^ C) ∧
      actualForecastDataModelRequired budget native mass u p ∈ Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨Cp, _, hpacket⟩ := exists_preparedConcreteSlicedForecastPacketLog_budget m
  let X : Polynomial ℕ := Polynomial.X
  let V : Polynomial ℕ := (X + Polynomial.C Cnative) ^ Cnative
  let Z : Polynomial ℕ := (6 * X + 12 + Polynomial.C Cp) ^ Cp
  let F : Polynomial ℕ := 2 * V + 8 * Z + 18 * X + 80
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget F
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc t Pdim cost pRadius gainLog Qstride PF Pchart childLog u p budget
    ht hDbase hDmod hPdim hcost hRadius hGain hStride hPF hChart hChild hu hp hbudget
    Edata period native mass commonBudget Qmodel
  let r : ℝ := 6 * t + 12
  let v : ℝ := (t + Cnative) ^ Cnative
  let z : ℝ := (r + Cp) ^ Cp
  have hr : 0 ≤ r := by dsimp only [r]; linarith only [ht]
  have htr : t ≤ r := by dsimp only [r]; linarith only [ht]
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  change budget ∈ Set.Icc 0 v at hbudget
  have hE0 : 0 ≤ Edata := by dsimp only [Edata]; linarith only [hu.1, hp.1]
  have hE : Edata ≤ r := by dsimp only [Edata, r]; linarith only [hu.2, hp.2]
  obtain ⟨hperiod, hnative, hmass⟩ := hpacket M nX Jalloc hr
    (hDbase.trans htr) (hDmod.trans htr)
    ⟨hPdim.1, hPdim.2.trans htr⟩ ⟨hcost.1, hcost.2.trans htr⟩
    ⟨hRadius.1, hRadius.2.trans htr⟩ ⟨hGain.1, hGain.2.trans htr⟩
    ⟨hStride.1, hStride.2.trans htr⟩ ⟨hPF.1, hPF.2.trans htr⟩
    ⟨hChart.1, hChart.2.trans htr⟩ ⟨hChild.1, hChild.2.trans htr⟩ ⟨hE0, hE⟩
  change period ∈ Set.Icc 0 z at hperiod
  change native ∈ Set.Icc 0 z at hnative
  change mass ∈ Set.Icc 0 z at hmass
  have hcommon0 : 0 ≤ commonBudget := hbudget.1.trans (le_max_left _ _)
  have hcommon : commonBudget ≤ v + 3 * z + 3 :=
    max_le (by linarith only [hbudget.2, hz]) (by linarith only [hnative.2, hv])
  have hQ0 : 0 ≤ Qmodel := hcommon0.trans (le_max_left _ _)
  have hQ : Qmodel ≤ v + 4 * z + 6 * t + 23 := by
    change max commonBudget (2 * u + 4 * p + max 0 mass + 20) ≤ _
    rw [max_eq_right hmass.1]
    exact max_le (by linarith only [hcommon, hz, ht])
      (by linarith only [hu.2, hp.2, hmass.2, hv, hz])
  have hrequired : actualForecastDataModelRequired budget native mass u p =
      u + 2 * p + Qmodel + 32 := rfl
  have hfinal : 2 * v + 8 * z + 18 * t + 80 ≤ (t + C) ^ C := by
    simpa [F, V, Z, X, v, z, r, Polynomial.eval₂_pow] using hpoly t ht
  have hraise : z ≤ (t + C) ^ C := by linarith only [hfinal, hv, hz, ht]
  refine ⟨⟨hperiod.1, hperiod.2.trans hraise⟩,
    ⟨hnative.1, hnative.2.trans hraise⟩, ⟨hmass.1, hmass.2.trans hraise⟩,
    ⟨hcommon0, ?_⟩, ⟨hQ0, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · linarith only [hcommon, hfinal, hv, hz, ht]
  · linarith only [hQ, hfinal, hv, hz, ht]
  · linarith only [hQ0]
  · linarith only [hQ, hfinal, hv, hz, ht]
  · linarith only [hQ0, hu.1, hp.1]
  · linarith only [hQ, hu.2, hp.2, hfinal]
  · linarith only [hrequired, hQ0, hu.1, hp.1]
  · linarith only [hrequired, hQ, hu.2, hp.2, hfinal, hv, hz, ht]

end Erdos3.VectorPolynomial

end

end OAI
end


