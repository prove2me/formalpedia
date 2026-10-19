-- Prove2me | Definitions.Def_OAIE3v2B301
-- name    : OAIE3v2B301
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:31:10.209083+00:00
-- url     : https://prove2.me/theorems/f7b01e72-3f96-4ad2-908c-2d069ff2a1ef
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 224 of 311
-- statement:
--   Definitions bundle 224 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B219` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateRefinementLabels.lean`, `Geometry/ActualFixedSpatialDenseSliceCenter.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Probability/AllocatedExternalLocalSliceLaw.lean`, `Sampling/ActualFixedSpatialSlicedForecastSourceLaw.lean`, `Sampling/ActualSlicedForecastLateData.lean`, `Sampling/AllocatedExternalLocalGoodForecastPath.lean`, `Sampling/ForecastLawNativeRawJointMean.lean`, `Sampling/PreparedActualSlicedForecastSetup.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B219

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

noncomputable def integerSampledLowTags {m : ℕ} {X τ : Type*}
    (J : Fin m → Type*) [∀ j, Fintype (J j)] (k : ℕ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ) (u : τ → ℤ) :
    Fin (Fintype.card (LowTaggedIndex J k)) → ℤ :=
  fun i => MvPolynomial.eval u (β (Sum.inr (lowTaggedIndex J k i)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRefinementLabels
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost newCost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (step : ℕ) (step_pos : 0 < step)
    (slice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) step)
    (dense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      newCost slice.integerPoints)

noncomputable def refineSlice : AllocatedExternalLocalChart (E := E) A newCost where
  path := C.path
  path_supported := C.path_supported
  centerLift := C.centerLift
  center_eq := C.center_eq
  sample := C.sample
  read := C.read
  recovered := C.recovered
  keep := C.keep
  fixed := C.fixed
  fixed_in_box := C.fixed_in_box
  step := step
  step_pos := step_pos
  slice := slice
  dense := dense

@[simp] theorem refineSlice_path :
    (C.refineSlice step step_pos slice dense).path = C.path := rfl

@[simp] theorem refineSlice_centerLift :
    (C.refineSlice step step_pos slice dense).centerLift = C.centerLift := rfl

@[simp] theorem refineSlice_integerChart :
    (C.refineSlice step step_pos slice dense).integerChart = C.integerChart := rfl

@[simp] theorem refineSlice_chartValues (u : C.Variables → ℤ) :
    (C.refineSlice step step_pos slice dense).chartValues u = C.chartValues u := rfl

@[simp] theorem refineSlice_parameter (u : C.Variables → ℤ) :
    (C.refineSlice step step_pos slice dense).parameter u = C.parameter u := rfl

@[simp] theorem refineSlice_physical (u : C.Variables → ℤ) :
    (C.refineSlice step step_pos slice dense).physical u = C.physical u := rfl

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalLocalGoodForecastPath
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

structure ActualFixedSpatialForecastPath where
  base : X → ℤ
  noise : Option (LayerSamplerVariables G I n B) × X → ℤ
  sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
  hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
    (allocatedLayerWidths B U b S j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)
  read : AllocatedActualCoefficientIndex G X I Eout n B → ℤ
  readNoise : allocatedReadNoise read = noise
  readProjection : ∀ (j : Fin m) (i : Fin (n j))
    (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
    allocatedReadProjection read ⟨j, Sum.inr i⟩ e = (sample j).2 i e
  center : ∀ j, U j
  commonTuple : G → IntegerScalarCubeBox Empty S.value
  primes : Finset ℕ
  prime : ∀ p ∈ primes, p.Prime
  exponent : ℕ → ℕ
  prescribed : ℕ → ℕ
  origin : ∀ p : primes, LayerSamplerLongVariables
    (allocatedShortAxis (I := I) U b S.value) G B → ZMod (p.val ^ exponent p.val)
  Rbad : ℕ
  hbad : letI := actualForecastPrimeNeZero primes prime
    (∏ p : primes, p.val ^ allocatedCongruenceBadDepth
      (allocatedShortAxis (I := I) U b S.value) noise (allocatedReadDeck read)
      (fun j a => allocatedReadProjection read ⟨j, a.val⟩)
      spatial kernel block primes exponent (modularForecastRankConstant m Dmod : ℝ)
      p.val) ≤ Rbad
  RbadBound : (Rbad : ℝ) ≤ Real.exp Pbad
  presBound : ((∏ p : primes, p.val ^ prescribed p.val : ℕ) : ℝ) ≤ Real.exp Ppres
  lower : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ
  width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ
  hwidth : ∀ a p, δslice ≤ width a p
  hlower : ∀ a p, 0 ≤ lower a p
  hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1
  detFalse : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp
    (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
      trimmedSpatialWidths Wsp τ physicalN k) false).det ≠ 0
  detTrue : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp
    (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
      trimmedSpatialWidths Wsp τ physicalN k) true).det ≠ 0
  hjac : inverseJacobian (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
    (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
      trimmedSpatialWidths Wsp τ physicalN k) true detTrue) ≤ Real.exp P
  hinverse : ‖(fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
    (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
      trimmedSpatialWidths Wsp τ physicalN k) false detFalse).symm.toContinuousLinearMap‖ ≤
    Real.exp P

namespace ActualFixedSpatialForecastPath

variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def normalizedNoise (k : Option G × X) : ℝ :=
  (path.noise (Option.map Sum.inl k.1, k.2) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k

omit [Fintype Tsp] in

theorem primeNeZero : ∀ p : path.primes, NeZero p.val :=
  actualForecastPrimeNeZero path.primes path.prime

end ActualFixedSpatialForecastPath

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type}
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres P' Pbad' Ppres' : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
variable (hP : P ≤ P') (hPbad : Pbad ≤ Pbad') (hPpres : Ppres ≤ Ppres')

def enlargeBudgets : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
    Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P' Pbad' Ppres' :=
  { path with
    RbadBound := path.RbadBound.trans (Real.exp_le_exp.mpr hPbad)
    presBound := path.presBound.trans (Real.exp_le_exp.mpr hPpres)
    hjac := path.hjac.trans (Real.exp_le_exp.mpr hP)
    hinverse := path.hinverse.trans (Real.exp_le_exp.mpr hP) }

@[simp] theorem enlargeBudgets_center :
    (path.enlargeBudgets hP hPbad hPpres).center = path.center := rfl

@[simp] theorem enlargeBudgets_base :
    (path.enlargeBudgets hP hPbad hPpres).base = path.base := rfl

@[simp] theorem enlargeBudgets_noise :
    (path.enlargeBudgets hP hPbad hPpres).noise = path.noise := rfl

@[simp] theorem enlargeBudgets_sample :
    (path.enlargeBudgets hP hPbad hPpres).sample = path.sample := rfl

@[simp] theorem enlargeBudgets_read :
    (path.enlargeBudgets hP hPbad hPpres).read = path.read := rfl

@[simp] theorem enlargeBudgets_commonTuple :
    (path.enlargeBudgets hP hPbad hPpres).commonTuple = path.commonTuple := rfl

@[simp] theorem enlargeBudgets_primes :
    (path.enlargeBudgets hP hPbad hPpres).primes = path.primes := rfl

@[simp] theorem enlargeBudgets_exponent :
    (path.enlargeBudgets hP hPbad hPpres).exponent = path.exponent := rfl

@[simp] theorem enlargeBudgets_prescribed :
    (path.enlargeBudgets hP hPbad hPpres).prescribed = path.prescribed := rfl

@[simp] theorem enlargeBudgets_origin :
    (path.enlargeBudgets hP hPbad hPpres).origin = path.origin := rfl

@[simp] theorem enlargeBudgets_Rbad :
    (path.enlargeBudgets hP hPbad hPpres).Rbad = path.Rbad := rfl

@[simp] theorem enlargeBudgets_lower :
    (path.enlargeBudgets hP hPbad hPpres).lower = path.lower := rfl

@[simp] theorem enlargeBudgets_width :
    (path.enlargeBudgets hP hPbad hPpres).width = path.width := rfl

@[simp] theorem enlargeBudgets_normalizedNoise :
    (path.enlargeBudgets hP hPbad hPpres).normalizedNoise = path.normalizedNoise := rfl

end Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type} [Fintype X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type}
variable (Dmod : ℕ) (selected : A → Σ j : Fin m, Fin (n j))
variable (τ δslice : ℝ)

structure ActualFixedSpatialForecastSetup where
  hm : 0 < m
  hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod
  hselected : Function.Injective selected
  selectedNonempty : ∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)
  D : ℝ
  P : ℝ
  Pcap : ℝ
  pcap : ℝ
  Pscale : ℝ
  Pbad : ℝ
  Ppres : ℝ
  Pτ : ℝ
  PK : ℝ
  PF : ℝ
  Pκ : ℝ
  κ : ℝ
  hD : AllocatedComparisonDimensions (G := G) B Empty
    (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D
  hP : 1 ≤ P
  hDP : D ≤ P
  haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D
  hdim : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ D
  hX : (Fintype.card X : ℝ) ≤ P
  hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P
  hPcap : 1 ≤ Pcap
  hpcap : 0 ≤ pcap
  hPcapp : Pcap ≤ Real.exp pcap
  hPscale : 0 ≤ Pscale
  hPbad : 0 ≤ Pbad
  hPpres : 0 ≤ Ppres
  hPτ : 0 ≤ Pτ
  hPK : 0 ≤ PK
  hPF : 0 ≤ PF
  hPκ : 0 ≤ Pκ
  hκ : 0 ≤ κ
  hκcap : κ ≤ Real.exp Pκ
  hτ : 0 < τ
  hτinv : τ⁻¹ ≤ Real.exp Pτ
  hδslice : 0 < δslice
  hδsliceInv : δslice⁻¹ ≤ Real.exp P
  hR1 : ∀ a, R (selected a).1 ≤ 1
  hσ1 : ∀ a, σ (selected a).1 ≤ 1
  hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
    S.value ^ ((selected a).1.val + 1)
  L : ℝ≥0
  hL : LipschitzWith L Real.smoothTransition
  hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap
  hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
    Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)
  hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale
  hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
    (selected a).1 (selected a).2).card : ℝ) ≤ Pscale
  hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    4 ≤ Fintype.card (B a.val)
  forward : Fin m → ℝ≥0
  hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖
  hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF
  K : ℝ≥0
  hK : ∀ j, (R j)⁻¹ ≤ K
  hKBound : (K : ℝ) ≤ Real.exp PK
  radius : ℝ≥0
  hr3 : (3 : ℝ) ≤ radius
  hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius
  inverse : Fin m → ℝ
  hinverse : ∀ j, 0 ≤ inverse j
  hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖
  hbudget : ∀ j, inverse j * (((Fintype.card (I j) : ℝ) + 1) *
    (2 * (radius : ℝ) * R j)) ≤ 1 / 4
  hexhaustive : ∀ a, allocatedShortAxis (I := I) U b S.value a → ∃ i,
    (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def physicalPolynomial
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    ∀ j, VectorPolynomial X ℝ (J j → ℝ) :=
  fun j => subtractConstant (path.center j).val (originalpoly j)

omit [Fintype Tsp] in

theorem physicalPolynomial_mem
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) :
    ∀ j d, coefficients (path.physicalPolynomial originalpoly j) d ∈ U j :=
  fun j => coefficients_subtractConstant_mem (U j) (path.center j) (originalpoly j) (hmem j)

end ActualFixedSpatialForecastPath

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawNativeRawJointMean
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

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

noncomputable def forecastLawDensityPhysicalTarget
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ) : ℂ :=
  restrictedComplexChartDensity chart region 1 (chartSource u)
    (physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedForecastSourceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type}
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)} {τ δslice : ℝ}

namespace ActualFixedSpatialForecastSetup

noncomputable def enlargeP
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)
    {P' : ℝ} (hP : s.P ≤ P') :
    ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice :=
  { s with
    P := P'
    hP := s.hP.trans hP
    hDP := s.hDP.trans hP
    hX := s.hX.trans hP
    hblocks := s.hblocks.trans hP
    hδsliceInv := s.hδsliceInv.trans (Real.exp_le_exp.mpr hP) }

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)
variable {P' : ℝ} (hP : s.P ≤ P')

@[simp] theorem enlargeP_P : (s.enlargeP hP).P = P' := rfl
@[simp] theorem enlargeP_D : (s.enlargeP hP).D = s.D := rfl
@[simp] theorem enlargeP_κ : (s.enlargeP hP).κ = s.κ := rfl
@[simp] theorem enlargeP_Pbad : (s.enlargeP hP).Pbad = s.Pbad := rfl
@[simp] theorem enlargeP_Ppres : (s.enlargeP hP).Ppres = s.Ppres := rfl

noncomputable def withSliceWidth
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)
    {δ' : ℝ} (hδ' : 0 < δ') (hδinv : δ'⁻¹ ≤ Real.exp s.P) :
    ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δ' :=
  { s with
    hδslice := hδ'
    hδsliceInv := hδinv }

variable {δ' : ℝ} (hδ' : 0 < δ') (hδinv : δ'⁻¹ ≤ Real.exp s.P)

@[simp] theorem withSliceWidth_P : (s.withSliceWidth hδ' hδinv).P = s.P := rfl
@[simp] theorem withSliceWidth_κ : (s.withSliceWidth hδ' hδinv).κ = s.κ := rfl
@[simp] theorem withSliceWidth_Pbad : (s.withSliceWidth hδ' hδinv).Pbad = s.Pbad := rfl
@[simp] theorem withSliceWidth_Ppres : (s.withSliceWidth hδ' hδinv).Ppres = s.Ppres := rfl

end ActualFixedSpatialForecastSetup

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

structure ActualFixedSpatialSlicedForecastPath where
  path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
    Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres
  step : ℕ
  step_pos : 0 < step
  kernelLength : G → ℕ
  kernelStart : G → ℤ
  kernelLength_two : ∀ g, 2 ≤ kernelLength g
  kernelInside : ∀ g (t : Fin (kernelLength g)),
    0 ≤ kernelStart g + (step : ℤ) * t.val ∧
      kernelStart g + (step : ℤ) * t.val < S.value
  principalLength : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ
  principalStep : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ
  principalStart : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ
  principalLength_pos : ∀ j, 0 < principalLength j
  principalInside : ∀ j (t : Fin (principalLength j)),
    0 ≤ principalStart j + (principalStep j : ℤ) * t.val ∧
      principalStart j + (principalStep j : ℤ) * t.val < allocatedPrincipalSides B U b S j
  principalStep_active : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), principalStep ⟨a.val,p⟩ = step
  prescribed_eq : ∀ p, path.prescribed p = padicValNat p step
  origin_eq : ∀ (p : path.primes) (v : LayerSamplerLongVariables
      (allocatedShortAxis (I := I) U b S.value) G B),
    path.origin p v = ((Sum.elim kernelStart
      (fun a => principalStart ⟨a.1.val,a.2⟩) v : ℤ) : ZMod (p.val ^ path.exponent p.val))
  lower_eq : ∀ a p, path.lower a p =
    (principalStart ⟨a.val,p⟩ : ℝ) / allocatedPrincipalSides B U b S ⟨a.val,p⟩
  width_eq : ∀ a p, path.width a p =
    (principalStep ⟨a.val,p⟩ : ℝ) * (principalLength ⟨a.val,p⟩ - 1 : ℕ) /
      allocatedPrincipalSides B U b S ⟨a.val,p⟩

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def kernelLower (g : G) : ℝ := (slice.kernelStart g : ℝ) / S.value
noncomputable def kernelWidth (g : G) : ℝ :=
  (slice.step : ℝ) * (slice.kernelLength g - 1 : ℕ) / S.value

omit [Fintype Tsp] in
theorem kernelWidth_pos (g : G) : 0 < slice.kernelWidth g := by
  have hstep : (0 : ℝ) < slice.step := Nat.cast_pos.mpr slice.step_pos
  have hlength : (0 : ℝ) < (slice.kernelLength g - 1 : ℕ) :=
    Nat.cast_pos.mpr (by have := slice.kernelLength_two g; omega)
  exact div_pos (mul_pos hstep hlength) (Nat.cast_pos.mpr S.positive)

omit [Fintype Tsp] in
theorem kernelWidth_ne_zero (g : G) : slice.kernelWidth g ≠ 0 :=
  (slice.kernelWidth_pos g).ne'

noncomputable def principalLaw : FiniteProbabilityWeights
    (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)) :=
  principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S)
    slice.principalLength slice.principalStep slice.principalStart slice.principalInside
    slice.principalLength_pos

noncomputable def density
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) :
    (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ)) → ℝ := by
  have h0 := det_ne_zero_change_decidable (inferInstance : DecidableEq X) (Classical.decEq X)
    (fixedSpatialKernelBlock spatialEquiv Wsp Lsp slice.path.normalizedNoise false) slice.path.detFalse
  have h1 := det_ne_zero_change_decidable (inferInstance : DecidableEq X) (Classical.decEq X)
    (fixedSpatialKernelBlock spatialEquiv Wsp Lsp slice.path.normalizedNoise true) slice.path.detTrue
  exact fixedSpatialKernelSliceOriginalForecastDensity
    (m := m) (G := G) (X := X) (T := Tsp) (I := I) (n := n) (J := J)
    B U b S spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth
    h0 h1 slice.kernelWidth_ne_zero hBactive slice.path.lower slice.path.width slice.path.sample

variable {A : Type} [Fintype A]

noncomputable def target
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ)
    (u : integerBox physicalN) : ℂ := by
  let : ∀ p : slice.path.primes, NeZero p.val := slice.path.primeNeZero
  let N := ∏ p : slice.path.primes, p.val ^ slice.path.exponent p.val
  let : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
    slice.path.base slice.path.noise (allocatedReadDeck slice.path.read)
    (fun j a => allocatedReadProjection slice.path.read ⟨j,a.val⟩)
  let pRat := crtPolynomialInputLaw (fun p : slice.path.primes => p.val)
    (fun p : slice.path.primes => slice.path.exponent p.val)
    (fun p : slice.path.primes => slice.path.prescribed p.val)
    (primePower_crt_coprime (fun p : slice.path.primes => p.val)
      (fun p : slice.path.primes => slice.path.exponent p.val)
      (fun p => slice.path.prime p.val p.property) Subtype.val_injective) slice.path.origin
  exact (κ : ℂ) * forecastLawDensityPhysicalTarget B U b S slice.principalLaw
    (slice.density hBactive) selected slice.path.sample slice.path.commonTuple (fun _ => pRat)
    (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW (slice.path.physicalPolynomial originalpoly)
    (slice.path.physicalPolynomial_mem originalpoly hmem) u.val

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

noncomputable def actualSlicedForecastDensityBudget (v : ℝ) : ℝ :=
  Real.exp (forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * v))

noncomputable def actualSlicedForecastDecayBudget : ℝ :=
  Real.exp ((s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m)

structure ActualFixedSpatialSlicedForecastNumerics where
  T : ℕ
  hT : 0 < T
  δ : ℝ
  hδ : 0 < δ
  Hchild : ℕ
  v : ℝ
  hv : 0 ≤ v
  Ptail : ℝ
  Ctail : ℝ
  hPtail : 1 ≤ Ptail
  hprimitive : s.Pcap ≤ Ptail
  hCtail : 0 ≤ Ctail
  Cactual : ℝ
  δout : ℝ
  Q : ℝ
  Nt : ℝ
  Vt : ℝ
  Ct : ℝ
  Ht : ℝ
  Lt : ℝ≥0
  hCactual : 0 ≤ Cactual
  hδout : 0 < δout
  hQ : 0 ≤ Q
  hCt : 0 ≤ Ct
  hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
    forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
      δ (Ptail * T) Cactual δout Q Nt Vt Ct Ht Lt
  htailactual : ∀ a,
    let degree := (selected a).1.val + 1
    let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := blockTorusFactor (Fintype.card Empty) degree
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
    let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
      (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
    max (cutoff : ℝ)
      (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree Ptail V V) ≤ Ctail
  Pnative : ℝ
  massLog : ℝ
  capLog : ℝ
  E : ℝ
  hPnative : 0 ≤ Pnative
  hperiod : (T : ℝ) * Vt ^ Fintype.card A ≤ Real.exp Pnative
  hfactor : (actualSlicedForecastDensityBudget s v + Fintype.card A * (Lt : ℝ)) *
    max (8 / τ) 1 ≤ Real.exp Pnative
  hcoord : ((s.K * ∑ j, s.forward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Pnative
  hcut : (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
    (2 * s.radius)) * (s.K * ∑ j, s.forward j * Fintype.card (J j)) : ℝ≥0) : ℝ) ≤ Real.exp Pnative
  hmass : s.κ * (2 * actualSlicedForecastDensityBudget s v *
    ((T : ℝ) ^ (Dmod + 1) * Ct ^ Fintype.card A)) ≤ Real.exp massLog
  herror : s.κ * (actualSlicedForecastDensityBudget s v *
    (Ctail ^ Fintype.card A * (actualSlicedForecastDecayBudget s / T) +
      (T : ℝ) ^ (Dmod + 1) * δout)) ≤ Real.exp (-E)
  hcap : s.κ * actualSlicedForecastDensityBudget s v * Ctail ^ Fintype.card A *
    (1 + actualSlicedForecastDecayBudget s) ≤ Real.exp capLog

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualSlicedForecastLateData
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))

namespace ActualFixedSpatialSlicedForecastPath

noncomputable def targetAt
    {Ppath Pbad Ppres : ℝ}
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice Ppath Pbad Ppres)
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ)
    (u : X → ℤ) : ℂ := by
  let : ∀ p : slice.path.primes, NeZero p.val := slice.path.primeNeZero
  let N := ∏ p : slice.path.primes, p.val ^ slice.path.exponent p.val
  let : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
    slice.path.base slice.path.noise (allocatedReadDeck slice.path.read)
    (fun j a => allocatedReadProjection slice.path.read ⟨j,a.val⟩)
  let pRat := crtPolynomialInputLaw (fun p : slice.path.primes => p.val)
    (fun p : slice.path.primes => slice.path.exponent p.val)
    (fun p : slice.path.primes => slice.path.prescribed p.val)
    (primePower_crt_coprime (fun p : slice.path.primes => p.val)
      (fun p : slice.path.primes => slice.path.exponent p.val)
      (fun p => slice.path.prime p.val p.property) Subtype.val_injective) slice.path.origin
  exact (κ : ℂ) * forecastLawDensityPhysicalTarget B U b S slice.principalLaw
    (slice.density hBactive) selected slice.path.sample slice.path.commonTuple (fun _ => pRat)
    (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW (slice.path.physicalPolynomial originalpoly)
    (slice.path.physicalPolynomial_mem originalpoly hmem) u

@[simp] theorem targetAt_eq_target
    {Ppath Pbad Ppres : ℝ}
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice Ppath Pbad Ppres)
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ)
    (u : integerBox physicalN) :
    slice.targetAt selected hBactive o bW hb originalpoly hmem κ u.val =
      slice.target selected hBactive o bW hb originalpoly hmem κ u := rfl

end ActualFixedSpatialSlicedForecastPath

attribute [local instance] ScalarSiteExpansion.termFinite

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

structure ActualFixedSpatialSlicedAdmissiblePath where
  slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
    Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres
  regular : ∀ a, (∃ b0 v0,
    allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < q.Hchild) ∨
    ((∀ i v, q.δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
      (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
     (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩))
  stride : ∀ a i v,
    (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ) ≤ q.Ptail
  kernelWidth : ∀ g, Real.exp (-q.v) ≤ slice.kernelWidth g

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable {s} {qEarly : ActualFixedSpatialSlicedForecastNumerics s}

namespace ActualFixedSpatialSlicedAdmissiblePath

def withNumerics (path : ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail) :
    ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qLate where
  slice := path.slice
  regular := by simpa only [hδ, hH] using path.regular
  stride := by simpa only [hTail] using path.stride
  kernelWidth := by simpa only [hv] using path.kernelWidth

omit [Fintype Tsp] in
@[simp] theorem withNumerics_slice (path : ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail) :
    (path.withNumerics qLate hδ hH hv hTail).slice = path.slice := rfl

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

@[simp] theorem withNumerics_target (path : ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail) :
    (path.withNumerics qLate hδ hH hv hTail).slice.target
      selected s.hBactive o bW hb originalpoly hmem s.κ =
    path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ := rfl

@[simp] theorem withNumerics_targetAt (path : ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail) :
    (path.withNumerics qLate hδ hH hv hTail).slice.targetAt
      selected s.hBactive o bW hb originalpoly hmem s.κ =
    path.slice.targetAt selected s.hBactive o bW hb originalpoly hmem s.κ := rfl

end ActualFixedSpatialSlicedAdmissiblePath

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialDenseSliceCenter
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

structure ActualFixedSpatialDenseSliceInput where
  keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop
  [keepDecidable : DecidablePred keep]
  keep_iff : ∀ k, keep k ↔ q.Hchild ≤
    Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k
  step : ℕ
  step_pos : 0 < step
  box : ResidueBoxSlice
    (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value)
      (allocatedPrincipalSides B U b S) k.val) step
  fixed : {k // ¬keep k} → ℤ
  fixed_inside : ∀ k, 0 ≤ fixed k ∧ fixed k <
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k.val : ℕ) : ℤ)
  commonTuple : G → IntegerScalarCubeBox Empty S.value
  cost : ℝ
  dense : ∀ k, Real.exp (-cost) *
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k.val : ℕ) : ℝ) ≤ box.length k
  kernel_nonempty : Nonempty G
  cutoff_le : q.Hchild ≤ S.value
  late_floor : 2 ≤ Real.exp (-cost) * (S.value : ℝ)
  density_le : q.δ ≤ Real.exp (-cost)
  active_width : δslice ≤ Real.exp (-cost) / 2
  kernel_log : cost + 1 ≤ q.v
  prescribed_log : cost + 1 ≤ s.Ppres
  stride_cap : 2 * Real.exp cost ≤ q.Ptail

attribute [instance] ActualFixedSpatialDenseSliceInput.keepDecidable

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalLocalSliceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

def retainedParameter (x : LayerSamplerVariables G I n B → ℤ) : C.Variables → ℤ :=
  fun i => x i.val

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end


