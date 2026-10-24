-- Prove2me | Definitions.Def_K24GlobalAnalysis
-- name    : K24GlobalAnalysis
-- status  : Definition
-- author  : @xwh
-- created : 2026-10-23T08:54:41.463582+00:00
-- url     : https://prove2.me/theorems/738f77a5-d72a-4017-95ce-870ad72cb8a2
-- title:
--   K24: bounded-cover Hölder and real Sobolev section norms
-- statement:
--   Actual full big Hölder derivative/seminorms, hierarchical local finite covers with separate downstairs and internal overlap counts, and real-order Bessel–Sobolev norms with explicit cover partitions and representative regularity. Concrete predicates specify norm/completeness laws, true Fréchet remainder on a positive-radius domain, bounded linear isomorphisms, inverse bounds and Banach-dual gaps. These are requested conclusions for actual spaces, not abstract supplied Banach operators. Cover degree is unrestricted and no degree-independent downstairs L2 identification is asserted.
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — full §§1–7; inherited conventions in K16/K21/K23. Explicit norm choices and still-open organizer recorded in natural-language statement.

import Definitions.Def_K24GlobalGeometry

/- Original source module: K24Work.Global.Holder -/

/-!
# Big Hölder coefficient spaces for K24

The extended norm is the sum of the uniform norms of derivatives of every
order `0, …, k` and the Hölder seminorm of the kth derivative. Derivatives
are taken within the specified domain. All applications in `Covers` use open
domains, so these are the ordinary derivatives there. The function spaces
require `ContDiffOn` and finiteness of this genuine norm. They are not defined
as completions of smooth functions (which would give little Hölder spaces).

All definitions and the elementary finiteness lemmas below are sorry-free.
No Banach-space or completeness assertion is assumed by this module.
-/

set_option autoImplicit false

noncomputable section

open scoped NNReal ENNReal ContDiff BigOperators

namespace K24.Global

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A valid exponent for the big Hölder spaces used in K24. -/
structure HolderExponent where
  value : ℝ≥0
  positive : 0 < value
  lessThanOne : value < 1

/-- Uniform norm of the actual jth derivative on the domain; possibly infinite. -/
def derivativeENorm (j : ℕ) (s : Set E) (f : E → V) : ℝ≥0∞ :=
  ⨆ x : s, (‖iteratedFDerivWithin ℝ j f s x‖₊ : ℝ≥0∞)

/-- The usual full coordinate `C^{k,α}` norm, with values in `ℝ≥0∞`. -/
def coordinateHolderENorm (k : ℕ) (α : ℝ≥0) (s : Set E) (f : E → V) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range (k + 1), derivativeENorm j s f) +
    eHolderNorm α (fun x : s => iteratedFDerivWithin ℝ k f s x)

/-- Big Hölder regularity of an actual coefficient function. Regularity is
recorded separately because iterated derivatives are totalized in Mathlib. -/
def BigHolderOn (k : ℕ) (α : ℝ≥0) (s : Set E) (f : E → V) : Prop :=
  ContDiffOn ℝ k f s ∧ coordinateHolderENorm k α s f < ⊤

/-- Actual coefficient functions with big Hölder regularity. No completion of
smooth functions appears in this definition. -/
abbrev CoordinateHolder (k : ℕ) (α : ℝ≥0) (s : Set E) :=
  {f : E → V // BigHolderOn k α s f}

/-- Real norm only for a function accompanied by its finite-norm proof. -/
def CoordinateHolder.norm {k : ℕ} {α : ℝ≥0} {s : Set E}
    (f : CoordinateHolder (V := V) k α s) : ℝ :=
  (coordinateHolderENorm k α s f.val).toReal

theorem CoordinateHolder.enorm_ne_top {k : ℕ} {α : ℝ≥0} {s : Set E}
    (f : CoordinateHolder (V := V) k α s) :
    coordinateHolderENorm k α s f.val ≠ ⊤ :=
  ne_of_lt f.property.2

theorem CoordinateHolder.norm_nonneg {k : ℕ} {α : ℝ≥0} {s : Set E}
    (f : CoordinateHolder (V := V) k α s) : 0 ≤ f.norm :=
  ENNReal.toReal_nonneg

/-- This equality explicitly rules out the `toReal ∞ = 0` pathology on the
declared coefficient space. -/
theorem CoordinateHolder.ofReal_norm {k : ℕ} {α : ℝ≥0} {s : Set E}
    (f : CoordinateHolder (V := V) k α s) :
    ENNReal.ofReal f.norm = coordinateHolderENorm k α s f.val :=
  ENNReal.ofReal_toReal f.enorm_ne_top

end K24.Global


/- Original source module: K24Work.Global.Covers -/

/-!
# Genuine bounded local-cover section norms

A `LocalFiniteCover` is a smooth finite-sheeted covering of an open subset of
the actual manifold, with an arbitrary covering four-manifold as total space.
`LocalCoverChart` is an internal coordinate chart on that covering manifold.
The two index levels are separate: downstairs overlap is counted per local
cover, never per coordinate chart or per sheet. Finite degree is required
separately on each cover, with no uniform degree or chart-cardinality bound.
Interior coordinate shrinks have a uniform positive Euclidean margin.

The Hölder norms below apply to literal pullbacks of the actual sections.
The norms are extended-valued on arbitrary raw sections and real-valued only
on subtypes carrying regularity and finiteness proofs. Numerical background
metric bounds are inequalities for actual metric coefficients and their
matrix inverses, never assumptions of a desired Bianchi estimate.

Definitions and lemmas in this file contain no `sorry` or new axioms.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff NNReal ENNReal BigOperators Matrix.Norms.Elementwise

namespace K24.Global

universe u

variable (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- An actual smooth finite-sheeted local cover. No Euclidean global chart or
uniform upper bound on its covering degree is required. -/
structure LocalFiniteCover where
  TotalSpace : Type u
  [totalTopology : TopologicalSpace TotalSpace]
  [totalCharted : ChartedSpace FourSpace TotalSpace]
  [totalManifold : IsManifold I4 ∞ TotalSpace]
  baseDomain : Set M
  innerBaseDomain : Set M
  baseOpen : IsOpen baseDomain
  innerBaseOpen : IsOpen innerBaseDomain
  innerBaseSubset : innerBaseDomain ⊆ baseDomain
  projection : TotalSpace → M
  mapsToBase : ∀ x : TotalSpace, projection x ∈ baseDomain
  covering : IsCoveringMap
    (fun x : TotalSpace => (⟨projection x, mapsToBase x⟩ : baseDomain))
  ontoBase : Function.Surjective
    (fun x : TotalSpace => (⟨projection x, mapsToBase x⟩ : baseDomain))
  finiteFiber : ∀ p : baseDomain, Set.Finite {x : TotalSpace | projection x = p.val}
  projectionSmooth : ContMDiff I4 I4 ∞ projection
  projectionDifferential : ∀ x : TotalSpace,
    TangentSpace I4 x ≃L[ℝ] TangentSpace I4 (projection x)
  projectionDifferential_eq : ∀ x : TotalSpace,
    (projectionDifferential x).toContinuousLinearMap = mfderiv I4 I4 projection x
  innerCompactClosure : IsCompact (closure (projection ⁻¹' innerBaseDomain))

attribute [instance] LocalFiniteCover.totalTopology LocalFiniteCover.totalCharted
  LocalFiniteCover.totalManifold

variable {M}

/-- An internal coordinate chart on a genuine finite covering manifold. -/
structure LocalCoverChart (F : LocalFiniteCover M) where
  coordinate : OpenPartialHomeomorph F.TotalSpace FourSpace
  coordinate_mem_atlas : coordinate ∈ atlas FourSpace F.TotalSpace
  outerDomain : Set FourSpace
  innerDomain : Set FourSpace
  outerOpen : IsOpen outerDomain
  innerOpen : IsOpen innerDomain
  innerNonempty : innerDomain.Nonempty
  innerCompactClosure : IsCompact (closure innerDomain)
  closureInnerSubset : closure innerDomain ⊆ outerDomain
  outerSubsetTarget : outerDomain ⊆ coordinate.target
  innerMapsToBase : ∀ x ∈ innerDomain,
    F.projection (coordinate.symm x) ∈ F.innerBaseDomain
  tangentMap : ∀ x : FourSpace,
    FourSpace ≃L[ℝ] TangentSpace I4 (F.projection (coordinate.symm x))
  tangentMap_eq : ∀ x ∈ outerDomain,
    (tangentMap x).toContinuousLinearMap =
      mfderiv I4 I4 (F.projection ∘ coordinate.symm) x

variable {F : LocalFiniteCover M}

def LocalCoverChart.liftToCover (c : LocalCoverChart F) : FourSpace → F.TotalSpace :=
  c.coordinate.symm

def LocalCoverChart.lift (c : LocalCoverChart F) : FourSpace → M :=
  F.projection ∘ c.liftToCover

def LocalCoverChart.baseDomain (_c : LocalCoverChart F) : Set M := F.baseDomain

/-- The lifted vector uses the inverse of the actual covering differential. -/
def LocalCoverChart.liftedVector (c : LocalCoverChart F) (Y : RawVector M)
    (x : FourSpace) : FourSpace :=
  (c.tangentMap x).symm (Y (c.lift x))

/-- Coordinate coefficients of the genuine pulled-back covector. -/
def LocalCoverChart.liftedCovector (c : LocalCoverChart F) (u : RawCovector M)
    (x : FourSpace) : Fin 4 → ℝ :=
  fun i => u (c.lift x) (c.tangentMap x (basisVector i))

/-- Coordinate coefficients of the genuine pulled-back covariant tensor. -/
def LocalCoverChart.liftedCov2 (c : LocalCoverChart F) (u : RawCov2 M)
    (x : FourSpace) : Mat4 :=
  fun i j => u (c.lift x)
    (c.tangentMap x (basisVector i)) (c.tangentMap x (basisVector j))

/-- The lifted vector is the genuine inverse-differential lift on its domain. -/
theorem LocalCoverChart.differential_liftedVector (c : LocalCoverChart F)
    (Y : RawVector M) (x : FourSpace) (hx : x ∈ c.outerDomain) :
    mfderiv I4 I4 c.lift x (c.liftedVector Y x) = Y (c.lift x) := by
  have hd : (c.tangentMap x).toContinuousLinearMap = mfderiv I4 I4 c.lift x :=
    c.tangentMap_eq x hx
  rw [← hd]
  exact (c.tangentMap x).apply_symm_apply _

theorem LocalCoverChart.liftedCovector_eq_pullback (c : LocalCoverChart F)
    (u : RawCovector M) (x : FourSpace) (hx : x ∈ c.outerDomain) (i : Fin 4) :
    c.liftedCovector u x i = pullbackCovector c.lift u x (basisVector i) := by
  have hd : (c.tangentMap x).toContinuousLinearMap = mfderiv I4 I4 c.lift x :=
    c.tangentMap_eq x hx
  change u (c.lift x) ((c.tangentMap x).toContinuousLinearMap (basisVector i)) = _
  rw [hd]
  rfl

theorem LocalCoverChart.liftedCov2_eq_pullback (c : LocalCoverChart F)
    (u : RawCov2 M) (x : FourSpace) (hx : x ∈ c.outerDomain) (i j : Fin 4) :
    c.liftedCov2 u x i j =
      pullbackCov2 c.lift u x (basisVector i) (basisVector j) := by
  have hd : (c.tangentMap x).toContinuousLinearMap = mfderiv I4 I4 c.lift x :=
    c.tangentMap_eq x hx
  change u (c.lift x) ((c.tangentMap x).toContinuousLinearMap (basisVector i))
    ((c.tangentMap x).toContinuousLinearMap (basisVector j)) = _
  rw [hd]
  rfl

/-- Numerical data fixed before quantifying over a family of covers. -/
structure CoverNumerics where
  shrinkRadius : ℝ
  shrinkRadius_pos : 0 < shrinkRadius
  outerRadius : ℝ
  outerRadius_pos : 0 < outerRadius
  overlap : ℕ
  overlap_pos : 0 < overlap
  atlasOverlap : ℕ
  atlasOverlap_pos : 0 < atlasOverlap

variable (M)

/-- Actual finite local covers and their internal coordinate atlases. The
source overlap bound counts `CoverIndex`; `atlasOverlap` counts coordinate
charts on each covering manifold, independently of downstairs sheet count. -/
structure BoundedLocalCover where
  CoverIndex : Type
  cover : CoverIndex → LocalFiniteCover M
  ChartIndex : CoverIndex → Type
  localChart : ∀ a : CoverIndex, ChartIndex a → LocalCoverChart (cover a)
  numerics : CoverNumerics
  innerCover : ∀ p : M, ∃ a : CoverIndex, p ∈ (cover a).innerBaseDomain
  internallyCovered : ∀ a : CoverIndex, ∀ p : (cover a).TotalSpace,
    (cover a).projection p ∈ (cover a).innerBaseDomain →
      ∃ j : ChartIndex a, ∃ x ∈ (localChart a j).innerDomain,
        (localChart a j).liftToCover x = p
  locallyFinite : LocallyFinite (fun a => (cover a).baseDomain)
  overlapBound : ∀ p : M,
    Set.Finite {a : CoverIndex | p ∈ (cover a).baseDomain} ∧
      Set.ncard {a : CoverIndex | p ∈ (cover a).baseDomain} ≤ numerics.overlap
  internalLocallyFinite : ∀ a : CoverIndex,
    LocallyFinite (fun j : ChartIndex a => (localChart a j).coordinate.source)
  internalOverlapBound : ∀ a : CoverIndex, ∀ p : (cover a).TotalSpace,
    Set.Finite {j : ChartIndex a | p ∈ (localChart a j).coordinate.source} ∧
      Set.ncard {j : ChartIndex a | p ∈ (localChart a j).coordinate.source} ≤
        numerics.atlasOverlap
  uniformShrink : ∀ a : CoverIndex, ∀ j : ChartIndex a,
    ∀ x ∈ closure (localChart a j).innerDomain,
      Metric.closedBall x numerics.shrinkRadius ⊆ (localChart a j).outerDomain
  uniformOuterRadius : ∀ a : CoverIndex, ∀ j : ChartIndex a, ∃ c : FourSpace,
    (localChart a j).outerDomain ⊆ Metric.ball c numerics.outerRadius

variable {M}

/-- Flattening only for taking a supremum of coordinate norms. It is never
used to count downstairs cover multiplicity. -/
abbrev BoundedLocalCover.Index (C : BoundedLocalCover M) :=
  Sigma C.ChartIndex

def BoundedLocalCover.owner (C : BoundedLocalCover M) (ν : C.Index) : C.CoverIndex := ν.1

def BoundedLocalCover.chart (C : BoundedLocalCover M) (ν : C.Index) :
    LocalCoverChart (C.cover (C.owner ν)) := C.localChart ν.1 ν.2

/-- Every actual base point is measured by an inner coordinate lift. -/
theorem BoundedLocalCover.exists_inner_lift (C : BoundedLocalCover M) (p : M) :
    ∃ ν : C.Index, ∃ x ∈ (C.chart ν).innerDomain, (C.chart ν).lift x = p := by
  obtain ⟨a, ha⟩ := C.innerCover p
  obtain ⟨q, hq⟩ := (C.cover a).ontoBase
    ⟨p, (C.cover a).innerBaseSubset ha⟩
  have hp : (C.cover a).projection q = p := congrArg Subtype.val hq
  obtain ⟨j, x, hx, hxp⟩ := C.internallyCovered a q (by simpa [hp] using ha)
  refine ⟨⟨a, j⟩, x, hx, ?_⟩
  change (C.cover a).projection ((C.localChart a j).liftToCover x) = p
  rw [hxp, hp]

/-- The actual cover-sup norm of lifted vectors, with values in `ℝ≥0∞`. -/
def BoundedLocalCover.vectorENorm (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (Y : RawVector M) : ℝ≥0∞ :=
  ⨆ ν : C.Index, coordinateHolderENorm k α (C.chart ν).innerDomain
    ((C.chart ν).liftedVector Y)

/-- The actual cover-sup norm of lifted covectors. -/
def BoundedLocalCover.covectorENorm (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (u : RawCovector M) : ℝ≥0∞ :=
  ⨆ ν : C.Index, coordinateHolderENorm k α (C.chart ν).innerDomain
    ((C.chart ν).liftedCovector u)

/-- The actual cover-sup norm of lifted covariant two-tensors. -/
def BoundedLocalCover.cov2ENorm (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (u : RawCov2 M) : ℝ≥0∞ :=
  ⨆ ν : C.Index, coordinateHolderENorm k α (C.chart ν).innerDomain
    ((C.chart ν).liftedCov2 u)

def BoundedLocalCover.VectorHolder (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (Y : RawVector M) : Prop :=
  (∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedVector Y)
    (C.chart ν).innerDomain) ∧ C.vectorENorm k α Y < ⊤

def BoundedLocalCover.CovectorHolder (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (u : RawCovector M) : Prop :=
  (∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCovector u)
    (C.chart ν).innerDomain) ∧ C.covectorENorm k α u < ⊤

def BoundedLocalCover.Cov2Holder (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (u : RawCov2 M) : Prop :=
  (∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 u)
    (C.chart ν).innerDomain) ∧ C.cov2ENorm k α u < ⊤

/-- Genuine big Hölder section spaces, as subtypes of actual sections. -/
abbrev VectorHolderSection (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :=
  {Y : RawVector M // C.VectorHolder k α Y}

abbrev CovectorHolderSection (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :=
  {u : RawCovector M // C.CovectorHolder k α u}

abbrev Cov2HolderSection (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :=
  {u : RawCov2 M // C.Cov2Holder k α u}

abbrev SymmetricHolderSection (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :=
  {u : RawCov2 M // IsSymmetricCov2 u ∧ C.Cov2Holder k α u}

def VectorHolderSection.norm {C : BoundedLocalCover M} {k : ℕ} {α : ℝ≥0}
    (Y : VectorHolderSection C k α) : ℝ := (C.vectorENorm k α Y.val).toReal

def CovectorHolderSection.norm {C : BoundedLocalCover M} {k : ℕ} {α : ℝ≥0}
    (u : CovectorHolderSection C k α) : ℝ := (C.covectorENorm k α u.val).toReal

def Cov2HolderSection.norm {C : BoundedLocalCover M} {k : ℕ} {α : ℝ≥0}
    (u : Cov2HolderSection C k α) : ℝ := (C.cov2ENorm k α u.val).toReal

theorem VectorHolderSection.ofReal_norm {C : BoundedLocalCover M} {k : ℕ} {α : ℝ≥0}
    (Y : VectorHolderSection C k α) :
    ENNReal.ofReal Y.norm = C.vectorENorm k α Y.val :=
  ENNReal.ofReal_toReal (ne_of_lt Y.property.2)

theorem CovectorHolderSection.ofReal_norm {C : BoundedLocalCover M} {k : ℕ} {α : ℝ≥0}
    (u : CovectorHolderSection C k α) :
    ENNReal.ofReal u.norm = C.covectorENorm k α u.val :=
  ENNReal.ofReal_toReal (ne_of_lt u.property.2)

theorem Cov2HolderSection.ofReal_norm {C : BoundedLocalCover M} {k : ℕ} {α : ℝ≥0}
    (u : Cov2HolderSection C k α) :
    ENNReal.ofReal u.norm = C.cov2ENorm k α u.val :=
  ENNReal.ofReal_toReal (ne_of_lt u.property.2)

/-- Fixed numerical metric data. For a theorem combining the natural and
shifted vector pairs use `3 ≤ order`; the natural pair alone needs order 2.
This bounds the backgrounds without changing the order in which differences
are measured in the theorem. -/
structure MetricCoefficientNumerics where
  exponent : HolderExponent
  order : ℕ
  order_ge_two : 2 ≤ order
  lower : ℝ
  lower_pos : 0 < lower
  upper : ℝ
  upper_pos : 0 < upper
  coefficientBound : ℝ≥0

def LocalCoverChart.inverseMetricCoefficients (c : LocalCoverChart F)
    (g : RawCov2 M) (x : FourSpace) : Mat4 :=
  ((c.liftedCov2 g x)⁻¹ : Mat4)

/-- Concrete coefficient hypotheses for an actual positive metric. These
bounds apply on the larger domains used for interior estimates. -/
structure MetricAdmissible (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (g : RawCov2 M) : Prop where
  metric : IsMetric g
  regularity : ∀ ν : C.Index, BigHolderOn b.order b.exponent.value
    (C.chart ν).outerDomain ((C.chart ν).liftedCov2 g)
  inverseRegularity : ∀ ν : C.Index, BigHolderOn b.order b.exponent.value
    (C.chart ν).outerDomain ((C.chart ν).inverseMetricCoefficients g)
  ellipticityLower : ∀ ν : C.Index, ∀ x ∈ (C.chart ν).outerDomain, ∀ v : FourSpace,
    b.lower * ‖v‖ ^ 2 ≤
      matrixToBilinear ((C.chart ν).liftedCov2 g x) v v
  ellipticityUpper : ∀ ν : C.Index, ∀ x ∈ (C.chart ν).outerDomain, ∀ v : FourSpace,
    matrixToBilinear ((C.chart ν).liftedCov2 g x) v v ≤ b.upper * ‖v‖ ^ 2
  coefficientBound : ∀ ν : C.Index,
    coordinateHolderENorm b.order b.exponent.value (C.chart ν).outerDomain
        ((C.chart ν).liftedCov2 g) +
      coordinateHolderENorm b.order b.exponent.value (C.chart ν).outerDomain
        ((C.chart ν).inverseMetricCoefficients g) ≤ (b.coefficientBound : ℝ≥0∞)

end K24.Global


/- Original source module: K24Work.Global.Sobolev -/

/-!
# Real-order adapted-cover Sobolev quantities for K24

The local realization is the standard Bessel-potential space on Euclidean
four-space. The order is a real number. All local and cover quantities first
take values in `ℝ≥0∞`; no infinite value is silently converted to zero.

This file defines the realization and proves its elementary membership facts.
It does not prove the nonlinear multiplication or geometric K24 estimates.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory TemperedDistribution FourierTransform
open scoped NNReal ENNReal SchwartzMap BigOperators Manifold ContDiff

namespace K24.Global

abbrev SobolevModel := EuclideanSpace ℝ (Fin 4)
abbrev LocalL2 := Lp ℂ 2 (volume : Measure SobolevModel)
abbrev LocalDistribution := 𝓢'(SobolevModel, ℂ)

/-- Real-order Bessel-potential membership, using Mathlib's distributional
Fourier transform and multiplier `(1 + ‖ξ‖²)^(s/2)`. -/
abbrev BesselMem (s : ℝ) (T : LocalDistribution) : Prop :=
  TemperedDistribution.MemSobolev s 2 T

/-- The `L²` representative of the Bessel potential. Its uniqueness follows
from the injectivity of the standard `L²` embedding into distributions. -/
def besselRepresentative {s : ℝ} {T : LocalDistribution} (h : BesselMem s T) :
    LocalL2 := Classical.choose h

theorem besselRepresentative_spec {s : ℝ} {T : LocalDistribution}
    (h : BesselMem s T) :
    besselPotential SobolevModel ℂ s T =
      (besselRepresentative h : LocalDistribution) := Classical.choose_spec h

theorem localL2_distribution_injective :
    Function.Injective (fun f : LocalL2 => (f : LocalDistribution)) := by
  exact LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
      (μ := (volume : Measure SobolevModel)) (p := 2))

theorem besselRepresentative_unique {s : ℝ} {T : LocalDistribution}
    (h : BesselMem s T) (v : LocalL2)
    (hv : besselPotential SobolevModel ℂ s T = (v : LocalDistribution)) :
    besselRepresentative h = v := by
  apply localL2_distribution_injective
  exact (besselRepresentative_spec h).symm.trans hv

/-- Extended Bessel-potential norm, infinite precisely outside `H^s`. -/
def besselSobolevENN (s : ℝ) (T : LocalDistribution) : ℝ≥0∞ := by
  classical
  exact if h : BesselMem s T then ENNReal.ofReal ‖besselRepresentative h‖ else ⊤

theorem besselSobolevENN_of_mem {s : ℝ} {T : LocalDistribution}
    (h : BesselMem s T) :
    besselSobolevENN s T = ENNReal.ofReal ‖besselRepresentative h‖ := by
  simp [besselSobolevENN, h]

theorem besselSobolevENN_lt_top_iff (s : ℝ) (T : LocalDistribution) :
    besselSobolevENN s T < ⊤ ↔ BesselMem s T := by
  classical
  by_cases h : BesselMem s T <;> simp [besselSobolevENN, h]

theorem besselSobolevENN_eq_of_rep {s : ℝ} {T : LocalDistribution}
    (v : LocalL2)
    (hv : besselPotential SobolevModel ℂ s T = (v : LocalDistribution)) :
    besselSobolevENN s T = ENNReal.ofReal ‖v‖ := by
  have h : BesselMem s T := ⟨v, hv⟩
  rw [besselSobolevENN_of_mem h, besselRepresentative_unique h v hv]

@[simp] theorem besselSobolevENN_zero (s : ℝ) :
    besselSobolevENN s 0 = 0 := by
  have hv : besselPotential SobolevModel ℂ s 0 =
      ((0 : LocalL2) : LocalDistribution) := by
    change besselPotential SobolevModel ℂ s 0 =
      Lp.toTemperedDistributionCLM ℂ (volume : Measure SobolevModel) 2 0
    rw [map_zero, map_zero]
  simpa using besselSobolevENN_eq_of_rep (0 : LocalL2) hv

/-- At order zero the definition is exactly the ordinary `L²` norm. -/
theorem besselSobolevENN_zero_order (v : LocalL2) :
    besselSobolevENN 0 (v : LocalDistribution) = ENNReal.ofReal ‖v‖ := by
  apply besselSobolevENN_eq_of_rep v
  simp

/-- Exact Fourier-side characterization; the exponent remains the original
real number `s / 2`, with no integer rounding. -/
theorem besselMem_iff_weighted_fourier (s : ℝ) (T : LocalDistribution) :
    BesselMem s T ↔ ∃ v : LocalL2,
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : SobolevModel => ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ))
        (𝓕 T) = (v : LocalDistribution) :=
  TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier

/-- Complexification allows real tensor coefficients to use the standard
complex Fourier transform without changing their absolute values. -/
def complexifyLocal (f : SobolevModel → ℝ) : SobolevModel → ℂ :=
  fun x => (f x : ℂ)

/-- Canonical distribution associated with a genuine square-integrable local
coefficient function. `MemLp` includes measurability and finite `L²` norm. -/
def localFunctionDistribution (f : SobolevModel → ℝ)
    (h : MemLp (complexifyLocal f) 2 volume) : LocalDistribution :=
  (h.toLp (complexifyLocal f) : LocalDistribution)

/-- The local function realization of `H^s`. For the K24 orders `s > 4`
and `s - 2 > 2`, imposing `L²` causes no loss. For negative orders the full
distribution space is instead provided by `BesselMem`. -/
def LocalSobolevMem (s : ℝ) (f : SobolevModel → ℝ) : Prop :=
  ∃ h : MemLp (complexifyLocal f) 2 volume,
    BesselMem s (localFunctionDistribution f h)

/-- Extended local norm of the actual function, with invalid `L²` input
assigned infinity rather than a default Fourier transform or zero norm. -/
def localSobolevENN (s : ℝ) (f : SobolevModel → ℝ) : ℝ≥0∞ := by
  classical
  exact if h : MemLp (complexifyLocal f) 2 volume then
    besselSobolevENN s (localFunctionDistribution f h)
  else ⊤

theorem localSobolevENN_lt_top_iff (s : ℝ) (f : SobolevModel → ℝ) :
    localSobolevENN s f < ⊤ ↔ LocalSobolevMem s f := by
  classical
  by_cases h : MemLp (complexifyLocal f) 2 volume
  · simp only [localSobolevENN, dif_pos h, besselSobolevENN_lt_top_iff,
      LocalSobolevMem]
    exact ⟨fun hs => ⟨h, hs⟩, fun ⟨_, hs⟩ => hs⟩
  · simp [localSobolevENN, h, LocalSobolevMem]

@[simp] theorem localSobolevENN_zero (s : ℝ) :
    localSobolevENN s 0 = 0 := by
  have hf : MemLp (complexifyLocal 0) 2 volume := by
    change MemLp (fun _ : SobolevModel => (0 : ℂ)) 2 volume
    exact MemLp.zero'
  simp only [localSobolevENN, dif_pos hf]
  have hd : localFunctionDistribution 0 hf = 0 := by
    unfold localFunctionDistribution
    rw [← Lp.toTemperedDistributionCLM_apply]
    have hz : hf.toLp (complexifyLocal 0) = 0 := rfl
    rw [hz, map_zero]
  rw [hd, besselSobolevENN_zero]

/-- A finite-norm local coefficient, before any almost-everywhere quotient
or completion is installed on the section space. -/
abbrev LocalSobolevFunction (s : ℝ) :=
  {f : SobolevModel → ℝ // localSobolevENN s f < ⊤}

/-- Real conversion is available only on the explicitly finite-norm subtype. -/
def LocalSobolevFunction.sobolevNorm {s : ℝ} (f : LocalSobolevFunction s) : ℝ :=
  (localSobolevENN s f.val).toReal

theorem LocalSobolevFunction.ofReal_sobolevNorm {s : ℝ}
    (f : LocalSobolevFunction s) :
    ENNReal.ofReal f.sobolevNorm = localSobolevENN s f.val :=
  ENNReal.ofReal_toReal f.property.ne

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- A partition on the base local covers and a separate coordinate partition
on each actual lifted cover. The Euclidean cutoff is the pullback of their
product and has compact support strictly inside its coordinate domain.
Thus zero extension is specified data, not an assumed extension operator.
All sums below use unit cover and internal-chart weights; there is no implicit
normalization by finite covering degree and no bound on that degree. -/
structure SobolevPartition (C : BoundedLocalCover M) where
  partition : SmoothPartitionOfUnity C.CoverIndex I4 M
  subordinate : ∀ a : C.CoverIndex,
    tsupport (partition a : M → ℝ) ⊆ (C.cover a).innerBaseDomain
  upstairsPartition : ∀ a : C.CoverIndex,
    SmoothPartitionOfUnity (C.ChartIndex a) I4 (C.cover a).TotalSpace
      ((C.cover a).projection ⁻¹' (C.cover a).innerBaseDomain)
  upstairsSubordinate : ∀ a : C.CoverIndex, ∀ j : C.ChartIndex a,
    tsupport (upstairsPartition a j : (C.cover a).TotalSpace → ℝ) ⊆
      (C.localChart a j).coordinate.source ∩
        (C.localChart a j).coordinate ⁻¹' (C.localChart a j).outerDomain
  cutoff : C.Index → FourSpace → ℝ
  cutoffSmooth : ∀ ν : C.Index, ContDiff ℝ ∞ (cutoff ν)
  cutoffCompact : ∀ ν : C.Index, HasCompactSupport (cutoff ν)
  cutoffSupport : ∀ ν : C.Index, tsupport (cutoff ν) ⊆ (C.chart ν).outerDomain
  cutoff_eq_partition : ∀ ν : C.Index, ∀ x ∈ (C.chart ν).outerDomain,
    cutoff ν x = partition ν.1 ((C.chart ν).lift x) *
      upstairsPartition ν.1 ν.2 ((C.chart ν).liftToCover x)

namespace SobolevPartition

variable {C : BoundedLocalCover M} (P : SobolevPartition C)

/-- Literal zero extension of a partition-localized lifted coefficient. -/
def localize (ν : C.Index) (f : FourSpace → ℝ) : FourSpace → ℝ := by
  classical
  exact fun x => if x ∈ (C.chart ν).outerDomain then P.cutoff ν x * f x else 0

theorem cutoff_eq_zero_outside (ν : C.Index) {x : FourSpace}
    (hx : x ∉ (C.chart ν).outerDomain) : P.cutoff ν x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun ht => hx (P.cutoffSupport ν ht))

theorem localize_eq_cutoff_mul (ν : C.Index) (f : FourSpace → ℝ) :
    P.localize ν f = P.cutoff ν * f := by
  classical
  funext x
  by_cases hx : x ∈ (C.chart ν).outerDomain
  · simp [localize, hx]
  · simp [localize, hx, P.cutoff_eq_zero_outside ν hx]

theorem localize_eq_zero_outside (ν : C.Index) (f : FourSpace → ℝ)
    {x : FourSpace} (hx : x ∉ (C.chart ν).outerDomain) :
    P.localize ν f x = 0 := by
  simp [localize, hx]

theorem localize_hasCompactSupport (ν : C.Index) (f : FourSpace → ℝ) :
    HasCompactSupport (P.localize ν f) := by
  rw [P.localize_eq_cutoff_mul]
  exact (P.cutoffCompact ν).mul_right

theorem localize_tsupport_subset (ν : C.Index) (f : FourSpace → ℝ) :
    tsupport (P.localize ν f) ⊆ (C.chart ν).outerDomain := by
  rw [P.localize_eq_cutoff_mul]
  exact tsupport_mul_subset_left.trans (P.cutoffSupport ν)

/-- Concrete cutoff bounds usable in a uniform multiplication/localization
theorem. These are ordinary derivative bounds, not a presumed operator norm
estimate. The required order relative to `s` belongs to that theorem. -/
def CutoffDerivativeBounds (m : ℕ) (B : ℝ≥0) : Prop :=
  ∀ ν : C.Index, ∀ j ≤ m,
    derivativeENorm j Set.univ (P.cutoff ν) ≤ (B : ℝ≥0∞)

/-- An explicit multiplicity bound for coordinate partition supports on each
lifted cover. This never counts sheets meeting a point downstairs. Finiteness
of these sets already follows from the actual partition's local finiteness. -/
def UpstairsOverlapBound (N : ℕ) : Prop :=
  ∀ a : C.CoverIndex, ∀ p : (C.cover a).TotalSpace,
    Set.ncard {j : C.ChartIndex a | P.upstairsPartition a j p ≠ 0} ≤ N

theorem upstairsOverlapBound : P.UpstairsOverlapBound C.numerics.atlasOverlap := by
  intro a p
  have hsub : {j : C.ChartIndex a | P.upstairsPartition a j p ≠ 0} ⊆
      {j : C.ChartIndex a | p ∈ (C.localChart a j).coordinate.source} := by
    intro j hj
    exact (P.upstairsSubordinate a j
      (subset_tsupport (P.upstairsPartition a j : (C.cover a).TotalSpace → ℝ) hj)).1
  exact (Set.ncard_le_ncard hsub (C.internalOverlapBound a p).1).trans
    (C.internalOverlapBound a p).2

/-- Squared partition norm of a finite family of coefficient components.
The cover weights and component weights are all exactly one. -/
def componentSobolevSquare {κ : Type*} [Fintype κ] (s : ℝ)
    (f : C.Index → κ → FourSpace → ℝ) : ℝ≥0∞ :=
  ∑' ν : C.Index, ∑ a : κ, (localSobolevENN s (P.localize ν (f ν a))) ^ (2 : ℕ)

/-- The actual `ℓ²` partition norm; this is an extended square root, so
an infinite sum or any infinite local term remains infinite. -/
def componentSobolevENorm {κ : Type*} [Fintype κ] (s : ℝ)
    (f : C.Index → κ → FourSpace → ℝ) : ℝ≥0∞ :=
  (P.componentSobolevSquare s f) ^ (1 / 2 : ℝ)

theorem componentSobolevENorm_lt_top_iff {κ : Type*} [Fintype κ] (s : ℝ)
    (f : C.Index → κ → FourSpace → ℝ) :
    P.componentSobolevENorm s f < ⊤ ↔ P.componentSobolevSquare s f < ⊤ := by
  exact ENNReal.rpow_lt_top_iff_of_pos (by norm_num)

/-- Finiteness of the global sum really implies finiteness and Sobolev
membership of every compactly supported localized coefficient. -/
theorem local_mem_of_component_finite {κ : Type*} [Fintype κ] {s : ℝ}
    {f : C.Index → κ → FourSpace → ℝ}
    (h : P.componentSobolevENorm s f < ⊤) (ν : C.Index) (a : κ) :
    LocalSobolevMem s (P.localize ν (f ν a)) := by
  classical
  have hsum : P.componentSobolevSquare s f < ⊤ :=
    (P.componentSobolevENorm_lt_top_iff s f).mp h
  have hsingle : (localSobolevENN s (P.localize ν (f ν a))) ^ (2 : ℕ) ≤
      ∑ b : κ, (localSobolevENN s (P.localize ν (f ν b))) ^ (2 : ℕ) :=
    Finset.single_le_sum
      (f := fun b : κ => (localSobolevENN s (P.localize ν (f ν b))) ^ (2 : ℕ))
      (fun _ _ => bot_le) (Finset.mem_univ a)
  have houter : (∑ b : κ, (localSobolevENN s (P.localize ν (f ν b))) ^ (2 : ℕ)) ≤
      P.componentSobolevSquare s f := ENNReal.le_tsum ν
  have hpow : (localSobolevENN s (P.localize ν (f ν a))) ^ (2 : ℕ) < ⊤ :=
    lt_of_le_of_lt (hsingle.trans houter) hsum
  apply (localSobolevENN_lt_top_iff s (P.localize ν (f ν a))).mp
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hpow

/-- Scalar components of the genuine lifted tensor, before localization. -/
def cov2Components (u : RawCov2 M) (ν : C.Index) (a : Fin 4 × Fin 4)
    (x : FourSpace) : ℝ := (C.chart ν).liftedCov2 u x a.1 a.2

/-- Scalar components of the genuine lifted covector. -/
def covectorComponents (u : RawCovector M) (ν : C.Index) (a : Fin 4)
    (x : FourSpace) : ℝ := (C.chart ν).liftedCovector u x a

/-- Scalar components of the vector pulled back by the inverse differential. -/
def vectorComponents (Y : RawVector M) (ν : C.Index) (a : Fin 4)
    (x : FourSpace) : ℝ := (C.chart ν).liftedVector Y x a

def cov2SobolevENorm (s : ℝ) (u : RawCov2 M) : ℝ≥0∞ :=
  P.componentSobolevENorm s (cov2Components (C := C) u)

def covectorSobolevENorm (s : ℝ) (u : RawCovector M) : ℝ≥0∞ :=
  P.componentSobolevENorm s (covectorComponents (C := C) u)

def vectorSobolevENorm (s : ℝ) (Y : RawVector M) : ℝ≥0∞ :=
  P.componentSobolevENorm s (vectorComponents (C := C) Y)

/-- A genuine pointwise tensor representative with real-order Sobolev norm.
For the K24 source use `k = 2, s > 4`; for the target use `k = 0, s - 2 > 2`.
The Sobolev embedding identifying these with the usual a.e. quotient spaces
is not claimed proved. No `C^k` quantity is added to the Sobolev norm. -/
def Cov2Sobolev (k : ℕ) (s : ℝ) (u : RawCov2 M) : Prop :=
  Cov2ContDiff k u ∧ P.cov2SobolevENorm s u < ⊤

def CovectorSobolev (k : ℕ) (s : ℝ) (u : RawCovector M) : Prop :=
  CovectorContDiff k u ∧ P.covectorSobolevENorm s u < ⊤

def VectorSobolev (k : ℕ) (s : ℝ) (Y : RawVector M) : Prop :=
  VectorContDiff k Y ∧ P.vectorSobolevENorm s Y < ⊤

end SobolevPartition

/-- Pointwise representatives of the indicated finite cover Sobolev spaces.
Normed-space and completeness instances are deliberately separate obligations. -/
abbrev Cov2SobolevSection {C : BoundedLocalCover M} (P : SobolevPartition C)
    (k : ℕ) (s : ℝ) := {u : RawCov2 M // P.Cov2Sobolev k s u}

abbrev CovectorSobolevSection {C : BoundedLocalCover M} (P : SobolevPartition C)
    (k : ℕ) (s : ℝ) := {u : RawCovector M // P.CovectorSobolev k s u}

abbrev VectorSobolevSection {C : BoundedLocalCover M} (P : SobolevPartition C)
    (k : ℕ) (s : ℝ) := {Y : RawVector M // P.VectorSobolev k s Y}

def Cov2SobolevSection.norm {C : BoundedLocalCover M} {P : SobolevPartition C}
    {k : ℕ} {s : ℝ} (u : Cov2SobolevSection P k s) : ℝ :=
  (P.cov2SobolevENorm s u.val).toReal

def CovectorSobolevSection.norm {C : BoundedLocalCover M} {P : SobolevPartition C}
    {k : ℕ} {s : ℝ} (u : CovectorSobolevSection P k s) : ℝ :=
  (P.covectorSobolevENorm s u.val).toReal

def VectorSobolevSection.norm {C : BoundedLocalCover M} {P : SobolevPartition C}
    {k : ℕ} {s : ℝ} (Y : VectorSobolevSection P k s) : ℝ :=
  (P.vectorSobolevENorm s Y.val).toReal

theorem Cov2SobolevSection.ofReal_norm {C : BoundedLocalCover M}
    {P : SobolevPartition C} {k : ℕ} {s : ℝ} (u : Cov2SobolevSection P k s) :
    ENNReal.ofReal u.norm = P.cov2SobolevENorm s u.val :=
  ENNReal.ofReal_toReal u.property.2.ne

theorem CovectorSobolevSection.ofReal_norm {C : BoundedLocalCover M}
    {P : SobolevPartition C} {k : ℕ} {s : ℝ} (u : CovectorSobolevSection P k s) :
    ENNReal.ofReal u.norm = P.covectorSobolevENorm s u.val :=
  ENNReal.ofReal_toReal u.property.2.ne

theorem VectorSobolevSection.ofReal_norm {C : BoundedLocalCover M}
    {P : SobolevPartition C} {k : ℕ} {s : ℝ} (Y : VectorSobolevSection P k s) :
    ENNReal.ofReal Y.norm = P.vectorSobolevENorm s Y.val :=
  ENNReal.ofReal_toReal Y.property.2.ne

end K24.Global


/- Original source module: K24Work.Global.Calculus -/

/-!
# Explicit analytic predicates for concrete K24 section spaces

These helpers expand into algebraic equalities, actual extended norm
inequalities, and the uniform epsilon-remainder definition of a Frechet
derivative. They allow an unproved geometric theorem to be stated before
proving normed-space/completeness instances for the genuine section spaces.
They do not supply geometric data or assume any K24 conclusion.
-/

set_option autoImplicit false

open scoped NNReal ENNReal

namespace K24.Global

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

/-- Concrete norm and completeness laws on a set of actual sections. This is
used as a conclusion about the defined section spaces, not supplied as an
unrelated abstract Banach space. -/
structure SectionBanachSpace (S : Set X) (nx : X → ℝ≥0∞) : Prop where
  zero_mem : (0 : X) ∈ S
  add_mem : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S
  smul_mem : ∀ (c : ℝ) (u : X), u ∈ S → c • u ∈ S
  finite : ∀ u ∈ S, nx u < ⊤
  zero_norm : nx 0 = 0
  definite : ∀ u ∈ S, nx u = 0 → u = 0
  triangle : ∀ u ∈ S, ∀ v ∈ S, nx (u + v) ≤ nx u + nx v
  homogeneous : ∀ (c : ℝ) (u : X), u ∈ S →
    nx (c • u) = ENNReal.ofReal |c| * nx u
  complete : ∀ f : ℕ → X, (∀ n, f n ∈ S) →
    (∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      nx (f i - f j) < ENNReal.ofReal eps) →
    ∃ v ∈ S, ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      nx (f i - v) < ENNReal.ofReal eps

/-- A nonvacuous neighborhood condition in the actual section norm. -/
def SectionNeighborhood (S U : Set X) (nx : X → ℝ≥0∞) (z : X) : Prop :=
  ∃ radius : ℝ, 0 < radius ∧
    ∀ h ∈ S, nx h < ENNReal.ofReal radius → z + h ∈ U

/-- Linearity restricted to a concrete linear section domain. -/
def SectionLinearOn (S : Set X) (A : X → Y) : Prop :=
  A 0 = 0 ∧
  (∀ u ∈ S, ∀ v ∈ S, A (u + v) = A u + A v) ∧
  (∀ (c : ℝ) (u : X), u ∈ S → A (c • u) = c • A u)

/-- A finite bound on a map between concrete section norms. -/
def SectionBoundedOn (S : Set X) (nx : X → ℝ≥0∞) (ny : Y → ℝ≥0∞)
    (A : X → Y) : Prop :=
  ∃ C : ℝ≥0, ∀ u ∈ S, ny (A u) ≤ (C : ℝ≥0∞) * nx u

/-- The actual operator norm expressed through all valid norm bounds. -/
noncomputable def sectionOperatorENorm (S : Set X) (nx : X → ℝ≥0∞)
    (ny : Y → ℝ≥0∞) (A : X → Y) : ℝ≥0∞ :=
  sInf {C : ℝ≥0∞ | ∀ u ∈ S, ny (A u) ≤ C * nx u}

/-- An actual linear bounded bijection between specified section sets.
The inverse estimate is stated separately, not manufactured by this predicate. -/
def SectionIsomorphism (S : Set X) (T : Set Y) (nx : X → ℝ≥0∞)
    (ny : Y → ℝ≥0∞) (A : X → Y) : Prop :=
  Set.MapsTo A S T ∧ SectionLinearOn S A ∧ SectionBoundedOn S nx ny A ∧
  Set.InjOn A S ∧ ∀ v ∈ T, ∃ u ∈ S, A u = v

/-- The inverse norm estimate, written without choosing an unrelated inverse. -/
def SectionInverseBound (S : Set X) (nx : X → ℝ≥0∞) (ny : Y → ℝ≥0∞)
    (A : X → Y) (C : ℝ≥0) : Prop :=
  ∀ u ∈ S, nx u ≤ (C : ℝ≥0∞) * ny (A u)

/-- The Banach-dual gap furnished by an inverse estimate. The adjoint is the
actual composition of a bounded linear functional with the actual operator. -/
def SectionDualGap (S : Set X) (T : Set Y) (nx : X → ℝ≥0∞) (ny : Y → ℝ≥0∞)
    (A : X → Y) (C : ℝ≥0) : Prop :=
  ∀ phi : Y → ℝ, SectionLinearOn T phi →
    SectionBoundedOn T ny (fun r : ℝ => ENNReal.ofReal |r|) phi →
    sectionOperatorENorm T ny (fun r : ℝ => ENNReal.ofReal |r|) phi ≤
      (C : ℝ≥0∞) *
        sectionOperatorENorm S nx (fun r : ℝ => ENNReal.ofReal |r|) (phi ∘ A)

/-- A genuine Frechet derivative in the indicated concrete norms: a bounded
linear derivative plus a uniform remainder estimate over every sufficiently
small admissible increment. This is stronger than directional differentiability.
`U` is the actual positive-metric domain and `S` the actual section directions.
The full target uses finite-norm sets for all these arguments. -/
def HasSectionFrechetDerivative (S U : Set X) (T : Set Y)
    (nx : X → ℝ≥0∞) (ny : Y → ℝ≥0∞)
    (F : X → Y) (D : X → Y) (z : X) : Prop :=
  z ∈ U ∧
  Set.MapsTo F U T ∧
  Set.MapsTo D S T ∧
  SectionLinearOn S D ∧
  SectionBoundedOn S nx ny D ∧
  ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
    ∀ h ∈ S, z + h ∈ U → nx h < ENNReal.ofReal delta →
      ny (F (z + h) - F z - D h) ≤ ENNReal.ofReal eps * nx h

end K24.Global


