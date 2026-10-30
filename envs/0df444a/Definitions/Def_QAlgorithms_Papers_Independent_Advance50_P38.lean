-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
-- name    : QAlgorithms_Papers_Independent_Advance50_P38
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T08:43:39.33914+00:00
-- url     : https://prove2.me/theorems/a9ece3ab-d2b9-4225-bf1a-33c6048868ac
-- title:
--   Definitions for Gradient Flows for Optimisation and Quantum Control: Foundations and Applications
-- statement:
--   The objects the formalized statements of *Gradient Flows for Optimisation and Quantum Control: Foundations and Applications* (arXiv:0802.4195) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `realHSPairing`: Real Hilbert--Schmidt pairing (123), PDF p.22.
--   - `frobSq`: Squared Frobenius norm, never the default matrix norm.
--   - `comm`: The source's commutator.
--   - `skew`: Skew-Hermitian part, including 1/2.
--   - `IsSpecialSkew`: Special skew-Hermitian matrices include trace zero (101).
--   - `realTraceOverlap`: Real overlap (115), for arbitrary complex A,C.
--   - `vInner`: Inner product (176), conjugate-linear in its first argument.
--   - `rankOneMatrix`: Rank-one operator xx dagger.
--   - `pureStateTransfer`: Pure transfer (169); normalization is imposed only where the source does.
--   - `IsHSProjection`: Universal property of the real orthogonal projection.
--   - `hsOrthogonal`: Orthogonal complement for the given real pairing.
--   - `matrixCarrier`: Ambient matrix image of a subgroup of GL(n,C).
--   - `matrixLieSet`: Actual real Lie algebra via its one-parameter subgroups; H is closed at use.
--   - `basisProjection`: Real orthonormal-basis expression (124).
--   - `skewPauli`: The skew-Hermitian generators (111), not Hermitian Pauli matrices.
--   - `LocalQubitIndex`
--   - `localGenerator`: Generator in tensor position k, (112).
--   - `localAlgebra`: Real local algebra (121).
--   - `localProjection`: Formula (127), including denominator 2^n.
--   - `numericalRadius`: Radius (100); attainment is part of the statement below.
--   - `ComplexCollinear`: Complex collinearity means dependence, allowing either matrix to vanish.
--   - `lineCosSq`: Squared cosine between complex lines (114), used only for nonzero A,C.
--   - `IsSUGradient`: Gradient defined by (106) with right-trivialized metric (103), using actual derivatives along exp(t Omega)U rather than an assumed formula.
--   - `unitaryGradientField`: Ascent field (108).
--   - `unitaryAscentStep`: Step (109), with C dagger as fixed by (104)--(108) and Table II U1.
--   - `colVec`: Column vectorization (172), with column coordinate first.
--   - `rectangularSigma`: Rectangular diagonal matrix of singular values.
--   - `FullSVD`: Full SVD with nonnegative decreasing singular values, PDF p.27.
--   - `svdOptimizer`: Sufficient determinant-one optimizer (171).
--   - `cSpectralSq`: Squared C-spectral norm, Corollary IV.1, PDF p.27.
--   - `ArrayIndex`: Lexicographic array indexing (179), with factors in their stated order.
--   - `tensorProduct`: Outer product (177).
--   - `tensorUnitary`: Tensor product of actual SU factors (174).
--   - `unitTensorFactors`: Unit Euclidean norm of each factor, not the Pi sup norm.
--   - `tensorSeed`: Product of the first basis vectors, (180).
--   - `pureProductProjectors`: Pure product states as projectors, (167).
--   - `centralizerAlgebra`: Centralizer algebra (197), in u(N) with no trace-zero restriction.
--   - `centralizerMatrix`: Homogeneous linear system (199), in column vectorization order.
--   - `IsBoundedQuadratic`: Bounded quadratic form means the diagonal of a bounded symmetric real bilinear form, exactly (202), PDF p.35.
--   - `orbitEulerStep`: Standard Euler update (156), PDF p.25.
--   - `IsSmoothHilbertEmbedding`: A finite-dimensional manifold smoothly embedded in a real Hilbert space. The topology is the induced topology and the differential is injective. These are conditions on the actual map, not an arbitrary tangent-space label.
--   - `embeddedRestriction`: The restriction of an ambient map through its two embeddings. Membership of the image supplies existence; embedding injectivity supplies uniqueness.
--   - `metricRepresentative`: Metric dual representative; the fallback is used only outside the nondegenerate finite-dimensional metrics appearing in the theorems.
--   - `riemannianGradient`: Riemannian gradient (33) constructed from the actual smooth positive metric and the manifold differential, not supplied as unrelated field data.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, https://arxiv.org/abs/0802.4195v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Information

/-! Statements from arXiv:0802.4195v2. All added definitions are paper-local.
Orthogonality of complex matrices is real. Frobenius norms are explicit. -/

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Real Hilbert--Schmidt pairing (123), PDF p.22. -/
def realHSPairing {ι κ : Type*} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℂ) : ℝ :=
  (Matrix.trace (A.conjTranspose * B)).re

/-- Squared Frobenius norm, never the default matrix norm. -/
def frobSq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- The source's commutator. -/
def comm {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) := A * B - B * A

/-- Skew-Hermitian part, including 1/2. -/
def skew {ι : Type*} (A : Matrix ι ι ℂ) := (2 : ℂ)⁻¹ • (A - A.conjTranspose)

/-- Special skew-Hermitian matrices include trace zero (101). -/
def IsSpecialSkew {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : Prop :=
  A.conjTranspose = -A ∧ Matrix.trace A = 0

/-- Real overlap (115), for arbitrary complex A,C. -/
def realTraceOverlap {ι : Type*} [Fintype ι] (A C U : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (C.conjTranspose * (U * A * U.conjTranspose))).re

/-- Inner product (176), conjugate-linear in its first argument. -/
def vInner {ι : Type*} [Fintype ι] (x y : ι → ℂ) : ℂ := ∑ i, star (x i) * y i

/-- Rank-one operator xx dagger. -/
def rankOneMatrix {ι : Type*} (x : ι → ℂ) : Matrix ι ι ℂ :=
  QAlgorithms.pureDensity (WithLp.toLp 2 x)

/-- Pure transfer (169); normalization is imposed only where the source does. -/
def pureStateTransfer {ι : Type*} [Fintype ι] (x y : ι → ℂ) (U : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (rankOneMatrix x * U * rankOneMatrix y * U.conjTranspose)).re

/-- Universal property of the real orthogonal projection. -/
def IsHSProjection {ι : Type*} [Fintype ι] (S : Set (Matrix ι ι ℂ))
    (g p : Matrix ι ι ℂ) : Prop := p ∈ S ∧ ∀ h ∈ S, realHSPairing (g - p) h = 0

/-- Orthogonal complement for the given real pairing. -/
def hsOrthogonal {ι : Type*} [Fintype ι] (S : Set (Matrix ι ι ℂ)) :
    Set (Matrix ι ι ℂ) := {g | ∀ h ∈ S, realHSPairing g h = 0}

/-- Ambient matrix image of a subgroup of GL(n,C). -/
def matrixCarrier {n : ℕ} (H : Subgroup ((Matrix (Fin n) (Fin n) ℂ))ˣ) : Set ((Matrix (Fin n) (Fin n) ℂ)) :=
  {A | ∃ u : ((Matrix (Fin n) (Fin n) ℂ))ˣ, u ∈ H ∧ (u : (Matrix (Fin n) (Fin n) ℂ)) = A}

/-- Actual real Lie algebra via its one-parameter subgroups; H is closed at use. -/
def matrixLieSet {n : ℕ} (H : Subgroup ((Matrix (Fin n) (Fin n) ℂ))ˣ) : Set ((Matrix (Fin n) (Fin n) ℂ)) :=
  {A | ∀ t : ℝ, NormedSpace.exp (t • A) ∈ matrixCarrier H}

/-- Real orthonormal-basis expression (124). -/
def basisProjection {n m : ℕ} (b : Fin m → (Matrix (Fin n) (Fin n) ℂ)) (g : (Matrix (Fin n) (Fin n) ℂ)) : (Matrix (Fin n) (Fin n) ℂ) :=
  ∑ j, realHSPairing (b j) g • b j

example {n : ℕ} (g : (Matrix (Fin n) (Fin n) ℂ)) : basisProjection (fun j : Fin 0 => Fin.elim0 j) g = 0 := by
  simp [basisProjection]

example {ι κ : Type*} [Fintype ι] [Fintype κ] : frobSq (0 : Matrix ι κ ℂ) = 0 := by
  simp [frobSq]

/-- The skew-Hermitian generators (111), not Hermitian Pauli matrices. -/
def skewPauli (a : Fin 3) : (Matrix (Fin 2) (Fin 2) ℂ) :=
  if a = 0 then Complex.I • (fun i j =>
    QAlgorithms.pauliX (decide (i.val = 1)) (decide (j.val = 1)))
  else if a = 1 then (-Complex.I) • (fun i j =>
    QAlgorithms.pauliY (decide (i.val = 1)) (decide (j.val = 1)))
  else Complex.I • (fun i j =>
    QAlgorithms.pauliZ (decide (i.val = 1)) (decide (j.val = 1)))

abbrev LocalQubitIndex (n : ℕ) := Fin n → Fin 2

/-- Generator in tensor position k, (112). -/
def localGenerator {n : ℕ} (k : Fin n) (a : Fin 3) : Matrix (LocalQubitIndex n) (LocalQubitIndex n) ℂ :=
  fun i j => ∏ l, if l = k then skewPauli a (i l) (j l) else if i l = j l then 1 else 0

/-- Real local algebra (121). -/
def localAlgebra (n : ℕ) : Submodule ℝ (Matrix (LocalQubitIndex n) (LocalQubitIndex n) ℂ) :=
  Submodule.span ℝ (Set.range (fun ka : Fin n × Fin 3 => localGenerator ka.1 ka.2))

/-- Formula (127), including denominator 2^n. -/
def localProjection {n : ℕ} (g : Matrix (LocalQubitIndex n) (LocalQubitIndex n) ℂ) :=
  ((2 : ℝ) ^ n)⁻¹ • ∑ k : Fin n, ∑ a : Fin 3, realHSPairing g (localGenerator k a) • localGenerator k a

example : skewPauli 1 0 1 = -1 := by
  change (-Complex.I) * (-Complex.I) = -1
  simp

example : skewPauli 0 0 1 = Complex.I := by
  change Complex.I * 1 = Complex.I
  simp

/-- Radius (100); attainment is part of the statement below. -/
def numericalRadius {n : ℕ} (A C : (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  sSup {r | ∃ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
    r = ‖Matrix.trace (C.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose))‖}

/-- Complex collinearity means dependence, allowing either matrix to vanish. -/
def ComplexCollinear {n : ℕ} (A C : (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ a • A + b • C = 0

/-- Squared cosine between complex lines (114), used only for nonzero A,C. -/
def lineCosSq {n : ℕ} (A C U : (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  Complex.normSq (Matrix.trace (C.conjTranspose * (U * A * U.conjTranspose))) /
    (frobSq A * frobSq C)

/-- Gradient defined by (106) with right-trivialized metric (103), using
actual derivatives along exp(t Omega)U rather than an assumed formula. -/
def IsSUGradient {n : ℕ} (A C U V : (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  ∃ K : (Matrix (Fin n) (Fin n) ℂ), IsSpecialSkew K ∧ V = K * U ∧
    ∀ Omega : (Matrix (Fin n) (Fin n) ℂ), IsSpecialSkew Omega →
      HasDerivAt (fun t : ℝ => realTraceOverlap A C (NormedSpace.exp (t • Omega) * U)) (realHSPairing K Omega) 0

/-- Ascent field (108). -/
def unitaryGradientField {n : ℕ} (A C U : (Matrix (Fin n) (Fin n) ℂ)) : (Matrix (Fin n) (Fin n) ℂ) :=
  -skew (comm (U * A * U.conjTranspose) C.conjTranspose) * U

/-- Step (109), with C dagger as fixed by (104)--(108) and Table II U1. -/
def unitaryAscentStep {n : ℕ} (A C U : (Matrix (Fin n) (Fin n) ℂ)) (a : ℝ) : (Matrix (Fin n) (Fin n) ℂ) :=
  NormedSpace.exp (a • (-skew (comm (U * A * U.conjTranspose) C.conjTranspose))) * U

/-- Column vectorization (172), with column coordinate first. -/
def colVec {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℂ) : Fin b × Fin a → ℂ :=
  fun ji => X ji.2 ji.1

/-- Rectangular diagonal matrix of singular values. -/
def rectangularSigma {a b : ℕ} (s : Fin (min a b) → ℝ) : Matrix (Fin a) (Fin b) ℂ :=
  fun i j => if h : i.val < min a b then
    if i.val = j.val then (s ⟨i.val, h⟩ : ℂ) else 0 else 0

/-- Full SVD with nonnegative decreasing singular values, PDF p.27. -/
structure FullSVD {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℂ) where
  V : Matrix.unitaryGroup (Fin a) ℂ
  W : Matrix.unitaryGroup (Fin b) ℂ
  singularValues : Fin (min a b) → ℝ
  nonneg : ∀ i, 0 ≤ singularValues i
  sorted : Antitone singularValues
  reconstruction : X = (V : (Matrix (Fin a) (Fin a) ℂ)) * rectangularSigma singularValues * (W : (Matrix (Fin b) (Fin b) ℂ)).conjTranspose

/-- Sufficient determinant-one optimizer (171). -/
def svdOptimizer {a b : ℕ} {X Y : Matrix (Fin a) (Fin b) ℂ}
    (sx : FullSVD X) (sy : FullSVD Y) : Matrix (Fin b × Fin a) (Fin b × Fin a) ℂ :=
  Matrix.kronecker ((sx.W : (Matrix (Fin b) (Fin b) ℂ)).map star) (sx.V : (Matrix (Fin a) (Fin a) ℂ)) *
    Matrix.kronecker (sy.W : (Matrix (Fin b) (Fin b) ℂ)).transpose (sy.V : (Matrix (Fin a) (Fin a) ℂ)).conjTranspose

example : colVec (!![(1 : ℂ), 2; 3, 4]) (0, 1) = 3 := by rfl

/-- Squared C-spectral norm, Corollary IV.1, PDF p.27. -/
def cSpectralSq {a b : ℕ} (A C : Matrix (Fin a) (Fin b) ℂ) : ℝ :=
  sSup {r | ∃ V : Matrix.unitaryGroup (Fin a) ℂ,
    ∃ W : Matrix.unitaryGroup (Fin b) ℂ,
      r = Complex.normSq (Matrix.trace (C.conjTranspose * (V : (Matrix (Fin a) (Fin a) ℂ)) * A * (W : (Matrix (Fin b) (Fin b) ℂ)).conjTranspose))}

/-- Lexicographic array indexing (179), with factors in their stated order. -/
abbrev ArrayIndex {r : ℕ} (d : Fin r → ℕ) := (k : Fin r) → Fin (d k)

/-- Outer product (177). -/
def tensorProduct {r : ℕ} {d : Fin r → ℕ} (z : (k : Fin r) → Fin (d k) → ℂ) :
    ArrayIndex d → ℂ := fun i => ∏ k, z k (i k)

/-- Tensor product of actual SU factors (174). -/
def tensorUnitary {r : ℕ} {d : Fin r → ℕ}
    (U : (k : Fin r) → Matrix.specialUnitaryGroup (Fin (d k)) ℂ) :
    Matrix (ArrayIndex d) (ArrayIndex d) ℂ := fun i j => ∏ k, (U k : (Matrix (Fin (d k)) (Fin (d k)) ℂ)) (i k) (j k)

/-- Unit Euclidean norm of each factor, not the Pi sup norm. -/
def unitTensorFactors {r : ℕ} {d : Fin r → ℕ} (z : (k : Fin r) → Fin (d k) → ℂ) : Prop :=
  ∀ k, ∑ j, Complex.normSq (z k j) = 1

/-- Product of the first basis vectors, (180). -/
def tensorSeed {r : ℕ} (d : Fin r → ℕ) : ArrayIndex d → ℂ :=
  fun i => if ∀ k, (i k).val = 0 then 1 else 0

/-- Pure product states as projectors, (167). -/
def pureProductProjectors {r : ℕ} (d : Fin r → ℕ) :
    Set (Matrix (ArrayIndex d) (ArrayIndex d) ℂ) :=
  {P | ∃ z : (k : Fin r) → Fin (d k) → ℂ, unitTensorFactors z ∧ P = rankOneMatrix (tensorProduct z)}

example : tensorProduct (d := fun _ : Fin 0 => 2) (fun k => Fin.elim0 k) = fun _ => 1 := by
  funext i
  simp [tensorProduct]

/-- Centralizer algebra (197), in u(N) with no trace-zero restriction. -/
def centralizerAlgebra {n : ℕ} (E : (Matrix (Fin n) (Fin n) ℂ)) : Set ((Matrix (Fin n) (Fin n) ℂ)) :=
  {K | K.conjTranspose = -K ∧ comm K E = 0}

/-- Homogeneous linear system (199), in column vectorization order. -/
def centralizerMatrix {n : ℕ} (E : (Matrix (Fin n) (Fin n) ℂ)) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  Matrix.kronecker (1 : (Matrix (Fin n) (Fin n) ℂ)) E - Matrix.kronecker E.transpose (1 : (Matrix (Fin n) (Fin n) ℂ))

/-- Bounded quadratic form means the diagonal of a bounded symmetric
real bilinear form, exactly (202), PDF p.35. -/
def IsBoundedQuadratic {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (beta : H → ℝ) : Prop :=
  ∃ B : H →L[ℝ] H →L[ℝ] ℝ, (∀ v w, B v w = B w v) ∧ ∀ v, beta v = B v v

example {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    IsBoundedQuadratic (fun _ : H => 0) := by
  exact ⟨0, fun _ _ => rfl, fun _ => rfl⟩

/-- Standard Euler update (156), PDF p.25. -/
def orbitEulerStep {n : ℕ} (X C : (Matrix (Fin n) (Fin n) ℂ)) (a : ℝ) : (Matrix (Fin n) (Fin n) ℂ) :=
  X + a • comm X (skew (comm X C.conjTranspose))

/-- A finite-dimensional manifold smoothly embedded in a real Hilbert space.
The topology is the induced topology and the differential is injective.
These are conditions on the actual map, not an arbitrary tangent-space label. -/
def IsSmoothHilbertEmbedding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (i : M → H) : Prop :=
  ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ i ∧ Function.Injective i ∧
    (∀ s : Set M, IsOpen s ↔ ∃ t : Set H, IsOpen t ∧ s = i ⁻¹' t) ∧
    ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) i x)

/-- The restriction of an ambient map through its two embeddings. Membership
of the image supplies existence; embedding injectivity supplies uniqueness. -/
def embeddedRestriction {M N H Hprime : Type*} (i : M → H) (j : N → Hprime)
    (F : H → Hprime) (hF : ∀ x, ∃ y, j y = F (i x)) : M → N :=
  fun x => Classical.choose (hF x)

example {M H : Type*} (i : M → H) (x : M) :
    embeddedRestriction i id id (fun x => ⟨i x, rfl⟩) x = i x := by
  exact Classical.choose_spec (show ∃ y, id y = id (i x) from ⟨i x, rfl⟩)

/-- Metric dual representative; the fallback is used only outside the
nondegenerate finite-dimensional metrics appearing in the theorems. -/
def metricRepresentative {V : Type*} [Zero V] (g : V → V → ℝ) (L : V → ℝ) : V := by
  classical
  exact if h : ∃ v, ∀ w, g v w = L w then Classical.choose h else 0

example {V : Type*} [Zero V] [Subsingleton V] (g : V → V → ℝ) (L : V → ℝ) :
    metricRepresentative g L = 0 := by
  exact Subsingleton.elim _ _

/-- Riemannian gradient (33) constructed from the actual smooth positive
metric and the manifold differential, not supplied as unrelated field data. -/
def riemannianGradient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M => TangentSpace 𝓘(ℝ, E) x)) (f : M → ℝ) (x : M) :
    TangentSpace 𝓘(ℝ, E) x :=
  metricRepresentative (fun v w => g.inner x v w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)

/-- Sanity examples for the elementary local definitions. These pin zero,
empty-product, scalar-field and sign conventions; they are not theorem proofs. -/

example {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : comm A A = 0 := by
  simp [comm]

example {n : ℕ} : skew (0 : (Matrix (Fin n) (Fin n) ℂ)) = 0 := by
  simp [skew]

example {n : ℕ} : IsSpecialSkew (0 : (Matrix (Fin n) (Fin n) ℂ)) := by
  simp [IsSpecialSkew]

example {n : ℕ} (C U : (Matrix (Fin n) (Fin n) ℂ)) : realTraceOverlap 0 C U = 0 := by
  simp [realTraceOverlap]

example : vInner (fun _ : Fin 1 => (1 : ℂ)) (fun _ => 1) = 1 := by
  simp [vInner]

example : rankOneMatrix (fun _ : Fin 1 => (1 : ℂ)) 0 0 = 1 := by
  simp [rankOneMatrix, QAlgorithms.pureDensity]

example {n : ℕ} (y : Fin n → ℂ) (U : (Matrix (Fin n) (Fin n) ℂ)) : pureStateTransfer 0 y U = 0 := by
  have hzero : rankOneMatrix (0 : Fin n → ℂ) = 0 := by
    ext i j
    simp [rankOneMatrix, QAlgorithms.pureDensity]
  simp [pureStateTransfer, hzero]

example {n : ℕ} (H : Subgroup ((Matrix (Fin n) (Fin n) ℂ))ˣ) : (1 : (Matrix (Fin n) (Fin n) ℂ)) ∈ matrixCarrier H := by
  exact ⟨1, H.one_mem, rfl⟩

example {n : ℕ} : hsOrthogonal (∅ : Set ((Matrix (Fin n) (Fin n) ℂ))) = Set.univ := by
  ext x
  simp [hsOrthogonal]

example (g : Matrix (LocalQubitIndex 0) (LocalQubitIndex 0) ℂ) : localProjection g = 0 := by
  simp [localProjection]

example {a b : ℕ} : rectangularSigma (a := a) (b := b) (fun _ => 0) = 0 := by
  ext i j
  simp [rectangularSigma]

example : unitTensorFactors (d := fun _ : Fin 0 => 2) (fun k => Fin.elim0 k) := by
  intro k
  exact Fin.elim0 k

example {n : ℕ} (E : (Matrix (Fin n) (Fin n) ℂ)) : (0 : (Matrix (Fin n) (Fin n) ℂ)) ∈ centralizerAlgebra E := by
  simp [centralizerAlgebra, comm]

example {n : ℕ} (X C : (Matrix (Fin n) (Fin n) ℂ)) : orbitEulerStep X C 0 = X := by
  simp [orbitEulerStep]

end

end QAlgorithms.Papers.Independent.Advance50.P38


