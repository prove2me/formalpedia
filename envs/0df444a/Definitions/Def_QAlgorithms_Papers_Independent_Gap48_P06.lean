-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P06
-- name    : QAlgorithms_Papers_Independent_Gap48_P06
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T21:04:42.046424+00:00
-- url     : https://prove2.me/theorems/77dfbf7b-d69c-46ec-9151-609028446ac2
-- title:
--   Definitions for Reflection Positive Stochastic Processes Indexed by Lie Groups
-- statement:
--   The objects the formalized statements of *Reflection Positive Stochastic Processes Indexed by Lie Groups* (arXiv:1510.07445) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `dualEvaluationSigma`: Evaluation sigma-algebra on the algebraic real dual, Theorem 5.2, PDF p.32. The printed evaluation codomain V is corrected to R: alpha(v) is a scalar.
--   - `dualFourier`: Fourier transform on the actual algebraic real dual with its evaluation sigma-algebra, PDF p.32. Its uses below require a finite positive measure.
--   - `AdditivePositiveDefinite`: Positive definiteness on the additive real vector space, PDF p.32. The imaginary part vanishes and the real part of each finite quadratic form is nonnegative; coefficients are arbitrary complex numbers.
--   - `FiniteDimensionalContinuous`: Continuity on all finite-dimensional subspaces without imposing a topology on the arbitrary vector space V, PDF p.32. All finite-dimensional linear parametrizations carry their usual Euclidean topology.
--   - `ContinuousInMeasureAt`: Continuity in measure uses ENNReal event measures directly, PDF pp.43--44. No finiteness assumption or conversion of infinite event measure to zero is used.
--   - `NonnegativeAE`: Positivity on real or complex-valued functions means a.e. real nonnegative values. This agrees with the positive cone of L-infinity, PDF pp.8,43.
--   - `CompatiblePositiveSemigroup`: The same positivity-preserving semigroup on L-infinity and L2 of one fixed measure, Lemma A.1, PDF p.43. Compatibility identifies their a.e. values on the intersection. Strong continuity remains a theorem hypothesis.
--   - `pathShift`: The canonical left shift on real-valued path space, Definition 3.11, PDF p.12 and Appendix A, PDF pp.43--44. The sigma-algebra on G -> R is the coordinate-generated product sigma-algebra, regardless of cardinality of G.
--   - `pathKoopman`: Actual Koopman pullback on canonical path L2, using the stationary law; there is no independent representation or auxiliary randomness, PDF pp.43--44.
--   - `RealHilbertTensor`: The real completed Hilbert tensor product, Lemma 5.24, PDF pp.41--42. Mathlib supplies the Hilbert tensor norm before uniform completion; the pinned Claimed50.P34.HilbertTensor is complex and is not this real tensor product.
--   - `realTensorDiagonalAction`: The diagonal orthogonal action on the completed tensor product, PDF p.41. This is the unique uniformly continuous extension of the actual algebraic isometry, not an independently supplied tensor representation. The accepted Renew46.P03.completedTensorAction acts on COMPLEX tensor products and cannot replace this real construction.
--   - `GroupInvariantSubspace`: Invariance under every group element, PDF pp.41--42. The accepted Dependency50.P37.InvariantSubspace instead concerns supported density matrices under a finite-dimensional quantum channel; it is a different source concept.
--   - `NoFiniteSubrepresentations`: Absence of nonzero finite-dimensional invariant subspaces, PDF p.41. The zero Hilbert space and zero-dimensional invariant subspace are allowed.
--   - `finiteInvariantPart`: The finite-dimensional invariant part H_f is a CLOSED linear span, Lemma 5.24 and Remark 5.27, PDF pp.41--42.
--   - `closedTensorSubspace`: Embedded completed tensor of two closed subspaces, PDF pp.41--42. The closed span of elementary tensors is their Hilbert tensor image in the ambient completed tensor, rather than an algebraic tensor subspace.
--   - `actionKoopman`: Koopman pullback for a measure-preserving action, Definition 5.28, PDF p.43. The inverse in the action gives a left representation.
--   - `MeasureWeaklyMixing`: Weak mixing on a finite measure space is absence of nonzero finite- dimensional invariant subspaces in 1-perp, Definition 5.28, PDF p.43. For finite measures, vanishing integral is exactly orthogonality to constants; it also covers zero total mass without division.
--   - `PairActionErgodic`: Ergodicity of the diagonal pair action means its invariant L2 functions are a.e. constants, Proposition 5.29, PDF p.43.
--   - `cumulativeProduct`: Ordered cumulative products, equations (4.1)--(4.2), PDF p.26. List.prod preserves the source's noncommutative multiplication order.
--   - `rightConvolution`: Right convolution of measures is the image under (x,y) -> x*y, PDF pp.25--26. Probability and sigma-finiteness are supplied at its uses.
--   - `convolutionTupleLaw`: The finite distributions of Lemma 4.8, PDF p.30. The initial factor is nu, not mu at the initial time. Only nondecreasing tuples occur in the theorem, so Real.toNNReal never truncates a genuinely negative time increment.
--   - `futureKernelLaw`: Successive transition law from one state, Appendix B, PDF pp.45--47. Every transition is an actual measurable Markov kernel. Fin.cons records the sampled next state before the subsequent states.
--   - `orderedKernelLaw`: Ordered Markov cylinder law with initial marginal nu, Appendix B, PDF pp.46--47. Ordered tuples have nonnegative successive differences.
-- source:
--   Reflection Positive Stochastic Processes Indexed by Lie Groups, arXiv:1510.07445v3, https://arxiv.org/abs/1510.07445v3

import Mathlib

/-!
Draft statements from Jorgensen--Neeb--Olafsson, arXiv:1510.07445v3.
Only nodes with complete local substrate are stated. Other nodes, including the
reviewed nuclearity/Gaussian-realization interface, are explicitly deferred in
this unit's HARD.md and GAPS.json. Compilation awaits the batch handoff.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Gap48.P06

/-- Evaluation sigma-algebra on the algebraic real dual, Theorem 5.2, PDF p.32.
The printed evaluation codomain V is corrected to R: alpha(v) is a scalar. -/
def dualEvaluationSigma (V : Type*) [AddCommGroup V] [Module ℝ V] :
    MeasurableSpace (Module.Dual ℝ V) :=
  ⨆ v : V, MeasurableSpace.comap (fun a : Module.Dual ℝ V => a v) (borel ℝ)

/-- Fourier transform on the actual algebraic real dual with its evaluation
sigma-algebra, PDF p.32. Its uses below require a finite positive measure. -/
def dualFourier {V : Type*} [AddCommGroup V] [Module ℝ V]
    (mu : @Measure (Module.Dual ℝ V) (dualEvaluationSigma V)) (v : V) : ℂ :=
  letI : MeasurableSpace (Module.Dual ℝ V) := dualEvaluationSigma V
  ∫ a, Complex.exp (Complex.I * (a v : ℂ)) ∂mu

/-- Positive definiteness on the additive real vector space, PDF p.32.
The imaginary part vanishes and the real part of each finite quadratic form is
nonnegative; coefficients are arbitrary complex numbers. -/
def AdditivePositiveDefinite {V : Type*} [AddCommGroup V] (chi : V → ℂ) : Prop :=
  ∀ (n : ℕ) (v : Fin n → V) (c : Fin n → ℂ),
    ∃ r : ℝ, 0 ≤ r ∧
      (∑ i, ∑ j, star (c i) * c j * chi (v j - v i)) = (r : ℂ)

/-- Continuity on all finite-dimensional subspaces without imposing a topology
on the arbitrary vector space V, PDF p.32. All finite-dimensional linear
parametrizations carry their usual Euclidean topology. -/
def FiniteDimensionalContinuous {V : Type*} [AddCommGroup V] [Module ℝ V]
    (chi : V → ℂ) : Prop :=
  ∀ (n : ℕ) (a : (Fin n → ℝ) →ₗ[ℝ] V), Continuous (fun x => chi (a x))

/-- Sanity check: the empty quadratic form is zero, not a positivity obstruction. -/
example {V : Type*} [AddCommGroup V] (chi : V → ℂ)
    (v : Fin 0 → V) (c : Fin 0 → ℂ) :
    (∑ i, ∑ j, star (c i) * c j * chi (v j - v i)) = 0 := by
  simp

/-- Sanity check: a zero characteristic function has no negative finite quadratic forms. -/
example {V : Type*} [AddCommGroup V] :
    AdditivePositiveDefinite (fun _ : V => (0 : ℂ)) := by
  intro n v c
  exact ⟨0, le_rfl, by simp⟩

/-- Sanity check: the zero function is continuous on every finite-dimensional slice. -/
example {V : Type*} [AddCommGroup V] [Module ℝ V] :
    FiniteDimensionalContinuous (fun _ : V => (0 : ℂ)) := by
  intro n a
  exact continuous_const

/-- Sanity check: the zero measure has zero Fourier transform, so Theorem 5.2
must allow zero mass and must not demand probability normalization. -/
example {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    dualFourier (0 : @Measure (Module.Dual ℝ V) (dualEvaluationSigma V)) v = 0 := by
  simp [dualFourier]

/-- Continuity in measure uses ENNReal event measures directly, PDF pp.43--44.
No finiteness assumption or conversion of infinite event measure to zero is used. -/
def ContinuousInMeasureAt {S X F : Type*} [TopologicalSpace S]
    [MeasurableSpace X] [NormedAddCommGroup F] (mu : Measure X)
    (f : S → X → F) (s0 : S) : Prop :=
  ∀ eps : ℝ, 0 < eps →
    Tendsto (fun s => mu {x | eps ≤ ‖f s x - f s0 x‖}) (𝓝 s0) (𝓝 0)

/-- Positivity on real or complex-valued functions means a.e. real nonnegative
values. This agrees with the positive cone of L-infinity, PDF pp.8,43. -/
def NonnegativeAE {X K : Type*} [MeasurableSpace X] [RCLike K]
    (mu : Measure X) (f : X → K) : Prop :=
  ∀ᵐ x ∂mu, RCLike.im (f x) = 0 ∧ 0 ≤ RCLike.re (f x)

/-- The same positivity-preserving semigroup on L-infinity and L2 of one fixed
measure, Lemma A.1, PDF p.43. Compatibility identifies their a.e. values on the
intersection. Strong continuity remains a theorem hypothesis. -/
structure CompatiblePositiveSemigroup (S X K : Type*) [Semigroup S]
    [MeasurableSpace X] [RCLike K] (mu : Measure X) where
  onL2 : S → (Lp K 2 mu →L[K] Lp K 2 mu)
  onLinf : S → (Lp K ∞ mu →L[K] Lp K ∞ mu)
  mulL2 : ∀ s t f, onL2 (s * t) f = onL2 s (onL2 t f)
  mulLinf : ∀ s t f, onLinf (s * t) f = onLinf s (onLinf t f)
  positive : ∀ s (f : Lp K ∞ mu),
    NonnegativeAE mu f → NonnegativeAE mu (onLinf s f)
  compatible : ∀ s (f : Lp K 2 mu) (h : Lp K ∞ mu),
    (f : X → K) =ᵐ[mu] h → (onL2 s f : X → K) =ᵐ[mu] onLinf s h

/-- Sanity check: identity operators give a compatible positive semigroup on
any one measure space; compatibility imposes no impossible normalization. -/
example {S X K : Type*} [Semigroup S] [MeasurableSpace X] [RCLike K]
    (mu : Measure X) : Nonempty (CompatiblePositiveSemigroup S X K mu) := by
  exact ⟨{
    onL2 := fun _ => ContinuousLinearMap.id K (Lp K 2 mu)
    onLinf := fun _ => ContinuousLinearMap.id K (Lp K ∞ mu)
    mulL2 := fun _ _ _ => rfl
    mulLinf := fun _ _ _ => rfl
    positive := fun _ _ hf => hf
    compatible := fun _ _ _ hf => hf }⟩

/-- Sanity check: a constant family converges in measure even on an infinite
measure space, because each positive-threshold event is empty. -/
example {S X F : Type*} [TopologicalSpace S] [MeasurableSpace X]
    [NormedAddCommGroup F] (mu : Measure X) (f : X → F) (s0 : S) :
    ContinuousInMeasureAt mu (fun _ => f) s0 := by
  intro eps heps
  simpa [not_le.mpr heps] using
    (tendsto_const_nhds : Tendsto (fun _ : S => (0 : ℝ≥0∞)) (𝓝 s0) (𝓝 0))

/-- The canonical left shift on real-valued path space, Definition 3.11,
PDF p.12 and Appendix A, PDF pp.43--44. The sigma-algebra on G -> R is the
coordinate-generated product sigma-algebra, regardless of cardinality of G. -/
def pathShift {G : Type*} [Group G] (g : G) (w : G → ℝ) (h : G) : ℝ :=
  w (g⁻¹ * h)

/-- Actual Koopman pullback on canonical path L2, using the stationary law;
there is no independent representation or auxiliary randomness, PDF pp.43--44. -/
def pathKoopman {G : Type*} [Group G] (nu : Measure (G → ℝ))
    (hstationary : ∀ g, MeasurePreserving (pathShift g) nu nu)
    (g : G) (f : Lp ℂ 2 nu) : Lp ℂ 2 nu :=
  Lp.compMeasurePreserving (pathShift g⁻¹) (hstationary g⁻¹) f

/-- Sanity check: the identity shift fixes every path, including on the trivial group. -/
example {G : Type*} [Group G] (w : G → ℝ) : pathShift (1 : G) w = w := by
  funext h
  simp [pathShift]

/-- The real completed Hilbert tensor product, Lemma 5.24, PDF pp.41--42.
Mathlib supplies the Hilbert tensor norm before uniform completion; the pinned
Claimed50.P34.HilbertTensor is complex and is not this real tensor product. -/
abbrev RealHilbertTensor (H K : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [NormedAddCommGroup K] [InnerProductSpace ℝ K] :=
  UniformSpace.Completion (TensorProduct ℝ H K)

/-- The diagonal orthogonal action on the completed tensor product, PDF p.41.
This is the unique uniformly continuous extension of the actual algebraic
isometry, not an independently supplied tensor representation. The accepted
Renew46.P03.completedTensorAction acts on COMPLEX tensor products and cannot
replace this real construction. -/
def realTensorDiagonalAction {G H K : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (pi : G →* (H ≃ₗᵢ[ℝ] H)) (rho : G →* (K ≃ₗᵢ[ℝ] K))
    (g : G) : RealHilbertTensor H K → RealHilbertTensor H K :=
  UniformSpace.Completion.map
    (TensorProduct.mapIsometry (pi g).toLinearIsometry (rho g).toLinearIsometry)

/-- Invariance under every group element, PDF pp.41--42. The accepted
Dependency50.P37.InvariantSubspace instead concerns supported density matrices
under a finite-dimensional quantum channel; it is a different source concept. -/
def GroupInvariantSubspace {G H : Type*} [AddCommGroup H] [Module ℝ H]
    (a : G → H → H) (F : Submodule ℝ H) : Prop :=
  ∀ g v, v ∈ F → a g v ∈ F

/-- Absence of nonzero finite-dimensional invariant subspaces, PDF p.41.
The zero Hilbert space and zero-dimensional invariant subspace are allowed. -/
def NoFiniteSubrepresentations {G H : Type*} [AddCommGroup H] [Module ℝ H]
    (a : G → H → H) : Prop :=
  ∀ F : Submodule ℝ H, FiniteDimensional ℝ F → GroupInvariantSubspace a F → F = ⊥

/-- The finite-dimensional invariant part H_f is a CLOSED linear span,
Lemma 5.24 and Remark 5.27, PDF pp.41--42. -/
def finiteInvariantPart {G H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (a : G → H → H) : Submodule ℝ H :=
  (Submodule.span ℝ {v | ∃ F : Submodule ℝ H,
    FiniteDimensional ℝ F ∧ GroupInvariantSubspace a F ∧ v ∈ F}).topologicalClosure

/-- Embedded completed tensor of two closed subspaces, PDF pp.41--42.
The closed span of elementary tensors is their Hilbert tensor image in the
ambient completed tensor, rather than an algebraic tensor subspace. -/
def closedTensorSubspace {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (F : Submodule ℝ H) (E : Submodule ℝ K) : Submodule ℝ (RealHilbertTensor H K) :=
  (Submodule.span ℝ {z | ∃ x ∈ F, ∃ y ∈ E,
    z = ((TensorProduct.tmul ℝ x y : TensorProduct ℝ H K) : RealHilbertTensor H K)}).topologicalClosure

/-- Sanity check: the zero factor stays zero after Hilbert completion. -/
example {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] (y : K) :
    ((TensorProduct.tmul ℝ (0 : H) y : TensorProduct ℝ H K) : RealHilbertTensor H K) = 0 := by
  simp

/-- Koopman pullback for a measure-preserving action, Definition 5.28,
PDF p.43. The inverse in the action gives a left representation. -/
def actionKoopman {G X : Type*} [Group G] [MeasurableSpace X]
    (mu : Measure X) (a : G → X → X)
    (hpres : ∀ g, MeasurePreserving (a g) mu mu)
    (g : G) (f : Lp ℂ 2 mu) : Lp ℂ 2 mu :=
  Lp.compMeasurePreserving (a g⁻¹) (hpres g⁻¹) f

/-- Weak mixing on a finite measure space is absence of nonzero finite-
dimensional invariant subspaces in 1-perp, Definition 5.28, PDF p.43.
For finite measures, vanishing integral is exactly orthogonality to constants;
it also covers zero total mass without division. -/
def MeasureWeaklyMixing {G X : Type*} [Group G] [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (a : G → X → X)
    (hpres : ∀ g, MeasurePreserving (a g) mu mu) : Prop :=
  ∀ F : Submodule ℂ (Lp ℂ 2 mu), FiniteDimensional ℂ F →
    (∀ f ∈ F, (∫ x, f x ∂mu) = 0) →
    (∀ g f, f ∈ F → actionKoopman mu a hpres g f ∈ F) → F = ⊥

/-- Ergodicity of the diagonal pair action means its invariant L2 functions
are a.e. constants, Proposition 5.29, PDF p.43. -/
def PairActionErgodic {G X : Type*} [Group G] [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (a : G → X → X)
    (hpres : ∀ g, MeasurePreserving (a g) mu mu) : Prop :=
  ∀ f : Lp ℂ 2 (mu.prod mu),
    (∀ g, Lp.compMeasurePreserving (Prod.map (a g⁻¹) (a g⁻¹))
      ((hpres g⁻¹).prod (hpres g⁻¹)) f = f) →
    ∃ c : ℂ, ∀ᵐ x ∂mu.prod mu, f x = c

/-- Sanity check: Koopman pullback takes the zero L2 vector to zero. -/
example {G X : Type*} [Group G] [MeasurableSpace X]
    (mu : Measure X) (a : G → X → X)
    (hpres : ∀ g, MeasurePreserving (a g) mu mu) (g : G) :
    actionKoopman mu a hpres g 0 = 0 := by
  exact map_zero (Lp.compMeasurePreserving (a g⁻¹) (hpres g⁻¹))

/-- Ordered cumulative products, equations (4.1)--(4.2), PDF p.26.
List.prod preserves the source's noncommutative multiplication order. -/
def cumulativeProduct {Q : Type*} [Group Q] {n : ℕ} (x : Fin n → Q)
    (i : Fin n) : Q :=
  ((List.ofFn x).take (i.val + 1)).prod

/-- Right convolution of measures is the image under (x,y) -> x*y,
PDF pp.25--26. Probability and sigma-finiteness are supplied at its uses. -/
def rightConvolution {Q : Type*} [Group Q] [MeasurableSpace Q]
    (nu mu : Measure Q) : Measure Q :=
  Measure.map (fun z : Q × Q => z.1 * z.2) (nu.prod mu)

/-- The finite distributions of Lemma 4.8, PDF p.30. The initial factor is nu,
not mu at the initial time. Only nondecreasing tuples occur in the theorem,
so Real.toNNReal never truncates a genuinely negative time increment. -/
def convolutionTupleLaw {Q : Type*} [Group Q] [MeasurableSpace Q]
    (nu : Measure Q) (mu : ℝ≥0 → Measure Q) (n : ℕ) (t : Fin (n + 1) → ℝ) :
    Measure (Fin (n + 1) → Q) :=
  Measure.map cumulativeProduct
    (Measure.pi (Fin.cons nu (fun i : Fin n =>
      mu (Real.toNNReal (t i.succ - t i.castSucc)))))

/-- Sanity check: the one-coordinate cumulative product is the starting point. -/
example {Q : Type*} [Group Q] (x : Q) :
    cumulativeProduct (fun _ : Fin 1 => x) 0 = x := by
  simp [cumulativeProduct]

/-- Successive transition law from one state, Appendix B, PDF pp.45--47.
Every transition is an actual measurable Markov kernel. Fin.cons records the
sampled next state before the subsequent states. -/
def futureKernelLaw {Q : Type*} [MeasurableSpace Q]
    (P : ℝ≥0 → Kernel Q Q) :
    (n : ℕ) → (Fin n → ℝ≥0) → Q → Measure (Fin n → Q)
  | 0, _, _ => Measure.dirac Fin.elim0
  | n + 1, d, x => (P (d 0) x).bind (fun y =>
      Measure.map (Fin.cons y) (futureKernelLaw P n (fun i => d i.succ) y))

/-- Ordered Markov cylinder law with initial marginal nu, Appendix B,
PDF pp.46--47. Ordered tuples have nonnegative successive differences. -/
def orderedKernelLaw {Q : Type*} [MeasurableSpace Q]
    (nu : Measure Q) (P : ℝ≥0 → Kernel Q Q) (n : ℕ) (t : Fin (n + 1) → ℝ) :
    Measure (Fin (n + 1) → Q) :=
  nu.bind (fun x => Measure.map (Fin.cons x)
    (futureKernelLaw P n
      (fun i => Real.toNNReal (t i.succ - t i.castSucc)) x))

/-- Sanity check: no transitions gives the unit point mass on the empty tuple. -/
example {Q : Type*} [MeasurableSpace Q] (P : ℝ≥0 → Kernel Q Q)
    (d : Fin 0 → ℝ≥0) (x : Q) :
    futureKernelLaw P 0 d x = Measure.dirac Fin.elim0 := rfl

end QAlgorithms.Papers.Independent.Gap48.P06


