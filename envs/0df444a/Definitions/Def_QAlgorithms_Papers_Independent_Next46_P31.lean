-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P31
-- name    : QAlgorithms_Papers_Independent_Next46_P31
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:22:07.917773+00:00
-- url     : https://prove2.me/theorems/29c29f23-74fd-4f4c-b8a9-993323fc26dc
-- title:
--   Definitions for Decoherence rates for Galilean covariant dynamics
-- statement:
--   The objects the formalized statements of *Decoherence rates for Galilean covariant dynamics* (arXiv:0710.1344) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ObservableGraph`: PDF p.8: an unbounded observable is represented by its actual operator graph.
--   - `observableGraph`: PDF p.8: the graph of the accepted densely defined self-adjoint observable.
--   - `ProductForm`: PDF p.8: P realizes A rho by the bounded form <A u,rho f>=<u,P f>. There is no application of an unbounded operator outside its domain.
--   - `RegularProduct`: PDF p.8: exactly the source's trace-class coordinate-product regularity.
--   - `observableProduct`: PDF p.8: the unique bounded realization, whenever the source domain holds. For a dense self-adjoint graph all witnesses have the same action.
--   - `IsHilbertSchmidt`: PDF pp.8,23: Hilbert–Schmidt membership in any complete Hilbert basis.
--   - `hsSize`: PDF pp.8,23: HS size on its finite domain. Trace-class inputs and their coordinate products are HS. Alternative indices explicitly guard this domain.
--   - `observableMean`: PDF p.8: expectation of the original density, not of its square root.
--   - `observableCommutator`: PDF p.8, (2.1): [A,rho] on its bounded realization.
--   - `centeredAnticommutator`: PDF p.8, (2.2): {A-Tr(A rho),rho}, including both centering terms.
--   - `coherenceLength`: PDF p.8, (2.1): normalized commutator length for the entire finite family.
--   - `coherenceSpread`: PDF p.8, (2.2): normalized centered anticommutator spread.
--   - `coherenceIndex`: PDF p.9, Definition 2.1: the index is used only where its spread is nonzero.
--   - `positiveSquareRoot`: PDF p.4: positive square root by continuous functional calculus.
--   - `RootRegular`: PDF p.4: finite second-moment domain for a square-root-state expression. Only HS, rather than trace-class, products of A with sqrt(rho) are required.
--   - `observableVariance`: PDF p.4: Tr(rho |A-Tr(A rho)|^2), expressed by its finite HS form.
--   - `alternativeNumerator`: PDF p.4: the proposed alternative numerator, without a rho HS normalization.
--   - `alternativeDenominator`: PDF p.4: preserve the printed factor 2 outside the square root.
--   - `EuclideanSchrodinger`: PDF p.8: Euclidean-coordinate Schrödinger L2. The accepted Cartesian Schrodinger uses Fin d -> R; its measure is on a different Lean type.
--   - `PhasePoint`: PDF p.8: actual phase points (q,p) or (x,k), rather than the accepted Phase alias, which is the coordinate index Fin d ⊕ Fin d.
--   - `weylAction`: Appendix A, PDF p.21: explicit Schrödinger action fixed by (A.1)–(A.2).
--   - `schrodingerWeyl`: Appendix A, PDF p.21: the bounded Weyl operator is specified on every L2 vector almost everywhere. Translation and a modulus-one multiplier determine an existing unique isometry; no Weyl product or trace isometry is assumed.
--   - `schrodingerCharacteristic`: PDF pp.8,21: phi_T=Tr(W T) for every trace-class operator T.
--   - `positionGraph`: PDF pp.1,8: canonical position as the maximal multiplication graph on L2.
--   - `momentumGraph`: PDF pp.8,21: canonical momentum is the generator of the actual translation subgroup. Its full strong-generator domain is used, with no finite cutoff.
--   - `CanonicallyRegular`: PDF pp.8,15,18: every canonical coordinate product is trace class.
--   - `positionMean`: PDF p.3: the vector of position expectations.
--   - `phaseShear`: PDF p.8, (1.19): volume-preserving free shear, with the specified plus sign.
--   - `phaseCoordinates`: PDF p.2: covariance coordinates in the source's (q,p) block order.
--   - `noiseQuadratic`: PDF p.8, (1.19): the real Gaussian quadratic form, not an operator norm.
--   - `jumpExponent`: PDF p.8, (1.20): symmetric jump exponent paired as q.k+p.x.
--   - `FiniteVarianceLevyNoise`: PDF pp.2,7–8,18: the full finite-second-moment Lévy domain. Infinite total mass is permitted; zero mass at the origin is the Lévy convention on R^(2d)\{0}.
--   - `characteristicEvolution`: PDF p.8, (1.19): the explicit multiplier/shear action on functions. No L2 membership, contraction, positivity, or semigroup law is assumed here.
--   - `CharacteristicDynamics`: PDF pp.8,11,13: (1.19) pins the dynamics on every trace-class input. With admissible noise this uniquely specifies the source's trace-preserving quantum dynamical semigroup; no asymptotic or derivative formulas are fields.
--   - `positionBlock`: PDF p.2: q,q block, denoted A_xx in the source.
--   - `momentumMoment`: PDF pp.2,18–19: explicit momentum second moment M, avoiding the source's inconsistent B-block labels: M_ij = integral k_i k_j dmu(x,k).
--   - `OnlyMomentumGaussian`: PDF p.15: only the A_xx block can be nonzero.
--   - `MomentumNoiseRegime`: PDF pp.18–20, Theorem 4.3(1): momentum-only noise, including both nonzero absolutely-continuous jump noise and positive-definite Gaussian noise.
--   - `FullNoiseRegime`: PDF pp.18–19, Theorem 4.3(3): full nondegenerate Gaussian or jump noise.
--   - `leadingCoefficient`: PDF pp.2,15: exact leading constant, including sqrt(3) and the inverse.
--   - `characteristicMeasure`: PDF p.23: the explicit weighted Lebesgue measure (2 pi)^(-d) dq dp.
--   - `RepresentsKernel`: PDF p.3: actual HS integral kernel, specified by all L2 matrix elements. The paired integrand is integrable for every pair of L2 test vectors by Cauchy–Schwarz.
--   - `kernelOperator`: PDF pp.3–4,9: the actual operator selected by a specified square-integrable kernel when it exists. All uses are Gaussian or finite rank kernels.
--   - `gaussianKernel`: PDF pp.4,9: the normalized one-dimensional Gaussian kernel. E^2/(4C) is constructed, not an independent parameter. R^1 is identified with R.
--   - `rareEndpoint`: PDF p.9: interval endpoint a_m=(6/pi^2) sum_{r=1}^m r^(-2), a_0=0.
--   - `rareVector`: PDF p.9: normalized indicator of [a_(m-1),a_m), for m>=1.
--   - `rareWeight`: PDF p.9: actual mixture weights; the first probability is 1/n, not 1/n^2.
--   - `rareKernel`: PDF p.9: the finite-rank mixture with all the prescribed components.
--   - `rareCoefficient`: PDF p.9: the final ratio's leading constant, evaluated on the first interval. Its mean is a_1/2, variance a_1^2/12, and centered squared distance to 1 is variance+(a_1/2-1)^2. Thus the denominator contains twice the latter square.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, https://arxiv.org/abs/0710.1344v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_PeriodicSchrodingerGeometry
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P22

/-!
arXiv:0710.1344v2, Jeremy Clark, Decoherence Rates for Galilean Covariant Dynamics.
Actual Schrödinger L2 spaces are used throughout. Nuclear trace class and genuinely
self-adjoint densely defined observables are reused from pinned accepted modules.
Density hypotheses use the imported trace-class, positivity and trace primitives;
purity uses Mathlib rankOne directly. Local choices select bounded operators by
their complete action or dense-domain forms, never by a coherence, asymptotic, or isometry property. Their defaults are
irrelevant on the stated domains; no existence conclusion is assumed as a field.
The eight source-ambiguous nodes and the unfinished appendix Fourier interface
are inventoried in HARD.md and GAPS.json. Compilation awaits the batch handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Next46.P31

open QAlgorithms.PeriodicSchrodinger (Position)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace)

section ObservableCoherence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.8: an unbounded observable is represented by its actual operator graph. -/
abbrev ObservableGraph (H : Type*) := H → H → Prop

/-- PDF p.8: the graph of the accepted densely defined self-adjoint observable. -/
def observableGraph
    (A : QAlgorithms.Papers.Independent.Frontier30.P22.SelfAdjointHamiltonian (H := H)) :
    ObservableGraph H :=
  fun f g => ∃ hf : f ∈ A.domain, A.action ⟨f, hf⟩ = g

/-- PDF p.8: P realizes A rho by the bounded form <A u,rho f>=<u,P f>.
There is no application of an unbounded operator outside its domain. -/
def ProductForm (A : ObservableGraph H) (rho P : H →L[ℂ] H) : Prop :=
  ∀ u v, A u v → ∀ f, inner ℂ v (rho f) = inner ℂ u (P f)

/-- PDF p.8: exactly the source's trace-class coordinate-product regularity. -/
def RegularProduct (A : ObservableGraph H) (rho : H →L[ℂ] H) : Prop :=
  ∃ P : H →L[ℂ] H, ProductForm A rho P ∧ IsTraceClass P

/-- PDF p.8: the unique bounded realization, whenever the source domain holds.
For a dense self-adjoint graph all witnesses have the same action. -/
def observableProduct (A : ObservableGraph H) (rho : H →L[ℂ] H) : H →L[ℂ] H :=
  if h : ∃ P : H →L[ℂ] H, ProductForm A rho P then Classical.choose h else 0

/-- PDF pp.8,23: Hilbert–Schmidt membership in any complete Hilbert basis. -/
def IsHilbertSchmidt {I : Type*} (b : HilbertBasis I ℂ H) (T : H →L[ℂ] H) : Prop :=
  Summable (fun i => ‖T (b i)‖ ^ 2)

/-- PDF pp.8,23: HS size on its finite domain. Trace-class inputs and their
coordinate products are HS. Alternative indices explicitly guard this domain. -/
def hsSize {I : Type*} (b : HilbertBasis I ℂ H) (T : H →L[ℂ] H) : ℝ :=
  Real.sqrt (∑' i, ‖T (b i)‖ ^ 2)

/-- PDF p.8: expectation of the original density, not of its square root. -/
def observableMean {I : Type*} (b : HilbertBasis I ℂ H)
    (A : ObservableGraph H) (rho : H →L[ℂ] H) : ℝ :=
  (operatorTrace b (observableProduct A rho)).re

/-- PDF p.8, (2.1): [A,rho] on its bounded realization. -/
def observableCommutator (A : ObservableGraph H) (rho : H →L[ℂ] H) : H →L[ℂ] H :=
  observableProduct A rho - (observableProduct A rho).adjoint

/-- PDF p.8, (2.2): {A-Tr(A rho),rho}, including both centering terms. -/
def centeredAnticommutator {I : Type*} (b : HilbertBasis I ℂ H)
    (A : ObservableGraph H) (rho : H →L[ℂ] H) : H →L[ℂ] H :=
  observableProduct A rho + (observableProduct A rho).adjoint -
    (2 * (observableMean b A rho : ℂ)) • rho

/-- PDF p.8, (2.1): normalized commutator length for the entire finite family. -/
def coherenceLength {I : Type*} {d : ℕ} (b : HilbertBasis I ℂ H)
    (A : Fin d → ObservableGraph H) (rho : H →L[ℂ] H) : ℝ :=
  Real.sqrt (∑ j, hsSize b (observableCommutator (A j) rho) ^ 2) / hsSize b rho

/-- PDF p.8, (2.2): normalized centered anticommutator spread. -/
def coherenceSpread {I : Type*} {d : ℕ} (b : HilbertBasis I ℂ H)
    (A : Fin d → ObservableGraph H) (rho : H →L[ℂ] H) : ℝ :=
  Real.sqrt (∑ j, hsSize b (centeredAnticommutator b (A j) rho) ^ 2) / hsSize b rho

/-- PDF p.9, Definition 2.1: the index is used only where its spread is nonzero. -/
def coherenceIndex {I : Type*} {d : ℕ} (b : HilbertBasis I ℂ H)
    (A : Fin d → ObservableGraph H) (rho : H →L[ℂ] H) : ℝ :=
  coherenceLength b A rho / coherenceSpread b A rho

example {I : Type*} (b : HilbertBasis I ℂ H) : hsSize b 0 = 0 := by
  simp [hsSize]

example {I : Type*} (b : HilbertBasis I ℂ H) (rho : H →L[ℂ] H)
    (A : Fin 0 → ObservableGraph H) : coherenceSpread b A rho = 0 := by
  simp [coherenceSpread]

/-- PDF p.4: positive square root by continuous functional calculus. -/
def positiveSquareRoot (rho : H →L[ℂ] H) : H →L[ℂ] H :=
  cfc (fun z : ℂ => (Real.sqrt z.re : ℂ)) rho

/-- PDF p.4: finite second-moment domain for a square-root-state expression.
Only HS, rather than trace-class, products of A with sqrt(rho) are required. -/
def RootRegular {I : Type*} {d : ℕ} (b : HilbertBasis I ℂ H)
    (A : Fin d → ObservableGraph H) (rho : H →L[ℂ] H) : Prop :=
  ∀ j, (∃ P : H →L[ℂ] H, ProductForm (A j) (positiveSquareRoot rho) P) ∧
    IsHilbertSchmidt b (observableProduct (A j) (positiveSquareRoot rho))

/-- PDF p.4: Tr(rho |A-Tr(A rho)|^2), expressed by its finite HS form. -/
def observableVariance {I : Type*} {d : ℕ} (b : HilbertBasis I ℂ H)
    (A : Fin d → ObservableGraph H) (rho : H →L[ℂ] H) : ℝ :=
  ∑ j, hsSize b (observableProduct (A j) (positiveSquareRoot rho) -
    (observableMean b (A j) rho : ℂ) • positiveSquareRoot rho) ^ 2

/-- PDF p.4: the proposed alternative numerator, without a rho HS normalization. -/
def alternativeNumerator {I : Type*} {d : ℕ} (b : HilbertBasis I ℂ H)
    (A : Fin d → ObservableGraph H) (rho : H →L[ℂ] H) : ℝ :=
  Real.sqrt (∑ j, hsSize b (observableCommutator (A j) (positiveSquareRoot rho)) ^ 2)

/-- PDF p.4: preserve the printed factor 2 outside the square root. -/
def alternativeDenominator {I : Type*} {d : ℕ} (b : HilbertBasis I ℂ H)
    (A : Fin d → ObservableGraph H) (rho : H →L[ℂ] H) : ℝ :=
  2 * Real.sqrt (observableVariance b A rho)

end ObservableCoherence

/-- PDF p.8: Euclidean-coordinate Schrödinger L2. The accepted Cartesian
Schrodinger uses Fin d -> R; its measure is on a different Lean type. -/
abbrev EuclideanSchrodinger (d : ℕ) := Lp ℂ 2 (volume : Measure (Position d))

/-- PDF p.8: actual phase points (q,p) or (x,k), rather than the accepted
Phase alias, which is the coordinate index Fin d ⊕ Fin d. -/
abbrev PhasePoint (d : ℕ) := Position d × Position d

/-- Appendix A, PDF p.21: explicit Schrödinger action fixed by (A.1)–(A.2). -/
def weylAction {d : ℕ} (z : PhasePoint d) (f : Position d → ℂ) (x : Position d) : ℂ :=
  Complex.exp (Complex.I * (∑ j, z.2 j * (x j - z.1 j / 2) : ℝ)) * f (x - z.1)

/-- Appendix A, PDF p.21: the bounded Weyl operator is specified on every L2
vector almost everywhere. Translation and a modulus-one multiplier determine
an existing unique isometry; no Weyl product or trace isometry is assumed. -/
def schrodingerWeyl {d : ℕ} (z : PhasePoint d) : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d) :=
  if h : ∃ U : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d), ∀ f : EuclideanSchrodinger d,
      (U f : Position d → ℂ) =ᵐ[volume] weylAction z f then Classical.choose h else 0

example {d : ℕ} : schrodingerWeyl (0 : PhasePoint d) = ContinuousLinearMap.id ℂ (EuclideanSchrodinger d) := by
  have hex : ∃ U : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d), ∀ f : EuclideanSchrodinger d,
      (U f : Position d → ℂ) =ᵐ[volume] weylAction (0 : PhasePoint d) f := by
    refine ⟨ContinuousLinearMap.id ℂ (EuclideanSchrodinger d), ?_⟩
    intro f
    filter_upwards [] with x
    simp [weylAction]
  rw [schrodingerWeyl, dif_pos hex]
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [Classical.choose_spec hex f] with x hx
  simpa [weylAction] using hx

/-- PDF pp.8,21: phi_T=Tr(W T) for every trace-class operator T. -/
def schrodingerCharacteristic {I : Type*} {d : ℕ} (b : HilbertBasis I ℂ (EuclideanSchrodinger d))
    (T : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d)) (z : PhasePoint d) : ℂ :=
  operatorTrace b ((schrodingerWeyl z).comp T)

/-- PDF pp.1,8: canonical position as the maximal multiplication graph on L2. -/
def positionGraph {d : ℕ} (j : Fin d) : ObservableGraph (EuclideanSchrodinger d) :=
  fun f g => (g : Position d → ℂ) =ᵐ[volume] fun x => (x j : ℂ) * f x

/-- PDF pp.8,21: canonical momentum is the generator of the actual translation
subgroup. Its full strong-generator domain is used, with no finite cutoff. -/
def momentumGraph {d : ℕ} (j : Fin d) : ObservableGraph (EuclideanSchrodinger d) :=
  fun f g => HasDerivAt
    (fun t : ℝ => schrodingerWeyl (t • (EuclideanSpace.single j 1 : Position d), 0) f)
    (Complex.I • g) 0

/-- PDF pp.8,15,18: every canonical coordinate product is trace class. -/
def CanonicallyRegular {d : ℕ} (rho : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d)) : Prop :=
  (∀ j, RegularProduct (positionGraph j) rho) ∧
    (∀ j, RegularProduct (momentumGraph j) rho)

/-- PDF p.3: the vector of position expectations. -/
def positionMean {I : Type*} {d : ℕ} (b : HilbertBasis I ℂ (EuclideanSchrodinger d))
    (rho : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d)) : Position d :=
  WithLp.toLp 2 (fun j => observableMean b (positionGraph j) rho)

/-- PDF p.8, (1.19): volume-preserving free shear, with the specified plus sign. -/
def phaseShear {d : ℕ} (t : ℝ) (z : PhasePoint d) : PhasePoint d := (z.1 + t • z.2, z.2)

/-- PDF p.2: covariance coordinates in the source's (q,p) block order. -/
def phaseCoordinates {d : ℕ} (z : PhasePoint d) : (Fin d ⊕ Fin d) → ℝ :=
  Sum.elim (fun j => z.1 j) (fun j => z.2 j)

/-- PDF p.8, (1.19): the real Gaussian quadratic form, not an operator norm. -/
def noiseQuadratic {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ)
    (z : PhasePoint d) : ℝ :=
  ∑ i, ∑ j, phaseCoordinates z i * A i j * phaseCoordinates z j

/-- PDF p.8, (1.20): symmetric jump exponent paired as q.k+p.x. -/
def jumpExponent {d : ℕ} (mu : Measure (PhasePoint d)) (z : PhasePoint d) : ℝ :=
  ∫ y, Real.cos (∑ j, (z.1 j * y.2 j + z.2 j * y.1 j)) - 1 ∂mu

/-- PDF pp.2,7–8,18: the full finite-second-moment Lévy domain. Infinite total
mass is permitted; zero mass at the origin is the Lévy convention on R^(2d)\{0}. -/
def FiniteVarianceLevyNoise {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ)
    (mu : Measure (PhasePoint d)) : Prop :=
  A.PosSemidef ∧ mu {0} = 0 ∧ Measure.map (fun z => -z) mu = mu ∧
    Integrable (fun z => ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) mu

/-- PDF p.8, (1.19): the explicit multiplier/shear action on functions.
No L2 membership, contraction, positivity, or semigroup law is assumed here. -/
def characteristicEvolution {d : ℕ}
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (mu : Measure (PhasePoint d))
    (t : ℝ) (f : PhasePoint d → ℂ) (z : PhasePoint d) : ℂ :=
  (Real.exp (∫ s in (0 : ℝ)..t,
    -noiseQuadratic A (phaseShear (t - s) z) / 2 +
      jumpExponent mu (phaseShear (t - s) z)) : ℂ) * f (phaseShear t z)

/-- PDF pp.8,11,13: (1.19) pins the dynamics on every trace-class input.
With admissible noise this uniquely specifies the source's trace-preserving
quantum dynamical semigroup; no asymptotic or derivative formulas are fields. -/
def CharacteristicDynamics {I : Type*} {d : ℕ}
    (b : HilbertBasis I ℂ (EuclideanSchrodinger d))
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (mu : Measure (PhasePoint d))
    (Gamma : ℝ → (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d) → (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d)) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ T : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d), IsTraceClass T →
    IsTraceClass (Gamma t T) ∧ ∀ z,
      schrodingerCharacteristic b (Gamma t T) z =
        characteristicEvolution A mu t (schrodingerCharacteristic b T) z

/-- PDF p.2: q,q block, denoted A_xx in the source. -/
def positionBlock {d : ℕ} (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun i j => A (Sum.inl i) (Sum.inl j)

/-- PDF pp.2,18–19: explicit momentum second moment M, avoiding the source's
inconsistent B-block labels: M_ij = integral k_i k_j dmu(x,k). -/
def momentumMoment {d : ℕ} (mu : Measure (PhasePoint d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∫ z, z.2 i * z.2 j ∂mu

/-- PDF p.15: only the A_xx block can be nonzero. -/
def OnlyMomentumGaussian {d : ℕ}
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) : Prop :=
  ∀ i j, A (Sum.inl i) (Sum.inr j) = 0 ∧
    A (Sum.inr i) (Sum.inl j) = 0 ∧ A (Sum.inr i) (Sum.inr j) = 0

/-- PDF pp.18–20, Theorem 4.3(1): momentum-only noise, including both
nonzero absolutely-continuous jump noise and positive-definite Gaussian noise. -/
def MomentumNoiseRegime {d : ℕ}
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (mu : Measure (PhasePoint d)) : Prop :=
  OnlyMomentumGaussian A ∧ ∃ nu : Measure (Position d),
    mu = Measure.map (fun k => ((0 : Position d), k)) nu ∧
      ((nu ≠ 0 ∧ nu ≪ volume) ∨ (positionBlock A).PosDef)

/-- PDF pp.18–19, Theorem 4.3(3): full nondegenerate Gaussian or jump noise. -/
def FullNoiseRegime {d : ℕ}
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (mu : Measure (PhasePoint d)) : Prop :=
  (mu ≠ 0 ∧ mu ≪ volume) ∨ A.PosDef

/-- PDF pp.2,15: exact leading constant, including sqrt(3) and the inverse. -/
def leadingCoefficient {d : ℕ} (D : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt 3 * Real.sqrt (Matrix.trace (D⁻¹)) / Real.sqrt (Matrix.trace D)

example {d : ℕ} (z : PhasePoint d) : phaseShear 0 z = z := by
  simp [phaseShear]

example {d : ℕ} (t : ℝ) : noiseQuadratic (0 : Matrix (Fin d ⊕ Fin d) _ ℝ)
    (phaseShear t (0 : PhasePoint d)) = 0 := by
  simp [noiseQuadratic]

example {d : ℕ} (mu : Measure (PhasePoint d)) : jumpExponent mu 0 = 0 := by
  simp [jumpExponent]

/-- PDF p.23: the explicit weighted Lebesgue measure (2 pi)^(-d) dq dp. -/
def characteristicMeasure (d : ℕ) : Measure (PhasePoint d) :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℤ))) • volume

/-- PDF p.3: actual HS integral kernel, specified by all L2 matrix elements.
The paired integrand is integrable for every pair of L2 test vectors by Cauchy–Schwarz. -/
def RepresentsKernel {d : ℕ} (T : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d)) (K : PhasePoint d → ℂ) : Prop :=
  MemLp K 2 volume ∧ ∀ f g : EuclideanSchrodinger d,
    inner ℂ g (T f) = ∫ z : PhasePoint d, star (g z.1) * K z * f z.2

/-- PDF pp.3–4,9: the actual operator selected by a specified square-integrable
kernel when it exists. All uses are Gaussian or finite rank kernels. -/
def kernelOperator {d : ℕ} (K : PhasePoint d → ℂ) : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d) :=
  if h : ∃ T : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d), RepresentsKernel T K then Classical.choose h else 0

/-- PDF pp.4,9: the normalized one-dimensional Gaussian kernel. E^2/(4C)
is constructed, not an independent parameter. R^1 is identified with R. -/
def gaussianKernel (A B C D E : ℝ) (z : PhasePoint 1) : ℂ :=
  (2 * Real.sqrt C / Real.sqrt Real.pi : ℝ) * Complex.exp
    ((-A * (z.1 0 - z.2 0) ^ 2 - C * (z.1 0 + z.2 0) ^ 2 -
      E * (z.1 0 + z.2 0) - E ^ 2 / (4 * C) : ℝ) -
      Complex.I * (B * ((z.1 0) ^ 2 - (z.2 0) ^ 2) + D * (z.1 0 - z.2 0) : ℝ))

/-- PDF p.9: interval endpoint a_m=(6/pi^2) sum_{r=1}^m r^(-2), a_0=0. -/
def rareEndpoint (m : ℕ) : ℝ :=
  (6 / Real.pi ^ 2) * ∑ r ∈ Finset.Icc 1 m, 1 / (r : ℝ) ^ 2

/-- PDF p.9: normalized indicator of [a_(m-1),a_m), for m>=1. -/
def rareVector (m : ℕ) (x : ℝ) : ℂ :=
  if x ∈ Set.Ico (rareEndpoint (m - 1)) (rareEndpoint m) then
    (1 / Real.sqrt (rareEndpoint m - rareEndpoint (m - 1)) : ℝ) else 0

/-- PDF p.9: actual mixture weights; the first probability is 1/n, not 1/n^2. -/
def rareWeight (n m : ℕ) : ℝ :=
  if m = 1 then 1 / (n : ℝ) else
    if 2 ≤ m ∧ m ≤ n ^ 3 - n ^ 2 + 1 then 1 / (n : ℝ) ^ 3 else 0

/-- PDF p.9: the finite-rank mixture with all the prescribed components. -/
def rareKernel (n : ℕ) (z : PhasePoint 1) : ℂ :=
  ∑ m ∈ Finset.range (n ^ 3 - n ^ 2 + 1),
    (rareWeight n (m + 1) : ℂ) * rareVector (m + 1) (z.1 0) *
      star (rareVector (m + 1) (z.2 0))

/-- PDF p.9: the final ratio's leading constant, evaluated on the first interval.
Its mean is a_1/2, variance a_1^2/12, and centered squared distance to 1 is
variance+(a_1/2-1)^2. Thus the denominator contains twice the latter square. -/
def rareCoefficient : ℝ :=
  Real.sqrt (rareEndpoint 1 ^ 2 / 12) /
    Real.sqrt (rareEndpoint 1 ^ 2 / 12 + 2 * (rareEndpoint 1 / 2 - 1) ^ 2)

example : rareWeight 1 1 = 1 := by norm_num [rareWeight]

example : rareWeight 2 1 = 1 / 2 := by norm_num [rareWeight]

end QAlgorithms.Papers.Independent.Next46.P31


