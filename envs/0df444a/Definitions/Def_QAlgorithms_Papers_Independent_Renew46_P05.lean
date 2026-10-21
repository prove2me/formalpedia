-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P05
-- name    : QAlgorithms_Papers_Independent_Renew46_P05
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T19:54:35.912725+00:00
-- url     : https://prove2.me/theorems/f3762286-d289-4ce0-94c9-d6e35126452e
-- title:
--   Definitions for Average sampling in certain subspaces of Hilbert-Schmidt operators on $L^2(\mathbb{R}^d)$
-- statement:
--   The objects the formalized statements of *Average sampling in certain subspaces of Hilbert-Schmidt operators on $L^2(\mathbb{R}^d)$* (arXiv:2011.05871) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SchrodingerOperator`: PDF p.4: actual bounded operators; HS domain is specified separately.
--   - `IsHS`: PDF pp.3–4: the accepted, basis-independent Hilbert–Schmidt domain.
--   - `sourceHSPair`: PDF p.4: source pairing is linear in T, hence reversed library arguments.
--   - `symplectic`: PDF p.5: sigma((x,w),(x',w'))=w.x'-w'.x.
--   - `shiftAction`: PDF p.4: the full explicit action of pi(z).
--   - `timeFrequencyShift`: PDF p.4: bounded realization determined on every L² function a.e. Translation and a modulus-one multiplier give a unique witness for all z; the default is off-domain everywhere. No sampling or covariance is assumed.
--   - `translateOperator`: PDF p.5: alpha_z(T)=pi(z) T pi(z)* with the actual adjoint.
--   - `Coordinate`: PDF p.5: 2d real or integer coordinate labels, position before frequency.
--   - `LatticeIndex`: PDF p.5: integer coordinates k of lambda=A k.
--   - `Lattice`: PDF p.5: a full-rank lattice presentation, not an arbitrary group action.
--   - `latticePoint`: PDF p.5: the actual phase-space point lambda=A k.
--   - `DualTorus`: PDF p.5: compact dual in character coordinates with normalized Haar volume.
--   - `dualCoordinates`: PDF p.5: theta_j=sigma(A e_j,z) mod Z; kernel is the adjoint lattice. Thus mFourier k (dualCoordinates L z)=exp(2 pi i sigma(A k,z)).
--   - `LatticeL2`: PDF p.5: scalar l² on the lattice.
--   - `Coefficients`: PDF pp.10–13: N copies of l², indexed by generator.
--   - `latticeFourier`: PDF p.5: continuous l² extension of the positive-sign Fourier series. No pointwise series on arbitrary l² is used.
--   - `inverseLatticeFourier`: PDF pp.8,12: inverse of the unitary lattice Fourier synthesis.
--   - `torusL2`: PDF pp.8,12: L² class of a function. SamplingStable reciprocals and bounded entries on the probability torus are MemLp; the default is unused in the theorems.
--   - `inverseFilter`: PDF p.8: p=(F^Lambda_sigma)^(-1)(1/F^Lambda_sigma q).
--   - `latticeConvolution`: PDF p.5: scalar latticeConvolution. Each scalar sum is absolutely convergent for l² inputs by Cauchy–Schwarz; no l²-output assertion is built in.
--   - `SamplingMatrix`: PDF p.11: M by N matrix with l² entries.
--   - `transfer`: PDF p.11: A-hat by entrywise lattice Fourier synthesis.
--   - `samples`: PDF pp.10–13: s=A*c, with source generator index n summed.
--   - `singleMatrix`: PDF p.9: the one-channel latticeConvolution matrix from arbitrary q.
--   - `HasHSSum`: PDF pp.7–14: unconditional convergence via ALL finite subsets, in HS norm. Terms and limit are explicitly Hilbert–Schmidt, ruling out divergent-norm defaults.
--   - `translatedGenerators`: PDF pp.6,10: all translates of all labelled generators.
--   - `synthesisTerms`: PDF pp.7,10,13: source l² synthesis summands.
--   - `samplingSpace`: PDF pp.7,10: actual l² synthesis range; with the Riesz hypothesis it is exactly the closed HS span and the representing coefficients are unique.
--   - `synthesize`: PDF pp.7,13: T_S c, determined by the actual unconditional HS sum. Riesz synthesis has a unique limit for every c; no desired reconstruction identity is included in this choice.
--   - `coefficients`: PDF pp.7,10: coefficient inverse on V²_S; zero away from that domain.
--   - `IsHSRieszSequence`: PDF pp.6–7: standard Riesz inequalities on all finite complex coefficients. Constants precede every coefficient family; all operators are HS.
--   - `IsHSRieszBasisFor`: PDF pp.8–9,14: Riesz sequence, membership and l² completeness in V.
--   - `IsHSFrameFor`: PDF pp.13–14: frame IN the specified HS space with convergent energy sums.
--   - `UpperStable`: PDF pp.11–13: beta_A finite by a uniform finite quadratic upper bound.
--   - `LowerStable`: PDF pp.11,13: alpha_A positive, without assuming an upper bound.
--   - `SamplingStable`: PDF p.13, (7): positive essential lower AND finite essential upper bound.
--   - `Reconstructs`: PDF pp.13–14: one fixed reconstruction family for every input coefficient tuple and its actual HS synthesis. The premise only identifies the input.
--   - `averageSample`: PDF pp.7–8: physical average samples for Q anywhere in HS.
--   - `physicalKernel`: PDF p.8: q(k)=<S,alpha_k(Q)>; Riesz plus Q in HS guarantees Memℓp. The zero fallback is unused in averageSampling_exact.
--   - `AverageReconstructs`: PDF pp.8–9: the physical reconstruction of every T in V²_S.
--   - `DeterminantStable`: PDF p.14: bounds on the MODULUS of the complex determinant. Full-system boundedness remains a separate standing premise.
--   - `BoundedTransfer`: PDF pp.12–14: measurable essentially bounded entries of a matrix function.
--   - `transferPseudoInverse`: PDF p.12: (A-hat* A-hat)^(-1) A-hat* on the full-column-rank a.e. domain. SamplingStable is required by the theorem; no singular inverse is treated as valid.
--   - `parametrizedInverse`: PDF p.14: all bounded left inverses; the parameter C need not be unique.
--   - `inverseColumn`: PDF pp.12–13: inverse Fourier column b_m of B-hat.
--   - `reconstructionFamily`: PDF pp.13–14: actual construction H_m=T_S b_m.
--   - `SymbolCoordinate`: PDF pp.4–6: Euclidean coordinates on the actual 2d-dimensional phase space.
--   - `phaseEuclideanCoordinates`: PDF p.5: phase-to-Euclidean identification, in position/frequency order.
--   - `coordinatesPhase`: PDF p.5: inverse coordinate identification on phase space.
--   - `SymbolSpace`: PDF p.4: phase L² with actual Lebesgue measure.
--   - `phaseL2`: PDF pp.4,6: take the L² equivalence class when it exists. Every use below on Wigner functions, translations, or the orthogonal Fourier rotation is on the MemLp domain; no existence is put in a Weyl-system record.
--   - `crossWignerFunction`: PDF p.4: actual cross-Wigner integral, including the conjugated second factor, midpoint arguments, and negative 2pi frequency exponent. For L² inputs the integral in t is absolutely integrable by Cauchy–Schwarz.
--   - `crossWigner`: PDF p.4: cross-Wigner L² class of actual L² vectors, without any angular frequency rescaling. Representative changes give the same phase L² class.
--   - `HasWeylSymbol`: PDF p.4: the defining weak Weyl pairing. Both source brackets are first-linear, so both Mathlib pairings have reversed arguments.
--   - `weylSymbol`: PDF p.4: a_S selected by the explicit weak Wigner pairing. For every HS operator the witness exists uniquely; no covariance, Gram bound, or isometry property is part of the choice. Outside HS the default is irrelevant here.
--   - `weylOperator`: PDF p.4: L_a selected by the same weak pairing on ALL Schrödinger vectors. Every phase L² symbol has a unique HS realization; no conclusion of a target target is imposed as a field or a choice condition.
--   - `translateSymbol`: PDF pp.5–7: ordinary symbol translation by an actual phase point.
--   - `symbolSynthesis`: PDF pp.7–8,13: the actual symbol synthesis T_(a_S)c. Under the source's Riesz hypotheses this tsum is summable; it is not a freely supplied symbol.
--   - `symplecticRotation`: PDF p.6: J(x,w)=(w,-x), so <Jz,z'>=sigma(z,z').
--   - `symplecticFourier`: PDF p.6: F_sigma a(z)=F a(Jz), using Mathlib's continuous L² Plancherel extension with exp(-2pi i <.,.>), then a measure-preserving orthogonal rotation. It is not the total Bochner integral of a merely L² symbol.
--   - `symbolSTFT`: PDF p.6 and cited [24], Section 3.2: Gaussian-window STFT of a phase symbol. The nonzero Gaussian normalization does not change S_0 membership. The inner integral is absolutely integrable for every (u,v), by L² Cauchy–Schwarz.
--   - `InFeichtinger`: PDF p.6: Feichtinger algebra S_0 on phase space, by integrable STFT. The outer integral is guarded by Integrable, avoiding a zero-default test.
--   - `InOperatorB`: PDF p.6: the source's class B, on actual HS operators and actual symbols. This hypothesis is used ONLY for the pointwise refinement.
--   - `fourierWigner`: PDF p.6: FW(S)(x,w)=exp(-pi i x.w) tr(pi(-z) S). On B the operator is trace class, so the accepted basis trace converges.
--   - `AdjointLattice`: PDF p.5: actual adjoint lattice, represented as its phase-coordinate subtype.
--   - `symbolGram`: PDF p.6: periodized symbol Gram entries v_n conjugate(v_n'), with NO covolume prefactor. For L² symbols the sums converge absolutely a.e.
--   - `wignerGram`: PDF pp.6–7: periodized Fourier-Wigner Gram entries. On B the continuous representatives and absolute summability make this a pointwise definition.
--   - `GramBounds`: PDF p.7: Hermitian quadratic-form bounds in the Euclidean vector norm. The matrices at issue are Gram matrices, hence Hermitian on their domains.
--   - `ConstructedWithSymbols`: PDF pp.13–14: the source's Weyl-symbol part of H_m=T_S b_m=L_(T_(a_S)b_m).
-- source:
--   Average sampling in certain subspaces of Hilbert-Schmidt operators on $L^2(\mathbb{R}^d)$, arXiv:2011.05871v2, https://arxiv.org/abs/2011.05871v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P31

/-!
García, arXiv:2011.05871v2, PDF pp.4–15.
Actual Lebesgue L²(R^d) operators and the pinned infinite-dimensional HS
membership/norm/pairing are used. All convergence is in HS norm.
The dual lattice is in character coordinates theta_i=sigma(A e_i,z) mod Z;
normalized torus Fourier synthesis is therefore the source's positive-sign
symplectic Fourier series. Weyl symbols are defined by the explicit weak
Wigner pairing, and the pointwise criterion uses the actual Feichtinger class.
Compilation is pending the requested batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P05

open Filter MeasureTheory
open QAlgorithms.PeriodicSchrodinger (Position)
open QAlgorithms.Papers.Independent.Next46.P31 (EuclideanSchrodinger PhasePoint)
open QAlgorithms.Papers.Independent.Next46.P02 (hilbertSchmidtNorm)
open scoped BigOperators ENNReal Topology ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

/-- PDF p.4: actual bounded operators; HS domain is specified separately. -/
abbrev SchrodingerOperator (d : ℕ) := EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d

/-- PDF pp.3–4: the accepted, basis-independent Hilbert–Schmidt domain. -/
abbrev IsHS {d : ℕ} (T : SchrodingerOperator d) : Prop :=
  QAlgorithms.Papers.Independent.Next46.P02.IsHilbertSchmidt T

/-- PDF p.4: source pairing is linear in T, hence reversed library arguments. -/
def sourceHSPair {d : ℕ} (T Q : SchrodingerOperator d) : ℂ :=
  QAlgorithms.Papers.Independent.Next46.P02.hilbertSchmidtInner Q T

/-- PDF p.5: sigma((x,w),(x',w'))=w.x'-w'.x. -/
def symplectic {d : ℕ} (z w : PhasePoint d) : ℝ :=
  (∑ j, z.2 j * w.1 j) - ∑ j, w.2 j * z.1 j

/-- PDF p.4: the full explicit action of pi(z). -/
def shiftAction {d : ℕ} (z : PhasePoint d) (f : Position d → ℂ)
    (t : Position d) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (∑ j, z.2 j * t j : ℝ)) * f (t - z.1)

/-- PDF p.4: bounded realization determined on every L² function a.e.
Translation and a modulus-one multiplier give a unique witness for all z;
the default is off-domain everywhere. No sampling or covariance is assumed. -/
def timeFrequencyShift {d : ℕ} (z : PhasePoint d) : SchrodingerOperator d :=
  if h : ∃ U : SchrodingerOperator d, ∀ f : EuclideanSchrodinger d,
      (U f : Position d → ℂ) =ᵐ[volume] shiftAction z f then
    Classical.choose h else 0

/-- PDF p.5: alpha_z(T)=pi(z) T pi(z)* with the actual adjoint. -/
def translateOperator {d : ℕ} (z : PhasePoint d) (T : SchrodingerOperator d) : SchrodingerOperator d :=
  (timeFrequencyShift z).comp (T.comp (timeFrequencyShift z).adjoint)

/-- PDF p.5: 2d real or integer coordinate labels, position before frequency. -/
abbrev Coordinate (d : ℕ) := Fin d ⊕ Fin d

/-- PDF p.5: integer coordinates k of lambda=A k. -/
abbrev LatticeIndex (d : ℕ) := Coordinate d → ℤ

/-- PDF p.5: a full-rank lattice presentation, not an arbitrary group action. -/
abbrev Lattice (d : ℕ) := (Coordinate d → ℝ) ≃ₗ[ℝ] PhasePoint d

/-- PDF p.5: the actual phase-space point lambda=A k. -/
def latticePoint {d : ℕ} (L : Lattice d) (k : LatticeIndex d) : PhasePoint d :=
  L (fun j => (k j : ℝ))

/-- PDF p.5: compact dual in character coordinates with normalized Haar volume. -/
abbrev DualTorus (d : ℕ) := UnitAddTorus (Coordinate d)

/-- PDF p.5: theta_j=sigma(A e_j,z) mod Z; kernel is the adjoint lattice.
Thus mFourier k (dualCoordinates L z)=exp(2 pi i sigma(A k,z)). -/
def dualCoordinates {d : ℕ} (L : Lattice d) (z : PhasePoint d) : DualTorus d :=
  fun j => (symplectic (L (Pi.single j 1)) z : UnitAddCircle)

/-- PDF p.5: scalar l² on the lattice. -/
abbrev LatticeL2 (d : ℕ) := lp (fun _ : LatticeIndex d => ℂ) 2

/-- PDF pp.10–13: N copies of l², indexed by generator. -/
abbrev Coefficients (d N : ℕ) := Fin N → LatticeL2 d

/-- PDF p.5: continuous l² extension of the positive-sign Fourier series.
No pointwise series on arbitrary l² is used. -/
def latticeFourier {d : ℕ} (c : LatticeL2 d) : Lp ℂ 2 (volume : Measure (DualTorus d)) :=
  (UnitAddTorus.mFourierBasis (d := Coordinate d)).repr.symm c

/-- PDF pp.8,12: inverse of the unitary lattice Fourier synthesis. -/
def inverseLatticeFourier {d : ℕ} (f : Lp ℂ 2 (volume : Measure (DualTorus d))) : LatticeL2 d :=
  (UnitAddTorus.mFourierBasis (d := Coordinate d)).repr f

/-- PDF pp.8,12: L² class of a function. SamplingStable reciprocals and bounded entries
on the probability torus are MemLp; the default is unused in the theorems. -/
def torusL2 {d : ℕ} (f : DualTorus d → ℂ) : Lp ℂ 2 (volume : Measure (DualTorus d)) :=
  if h : MemLp f 2 (volume : Measure (DualTorus d)) then h.toLp f else 0

/-- PDF p.8: p=(F^Lambda_sigma)^(-1)(1/F^Lambda_sigma q). -/
def inverseFilter {d : ℕ} (q : LatticeL2 d) : LatticeL2 d :=
  inverseLatticeFourier (torusL2 (fun t => (latticeFourier q t)⁻¹))

/-- PDF p.5: scalar latticeConvolution. Each scalar sum is absolutely convergent
for l² inputs by Cauchy–Schwarz; no l²-output assertion is built in. -/
def latticeConvolution {d : ℕ} (a c : LatticeL2 d) (k : LatticeIndex d) : ℂ :=
  ∑' j : LatticeIndex d, a j * c (k - j)

/-- PDF p.11: M by N matrix with l² entries. -/
abbrev SamplingMatrix (d M N : ℕ) := Matrix (Fin M) (Fin N) (LatticeL2 d)

/-- PDF p.11: A-hat by entrywise lattice Fourier synthesis. -/
def transfer {d M N : ℕ} (A : SamplingMatrix d M N) (t : DualTorus d) :
    Matrix (Fin M) (Fin N) ℂ :=
  fun m n => latticeFourier (A m n) t

/-- PDF pp.10–13: s=A*c, with source generator index n summed. -/
def samples {d M N : ℕ} (A : SamplingMatrix d M N) (c : Coefficients d N)
    (i : Fin M × LatticeIndex d) : ℂ :=
  ∑ n : Fin N, latticeConvolution (A i.1 n) (c n) i.2

/-- PDF p.9: the one-channel latticeConvolution matrix from arbitrary q. -/
def singleMatrix {d : ℕ} (q : LatticeL2 d) : SamplingMatrix d 1 1 :=
  fun _ _ => q

/-- PDF pp.7–14: unconditional convergence via ALL finite subsets, in HS norm.
Terms and limit are explicitly Hilbert–Schmidt, ruling out divergent-norm defaults. -/
def HasHSSum {d : ℕ} {I : Type*} (f : I → SchrodingerOperator d) (T : SchrodingerOperator d) : Prop :=
  (∀ i, IsHS (f i)) ∧ IsHS T ∧
    Tendsto (fun F : Finset I => hilbertSchmidtNorm ((∑ i ∈ F, f i) - T)) atTop (nhds 0)

/-- PDF pp.6,10: all translates of all labelled generators. -/
def translatedGenerators {d N : ℕ} (L : Lattice d) (S : Fin N → SchrodingerOperator d)
    (i : Fin N × LatticeIndex d) : SchrodingerOperator d :=
  translateOperator (latticePoint L i.2) (S i.1)

/-- PDF pp.7,10,13: source l² synthesis summands. -/
def synthesisTerms {d N : ℕ} (L : Lattice d) (S : Fin N → SchrodingerOperator d)
    (c : Coefficients d N) (i : Fin N × LatticeIndex d) : SchrodingerOperator d :=
  c i.1 i.2 • translatedGenerators L S i

/-- PDF pp.7,10: actual l² synthesis range; with the Riesz hypothesis it is
exactly the closed HS span and the representing coefficients are unique. -/
def samplingSpace {d N : ℕ} (L : Lattice d) (S : Fin N → SchrodingerOperator d) : Set (SchrodingerOperator d) :=
  {T | ∃ c : Coefficients d N, HasHSSum (synthesisTerms L S c) T}

/-- PDF pp.7,13: T_S c, determined by the actual unconditional HS sum.
Riesz synthesis has a unique limit for every c; no desired reconstruction
identity is included in this choice. -/
def synthesize {d N : ℕ} (L : Lattice d) (S : Fin N → SchrodingerOperator d)
    (c : Coefficients d N) : SchrodingerOperator d :=
  if h : ∃ T, HasHSSum (synthesisTerms L S c) T then Classical.choose h else 0

/-- PDF pp.7,10: coefficient inverse on V²_S; zero away from that domain. -/
def coefficients {d N : ℕ} (L : Lattice d) (S : Fin N → SchrodingerOperator d)
    (T : SchrodingerOperator d) : Coefficients d N :=
  if h : ∃ c, HasHSSum (synthesisTerms L S c) T then Classical.choose h else fun _ => 0

/-- PDF pp.6–7: standard Riesz inequalities on all finite complex coefficients.
Constants precede every coefficient family; all operators are HS. -/
def IsHSRieszSequence {d : ℕ} {I : Type*} (f : I → SchrodingerOperator d) : Prop :=
  (∀ i, IsHS (f i)) ∧ ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
    ∀ c : I →₀ ℂ,
      a * (∑ i ∈ c.support, ‖c i‖ ^ 2) ≤ hilbertSchmidtNorm (∑ i ∈ c.support, c i • f i) ^ 2 ∧
      hilbertSchmidtNorm (∑ i ∈ c.support, c i • f i) ^ 2 ≤ b * (∑ i ∈ c.support, ‖c i‖ ^ 2)

/-- PDF pp.8–9,14: Riesz sequence, membership and l² completeness in V. -/
def IsHSRieszBasisFor {d : ℕ} {I : Type*} (V : Set (SchrodingerOperator d))
    (f : I → SchrodingerOperator d) : Prop :=
  IsHSRieszSequence f ∧ (∀ i, f i ∈ V) ∧
    ∀ T ∈ V, ∃ c : lp (fun _ : I => ℂ) 2, HasHSSum (fun i => c i • f i) T

/-- PDF pp.13–14: frame IN the specified HS space with convergent energy sums. -/
def IsHSFrameFor {d : ℕ} {I : Type*} (V : Set (SchrodingerOperator d))
    (f : I → SchrodingerOperator d) : Prop :=
  (∀ i, IsHS (f i) ∧ f i ∈ V) ∧
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ T ∈ V, IsHS T ∧
      Summable (fun i => ‖sourceHSPair T (f i)‖ ^ 2) ∧
      a * hilbertSchmidtNorm T ^ 2 ≤ ∑' i, ‖sourceHSPair T (f i)‖ ^ 2 ∧
      (∑' i, ‖sourceHSPair T (f i)‖ ^ 2) ≤ b * hilbertSchmidtNorm T ^ 2

/-- PDF pp.11–13: beta_A finite by a uniform finite quadratic upper bound. -/
def UpperStable {d M N : ℕ} (A : SamplingMatrix d M N) : Prop :=
  ∃ b : ℝ, 0 < b ∧ ∀ᵐ t ∂(volume : Measure (DualTorus d)),
    ∀ v : Fin N → ℂ,
      (∑ m, ‖(transfer A t).mulVec v m‖ ^ 2) ≤ b * (∑ n, ‖v n‖ ^ 2)

/-- PDF pp.11,13: alpha_A positive, without assuming an upper bound. -/
def LowerStable {d M N : ℕ} (A : SamplingMatrix d M N) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ᵐ t ∂(volume : Measure (DualTorus d)),
    ∀ v : Fin N → ℂ,
      a * (∑ n, ‖v n‖ ^ 2) ≤ ∑ m, ‖(transfer A t).mulVec v m‖ ^ 2

/-- PDF p.13, (7): positive essential lower AND finite essential upper bound. -/
def SamplingStable {d M N : ℕ} (A : SamplingMatrix d M N) : Prop :=
  LowerStable A ∧ UpperStable A

/-- PDF pp.13–14: one fixed reconstruction family for every input coefficient
tuple and its actual HS synthesis. The premise only identifies the input. -/
def Reconstructs {d M N : ℕ} (L : Lattice d) (S : Fin N → SchrodingerOperator d)
    (A : SamplingMatrix d M N) (H : Fin M → SchrodingerOperator d) : Prop :=
  (∀ m, H m ∈ samplingSpace L S) ∧
    ∀ (c : Coefficients d N) (T : SchrodingerOperator d),
      HasHSSum (synthesisTerms L S c) T →
        HasHSSum (fun i : Fin M × LatticeIndex d => samples A c i • translatedGenerators L H i) T

/-- PDF pp.7–8: physical average samples for Q anywhere in HS. -/
def averageSample {d : ℕ} (L : Lattice d) (Q T : SchrodingerOperator d)
    (k : LatticeIndex d) : ℂ :=
  sourceHSPair T (translateOperator (latticePoint L k) Q)

/-- PDF p.8: q(k)=<S,alpha_k(Q)>; Riesz plus Q in HS guarantees Memℓp.
The zero fallback is unused in averageSampling_exact. -/
def physicalKernel {d : ℕ} (L : Lattice d) (S Q : SchrodingerOperator d) : LatticeL2 d :=
  if h : Memℓp (averageSample L Q S) 2 then ⟨averageSample L Q S, h⟩ else 0

/-- PDF pp.8–9: the physical reconstruction of every T in V²_S. -/
def AverageReconstructs {d : ℕ} (L : Lattice d) (S Q H : SchrodingerOperator d) : Prop :=
  H ∈ samplingSpace L (fun _ : Fin 1 => S) ∧
    ∀ T ∈ samplingSpace L (fun _ : Fin 1 => S),
      HasHSSum (fun k => averageSample L Q T k • translateOperator (latticePoint L k) H) T

/-- PDF p.14: bounds on the MODULUS of the complex determinant.
Full-system boundedness remains a separate standing premise. -/
def DeterminantStable {d N : ℕ} (A : SamplingMatrix d N N) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ᵐ t ∂(volume : Measure (DualTorus d)),
    a ≤ ‖(transfer A t).det‖ ∧ ‖(transfer A t).det‖ ≤ b

/-- PDF pp.12–14: measurable essentially bounded entries of a matrix function. -/
def BoundedTransfer {d M N : ℕ}
    (B : DualTorus d → Matrix (Fin M) (Fin N) ℂ) : Prop :=
  ∀ m n, AEStronglyMeasurable (fun t => B t m n) (volume : Measure (DualTorus d)) ∧
    ∃ b : ℝ, 0 ≤ b ∧ ∀ᵐ t ∂(volume : Measure (DualTorus d)), ‖B t m n‖ ≤ b

/-- PDF p.12: (A-hat* A-hat)^(-1) A-hat* on the full-column-rank a.e. domain.
SamplingStable is required by the theorem; no singular inverse is treated as valid. -/
def transferPseudoInverse {d M N : ℕ} (A : SamplingMatrix d M N) (t : DualTorus d) :
    Matrix (Fin N) (Fin M) ℂ :=
  ((transfer A t).conjTranspose * transfer A t)⁻¹ * (transfer A t).conjTranspose

/-- PDF p.14: all bounded left inverses; the parameter C need not be unique. -/
def parametrizedInverse {d M N : ℕ} (A : SamplingMatrix d M N)
    (C : DualTorus d → Matrix (Fin N) (Fin M) ℂ) (t : DualTorus d) :
    Matrix (Fin N) (Fin M) ℂ :=
  transferPseudoInverse A t + C t * (1 - transfer A t * transferPseudoInverse A t)

/-- PDF pp.12–13: inverse Fourier column b_m of B-hat. -/
def inverseColumn {d M N : ℕ}
    (B : DualTorus d → Matrix (Fin N) (Fin M) ℂ) (m : Fin M) : Coefficients d N :=
  fun n => inverseLatticeFourier (torusL2 (fun t => B t n m))

/-- PDF pp.13–14: actual construction H_m=T_S b_m. -/
def reconstructionFamily {d M N : ℕ} (L : Lattice d) (S : Fin N → SchrodingerOperator d)
    (B : DualTorus d → Matrix (Fin N) (Fin M) ℂ) : Fin M → SchrodingerOperator d :=
  fun m => synthesize L S (inverseColumn B m)

/-- PDF pp.4–6: Euclidean coordinates on the actual 2d-dimensional phase space. -/
abbrev SymbolCoordinate (d : ℕ) := EuclideanSpace ℝ (Coordinate d)

/-- PDF p.5: phase-to-Euclidean identification, in position/frequency order. -/
def phaseEuclideanCoordinates {d : ℕ} (z : PhasePoint d) : SymbolCoordinate d :=
  WithLp.toLp 2 (QAlgorithms.Papers.Independent.Next46.P31.phaseCoordinates z)

/-- PDF p.5: inverse coordinate identification on phase space. -/
def coordinatesPhase {d : ℕ} (z : SymbolCoordinate d) : PhasePoint d :=
  (WithLp.toLp 2 (fun j => z (Sum.inl j)), WithLp.toLp 2 (fun j => z (Sum.inr j)))

/-- PDF p.4: phase L² with actual Lebesgue measure. -/
abbrev SymbolSpace (d : ℕ) := Lp ℂ 2 (volume : Measure (SymbolCoordinate d))

/-- PDF pp.4,6: take the L² equivalence class when it exists. Every use below
on Wigner functions, translations, or the orthogonal Fourier rotation is on
the MemLp domain; no existence is put in a Weyl-system record. -/
def phaseL2 {d : ℕ} (f : SymbolCoordinate d → ℂ) : SymbolSpace d :=
  if h : MemLp f 2 (volume : Measure (SymbolCoordinate d)) then h.toLp f else 0

/-- PDF p.4: actual cross-Wigner integral, including the conjugated second
factor, midpoint arguments, and negative 2pi frequency exponent. For L²
inputs the integral in t is absolutely integrable by Cauchy–Schwarz. -/
def crossWignerFunction {d : ℕ} (psi phi : Position d → ℂ)
    (z : SymbolCoordinate d) : ℂ :=
  ∫ t : Position d,
    psi ((coordinatesPhase z).1 + (1 / 2 : ℝ) • t) *
    conj (phi ((coordinatesPhase z).1 - (1 / 2 : ℝ) • t)) *
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      (∑ j, (coordinatesPhase z).2 j * t j : ℝ))

/-- PDF p.4: cross-Wigner L² class of actual L² vectors, without any angular
frequency rescaling. Representative changes give the same phase L² class. -/
def crossWigner {d : ℕ} (psi phi : EuclideanSchrodinger d) : SymbolSpace d :=
  phaseL2 (crossWignerFunction psi phi)

/-- PDF p.4: the defining weak Weyl pairing. Both source brackets are
first-linear, so both Mathlib pairings have reversed arguments. -/
def HasWeylSymbol {d : ℕ} (T : SchrodingerOperator d) (a : SymbolSpace d) : Prop :=
  ∀ phi psi : EuclideanSchrodinger d,
    inner ℂ psi (T phi) = inner ℂ (crossWigner psi phi) a

/-- PDF p.4: a_S selected by the explicit weak Wigner pairing. For every HS
operator the witness exists uniquely; no covariance, Gram bound, or isometry
property is part of the choice. Outside HS the default is irrelevant here. -/
def weylSymbol {d : ℕ} (T : SchrodingerOperator d) : SymbolSpace d :=
  if h : ∃ a, HasWeylSymbol T a then Classical.choose h else 0

/-- PDF p.4: L_a selected by the same weak pairing on ALL Schrödinger vectors.
Every phase L² symbol has a unique HS realization; no conclusion of a target
target is imposed as a field or a choice condition. -/
def weylOperator {d : ℕ} (a : SymbolSpace d) : SchrodingerOperator d :=
  if h : ∃ T : SchrodingerOperator d, IsHS T ∧ HasWeylSymbol T a then Classical.choose h else 0

/-- PDF pp.5–7: ordinary symbol translation by an actual phase point. -/
def translateSymbol {d : ℕ} (z : PhasePoint d) (a : SymbolSpace d) : SymbolSpace d :=
  phaseL2 (fun y => a (y - phaseEuclideanCoordinates z))

/-- PDF pp.7–8,13: the actual symbol synthesis T_(a_S)c. Under the source's
Riesz hypotheses this tsum is summable; it is not a freely supplied symbol. -/
def symbolSynthesis {d N : ℕ} (L : Lattice d) (S : Fin N → SchrodingerOperator d)
    (c : Coefficients d N) : SymbolSpace d :=
  ∑' i : Fin N × LatticeIndex d,
    c i.1 i.2 • translateSymbol (latticePoint L i.2) (weylSymbol (S i.1))

/-- PDF p.6: J(x,w)=(w,-x), so <Jz,z'>=sigma(z,z'). -/
def symplecticRotation {d : ℕ} (z : SymbolCoordinate d) : SymbolCoordinate d :=
  WithLp.toLp 2 (Sum.elim (fun j => z (Sum.inr j)) (fun j => -z (Sum.inl j)))

/-- PDF p.6: F_sigma a(z)=F a(Jz), using Mathlib's continuous L² Plancherel
extension with exp(-2pi i <.,.>), then a measure-preserving orthogonal rotation.
It is not the total Bochner integral of a merely L² symbol. -/
def symplecticFourier {d : ℕ} (a : SymbolSpace d) : SymbolSpace d :=
  phaseL2 (fun z => (Lp.fourierTransformₗᵢ (SymbolCoordinate d) ℂ a) (symplecticRotation z))

/-- PDF p.6 and cited [24], Section 3.2: Gaussian-window STFT of a phase symbol.
The nonzero Gaussian normalization does not change S_0 membership. The inner
integral is absolutely integrable for every (u,v), by L² Cauchy–Schwarz. -/
def symbolSTFT {d : ℕ} (a : SymbolSpace d) (u v : SymbolCoordinate d) : ℂ :=
  ∫ y : SymbolCoordinate d,
    a y * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (∑ j, v j * y j : ℝ)) *
      (Real.exp (-Real.pi * ‖y - u‖ ^ 2) : ℂ)

/-- PDF p.6: Feichtinger algebra S_0 on phase space, by integrable STFT.
The outer integral is guarded by Integrable, avoiding a zero-default test. -/
def InFeichtinger {d : ℕ} (a : SymbolSpace d) : Prop :=
  Integrable (fun uv : SymbolCoordinate d × SymbolCoordinate d =>
    ‖symbolSTFT a uv.1 uv.2‖) volume

/-- PDF p.6: the source's class B, on actual HS operators and actual symbols.
This hypothesis is used ONLY for the pointwise refinement. -/
def InOperatorB {d : ℕ} (T : SchrodingerOperator d) : Prop :=
  IsHS T ∧ InFeichtinger (weylSymbol T)

/-- PDF p.6: FW(S)(x,w)=exp(-pi i x.w) tr(pi(-z) S).
On B the operator is trace class, so the accepted basis trace converges. -/
def fourierWigner {d : ℕ} (T : SchrodingerOperator d) (z : SymbolCoordinate d) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * Complex.I *
      (∑ j, (coordinatesPhase z).1 j * (coordinatesPhase z).2 j : ℝ)) *
    QAlgorithms.Papers.Independent.Next46.P02.basisOperatorTrace
      ((timeFrequencyShift (-(coordinatesPhase z))).comp T)

/-- PDF p.5: actual adjoint lattice, represented as its phase-coordinate subtype. -/
def AdjointLattice {d : ℕ} (L : Lattice d) :=
  {z : SymbolCoordinate d // ∀ k : LatticeIndex d,
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (symplectic (coordinatesPhase z) (latticePoint L k) : ℝ)) = 1}

/-- PDF p.6: periodized symbol Gram entries v_n conjugate(v_n'), with NO
covolume prefactor. For L² symbols the sums converge absolutely a.e. -/
def symbolGram {d N : ℕ} (L : Lattice d) (S : Fin N → SchrodingerOperator d)
    (z : SymbolCoordinate d) : Matrix (Fin N) (Fin N) ℂ :=
  fun n nprime => ∑' k : AdjointLattice L,
    symplecticFourier (weylSymbol (S n)) (z + k.val) *
      conj (symplecticFourier (weylSymbol (S nprime)) (z + k.val))

/-- PDF pp.6–7: periodized Fourier-Wigner Gram entries. On B the continuous
representatives and absolute summability make this a pointwise definition. -/
def wignerGram {d N : ℕ} (L : Lattice d) (S : Fin N → SchrodingerOperator d)
    (z : SymbolCoordinate d) : Matrix (Fin N) (Fin N) ℂ :=
  fun n nprime => ∑' k : AdjointLattice L,
    fourierWigner (S n) (z + k.val) * conj (fourierWigner (S nprime) (z + k.val))

/-- PDF p.7: Hermitian quadratic-form bounds in the Euclidean vector norm.
The matrices at issue are Gram matrices, hence Hermitian on their domains. -/
def GramBounds {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (a b : ℝ) : Prop :=
  ∀ v : Fin N → ℂ,
    a * (∑ n, ‖v n‖ ^ 2) ≤ (∑ n, conj (v n) * G.mulVec v n).re ∧
    (∑ n, conj (v n) * G.mulVec v n).re ≤ b * (∑ n, ‖v n‖ ^ 2)

/-- PDF pp.13–14: the source's Weyl-symbol part of H_m=T_S b_m=L_(T_(a_S)b_m). -/
def ConstructedWithSymbols {d M N : ℕ} (L : Lattice d) (S : Fin N → SchrodingerOperator d)
    (B : DualTorus d → Matrix (Fin N) (Fin M) ℂ) : Prop :=
  ∀ m, let h := symbolSynthesis L S (inverseColumn B m)
    weylSymbol (reconstructionFamily L S B m) = h ∧
      reconstructionFamily L S B m = weylOperator h

example {d : ℕ} (phi : Position d → ℂ) (z : SymbolCoordinate d) :
    crossWignerFunction (fun _ => 0) phi z = 0 := by
  simp [crossWignerFunction]

example {d : ℕ} : symplecticRotation (0 : SymbolCoordinate d) = 0 := by
  ext j
  cases j <;> simp [symplecticRotation]

example {d : ℕ} : shiftAction (0 : PhasePoint d) = fun f => f := by
  funext f t
  simp [shiftAction]

example {d : ℕ} : timeFrequencyShift (0 : PhasePoint d) = ContinuousLinearMap.id ℂ (EuclideanSchrodinger d) := by
  have hex : ∃ U : SchrodingerOperator d, ∀ f : EuclideanSchrodinger d,
      (U f : Position d → ℂ) =ᵐ[volume] shiftAction (0 : PhasePoint d) f := by
    refine ⟨ContinuousLinearMap.id ℂ (EuclideanSchrodinger d), ?_⟩
    intro f
    filter_upwards [] with x
    simp [shiftAction]
  rw [timeFrequencyShift, dif_pos hex]
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [Classical.choose_spec hex f] with x hx
  simpa [shiftAction] using hx

example {d : ℕ} : hilbertSchmidtNorm (0 : SchrodingerOperator d) = 0 := by
  simp [hilbertSchmidtNorm]

example {d : ℕ} (L : Lattice d) : latticePoint L 0 = 0 := by
  have hzero : (fun j : Coordinate d => ((0 : LatticeIndex d) j : ℝ)) =
      (0 : Coordinate d → ℝ) := by
    funext j
    exact Int.cast_zero
  unfold latticePoint
  rw [hzero]
  exact map_zero L

example {d : ℕ} (c : LatticeL2 d) : inverseLatticeFourier (latticeFourier c) = c := by
  exact (UnitAddTorus.mFourierBasis (d := Coordinate d)).repr.apply_symm_apply c

example {d : ℕ} (c : LatticeL2 d) (k : LatticeIndex d) :
    latticeConvolution (0 : LatticeL2 d) c k = 0 := by
  simp [latticeConvolution]

example {d : ℕ} (A : SamplingMatrix d 1 1) (t : DualTorus d) :
    parametrizedInverse A (fun _ => 0) t = transferPseudoInverse A t := by
  simp [parametrizedInverse]

end QAlgorithms.Papers.Independent.Renew46.P05


