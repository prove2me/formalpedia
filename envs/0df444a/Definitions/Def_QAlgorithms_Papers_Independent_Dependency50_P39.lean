-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
-- name    : QAlgorithms_Papers_Independent_Dependency50_P39
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:23:55.848008+00:00
-- url     : https://prove2.me/theorems/278cbe89-a37f-4460-ae98-438f3fb44512
-- title:
--   Definitions for Operator-sum Representation for Bosonic Gaussian Channels
-- statement:
--   The objects the formalized statements of *Operator-sum Representation for Bosonic Gaussian Channels* (arXiv:1012.4266) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Fock`: The single-mode Fock space, PDF pp.1–4, with no energy cutoff.
--   - `FockOperator`: Bounded complex-linear operators on the complete oscillator space, PDF p.3. This alias reuses Mathlib ContinuousLinearMap on lp. The pinned Operator aliases use matrices, so they do not denote this infinite-dimensional type.
--   - `fockKet`: The norm-one Fock fockKet |n>, PDF p.4. Unlike frozen QAlgorithms.ket : EuclideanSpace, this basis vector lies in the countable lp Hilbert space; reuse the Mathlib lp.single construction.
--   - `fockDyad`: The bounded matrix unit |m><n|, PDF pp.4,7. Reuse Mathlib rankOne on lp; the pinned dyad returns a coordinate matrix on EuclideanSpace, not a bounded operator on countable Fock space.
--   - `HasFockMatrix`: Fock coefficients, with the row as output and column as input, PDF p.4 Eq.(2.4). Since the kets form a total orthonormal system, at most one bounded operator has these coefficients. The coordinate is <m|A|n>, with conjugation on the bra.
--   - `operatorOfMatrix`: Realize a coefficient array as its unique bounded operator when possible. The zero fallback is never silently used: each result involving the infinite weighted shifts concludes HasFockMatrix for every participating operator. Source: PDF pp.14,19 Eqs.(4.6),(5.5).
--   - `phaseCoefficient`: The coefficient of |ell-n><n| in Eq.(3.11), PDF p.6; only n≤ell is used.
--   - `phaseKraus`: Eq.(3.11), PDF p.6: an actual finite sum of bounded dyads, on the infinite Fock space. At k=0 the separately specified vacuum-replacer family is used; no reciprocal formula at k=0 is claimed.
--   - `attenuatorMatrix`: Eq.(4.6), PDF p.14: the coefficients of the bounded lowering shift. The formula includes B_ell(0)=|0><ell| and the identity endpoint k=1.
--   - `attenuatorKraus`: The actual bounded lowering shift of Eq.(4.6), PDF p.14. Every theorem using it includes its matrix-realization conclusion.
--   - `amplifierMatrix`: Eq.(5.5), PDF p.19: coefficients of the raising shift, including k⁻¹. At k=1, A_0=I and the other indexed operators are zero.
--   - `amplifierKraus`: The actual bounded raising shift of Eq.(5.5), PDF p.19.
--   - `AttenuatorRealized`: Bounded realization of every displayed attenuator coefficient, PDF p.14. This is a theorem conclusion, never an assumption standing in for boundedness.
--   - `AmplifierRealized`: Bounded realization of every displayed amplifier coefficient, PDF p.19.
--   - `StrongHasSum`: Pointwise norm convergence on every Hilbert vector: strong operator summation. PDF pp.7,19 Eqs.(3.12),(5.6). The identity is a bounded operator, not a density.
--   - `KrausComplete`: Countable Kraus normalization in the strong topology, PDF p.3 Eq.(1.4).
--   - `NuclearExpansion`: A nuclear expansion of an operator as sum |u_r><v_r| with summable products of Hilbert norms. This is exactly trace class on a Hilbert space, without an energy or finite-rank restriction. Source concept: PDF pp.1–4; the same nuclear criterion was checked in the pinned accepted P51 source at lines 28–32. HasSum here is operator-norm convergence; norm-product summability also gives trace-norm convergence of the nuclear expansion.
--   - `IsTraceClass`: Trace-class bounded operators on the full oscillator space, PDF pp.1–4.
--   - `IsDensity`: Normalized positive trace-class density operators, PDF pp.1–4. Hermiticity and nonnegative quadratic forms express positivity. The trace is the absolutely convergent Fock-diagonal sum. No moment or finite-energy hypothesis is imposed, and no expression applies a trace-class map to the identity.
--   - `nuclearTraceNorm`: Nuclear (trace) norm, as the infimum of nuclear expansion costs. On IsTraceClass its defining set is nonempty and bounded below by zero. Outside trace class this total expression is not used as a norm. Source topology for the operator sums: PDF p.3 Eq.(1.4). The frozen QAlgorithms.traceNorm accepts finite matrices. This nuclear expansion norm instead applies to bounded operators on an arbitrary Hilbert space.
--   - `TraceHasSum`: Unconditional trace-norm summation, over the directed finite subsets of the index type. Domain guards on every difference prevent the empty-infimum default from giving spurious convergence. PDF p.3 Eq.(1.4), p.4 Eqs.(2.2)–(2.4).
--   - `krausTerm`: Kraus action on an operator, PDF p.3 Eq.(1.4); the summation is separate.
--   - `KrausWellDefined`: A normalized Kraus family with a trace-class output sum for every trace-class input, including nonpositive operators. These are conclusions in the theorems. No characteristic-function law is included or assumed. PDF pp.3–4.
--   - `KrausEquivalent`: Equality of two Kraus maps on all trace-class operators, through their common trace-norm sum. Normalization and convergence are included, rather than presumed. PDF pp.7,17,19,23,32–33.
--   - `BipartiteFock`: A countably infinite reference register and oscillator, PDF pp.12,16,22. A countable reference suffices for the operational EB test: every density on an arbitrary reference tensor a separable oscillator has separable support on its reference factor. No restriction to unentangled or Gaussian inputs is imposed.
--   - `BipartiteOperator`: Bounded operators on reference tensor oscillator.
--   - `bipartiteKet`: The product Fock basis, with reference first.
--   - `IsBipartiteDensity`: Bipartite normalized positive trace-class densities, without energy bounds.
--   - `IsSeparable`: The trace-norm closed convex hull of product densities, i.e. separability. The product operators are specified by all of their Fock coefficients; they are bounded operators, not arbitrary coefficient arrays. PDF pp.12,16,22, using the standard operational meaning of entanglement breaking.
--   - `IsCountableEntanglementBreaking`: Operational entanglement breaking for a countable Kraus representation. The bounded reference ampliation is specified independently by its matrix; every bipartite density must have a separable trace-norm output sum. This is not an assumption of rank-one Kraus representability. PDF pp.12,16,22. Generalized continuous rank-one representations are not excluded by this test. Frozen Entanglement.IsEntanglementBreaking acts on qubit matrices. This countable-oscillator predicate uses normal bipartite densities and trace-norm closed separability, preserving the source domain rather than truncating it.
--   - `coherentCoefficient`: Normalized coherent-state coefficients, PDF p.12 Eq.(3.41).
--   - `coherentKet`: The unique square-summable coherent vector. Every theorem using classicality concludes CoherentRealized, so the total-function fallback is never used to manufacture a state or a Husimi zero. PDF pp.12–13.
--   - `CoherentRealized`: All coherent coefficients and unit norms are established as conclusions, not assumed. PDF p.12 Eq.(3.41).
--   - `coherentProjector`: The coherent projector |alpha><alpha|, PDF pp.13–15.
--   - `husimiQ`: The Husimi Q function <alpha|rho|alpha>, with no pi factor, PDF p.20. It is real on densities; the real part gives its scalar value.
--   - `coherentMeasure`: The source's planar measure d²alpha/pi, PDF pp.13–14,20.
--   - `IsClassical`: A positive probability-measure coherent-state mixture. Singular measures, including Dirac masses, are allowed. The matrix integral is genuine: every coefficient integrand is integrable and the represented operator is a density. PDF pp.9,13,15,21; the measure formulation retains the source's classical states.
--   - `IsPositivePWeight`: A nonnegative normalized P density with respect to d²alpha/pi. This predicate is used for the smooth output weight in (3.24),(3.43), not as a restriction on the generalized diagonal weight of arbitrary input states.
--   - `coherentPhaseKraus`: The distinct square-root denominators and conjugated bra of (3.42), PDF p.13.
--   - `displacementMatrix`: Finite normal-ordered expression for <m|D(z)|n>, equivalent to the Laguerre formula (3.15), PDF p.7. Its m=0,n=1 entry has the -conjugate(z) sign.
--   - `displacement`: Actual bounded Weyl displacement selected by all its Fock entries. Every Weyl-semantic theorem concludes DisplacementRealized, including unitarity and all trace-pairing convergence guards. PDF pp.7–9 Eq.(3.15).
--   - `fockTrace`: The trace of a trace-class operator in the Fock basis. It is used only with nuclearity and diagonal summability supplied as conclusions. PDF p.7.
--   - `characteristic`: Weyl characteristic function tr[D(z)X], with the source ordering and sign. No total exponential of an unbounded creation/annihilation operator is used. PDF pp.7–9 Eqs.(3.14)–(3.15).
--   - `DisplacementRealized`: Every displacement is its actual unitary realization, and the nuclear trace pairing is well defined for all trace-class inputs. All these facts are conclusions of Weyl-semantic targets, never assumed transformation laws.
--   - `thermalMatrix`: Thermal density coefficients, PDF p.10 Eq.(3.30), for finite a>=1.
--   - `thermalDensity`: The actual thermal operator, with matrix realization and density asserted in every applicable theorem. No formal infinite-temperature endpoint is used.
--   - `poissonMatrix`: Poissonian phase-averaged coherent input, PDF p.12 Eq.(3.38), lambda>=0.
--   - `poissonDensity`: The phase-averaged coherent density, with no finite support cutoff.
--   - `ThermalRealized`: A normalized bounded realization of the thermal state, PDF p.10 Eq.(3.30).
--   - `PoissonRealized`: A normalized bounded realization of the Poisson density, PDF p.12 Eq.(3.38).
--   - `photonProbability`: Photon-number probabilities and first/second moments for densities. Moment uses below are explicitly guarded by Summable. PDF pp.12,16,22.
--   - `photonMean`: The finite first photon-number moment when summable, PDF pp.12,16,22.
--   - `photonVariance`: The second moment minus the square of the first moment; used only on densities with summable first and second moments. PDF pp.12,22.
--   - `SuperPoissonian`: Strict super-Poissonian photon statistics, including genuine moments. No undefined infinite-moment tsum default can satisfy this predicate.
--   - `attenuatorDyadOutput`: The exact finite Fock-fockDyad attenuator output of (4.11), PDF p.15.
--   - `amplifierDyadCoefficient`: The coefficient of the ell-th amplifier fockDyad term, PDF p.20 Eq.(5.13).
--   - `amplifierDyadMatrix`: Amplifier fockDyad output coefficients, each entry involving at most one ell. The object is computed from the source data; boundedness is a conclusion.
--   - `amplifierDyadOutput`: The operator specified by the infinite series (5.13), PDF p.20.
--   - `phaseFockMatrix`: Exact Fock-input phase-conjugator output weights, PDF p.12 Eq.(3.37).
--   - `phaseFockOutput`: The source's Fock-input output, computed before any output property.
--   - `phasePoissonTerm`: The j-th term of the Poisson-averaged output diagonal series (3.39), p.12.
--   - `phasePoissonMatrix`: Phase-conjugator Poisson-input output coefficients, PDF p.12 Eq.(3.39). The theorem also concludes summability of every defining scalar series.
--   - `phasePoissonOutput`: The exact Poisson-input output operator of Eq.(3.39), p.12.
--   - `amplifierPoissonMatrix`: The normalized finite-sum output of a Poissonian amplifier input. PDF p.22 Eq.(5.23) omits the k^-2 prefactor; Eq.(5.22), which it substitutes, requires the factor included here. Independent moderation is required.
--   - `amplifierPoissonOutput`: The normalized operator computed from (5.22) and the Poisson input.
--   - `attenuatorThermalParameter`: Exact thermal parameter update of attenuation, PDF p.16 Eq.(4.18).
--   - `productKraus`: Cartesian product Kraus indices; the first factor acts after the second. PDF pp.30–33, all seven composition subsections.
--   - `iteratedKraus`: Finite iteration with a fresh vacuum environment at each step, PDF pp.18,24. The unique empty index sequence gives the identity operator.
--   - `FockDiagonalEffect`: Simultaneous Fock diagonality of the positive effects W†W, PDF p.34. Only off-diagonal matrix entries are required to vanish; no eigenbasis for position generalized kets is postulated.
--   - `DiscreteFamily`: The discrete canonical families with their exact parameter domains. The identity and vacuum-replacer endpoints are included for effects/iteration. PDF pp.2,6,14,19,34.
--   - `discreteKraus`: The source's explicit Kraus family for each discrete canonical parameter.
--   - `DiscreteRealized`: Realization guard for the displayed infinite shifts; phase Kraus operators are already literal finite sums of bounded dyads. PDF pp.6,14,19.
-- source:
--   Operator-sum Representation for Bosonic Gaussian Channels, arXiv:1012.4266v1, https://arxiv.org/abs/1012.4266v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters

/-!
Paper-local operator interfaces for arXiv:1012.4266v1.
The Hilbert space is the full countable oscillator space. All theorem proofs are
intentionally omitted. The discrete characteristic laws are targeted explicitly.
General metaplectic, singular-instrument and ambient-channel extremality results
are deferred in the unit artifacts; they are not assumptions of this module.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P39

open Filter MeasureTheory
open scoped Topology

attribute [local instance] Classical.propDecidable

/-- The single-mode Fock space, PDF pp.1–4, with no energy cutoff. -/
abbrev Fock := QAlgorithms.RealRegisters.Hilbert ℕ

/-- Bounded complex-linear operators on the complete oscillator space, PDF p.3. 
This alias reuses Mathlib ContinuousLinearMap on lp. The pinned Operator
aliases use matrices, so they do not denote this infinite-dimensional type.
-/
abbrev FockOperator := Fock →L[ℂ] Fock

/-- The norm-one Fock fockKet |n>, PDF p.4. 
Unlike frozen QAlgorithms.ket : EuclideanSpace, this basis vector lies
in the countable lp Hilbert space; reuse the Mathlib lp.single construction.
-/
def fockKet (n : ℕ) : Fock := lp.single 2 n 1

/-- The bounded matrix unit |m><n|, PDF pp.4,7. 
Reuse Mathlib rankOne on lp; the pinned dyad returns a coordinate
matrix on EuclideanSpace, not a bounded operator on countable Fock space.
-/
def fockDyad (m n : ℕ) : FockOperator := InnerProductSpace.rankOne ℂ (fockKet m) (fockKet n)

/-- Fock coefficients, with the row as output and column as input, PDF p.4 Eq.(2.4).
Since the kets form a total orthonormal system, at most one bounded operator has
these coefficients. The coordinate is <m|A|n>, with conjugation on the bra. -/
def HasFockMatrix (A : FockOperator) (K : ℕ → ℕ → ℂ) : Prop :=
  ∀ m n, A (fockKet n) m = K m n

/-- Realize a coefficient array as its unique bounded operator when possible.
The zero fallback is never silently used: each result involving the infinite
weighted shifts concludes HasFockMatrix for every participating operator.
Source: PDF pp.14,19 Eqs.(4.6),(5.5). -/
def operatorOfMatrix (K : ℕ → ℕ → ℂ) : FockOperator :=
  if h : ∃ A : FockOperator, HasFockMatrix A K then Classical.choose h else 0

/-- The coefficient of |ell-n><n| in Eq.(3.11), PDF p.6; only n≤ell is used. -/
def phaseCoefficient (k : ℝ) (ell n : ℕ) : ℂ :=
  ((Real.sqrt (1 + k ^ 2))⁻¹ ^ (n + 1) *
    (Real.sqrt (1 + (k⁻¹) ^ 2))⁻¹ ^ (ell - n) *
    Real.sqrt (Nat.choose ell n : ℝ) : ℝ)

/-- Eq.(3.11), PDF p.6: an actual finite sum of bounded dyads, on the infinite
Fock space. At k=0 the separately specified vacuum-replacer family is used;
no reciprocal formula at k=0 is claimed. -/
def phaseKraus (k : ℝ) (ell : ℕ) : FockOperator :=
  if k = 0 then fockDyad 0 ell else
    ∑ n ∈ Finset.range (ell + 1), phaseCoefficient k ell n • fockDyad (ell - n) n

/-- Eq.(4.6), PDF p.14: the coefficients of the bounded lowering shift.
The formula includes B_ell(0)=|0><ell| and the identity endpoint k=1. -/
def attenuatorMatrix (k : ℝ) (ell m n : ℕ) : ℂ :=
  if n = m + ell then
    (Real.sqrt (Nat.choose (m + ell) ell : ℝ) *
      Real.sqrt (1 - k ^ 2) ^ ell * k ^ m : ℝ) else 0

/-- The actual bounded lowering shift of Eq.(4.6), PDF p.14.
Every theorem using it includes its matrix-realization conclusion. -/
def attenuatorKraus (k : ℝ) (ell : ℕ) : FockOperator :=
  operatorOfMatrix (attenuatorMatrix k ell)

/-- Eq.(5.5), PDF p.19: coefficients of the raising shift, including k⁻¹.
At k=1, A_0=I and the other indexed operators are zero. -/
def amplifierMatrix (k : ℝ) (ell m n : ℕ) : ℂ :=
  if m = n + ell then
    (k⁻¹ * Real.sqrt (Nat.choose (n + ell) ell : ℝ) *
      Real.sqrt (1 - (k⁻¹) ^ 2) ^ ell * (k⁻¹) ^ n : ℝ) else 0

/-- The actual bounded raising shift of Eq.(5.5), PDF p.19. -/
def amplifierKraus (k : ℝ) (ell : ℕ) : FockOperator :=
  operatorOfMatrix (amplifierMatrix k ell)

/-- Bounded realization of every displayed attenuator coefficient, PDF p.14.
This is a theorem conclusion, never an assumption standing in for boundedness. -/
def AttenuatorRealized (k : ℝ) : Prop :=
  ∀ ell, HasFockMatrix (attenuatorKraus k ell) (attenuatorMatrix k ell)

/-- Bounded realization of every displayed amplifier coefficient, PDF p.19. -/
def AmplifierRealized (k : ℝ) : Prop :=
  ∀ ell, HasFockMatrix (amplifierKraus k ell) (amplifierMatrix k ell)

/-- Pointwise norm convergence on every Hilbert vector: strong operator summation.
PDF pp.7,19 Eqs.(3.12),(5.6). The identity is a bounded operator, not a density. -/
def StrongHasSum {I : Type*} (K : I → FockOperator) (A : FockOperator) : Prop :=
  ∀ v : Fock, HasSum (fun i => K i v) (A v)

/-- Countable Kraus normalization in the strong topology, PDF p.3 Eq.(1.4). -/
def KrausComplete {I : Type*} (K : I → FockOperator) : Prop :=
  StrongHasSum (fun i => (ContinuousLinearMap.adjoint (K i)).comp (K i)) 1

/-- A nuclear expansion of an operator as sum |u_r><v_r| with summable products
of Hilbert norms. This is exactly trace class on a Hilbert space, without an
energy or finite-rank restriction. Source concept: PDF pp.1–4; the same nuclear
criterion was checked in the pinned accepted P51 source at lines 28–32.
HasSum here is operator-norm convergence; norm-product summability also gives
trace-norm convergence of the nuclear expansion. -/
def NuclearExpansion {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (X : H →L[ℂ] H) (u v : ℕ → H) : Prop :=
  Summable (fun r => ‖u r‖ * ‖v r‖) ∧
    HasSum (fun r => InnerProductSpace.rankOne ℂ (u r) (v r)) X

/-- Trace-class bounded operators on the full oscillator space, PDF pp.1–4. -/
def IsTraceClass {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (X : H →L[ℂ] H) : Prop :=
  ∃ u v : ℕ → H, NuclearExpansion X u v

/-- Normalized positive trace-class density operators, PDF pp.1–4.
Hermiticity and nonnegative quadratic forms express positivity. The trace is the
absolutely convergent Fock-diagonal sum. No moment or finite-energy hypothesis
is imposed, and no expression applies a trace-class map to the identity. -/
def IsDensity (X : FockOperator) : Prop :=
  IsTraceClass X ∧ ContinuousLinearMap.adjoint X = X ∧
    (∀ u : Fock, 0 ≤ (inner (𝕜 := ℂ) u (X u)).re) ∧
    Summable (fun n : ℕ => X (fockKet n) n) ∧
    (∑' n : ℕ, X (fockKet n) n) = 1

/-- Nuclear (trace) norm, as the infimum of nuclear expansion costs.
On IsTraceClass its defining set is nonempty and bounded below by zero.
Outside trace class this total expression is not used as a norm.
Source topology for the operator sums: PDF p.3 Eq.(1.4). 
The frozen QAlgorithms.traceNorm accepts finite matrices. This nuclear
expansion norm instead applies to bounded operators on an arbitrary Hilbert space.
-/
def nuclearTraceNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (X : H →L[ℂ] H) : ℝ :=
  sInf {c : ℝ | ∃ u v : ℕ → H,
    NuclearExpansion X u v ∧ c = ∑' r, ‖u r‖ * ‖v r‖}

/-- Unconditional trace-norm summation, over the directed finite subsets of the
index type. Domain guards on every difference prevent the empty-infimum default
from giving spurious convergence. PDF p.3 Eq.(1.4), p.4 Eqs.(2.2)–(2.4). -/
def TraceHasSum {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (f : I → (H →L[ℂ] H)) (Y : H →L[ℂ] H) : Prop :=
  IsTraceClass Y ∧
    (∀ s : Finset I, IsTraceClass (∑ i ∈ s, f i)) ∧
    (∀ s : Finset I, IsTraceClass ((∑ i ∈ s, f i) - Y)) ∧
    Tendsto (fun s : Finset I => nuclearTraceNorm ((∑ i ∈ s, f i) - Y)) atTop (nhds 0)

/-- Kraus action on an operator, PDF p.3 Eq.(1.4); the summation is separate. -/
def krausTerm (A X : FockOperator) : FockOperator :=
  (A.comp X).comp (ContinuousLinearMap.adjoint A)

/-- A normalized Kraus family with a trace-class output sum for every trace-class
input, including nonpositive operators. These are conclusions in the theorems.
No characteristic-function law is included or assumed. PDF pp.3–4. -/
def KrausWellDefined {I : Type*} (K : I → FockOperator) : Prop :=
  KrausComplete K ∧ ∀ X : FockOperator, IsTraceClass X →
    ∃ Y : FockOperator, TraceHasSum (fun i => krausTerm (K i) X) Y

/-- Equality of two Kraus maps on all trace-class operators, through their common
trace-norm sum. Normalization and convergence are included, rather than presumed.
PDF pp.7,17,19,23,32–33. -/
def KrausEquivalent {I J : Type*} (K : I → FockOperator) (L : J → FockOperator) : Prop :=
  KrausWellDefined K ∧ KrausWellDefined L ∧
    ∀ X : FockOperator, IsTraceClass X → ∃ Y : FockOperator,
      TraceHasSum (fun i => krausTerm (K i) X) Y ∧
      TraceHasSum (fun j => krausTerm (L j) X) Y

/-- A countably infinite reference register and oscillator, PDF pp.12,16,22.
A countable reference suffices for the operational EB test: every density on an
arbitrary reference tensor a separable oscillator has separable support on its
reference factor. No restriction to unentangled or Gaussian inputs is imposed. -/
abbrev BipartiteFock := QAlgorithms.RealRegisters.Hilbert (ℕ × ℕ)

/-- Bounded operators on reference tensor oscillator. -/
abbrev BipartiteOperator := BipartiteFock →L[ℂ] BipartiteFock

/-- The product Fock basis, with reference first. -/
def bipartiteKet (p : ℕ × ℕ) : BipartiteFock := lp.single 2 p 1

/-- Bipartite normalized positive trace-class densities, without energy bounds. -/
def IsBipartiteDensity (X : BipartiteOperator) : Prop :=
  IsTraceClass X ∧ ContinuousLinearMap.adjoint X = X ∧
    (∀ u : BipartiteFock, 0 ≤ (inner (𝕜 := ℂ) u (X u)).re) ∧
    Summable (fun p : ℕ × ℕ => X (bipartiteKet p) p) ∧
    (∑' p : ℕ × ℕ, X (bipartiteKet p) p) = 1

/-- The trace-norm closed convex hull of product densities, i.e. separability.
The product operators are specified by all of their Fock coefficients; they
are bounded operators, not arbitrary coefficient arrays. PDF pp.12,16,22,
using the standard operational meaning of entanglement breaking. -/
def IsSeparable (Y : BipartiteOperator) : Prop :=
  IsBipartiteDensity Y ∧ ∀ eps : ℝ, 0 < eps →
    ∃ (d : ℕ) (p : Fin d → ℝ) (R S : Fin d → FockOperator)
      (V : Fin d → BipartiteOperator),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      (∀ i, IsDensity (R i) ∧ IsDensity (S i)) ∧
      (∀ i a b m n, V i (bipartiteKet (b, n)) (a, m) =
        R i (fockKet b) a * S i (fockKet n) m) ∧
      IsTraceClass (Y - ∑ i, (p i : ℂ) • V i) ∧
      nuclearTraceNorm (Y - ∑ i, (p i : ℂ) • V i) < eps

/-- Operational entanglement breaking for a countable Kraus representation.
The bounded reference ampliation is specified independently by its matrix;
every bipartite density must have a separable trace-norm output sum.
This is not an assumption of rank-one Kraus representability. PDF pp.12,16,22.
Generalized continuous rank-one representations are not excluded by this test. 
Frozen Entanglement.IsEntanglementBreaking acts on qubit matrices.
This countable-oscillator predicate uses normal bipartite densities and trace-norm
closed separability, preserving the source domain rather than truncating it.
-/
def IsCountableEntanglementBreaking (K : ℕ → FockOperator) : Prop :=
  ∃ L : ℕ → BipartiteOperator,
    (∀ ell a b m n, L ell (bipartiteKet (b, n)) (a, m) =
      if a = b then K ell (fockKet n) m else 0) ∧
    ∀ X : BipartiteOperator, IsBipartiteDensity X →
      ∃ Y : BipartiteOperator,
        TraceHasSum (fun ell => ((L ell).comp X).comp
          (ContinuousLinearMap.adjoint (L ell))) Y ∧ IsSeparable Y

/-- Normalized coherent-state coefficients, PDF p.12 Eq.(3.41). -/
def coherentCoefficient (alpha : ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-Complex.normSq alpha / 2) : ℂ) * alpha ^ n /
    (Real.sqrt (Nat.factorial n : ℝ) : ℂ)

/-- The unique square-summable coherent vector. Every theorem using classicality
concludes CoherentRealized, so the total-function fallback is never used to
manufacture a state or a Husimi zero. PDF pp.12–13. -/
def coherentKet (alpha : ℂ) : Fock :=
  if h : ∃ u : Fock, ∀ n, u n = coherentCoefficient alpha n then
    Classical.choose h else 0

/-- All coherent coefficients and unit norms are established as conclusions,
not assumed. PDF p.12 Eq.(3.41). -/
def CoherentRealized : Prop :=
  ∀ alpha : ℂ, (∀ n, coherentKet alpha n = coherentCoefficient alpha n) ∧
    ‖coherentKet alpha‖ = 1

/-- The coherent projector |alpha><alpha|, PDF pp.13–15. -/
def coherentProjector (alpha : ℂ) : FockOperator :=
  InnerProductSpace.rankOne ℂ (coherentKet alpha) (coherentKet alpha)

/-- The Husimi Q function <alpha|rho|alpha>, with no pi factor, PDF p.20.
It is real on densities; the real part gives its scalar value. -/
def husimiQ (X : FockOperator) (alpha : ℂ) : ℝ :=
  (inner (𝕜 := ℂ) (coherentKet alpha) (X (coherentKet alpha))).re

/-- The source's planar measure d²alpha/pi, PDF pp.13–14,20. -/
def coherentMeasure : Measure ℂ :=
  ENNReal.ofReal (1 / Real.pi) • volume

/-- A positive probability-measure coherent-state mixture. Singular measures,
including Dirac masses, are allowed. The matrix integral is genuine: every
coefficient integrand is integrable and the represented operator is a density.
PDF pp.9,13,15,21; the measure formulation retains the source's classical states. -/
def IsClassical (X : FockOperator) : Prop :=
  IsDensity X ∧ ∃ mu : Measure ℂ, IsProbabilityMeasure mu ∧
    ∀ m n : ℕ,
      Integrable (fun alpha => coherentProjector alpha (fockKet n) m) mu ∧
      X (fockKet n) m = ∫ alpha, coherentProjector alpha (fockKet n) m ∂mu

/-- A nonnegative normalized P density with respect to d²alpha/pi.
This predicate is used for the smooth output weight in (3.24),(3.43), not as
a restriction on the generalized diagonal weight of arbitrary input states. -/
def IsPositivePWeight (X : FockOperator) (w : ℂ → ℝ) : Prop :=
  IsDensity X ∧ (∀ alpha, 0 ≤ w alpha) ∧ Integrable w coherentMeasure ∧
    (∫ alpha, w alpha ∂coherentMeasure) = 1 ∧
    ∀ m n : ℕ,
      Integrable (fun alpha => (w alpha : ℂ) * coherentProjector alpha (fockKet n) m)
        coherentMeasure ∧
      X (fockKet n) m = ∫ alpha,
        (w alpha : ℂ) * coherentProjector alpha (fockKet n) m ∂coherentMeasure

/-- The distinct square-root denominators and conjugated bra of (3.42), PDF p.13. -/
def coherentPhaseKraus (k : ℝ) (alpha : ℂ) : FockOperator :=
  ((Real.sqrt (1 + k ^ 2))⁻¹ : ℂ) •
    InnerProductSpace.rankOne ℂ
      (coherentKet (alpha / (Real.sqrt (1 + (k⁻¹) ^ 2) : ℂ)))
      (coherentKet (star alpha / (Real.sqrt (1 + k ^ 2) : ℂ)))

/-- Finite normal-ordered expression for <m|D(z)|n>, equivalent to the
Laguerre formula (3.15), PDF p.7. Its m=0,n=1 entry has the -conjugate(z) sign. -/
def displacementMatrix (z : ℂ) (m n : ℕ) : ℂ :=
  (Real.exp (-Complex.normSq z / 2) *
    Real.sqrt ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ)) : ℝ) *
    ∑ j ∈ Finset.range (min m n + 1),
      z ^ (m - j) * (-star z) ^ (n - j) /
        ((Nat.factorial j : ℂ) * (Nat.factorial (m - j) : ℂ) *
          (Nat.factorial (n - j) : ℂ))

/-- Actual bounded Weyl displacement selected by all its Fock entries.
Every Weyl-semantic theorem concludes DisplacementRealized, including unitarity
and all trace-pairing convergence guards. PDF pp.7–9 Eq.(3.15). -/
def displacement (z : ℂ) : FockOperator := operatorOfMatrix (displacementMatrix z)

/-- The trace of a trace-class operator in the Fock basis. It is used only
with nuclearity and diagonal summability supplied as conclusions. PDF p.7. -/
def fockTrace (X : FockOperator) : ℂ := ∑' n : ℕ, X (fockKet n) n

/-- Weyl characteristic function tr[D(z)X], with the source ordering and sign.
No total exponential of an unbounded creation/annihilation operator is used.
PDF pp.7–9 Eqs.(3.14)–(3.15). -/
def characteristic (X : FockOperator) (z : ℂ) : ℂ := fockTrace ((displacement z).comp X)

/-- Every displacement is its actual unitary realization, and the nuclear
trace pairing is well defined for all trace-class inputs. All these facts
are conclusions of Weyl-semantic targets, never assumed transformation laws. -/
def DisplacementRealized : Prop :=
  ∀ z : ℂ, HasFockMatrix (displacement z) (displacementMatrix z) ∧
    (ContinuousLinearMap.adjoint (displacement z)).comp (displacement z) = 1 ∧
    (displacement z).comp (ContinuousLinearMap.adjoint (displacement z)) = 1 ∧
    ∀ X : FockOperator, IsTraceClass X → IsTraceClass ((displacement z).comp X) ∧
      Summable (fun n : ℕ => ((displacement z).comp X) (fockKet n) n)

/-- Thermal density coefficients, PDF p.10 Eq.(3.30), for finite a>=1. -/
def thermalMatrix (a : ℝ) (m n : ℕ) : ℂ :=
  if m = n then (2 / (a + 1) * ((a - 1) / (a + 1)) ^ n : ℝ) else 0

/-- The actual thermal operator, with matrix realization and density asserted
in every applicable theorem. No formal infinite-temperature endpoint is used. -/
def thermalDensity (a : ℝ) : FockOperator := operatorOfMatrix (thermalMatrix a)

/-- Poissonian phase-averaged coherent input, PDF p.12 Eq.(3.38), lambda>=0. -/
def poissonMatrix (lambda : ℝ) (m n : ℕ) : ℂ :=
  if m = n then (Real.exp (-lambda) * lambda ^ n / (Nat.factorial n : ℝ) : ℝ) else 0

/-- The phase-averaged coherent density, with no finite support cutoff. -/
def poissonDensity (lambda : ℝ) : FockOperator := operatorOfMatrix (poissonMatrix lambda)

/-- A normalized bounded realization of the thermal state, PDF p.10 Eq.(3.30). -/
def ThermalRealized (a : ℝ) : Prop :=
  HasFockMatrix (thermalDensity a) (thermalMatrix a) ∧ IsDensity (thermalDensity a)

/-- A normalized bounded realization of the Poisson density, PDF p.12 Eq.(3.38). -/
def PoissonRealized (lambda : ℝ) : Prop :=
  HasFockMatrix (poissonDensity lambda) (poissonMatrix lambda) ∧
    IsDensity (poissonDensity lambda)

/-- Photon-number probabilities and first/second moments for densities.
Moment uses below are explicitly guarded by Summable. PDF pp.12,16,22. -/
def photonProbability (X : FockOperator) (n : ℕ) : ℝ := (X (fockKet n) n).re

/-- The finite first photon-number moment when summable, PDF pp.12,16,22. -/
def photonMean (X : FockOperator) : ℝ := ∑' n : ℕ, (n : ℝ) * photonProbability X n

/-- The second moment minus the square of the first moment; used only on
densities with summable first and second moments. PDF pp.12,22. -/
def photonVariance (X : FockOperator) : ℝ :=
  (∑' n : ℕ, (n : ℝ) ^ 2 * photonProbability X n) - photonMean X ^ 2

/-- Strict super-Poissonian photon statistics, including genuine moments.
No undefined infinite-moment tsum default can satisfy this predicate. -/
def SuperPoissonian (X : FockOperator) : Prop :=
  IsDensity X ∧ Summable (fun n : ℕ => (n : ℝ) * photonProbability X n) ∧
    Summable (fun n : ℕ => (n : ℝ) ^ 2 * photonProbability X n) ∧
    photonMean X < photonVariance X

/-- The exact finite Fock-fockDyad attenuator output of (4.11), PDF p.15. -/
def attenuatorDyadOutput (k : ℝ) (m n : ℕ) : FockOperator :=
  ∑ ell ∈ Finset.range (min m n + 1),
    (Real.sqrt ((Nat.choose m ell : ℝ) * (Nat.choose n ell : ℝ)) *
      (1 - k ^ 2) ^ ell * k ^ (m + n - 2 * ell) : ℂ) • fockDyad (m - ell) (n - ell)

/-- The coefficient of the ell-th amplifier fockDyad term, PDF p.20 Eq.(5.13). -/
def amplifierDyadCoefficient (k : ℝ) (n m ell : ℕ) : ℂ :=
  ((k⁻¹) ^ (n + m + 2) * (1 - (k⁻¹) ^ 2) ^ ell *
    Real.sqrt ((Nat.factorial (n + ell) : ℝ) * (Nat.factorial (m + ell) : ℝ)) /
    ((Nat.factorial ell : ℝ) *
      Real.sqrt ((Nat.factorial n : ℝ) * (Nat.factorial m : ℝ))) : ℝ)

/-- Amplifier fockDyad output coefficients, each entry involving at most one ell.
The object is computed from the source data; boundedness is a conclusion. -/
def amplifierDyadMatrix (k : ℝ) (n m r q : ℕ) : ℂ :=
  if n ≤ r ∧ q = m + (r - n) then amplifierDyadCoefficient k n m (r - n) else 0

/-- The operator specified by the infinite series (5.13), PDF p.20. -/
def amplifierDyadOutput (k : ℝ) (n m : ℕ) : FockOperator :=
  operatorOfMatrix (amplifierDyadMatrix k n m)

/-- Exact Fock-input phase-conjugator output weights, PDF p.12 Eq.(3.37). -/
def phaseFockMatrix (k : ℝ) (n r q : ℕ) : ℂ :=
  if r = q then
    ((Nat.choose (n + r) r : ℝ) * k ^ (2 * r) / (1 + k ^ 2) ^ (n + r + 1) : ℝ)
  else 0

/-- The source's Fock-input output, computed before any output property. -/
def phaseFockOutput (k : ℝ) (n : ℕ) : FockOperator := operatorOfMatrix (phaseFockMatrix k n)

/-- The j-th term of the Poisson-averaged output diagonal series (3.39), p.12. -/
def phasePoissonTerm (k lambda : ℝ) (n j : ℕ) : ℝ :=
  lambda ^ j / (Nat.factorial j : ℝ) * (Nat.choose (n + j) j : ℝ) *
    ((1 + k ^ 2)⁻¹) ^ j * ((1 + (k⁻¹) ^ 2)⁻¹) ^ n

/-- Phase-conjugator Poisson-input output coefficients, PDF p.12 Eq.(3.39).
The theorem also concludes summability of every defining scalar series. -/
def phasePoissonMatrix (k lambda : ℝ) (r q : ℕ) : ℂ :=
  if r = q then (Real.exp (-lambda) / (1 + k ^ 2) *
    (∑' j : ℕ, phasePoissonTerm k lambda r j) : ℝ) else 0

/-- The exact Poisson-input output operator of Eq.(3.39), p.12. -/
def phasePoissonOutput (k lambda : ℝ) : FockOperator :=
  operatorOfMatrix (phasePoissonMatrix k lambda)

/-- The normalized finite-sum output of a Poissonian amplifier input.
PDF p.22 Eq.(5.23) omits the k^-2 prefactor; Eq.(5.22), which it substitutes,
requires the factor included here. Independent moderation is required. -/
def amplifierPoissonMatrix (k lambda : ℝ) (r q : ℕ) : ℂ :=
  if r = q then (Real.exp (-lambda) * (k⁻¹) ^ 2 *
    (∑ j ∈ Finset.range (r + 1),
      lambda ^ j / (Nat.factorial j : ℝ) * (Nat.choose r j : ℝ) *
        (1 - (k⁻¹) ^ 2) ^ (r - j) * (k⁻¹) ^ (2 * j)) : ℝ) else 0

/-- The normalized operator computed from (5.22) and the Poisson input. -/
def amplifierPoissonOutput (k lambda : ℝ) : FockOperator :=
  operatorOfMatrix (amplifierPoissonMatrix k lambda)

/-- Exact thermal parameter update of attenuation, PDF p.16 Eq.(4.18). -/
def attenuatorThermalParameter (k a : ℝ) : ℝ := k ^ 2 * a + 1 - k ^ 2

/-- Cartesian product Kraus indices; the first factor acts after the second.
PDF pp.30–33, all seven composition subsections. -/
def productKraus (K L : ℕ → FockOperator) (p : ℕ × ℕ) : FockOperator :=
  (K p.1).comp (L p.2)

/-- Finite iteration with a fresh vacuum environment at each step, PDF pp.18,24.
The unique empty index sequence gives the identity operator. -/
def iteratedKraus (K : ℕ → FockOperator) : (ell : ℕ) → (Fin ell → ℕ) → FockOperator
  | 0, _ => 1
  | ell + 1, j => (K (j 0)).comp (iteratedKraus K ell (fun i => j i.succ))

/-- Simultaneous Fock diagonality of the positive effects W†W, PDF p.34.
Only off-diagonal matrix entries are required to vanish; no eigenbasis for
position generalized kets is postulated. -/
def FockDiagonalEffect (W : FockOperator) : Prop :=
  ∀ m n : ℕ, m ≠ n →
    ((ContinuousLinearMap.adjoint W).comp W) (fockKet n) m = 0

/-- The discrete canonical families with their exact parameter domains.
The identity and vacuum-replacer endpoints are included for effects/iteration.
PDF pp.2,6,14,19,34. -/
inductive DiscreteFamily where
  | phase (k : ℝ) (positive : 0 < k)
  | loss (k : ℝ) (nonnegative : 0 ≤ k) (atMostOne : k ≤ 1)
  | gain (k : ℝ) (atLeastOne : 1 ≤ k)

/-- The source's explicit Kraus family for each discrete canonical parameter. -/
def discreteKraus : DiscreteFamily → ℕ → FockOperator
  | .phase k _ => phaseKraus k
  | .loss k _ _ => attenuatorKraus k
  | .gain k _ => amplifierKraus k

/-- Realization guard for the displayed infinite shifts; phase Kraus operators
are already literal finite sums of bounded dyads. PDF pp.6,14,19. -/
def DiscreteRealized : DiscreteFamily → Prop
  | .phase _ _ => True
  | .loss k _ _ => AttenuatorRealized k
  | .gain k _ => AmplifierRealized k

/-! Sanity examples pinning the vacuum index, shift orientation, and zero input. -/

example (n : ℕ) : fockKet n n = 1 := by
  simp [fockKet]

example (k : ℝ) : attenuatorMatrix k 0 0 1 = 0 := by
  simp [attenuatorMatrix]

example (k : ℝ) : amplifierMatrix k 0 0 1 = 0 := by
  simp [amplifierMatrix]

example (ell : ℕ) : attenuatorMatrix 0 ell 0 ell = 1 := by
  simp [attenuatorMatrix]

example (ell : ℕ) : phaseKraus 0 ell = fockDyad 0 ell := by
  simp [phaseKraus]

example (K : ℕ → FockOperator) (j : Fin 0 → ℕ) : iteratedKraus K 0 j = 1 := rfl

example : IsTraceClass (0 : FockOperator) := by
  refine ⟨0, 0, ?_⟩
  simp [NuclearExpansion]

example : coherentCoefficient 0 0 = 1 := by
  simp [coherentCoefficient]

example : ¬ IsDensity (0 : FockOperator) := by
  simp [IsDensity]

example : displacementMatrix 0 0 0 = 1 := by
  simp [displacementMatrix]

example : thermalMatrix 1 0 0 = 1 := by
  norm_num [thermalMatrix]

example : poissonMatrix 0 0 0 = 1 := by
  simp [poissonMatrix]

end QAlgorithms.Papers.Independent.Dependency50.P39


