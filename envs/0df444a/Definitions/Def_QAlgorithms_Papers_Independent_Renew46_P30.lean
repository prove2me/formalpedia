-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30
-- name    : QAlgorithms_Papers_Independent_Renew46_P30
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T03:03:12.021763+00:00
-- url     : https://prove2.me/theorems/69243b0d-6771-4638-8512-95108cbd3eec
-- title:
--   Definitions for Covariant quantum measurements which maximize the likelihood
-- statement:
--   The objects the formalized statements of *Covariant quantum measurements which maximize the likelihood* (arXiv:quant-ph/0403083) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PhysicalOperator`: PDF p.2: bounded operators on the complete physical Hilbert space.
--   - `nuclearExpansionTrace`: PDF pp.3–4: ordinary trace from any nuclear expansion. On IsTraceClass the series is absolutely summable and independent of the selected expansion.
--   - `HilbertDensity`: PDF p.4: positive trace-one density operator.
--   - `pureSeedDensity`: PDF p.4: likelihood of a pure input, a real density rather than an event probability.
--   - `mixedLikelihood`: PDF pp.3–4: mixed-input trace pairing.
--   - `WeakIntegral`: PDF pp.2–4: a genuine weak operator integral, including all scalar integrability.
--   - `weakOperator`: PDF pp.2–4: select a weak integral if it exists; realization is always concluded.
--   - `RealLie`: PDF p.2: the real finite-dimensional Lie-group restriction of the source.
--   - `CovariantHilbertData`: PDF pp.2–3: strongly continuous projective unitary action and regular two-sided Haar measure. Continuity is tested on rank-one conjugations, so no globally continuous choice of projective phases is required. The Lie restriction is separate for discrete groups.
--   - `representedOperator`: PDF p.2: the bounded physical action.
--   - `conjugatedSeed`: PDF pp.2–3: U_g A U_g-adjoint, with the source's conjugation order.
--   - `WeaklyNormalizedSeed`: PDF p.3, Eq.(2): actual Haar completeness, in weak sense.
--   - `Seed`: PDF pp.2–3: stabilizer commutation is required for descent to G/K. The quotient measure is the pushforward of dg, not an extra probability measure.
--   - `RayStabilizer`: PDF p.2: the actual ray stabilizer, with the compactness required in §II.
--   - `quotientMeasure`: PDF p.9, note [27]: measure on the actual coset space.
--   - `Maximum`: PDF p.4: operational maximum: an admissible seed, attainment, and bound for all competitors.
--   - `StabilizerHaar`: PDF p.4, Eq.(13): probability Haar on the compact subgroup.
--   - `stabilize`: PDF p.4, Eq.(13): the actual weak stabilizer average.
--   - `goalMap`: PDF p.4: normalized weighted conjugation on the trace-class domain.
--   - `HilbertBlockPositive`: PDF p.4: finite matrix positivity, used to state complete positivity on trace class.
--   - `TraceClassCPTP`: PDF p.4: complex linearity, trace-class preservation, trace preservation, and positivity of every finite matrix amplification.
--   - `Goal`: PDF p.4: invariant goal reduced to a function at the identity. K-biinvariance is exactly the condition for this lift to descend to G/K.
--   - `invariantGoalScore`: PDF p.4: the actual average score for the lifted invariant goal.
--   - `Components`: PDF p.3: complete discrete orthogonal irreducible decomposition. The index may be infinite, and every component may be infinite dimensional. I_mu_nu is zero on inequivalent pairs; equivalent-pair partial isometries have coherent phases.
--   - `formalCoefficient`: PDF p.3, Eq.(12): b_mu is the actual coefficient-square Haar integral.
--   - `componentTrace`: PDF p.3: ordinary component trace pairing, with the explicit index order.
--   - `projectedUnit`: PDF p.4: normalized nonzero projection, zero on an absent component.
--   - `occupied`: PDF p.4: occupied components are exactly nonzero orthogonal projections.
--   - `sharpBound`: PDF p.4: nonnegative sharp formula in the extended nonnegative reals. The ENNReal sum retains infinity and never defaults to a finite real number.
--   - `coarseBound`: PDF p.4, Eq.(15): the coarser support-dependent ceiling.
--   - `Adapted`: PDF pp.4–5, corrected Eq.(18): orthogonality concerns distinct equivalent pairs.
--   - `SameIsotypic`: PDF pp.4–5: the decomposition is changed only inside its isotypic blocks.
--   - `canonicalEta`: PDF p.4, Eq.(16): phases absorbed into the normalized projections. The coefficient of a projection is its nonnegative norm.
--   - `canonicalSeed`: PDF p.4, Eq.(17): full-space completion on every absent component.
--   - `SupportedOn`: PDF p.7, §VI: support containment in the span of the selected component vectors.
--   - `MatrixNormalized`: PDF p.5: scalar-entry weak normalization, equivalent to full finite-matrix normalization.
--   - `MatrixSeed`: PDF pp.2–3,5: positivity, full normalization and the actual ray-stabilizer commutant.
--   - `MatrixMaximum`: PDF p.5: attained maximum over all actual covariant full-space seeds.
--   - `TensorIndex`: PDF p.5: the full N-fold tensor basis, with the source's qudit dimension.
--   - `suTensorAction`: PDF p.5: actual tensor-power SU(d) action, including all nonsymmetric sectors.
--   - `identicalVector`: PDF p.5: N identical copies as an actual full-space vector.
--   - `symmetricProjector`: PDF p.5: symmetric projector, the average of the permutation action.
--   - `symmetricSpace`: PDF p.5: the actual symmetric subspace, defined by the symmetrizing projector.
--   - `identicalSeed`: PDF p.5: the indicated full-space completion, with the corrected symmetric dimension.
--   - `PositiveTensorSum`: PDF p.5: full N-partite separability as a finite sum of products of positive factors.
--   - `swapProjector`: PDF p.5, §V.A.3: symmetric and antisymmetric tensor-square projectors.
--   - `pairFormula`: PDF p.5: the printed sharp likelihood as a function of the squared overlap.
--   - `pairEta`: PDF p.5: the canonical two-sector vector, with no division at the absent sector.
--   - `pairSeed`: PDF p.5: at overlap one the missing antisymmetric sector is completed by its identity.
--   - `fockOrbit`: PDF p.6: actual bounded displacement orbit on full one-mode Fock space.
--   - `FockNormalized`: PDF p.6: weak full-Fock Haar normalization relative to d²z/pi.
--   - `HilbertOperatorMeasure`: PDF pp.2–3,6–7: actual normalized positive operator-valued measure. Countable additivity is weak, tested on arbitrary full-space Hilbert vectors.
--   - `FormSeed`: PDF pp.6–7: a generalized positive covariant seed form on a dense invariant linear test domain, together with its genuine bounded operator measure. The seed form need not be continuous in Hilbert norm or come from a Hilbert vector.
--   - `BoundedPOVM`: PDF pp.3,6: the bounded covariant density has an actual integrated full-space POVM.
--   - `closedHilbertRow`: PDF pp.7–8: closed row subspace of a complete coherent Hilbert basis.
--   - `rowTransport`: PDF p.8: coherent identification of row j with row i, by norm-convergent basis sum.
--   - `Isotypic`: PDF pp.7–8: original invariant irreducible rows and their coherent intertwiners. Completeness and orthogonality come from HilbertBasis, not an arbitrary scalar array.
--   - `unitaryEntry`: PDF p.8: row matrix coefficients of the actual multiplicity-space unitary.
--   - `MultiFock`: PDF p.6: full N-mode number basis, without a photon cutoff.
--   - `multiKet`: PDF p.6: normalized multimode number vector.
--   - `multiOperator`: PDF p.6: choose a bounded operator from all number-basis coefficients. All physical uses below conclude the coefficient realization, excluding the fallback.
--   - `multiDisplacement`: PDF p.6: the actual tensor Weyl coefficient array, selected as a bounded map.
--   - `MultiWeylRealized`: PDF p.6: coefficient realization and unitarity, never assumed as a Weyl axiom.
--   - `photonTotal`: PDF p.6: total occupation, used only to write a finite creation-polynomial coefficient.
--   - `passiveEntry`: PDF p.6: second quantization of a mode matrix on number vectors. Contingency arrays have prescribed row and column sums, and all factorial indices are nonnegative. This finite coefficient formula covers every number sector.
--   - `passiveOperator`: PDF p.6: passive unitary selected from the entire finite-sector coefficient array.
--   - `modeAngle`: PDF p.6: phi_N, for N=r+1>1.
--   - `concentrationGenerator`: PDF p.6: the mode-space generator of the printed oscillator exponential. Its 0,j entries are positive and j,0 entries negative.
--   - `concentrationMatrix`: PDF p.6: explicit real rotation taking (z,...,z) to (sqrt(N)z,0,...,0).
--   - `fockConcentration`: PDF p.6: the actual full-Fock V in the source, implemented by number coefficients.
--   - `splitVector`: PDF p.6: completed tensor product of one oscillator and r spectator oscillators. The theorem concludes the exact coefficients for all inputs.
--   - `spectatorDyad`: PDF p.6: I tensor |Phi_m><Phi_n| from its actual bounded number coefficients.
--   - `oscillatorComponent`: PDF p.6: invariant irreducible subspace V-adjoint(H tensor Phi_j), with closed span.
--   - `oscillatorIntertwiner`: PDF p.6: the explicit partial intertwiner between two multiplicity copies.
--   - `multiOrbit`: PDF p.6: identical-displacement orbit of an arbitrary bounded multimode seed.
--   - `MultiMaximum`: PDF p.6: full-space optimality, not just normalization on the occupied subspace.
--   - `remainingVector`: PDF p.6: actual remaining-mode coefficient vector in the concentrated number input.
--   - `numberCoefficient`: PDF p.6: C_n is a computed norm of the actual coefficient row.
--   - `numberPhi`: PDF p.6: occupied Phi_n; at C_n=0 this is zero, without a normalized zero vector.
--   - `vacuumTensor`: PDF p.6: first-mode vacuum projector tensor an arbitrary spectator operator.
--   - `numberEta`: PDF p.6: canonical eta for the finite occupied rows of a product number input.
--   - `numberSeed`: PDF p.6: bounded full-space completion on the complement of the occupied Phi_n.
--   - `equalNumberFormula`: PDF p.6, §V.B.2(ii): the exact factorial sum, only evaluated with k<=n.
--   - `twoPhotonSeed`: PDF p.6: the displayed one-photon seed, with the complementary sum realized as a bounded vacuum-tensor projection rather than an operator-norm series.
--   - `OscillatorSchwartz`: PDF pp.6–7: the common invariant oscillator Schwartz test space, expressed by rapid decay in every polynomial number weight. This is a condition on the completed full-Fock vector; the physical Hilbert space is never replaced by the core.
--   - `diagonalFunctional`: PDF p.7: the generalized diagonal-sum functional; it is used only on the specified Schwartz core, where the defining scalar series is absolutely summable.
--   - `jointQuadratureForm`: PDF p.6: positive form of sqrt(2) V-adjoint sum_n |n,n>, for joint Q1,P2.
--   - `displacedVacuumPair`: PDF pp.6–7: an actual coherent pair, generated by the bounded two-mode action.
--   - `formDensity`: PDF p.7: Born density of a specified seed form and full-Fock input.
--   - `gaussianDensity`: PDF p.7: planar Gaussian density relative to d²alpha/pi.
--   - `spectralFunctional`: PDF p.7: constant spectral-amplitude functional under the concrete Weyl unitary. It is a distributional functional on the oscillator core, never an L² constant vector.
--   - `twinBeam`: PDF p.7, §V.B.4: the normalizable twin-beam input, selected only from an actual Hilbert-norm HasSum. Realization and norm one are theorem conclusions.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, https://arxiv.org/abs/quant-ph/0403083v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

/-!
Chiribella et al., quant-ph/0403083v1. Likelihood means density relative to the
specified Haar measure. Infinite-dimensional operators below are bounded maps;
weak integrals include scalar integrability. Nuclearity supplies ordinary traces.
No twirling identity or optimum is a field of the representation data.
Compilation is pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P30

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39 (IsTraceClass)
open QAlgorithms.Papers.Independent.Claimed50.P14 (SU)
open QAlgorithms.Papers.Independent.Claimed50.P17 (pairAction)
open scoped ComplexConjugate ComplexOrder Manifold ContDiff ENNReal Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.2: bounded operators on the complete physical Hilbert space. -/
abbrev PhysicalOperator (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] := H →L[ℂ] H

/-- PDF pp.3–4: ordinary trace from any nuclear expansion. On IsTraceClass the
series is absolutely summable and independent of the selected expansion. -/
def nuclearExpansionTrace (A : PhysicalOperator H) : ℂ :=
  if h : IsTraceClass A then
    let u := Classical.choose h
    let v := Classical.choose (Classical.choose_spec h)
    ∑' n, inner ℂ (v n) (u n)
  else 0

/-- PDF p.4: positive trace-one density operator. -/
def HilbertDensity (rho : PhysicalOperator H) : Prop :=
  IsTraceClass rho ∧ ContinuousLinearMap.IsPositive rho ∧ nuclearExpansionTrace rho = 1

/-- PDF p.4: likelihood of a pure input, a real density rather than an event probability. -/
def pureSeedDensity (A : PhysicalOperator H) (psi : H) : ℝ := (inner ℂ psi (A psi)).re

/-- PDF pp.3–4: mixed-input trace pairing. -/
def mixedLikelihood (A rho : PhysicalOperator H) : ℝ := (nuclearExpansionTrace (A.comp rho)).re

/-- PDF pp.2–4: a genuine weak operator integral, including all scalar integrability. -/
def WeakIntegral {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (F : X → PhysicalOperator H) (B : PhysicalOperator H) : Prop :=
  ∀ v w, Integrable (fun x => inner ℂ v (F x w)) mu ∧
    (∫ x, inner ℂ v (F x w) ∂mu) = inner ℂ v (B w)

/-- PDF pp.2–4: select a weak integral if it exists; realization is always concluded. -/
def weakOperator {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (F : X → PhysicalOperator H) : PhysicalOperator H :=
  if h : ∃ B : PhysicalOperator H, WeakIntegral mu F B then Classical.choose h else 0

/-- PDF p.2: the real finite-dimensional Lie-group restriction of the source. -/
def RealLie (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  SecondCountableTopology G ∧ ∃ n : ℕ, ∃ charts : ChartedSpace (EuclideanSpace ℝ (Fin n)) G,
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G := charts
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G ∧
      LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- PDF pp.2–3: strongly continuous projective unitary action and regular two-sided
Haar measure. Continuity is tested on rank-one conjugations, so no globally continuous
choice of projective phases is required. The Lie restriction is separate for discrete groups. -/
structure CovariantHilbertData (G H : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  U : G → H ≃ₗᵢ[ℂ] H
  strong : ∀ v w, Continuous (fun g =>
    InnerProductSpace.rankOne ℂ (U g v) (U g v) w)
  identity : ∀ v, U 1 v = v
  projective : ∀ g h, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, U (g * h) v = c • U g (U h v)
  dg : Measure G
  haar : dg.IsHaarMeasure
  regular : dg.Regular
  right_invariant : ∀ h, Measure.map (fun g => g * h) dg = dg
  compact_scale : IsCompact (Set.univ : Set G) → dg Set.univ = 1

variable (R : CovariantHilbertData G H)

/-- PDF p.2: the bounded physical action. -/
def representedOperator (g : G) : PhysicalOperator H := (R.U g).toContinuousLinearEquiv.toContinuousLinearMap

/-- PDF pp.2–3: U_g A U_g-adjoint, with the source's conjugation order. -/
def conjugatedSeed (A : PhysicalOperator H) (g : G) : PhysicalOperator H :=
  (representedOperator R g).comp (A.comp (R.U g).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- PDF p.3, Eq.(2): actual Haar completeness, in weak sense. -/
def WeaklyNormalizedSeed (A : PhysicalOperator H) : Prop := WeakIntegral R.dg (conjugatedSeed R A) 1

/-- PDF pp.2–3: stabilizer commutation is required for descent to G/K.
The quotient measure is the pushforward of dg, not an extra probability measure. -/
def Seed (K : Subgroup G) (A : PhysicalOperator H) : Prop :=
  ContinuousLinearMap.IsPositive A ∧ WeaklyNormalizedSeed R A ∧ ∀ h : K, (representedOperator R h).comp A = A.comp (representedOperator R h)

/-- PDF p.2: the actual ray stabilizer, with the compactness required in §II. -/
def RayStabilizer (psi : H) (K : Subgroup G) : Prop :=
  IsCompact (K : Set G) ∧
  ∀ h : G, h ∈ K ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ R.U h psi = c • psi

/-- PDF p.9, note [27]: measure on the actual coset space. -/
def quotientMeasure (K : Subgroup G) : Measure (G ⧸ K) :=
  Measure.map (fun g : G => (g : G ⧸ K)) R.dg

/-- PDF p.4: operational maximum: an admissible seed, attainment, and bound for all competitors. -/
def Maximum (K : Subgroup G) (psi : H) (A : PhysicalOperator H) (L : ℝ) : Prop :=
  Seed R K A ∧ pureSeedDensity A psi = L ∧
    ∀ B : PhysicalOperator H, Seed R K B → pureSeedDensity B psi ≤ L

/-- PDF p.4, Eq.(13): probability Haar on the compact subgroup. -/
structure StabilizerHaar (K : Subgroup G) where
  dh : Measure K
  haar : dh.IsHaarMeasure
  regular : dh.Regular
  probability : dh Set.univ = 1
  right_invariant : ∀ h, Measure.map (fun k : K => k * h) dh = dh

/-- PDF p.4, Eq.(13): the actual weak stabilizer average. -/
def stabilize {K : Subgroup G} (S : StabilizerHaar K) (A : PhysicalOperator H) : PhysicalOperator H :=
  weakOperator S.dh (fun h : K => conjugatedSeed R A h)

/-- PDF p.4: normalized weighted conjugation on the trace-class domain. -/
def goalMap (h : G → ℝ) (rho : PhysicalOperator H) : PhysicalOperator H :=
  weakOperator R.dg (fun g => ((h g / (∫ t, h t ∂(R.dg)) : ℝ) : ℂ) •
    (representedOperator R g⁻¹).comp (rho.comp (ContinuousLinearMap.adjoint (representedOperator R g⁻¹))))

/-- PDF p.4: finite matrix positivity, used to state complete positivity on trace class. -/
def HilbertBlockPositive (n : ℕ) (A : Fin n → Fin n → PhysicalOperator H) : Prop :=
  ∀ v : Fin n → H,
    (∑ i, ∑ j, inner ℂ (v i) (A i j (v j))).im = 0 ∧
      0 ≤ (∑ i, ∑ j, inner ℂ (v i) (A i j (v j))).re

/-- PDF p.4: complex linearity, trace-class preservation, trace preservation,
and positivity of every finite matrix amplification. -/
def TraceClassCPTP (Phi : PhysicalOperator H → PhysicalOperator H) : Prop :=
  (∀ A B, IsTraceClass A → IsTraceClass B → Phi (A + B) = Phi A + Phi B) ∧
  (∀ (c : ℂ) A, IsTraceClass A → Phi (c • A) = c • Phi A) ∧
  (∀ A, IsTraceClass A → IsTraceClass (Phi A) ∧ nuclearExpansionTrace (Phi A) = nuclearExpansionTrace A) ∧
  ∀ n (A : Fin n → Fin n → PhysicalOperator H), (∀ i j, IsTraceClass (A i j)) →
    HilbertBlockPositive n A → HilbertBlockPositive n (fun i j => Phi (A i j))

/-- PDF p.4: invariant goal reduced to a function at the identity.
K-biinvariance is exactly the condition for this lift to descend to G/K. -/
def Goal (K : Subgroup G) (h : G → ℝ) : Prop :=
  Measurable h ∧ (∀ g, 0 ≤ h g) ∧ Integrable h R.dg ∧
  0 < (∫ g, h g ∂(R.dg)) ∧ ∀ (k l : K) g, h (k * g * l) = h g

/-- PDF p.4: the actual average score for the lifted invariant goal. -/
def invariantGoalScore (h : G → ℝ) (rho A : PhysicalOperator H) : ℝ :=
  ∫ g, h g * mixedLikelihood (conjugatedSeed R A g) rho ∂(R.dg)

variable {M : Type*} [DecidableEq M]

/-- PDF p.3: complete discrete orthogonal irreducible decomposition. The index
may be infinite, and every component may be infinite dimensional. I_mu_nu is zero
on inequivalent pairs; equivalent-pair partial isometries have coherent phases. -/
structure Components (R : CovariantHilbertData G H) (M : Type*) [DecidableEq M] where
  equiv : Setoid M
  I : M → M → PhysicalOperator H
  e : M → H
  e_unit : ∀ i, ‖e i‖ = 1
  e_range : ∀ i, I i i (e i) = e i
  self_adjoint : ∀ i, ContinuousLinearMap.adjoint (I i i) = I i i
  projection : ∀ i, (I i i).comp (I i i) = I i i
  orthogonal : ∀ i j, i ≠ j → (I i i).comp (I j j) = 0
  complete : ∀ v : H, HasSum (fun i => I i i v) v
  intertwines : ∀ i j g, (representedOperator R g).comp (I i j) = (I i j).comp (representedOperator R g)
  zero_inequivalent : ∀ i j, ¬ equiv.r i j → I i j = 0
  adjoint : ∀ i j, ContinuousLinearMap.adjoint (I i j) = I j i
  coherent : ∀ i j k, equiv.r i j → equiv.r j k → (I i j).comp (I j k) = I i k
  supported : ∀ i j, I i j = (I i i).comp ((I i j).comp (I j j))
  irreducible : ∀ i (W : Submodule ℂ H), IsClosed (W : Set H) →
    W ≤ (I i i).range →
    (∀ g v, v ∈ W → R.U g v ∈ W) → W = ⊥ ∨ W = (I i i).range
  inequivalent : ∀ i j, ¬ equiv.r i j → ∀ T : PhysicalOperator H,
    T = (I i i).comp (T.comp (I j j)) →
    (∀ g, (representedOperator R g).comp T = T.comp (representedOperator R g)) → T = 0
  square_integrable : ∀ i v w, I i i v = v → I i i w = w →
    Integrable (fun g => ‖inner ℂ v (R.U g w)‖ ^ 2) R.dg

variable (D : Components R M)

/-- PDF p.3, Eq.(12): b_mu is the actual coefficient-square Haar integral. -/
def formalCoefficient (i : M) : ℝ :=
  ∫ g, ‖inner ℂ (D.e i) (R.U g (D.e i))‖ ^ 2 ∂(R.dg)

/-- PDF p.3: ordinary component trace pairing, with the explicit index order. -/
def componentTrace (i j : M) (A : PhysicalOperator H) : ℂ := nuclearExpansionTrace ((D.I i j).comp A)

/-- PDF p.4: normalized nonzero projection, zero on an absent component. -/
def projectedUnit (psi : H) (i : M) : H :=
  ((‖D.I i i psi‖ : ℝ)⁻¹ : ℂ) • D.I i i psi

/-- PDF p.4: occupied components are exactly nonzero orthogonal projections. -/
def occupied (psi : H) : Set M := {i | D.I i i psi ≠ 0}

/-- PDF p.4: nonnegative sharp formula in the extended nonnegative reals.
The ENNReal sum retains infinity and never defaults to a finite real number. -/
def sharpBound (psi : H) : ℝ≥0∞ :=
  (∑' i, ENNReal.ofReal (‖D.I i i psi‖ * Real.sqrt ((formalCoefficient R D i)⁻¹))) ^ 2

/-- PDF p.4, Eq.(15): the coarser support-dependent ceiling. -/
def coarseBound (psi : H) : ℝ≥0∞ :=
  ∑' i, if D.I i i psi = 0 then 0 else ENNReal.ofReal ((formalCoefficient R D i)⁻¹)

/-- PDF pp.4–5, corrected Eq.(18): orthogonality concerns distinct equivalent pairs. -/
def Adapted (psi : H) : Prop :=
  ∀ i j, i ≠ j → D.equiv.r i j →
    inner ℂ (projectedUnit R D psi i) (D.I i j (projectedUnit R D psi j)) = 0

/-- PDF pp.4–5: the decomposition is changed only inside its isotypic blocks. -/
def SameIsotypic [Fintype M] (E : Components R M) : Prop :=
  E.equiv = D.equiv ∧ ∀ i,
    (∑ j, if D.equiv.r i j then E.I j j else 0) =
      ∑ j, if D.equiv.r i j then D.I j j else 0

/-- PDF p.4, Eq.(16): phases absorbed into the normalized projections.
The coefficient of a projection is its nonnegative norm. -/
def canonicalEta [Fintype M] (psi : H) : H :=
  ∑ i, (Real.sqrt ((formalCoefficient R D i)⁻¹) : ℂ) • projectedUnit R D psi i

/-- PDF p.4, Eq.(17): full-space completion on every absent component. -/
def canonicalSeed [Fintype M] (psi : H) : PhysicalOperator H :=
  InnerProductSpace.rankOne ℂ (canonicalEta R D psi) (canonicalEta R D psi) +
    ∑ i, if D.I i i psi = 0 then
      ((formalCoefficient R D i)⁻¹ : ℂ) • InnerProductSpace.rankOne ℂ (D.e i) (D.e i)
    else 0

/-- PDF p.7, §VI: support containment in the span of the selected component vectors. -/
def SupportedOn [Fintype M] (rho : PhysicalOperator H) (v : M → H) : Prop :=
  rho.range ≤ Submodule.span ℂ (Set.range v)

example : ContinuousLinearMap.IsPositive (0 : PhysicalOperator H) := ContinuousLinearMap.isPositive_zero

example (psi : H) : pureSeedDensity (0 : PhysicalOperator H) psi = 0 := by simp [pureSeedDensity]

example (A : PhysicalOperator H) (h : WeaklyNormalizedSeed R A) : WeakIntegral R.dg (conjugatedSeed R A) 1 := h

example (psi : H) (i : M) : i ∈ occupied R D psi ↔ D.I i i psi ≠ 0 := Iff.rfl

example [Fintype M] (psi : H) :
    canonicalEta R D psi = ∑ i, (Real.sqrt ((formalCoefficient R D i)⁻¹) : ℂ) •
      projectedUnit R D psi i := rfl

/-- PDF p.5: scalar-entry weak normalization, equivalent to full finite-matrix normalization. -/
def MatrixNormalized {X A : Type*} [MeasurableSpace X] [Fintype A] [DecidableEq A]
    (mu : Measure X) (U : X → Matrix A A ℂ) (Xi : Matrix A A ℂ) : Prop :=
  ∀ i j, Integrable (fun g => (U g * Xi * (U g)ᴴ) i j) mu ∧
    (∫ g, (U g * Xi * (U g)ᴴ) i j ∂mu) = (1 : Matrix A A ℂ) i j

/-- PDF pp.2–3,5: positivity, full normalization and the actual ray-stabilizer commutant. -/
def MatrixSeed {X A : Type*} [MeasurableSpace X] [Fintype A] [DecidableEq A]
    (mu : Measure X) (U : X → Matrix A A ℂ) (psi : EuclideanSpace ℂ A)
    (Xi : Matrix A A ℂ) : Prop :=
  Xi.PosSemidef ∧ MatrixNormalized mu U Xi ∧
    ∀ g, (∃ c : ℂ, ‖c‖ = 1 ∧ QAlgorithms.act (U g) psi = c • psi) → U g * Xi = Xi * U g

/-- PDF p.5: attained maximum over all actual covariant full-space seeds. -/
def MatrixMaximum {X A : Type*} [MeasurableSpace X] [Fintype A] [DecidableEq A]
    (mu : Measure X) (U : X → Matrix A A ℂ) (psi : EuclideanSpace ℂ A)
    (Xi : Matrix A A ℂ) (L : ℝ) : Prop :=
  MatrixSeed mu U psi Xi ∧ QAlgorithms.effectProb Xi (QAlgorithms.pureDensity psi) = L ∧
    ∀ B, MatrixSeed mu U psi B → QAlgorithms.effectProb B (QAlgorithms.pureDensity psi) ≤ L

/-- PDF p.5: the full N-fold tensor basis, with the source's qudit dimension. -/
abbrev TensorIndex (d N : ℕ) := Fin N → Fin d

/-- PDF p.5: actual tensor-power SU(d) action, including all nonsymmetric sectors. -/
def suTensorAction (d N : ℕ) (g : SU d) : Matrix (TensorIndex d N) (TensorIndex d N) ℂ :=
  fun x y => ∏ i, (g : Matrix (Fin d) (Fin d) ℂ) (x i) (y i)

/-- PDF p.5: N identical copies as an actual full-space vector. -/
def identicalVector (d N : ℕ) (psi : EuclideanSpace ℂ (Fin d)) :
    EuclideanSpace ℂ (TensorIndex d N) := WithLp.toLp 2 (fun x => ∏ i, psi (x i))

/-- PDF p.5: symmetric projector, the average of the permutation action. -/
def symmetricProjector (d N : ℕ) : Matrix (TensorIndex d N) (TensorIndex d N) ℂ :=
  fun x y => (Nat.factorial N : ℂ)⁻¹ *
    ∑ sigma : Equiv.Perm (Fin N), if x = fun i => y (sigma i) then 1 else 0

/-- PDF p.5: the actual symmetric subspace, defined by the symmetrizing projector. -/
def symmetricSpace (d N : ℕ) : Submodule ℂ (TensorIndex d N → ℂ) :=
  (Matrix.toLin' (symmetricProjector d N)).range

/-- PDF p.5: the indicated full-space completion, with the corrected symmetric dimension. -/
def identicalSeed (d N : ℕ) (psi : EuclideanSpace ℂ (Fin d)) :
    Matrix (TensorIndex d N) (TensorIndex d N) ℂ :=
  ((Nat.choose (d + N - 1) N : ℂ) • QAlgorithms.pureDensity (identicalVector d N psi)) +
    (1 - symmetricProjector d N)

/-- PDF p.5: full N-partite separability as a finite sum of products of positive factors. -/
def PositiveTensorSum (d N : ℕ) (Xi : Matrix (TensorIndex d N) (TensorIndex d N) ℂ) : Prop :=
  ∃ r : ℕ, ∃ B : Fin r → Fin N → Matrix (Fin d) (Fin d) ℂ,
    (∀ k i, (B k i).PosSemidef) ∧ ∀ x y, Xi x y = ∑ k, ∏ i, B k i (x i) (y i)

/-- PDF p.5, §V.A.3: symmetric and antisymmetric tensor-square projectors. -/
def swapProjector (d : ℕ) (positive : Bool) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun x y => ((if x = y then 1 else 0) +
    (if positive then 1 else -1) * (if x = (y.2, y.1) then 1 else 0)) / 2

/-- PDF p.5: the printed sharp likelihood as a function of the squared overlap. -/
def pairFormula (d : ℕ) (s2 : ℝ) : ℝ :=
  (Real.sqrt ((d : ℝ) * (d + 1) / 2 * (1 + s2) / 2) +
    Real.sqrt ((d : ℝ) * (d - 1) / 2 * (1 - s2) / 2)) ^ 2

/-- PDF p.5: the canonical two-sector vector, with no division at the absent sector. -/
def pairEta (d : ℕ) (psi phi : EuclideanSpace ℂ (Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  let s2 := Complex.normSq (inner ℂ psi phi)
  let plus := QAlgorithms.tensorVec psi phi + QAlgorithms.tensorVec phi psi
  let minus := QAlgorithms.tensorVec psi phi - QAlgorithms.tensorVec phi psi
  (Real.sqrt ((d : ℝ) * (d + 1) / 2) / Real.sqrt (2 * (1 + s2)) : ℂ) • plus +
    (if s2 = 1 then 0 else
      (Real.sqrt ((d : ℝ) * (d - 1) / 2) / Real.sqrt (2 * (1 - s2)) : ℂ) • minus)

/-- PDF p.5: at overlap one the missing antisymmetric sector is completed by its identity. -/
def pairSeed (d : ℕ) (psi phi : EuclideanSpace ℂ (Fin d)) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  QAlgorithms.pureDensity (pairEta d psi phi) +
    if Complex.normSq (inner ℂ psi phi) = 1 then swapProjector d false else 0

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet displacement displacementMatrix coherentMeasure coherentKet)

/-- PDF p.6: actual bounded displacement orbit on full one-mode Fock space. -/
def fockOrbit (A : FockOperator) (z : ℂ) : FockOperator :=
  (displacement z).comp (A.comp (ContinuousLinearMap.adjoint (displacement z)))

/-- PDF p.6: weak full-Fock Haar normalization relative to d²z/pi. -/
def FockNormalized (A : FockOperator) : Prop := WeakIntegral coherentMeasure (fockOrbit A) 1

/-- PDF pp.2–3,6–7: actual normalized positive operator-valued measure.
Countable additivity is weak, tested on arbitrary full-space Hilbert vectors. -/
structure HilbertOperatorMeasure (X E : Type*) [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  effect : Set X → PhysicalOperator E
  positive : ∀ A, MeasurableSet A → ContinuousLinearMap.IsPositive (effect A)
  empty : effect ∅ = 0
  univ : effect Set.univ = 1
  additive : ∀ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) → Pairwise (fun i j => Disjoint (A i) (A j)) →
    ∀ v w : E, HasSum (fun n => inner ℂ v (effect (A n) w))
      (inner ℂ v (effect (⋃ n, A n) w))

/-- PDF pp.6–7: a generalized positive covariant seed form on a dense invariant
linear test domain, together with its genuine bounded operator measure.
The seed form need not be continuous in Hilbert norm or come from a Hilbert vector. -/
structure FormSeed {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (mu : Measure X)
    (inverseAction : X → PhysicalOperator H) where
  domain : Submodule ℂ H
  dense : Dense (domain : Set H)
  invariant : ∀ x v, v ∈ domain → inverseAction x v ∈ domain
  form : H → H → ℂ
  add_left : ∀ u v w, u ∈ domain → v ∈ domain → w ∈ domain →
    form (u + v) w = form u w + form v w
  add_right : ∀ u v w, u ∈ domain → v ∈ domain → w ∈ domain →
    form u (v + w) = form u v + form u w
  smul_left : ∀ c u v, u ∈ domain → v ∈ domain → form (c • u) v = star c * form u v
  smul_right : ∀ c u v, u ∈ domain → v ∈ domain → form u (c • v) = c * form u v
  hermitian : ∀ u v, u ∈ domain → v ∈ domain → form u v = star (form v u)
  positive : ∀ v, v ∈ domain → 0 ≤ (form v v).re
  orbit_continuous : ∀ v w, v ∈ domain → w ∈ domain →
    Continuous (fun x => form (inverseAction x v) (inverseAction x w))
  measure : HilbertOperatorMeasure X H
  represents : ∀ A, MeasurableSet A → ∀ v w, v ∈ domain → w ∈ domain →
    Integrable (fun x => form (inverseAction x v) (inverseAction x w)) (mu.restrict A) ∧
    (∫ x, form (inverseAction x v) (inverseAction x w) ∂(mu.restrict A)) =
      inner ℂ v (measure.effect A w)

/-- PDF pp.3,6: the bounded covariant density has an actual integrated full-space POVM. -/
def BoundedPOVM {X : Type*} [MeasurableSpace X] (mu : Measure X) (F : X → PhysicalOperator H) : Prop :=
  ∃ E : HilbertOperatorMeasure X H, ∀ A, MeasurableSet A → WeakIntegral (mu.restrict A) F (E.effect A)

variable {J : Type*} [DecidableEq J]

/-- PDF pp.7–8: closed row subspace of a complete coherent Hilbert basis. -/
def closedHilbertRow (b : HilbertBasis (M × J) ℂ H) (m : M) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range (fun j => b (m, j)))).topologicalClosure

/-- PDF p.8: coherent identification of row j with row i, by norm-convergent basis sum. -/
def rowTransport (b : HilbertBasis (M × J) ℂ H) (i j : M) (v : H) : H :=
  ∑' k : J, inner ℂ (b (j, k)) v • b (i, k)

/-- PDF pp.7–8: original invariant irreducible rows and their coherent intertwiners.
Completeness and orthogonality come from HilbertBasis, not an arbitrary scalar array. -/
def Isotypic (b : HilbertBasis (M × J) ℂ H) : Prop :=
  (∀ m g v, v ∈ closedHilbertRow b m → R.U g v ∈ closedHilbertRow b m) ∧
  (∀ m (W : Submodule ℂ H), IsClosed (W : Set H) → W ≤ closedHilbertRow b m →
    (∀ g v, v ∈ W → R.U g v ∈ W) → W = ⊥ ∨ W = closedHilbertRow b m) ∧
  ∀ i j g v, rowTransport b i j (R.U g v) = R.U g (rowTransport b i j v)

/-- PDF p.8: row matrix coefficients of the actual multiplicity-space unitary. -/
def unitaryEntry (V : lp (fun _ : M => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : M => ℂ) 2)
    (i j : M) : ℂ := V (lp.single 2 j 1) i

example (b : HilbertBasis (M × J) ℂ H) (i j : M) : rowTransport b i j 0 = 0 := by
  simp [rowTransport]

example (d : ℕ) : identicalVector d 0 (0 : EuclideanSpace ℂ (Fin d)) =
    WithLp.toLp 2 (fun _ => (1 : ℂ)) := by
  ext x
  simp [identicalVector]

example (d : ℕ) : pairFormula d 1 =
    (Real.sqrt ((d : ℝ) * (d + 1) / 2 * (1 + 1) / 2) +
      Real.sqrt ((d : ℝ) * (d - 1) / 2 * (1 - 1) / 2)) ^ 2 := rfl

/-! Number-preserving N-mode construction on the completed Fock space. -/

/-- PDF p.6: full N-mode number basis, without a photon cutoff. -/
abbrev MultiFock (N : ℕ) := QAlgorithms.RealRegisters.Hilbert (Fin N → ℕ)

/-- PDF p.6: normalized multimode number vector. -/
def multiKet {N : ℕ} (occupation : Fin N → ℕ) : MultiFock N := lp.single 2 occupation 1

/-- PDF p.6: choose a bounded operator from all number-basis coefficients.
All physical uses below conclude the coefficient realization, excluding the fallback. -/
def multiOperator {N : ℕ} (K : (Fin N → ℕ) → (Fin N → ℕ) → ℂ) : PhysicalOperator (MultiFock N) :=
  if h : ∃ A : PhysicalOperator (MultiFock N), ∀ m n, A (multiKet n) m = K m n then
    Classical.choose h else 0

/-- PDF p.6: the actual tensor Weyl coefficient array, selected as a bounded map. -/
def multiDisplacement {N : ℕ} (z : Fin N → ℂ) : PhysicalOperator (MultiFock N) :=
  multiOperator (fun m n => ∏ j, displacementMatrix (z j) (m j) (n j))

/-- PDF p.6: coefficient realization and unitarity, never assumed as a Weyl axiom. -/
def MultiWeylRealized (N : ℕ) : Prop :=
  ∀ z : Fin N → ℂ,
    (∀ m n, multiDisplacement z (multiKet n) m = ∏ j, displacementMatrix (z j) (m j) (n j)) ∧
    (ContinuousLinearMap.adjoint (multiDisplacement z)).comp (multiDisplacement z) = 1 ∧
    (multiDisplacement z).comp (ContinuousLinearMap.adjoint (multiDisplacement z)) = 1

/-- PDF p.6: total occupation, used only to write a finite creation-polynomial coefficient. -/
def photonTotal {N : ℕ} (n : Fin N → ℕ) : ℕ := ∑ j, n j

/-- PDF p.6: second quantization of a mode matrix on number vectors.
Contingency arrays have prescribed row and column sums, and all factorial indices
are nonnegative. This finite coefficient formula covers every number sector. -/
def passiveEntry {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ)
    (m n : Fin N → ℕ) : ℂ :=
  let K := photonTotal n
  (Real.sqrt ((∏ i, (Nat.factorial (m i) : ℝ)) *
    ∏ j, (Nat.factorial (n j) : ℝ)) : ℂ) *
  ∑ a : Fin N → Fin N → Fin (K + 1),
    if (∀ i, (∑ j, (a i j).val) = m i) ∧ (∀ j, (∑ i, (a i j).val) = n j) then
      ∏ i, ∏ j, B i j ^ (a i j).val / (Nat.factorial (a i j).val : ℂ)
    else 0

/-- PDF p.6: passive unitary selected from the entire finite-sector coefficient array. -/
def passiveOperator {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) : PhysicalOperator (MultiFock N) :=
  multiOperator (passiveEntry B)

/-- PDF p.6: phi_N, for N=r+1>1. -/
def modeAngle (r : ℕ) : ℝ := Real.arctan (Real.sqrt r) / Real.sqrt r

/-- PDF p.6: the mode-space generator of the printed oscillator exponential.
Its 0,j entries are positive and j,0 entries negative. -/
def concentrationGenerator (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun i j => if i.val = 0 ∧ j.val ≠ 0 then (modeAngle r : ℂ)
    else if j.val = 0 ∧ i.val ≠ 0 then -(modeAngle r : ℂ) else 0

/-- PDF p.6: explicit real rotation taking (z,...,z) to (sqrt(N)z,0,...,0). -/
def concentrationMatrix (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun i j =>
    if i.val = 0 then (1 / Real.sqrt (r + 1) : ℝ)
    else if j.val = 0 then (-1 / Real.sqrt (r + 1) : ℝ)
    else (if i = j then 1 else 0) +
      ((1 / Real.sqrt (r + 1) - 1) / (r : ℝ) : ℝ)

/-- PDF p.6: the actual full-Fock V in the source, implemented by number coefficients. -/
def fockConcentration (r : ℕ) : PhysicalOperator (MultiFock (r + 1)) := passiveOperator (concentrationMatrix r)

/-- PDF p.6: completed tensor product of one oscillator and r spectator oscillators.
The theorem concludes the exact coefficients for all inputs. -/
def splitVector (r : ℕ) (v : Fock) (w : MultiFock r) : MultiFock (r + 1) :=
  let c : (Fin (r + 1) → ℕ) → ℂ := fun n => v (n 0) * w (fun j => n j.succ)
  if h : Memℓp c 2 then ⟨c, h⟩ else 0

/-- PDF p.6: I tensor |Phi_m><Phi_n| from its actual bounded number coefficients. -/
def spectatorDyad (r : ℕ) (v w : MultiFock r) : PhysicalOperator (MultiFock (r + 1)) :=
  multiOperator (fun m n => (if m 0 = n 0 then 1 else 0) *
    v (fun j => m j.succ) * star (w (fun j => n j.succ)))

/-- PDF p.6: invariant irreducible subspace V-adjoint(H tensor Phi_j), with closed span. -/
def oscillatorComponent (r : ℕ) (phi : MultiFock r) : Submodule ℂ (MultiFock (r + 1)) :=
  (Submodule.span ℂ (Set.range (fun v : Fock =>
    ContinuousLinearMap.adjoint (fockConcentration r) (splitVector r v phi)))).topologicalClosure

/-- PDF p.6: the explicit partial intertwiner between two multiplicity copies. -/
def oscillatorIntertwiner (r : ℕ) (v w : MultiFock r) : PhysicalOperator (MultiFock (r + 1)) :=
  (ContinuousLinearMap.adjoint (fockConcentration r)).comp
    ((spectatorDyad r v w).comp (fockConcentration r))

/-- PDF p.6: identical-displacement orbit of an arbitrary bounded multimode seed. -/
def multiOrbit {N : ℕ} (A : PhysicalOperator (MultiFock N)) (z : ℂ) : PhysicalOperator (MultiFock N) :=
  (multiDisplacement (fun _ => z)).comp
    (A.comp (ContinuousLinearMap.adjoint (multiDisplacement (fun _ => z))))

/-- PDF p.6: full-space optimality, not just normalization on the occupied subspace. -/
def MultiMaximum {N : ℕ} (psi : MultiFock N) (A : PhysicalOperator (MultiFock N)) (L : ℝ) : Prop :=
  ContinuousLinearMap.IsPositive A ∧ WeakIntegral coherentMeasure (multiOrbit A) 1 ∧
    BoundedPOVM coherentMeasure (multiOrbit A) ∧ pureSeedDensity A psi = L ∧
    (∀ B : PhysicalOperator (MultiFock N), ContinuousLinearMap.IsPositive B → WeakIntegral coherentMeasure (multiOrbit B) 1 →
      pureSeedDensity B psi ≤ L) ∧
    ∀ B : FormSeed coherentMeasure (fun z : ℂ =>
      ContinuousLinearMap.adjoint (multiDisplacement (fun _ : Fin N => z))),
      psi ∈ B.domain → (B.form psi psi).re ≤ L

/-- PDF p.6: actual remaining-mode coefficient vector in the concentrated number input. -/
def remainingVector (r : ℕ) (input : Fin (r + 1) → ℕ) (n : ℕ) : MultiFock r :=
  ∑ tail : Fin r → Fin (photonTotal input + 1),
    fockConcentration r (multiKet input) (Fin.cases n (fun j => (tail j).val)) •
      multiKet (fun j => (tail j).val)

/-- PDF p.6: C_n is a computed norm of the actual coefficient row. -/
def numberCoefficient (r : ℕ) (input : Fin (r + 1) → ℕ) (n : ℕ) : ℝ :=
  ‖remainingVector r input n‖

/-- PDF p.6: occupied Phi_n; at C_n=0 this is zero, without a normalized zero vector. -/
def numberPhi (r : ℕ) (input : Fin (r + 1) → ℕ) (n : ℕ) : MultiFock r :=
  ((numberCoefficient r input n)⁻¹ : ℂ) • remainingVector r input n

/-- PDF p.6: first-mode vacuum projector tensor an arbitrary spectator operator. -/
def vacuumTensor (r : ℕ) (A : PhysicalOperator (MultiFock r)) : PhysicalOperator (MultiFock (r + 1)) :=
  multiOperator (fun m n => if m 0 = 0 ∧ n 0 = 0 then
    A (multiKet (fun j => n j.succ)) (fun j => m j.succ) else 0)

/-- PDF p.6: canonical eta for the finite occupied rows of a product number input. -/
def numberEta (r : ℕ) (input : Fin (r + 1) → ℕ) : MultiFock (r + 1) :=
  (Real.sqrt (r + 1) : ℂ) •
    ∑ n ∈ Finset.range (photonTotal input + 1),
      ContinuousLinearMap.adjoint (fockConcentration r)
        (splitVector r (fockKet n) (numberPhi r input n))

/-- PDF p.6: bounded full-space completion on the complement of the occupied Phi_n. -/
def numberSeed (r : ℕ) (input : Fin (r + 1) → ℕ) : PhysicalOperator (MultiFock (r + 1)) :=
  InnerProductSpace.rankOne ℂ (numberEta r input) (numberEta r input) +
    ((r + 1 : ℕ) : ℂ) •
      (ContinuousLinearMap.adjoint (fockConcentration r)).comp
        ((vacuumTensor r (1 - ∑ n ∈ Finset.range (photonTotal input + 1),
          InnerProductSpace.rankOne ℂ (numberPhi r input n) (numberPhi r input n))).comp
          (fockConcentration r))

/-- PDF p.6, §V.B.2(ii): the exact factorial sum, only evaluated with k<=n. -/
def equalNumberFormula (n : ℕ) : ℝ :=
  2 * (∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) * Real.sqrt ((Nat.factorial (2 * k) : ℝ) *
      (Nat.factorial (2 * n - 2 * k) : ℝ)) / (2 ^ n * (Nat.factorial n : ℝ))) ^ 2

/-- PDF p.6: the displayed one-photon seed, with the complementary sum realized
as a bounded vacuum-tensor projection rather than an operator-norm series. -/
def twoPhotonSeed : PhysicalOperator (MultiFock 2) :=
  (4 : ℂ) • InnerProductSpace.rankOne ℂ (multiKet (fun _ => 1)) (multiKet (fun _ => 1)) +
    (2 : ℂ) • (ContinuousLinearMap.adjoint (fockConcentration 1)).comp
      ((vacuumTensor 1 (1 - InnerProductSpace.rankOne ℂ (multiKet (fun _ => 0)) (multiKet (fun _ => 0)) -
        InnerProductSpace.rankOne ℂ (multiKet (fun _ => 2)) (multiKet (fun _ => 2)))).comp
        (fockConcentration 1))

example {N : ℕ} (n : Fin N → ℕ) : ‖multiKet n‖ = 1 := by
  simp [multiKet, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

example (r : ℕ) (input : Fin (r + 1) → ℕ) (n : ℕ)
    (h : remainingVector r input n = 0) : numberPhi r input n = 0 := by
  simp [numberPhi, h]

example : concentrationMatrix 1 0 1 = (1 / Real.sqrt 2 : ℝ) := by
  norm_num [concentrationMatrix]

/-- PDF pp.6–7: the common invariant oscillator Schwartz test space, expressed
by rapid decay in every polynomial number weight. This is a condition on the
completed full-Fock vector; the physical Hilbert space is never replaced by the core. -/
def OscillatorSchwartz {N : ℕ} (v : MultiFock N) : Prop :=
  ∀ p : ℕ, Summable (fun n : Fin N → ℕ =>
    ((1 + photonTotal n : ℕ) : ℝ) ^ (2 * p) * ‖v n‖ ^ 2)

/-- PDF p.7: the generalized diagonal-sum functional; it is used only on the
specified Schwartz core, where the defining scalar series is absolutely summable. -/
def diagonalFunctional (v : MultiFock 2) : ℂ :=
  ∑' n : ℕ, v (fun _ => n)

/-- PDF p.6: positive form of sqrt(2) V-adjoint sum_n |n,n>, for joint Q1,P2. -/
def jointQuadratureForm (v w : MultiFock 2) : ℂ :=
  (2 : ℂ) * star (diagonalFunctional (fockConcentration 1 v)) *
    diagonalFunctional (fockConcentration 1 w)

/-- PDF pp.6–7: an actual coherent pair, generated by the bounded two-mode action. -/
def displacedVacuumPair (a b : ℂ) : MultiFock 2 :=
  multiDisplacement (Fin.cases a (fun _ => b)) (multiKet (fun _ => 0))

/-- PDF p.7: Born density of a specified seed form and full-Fock input. -/
def formDensity {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {mu : Measure X} {Uinv : X → PhysicalOperator H} (A : FormSeed mu Uinv) (psi : H) (x : X) : ℝ :=
  (A.form (Uinv x psi) (Uinv x psi)).re

/-- PDF p.7: planar Gaussian density relative to d²alpha/pi. -/
def gaussianDensity (k : ℝ) (trueValue estimate : ℂ) : ℝ :=
  k * Real.exp (-k * Complex.normSq (estimate - trueValue))

/-- PDF p.7: constant spectral-amplitude functional under the concrete Weyl unitary.
It is a distributional functional on the oscillator core, never an L² constant vector. -/
def spectralFunctional
    (T : MultiFock 2 ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 coherentMeasure) (v : MultiFock 2) : ℂ :=
  ∫ w : ℂ, T v w ∂coherentMeasure

/-- PDF p.7, §V.B.4: the normalizable twin-beam input, selected only from an
actual Hilbert-norm HasSum. Realization and norm one are theorem conclusions. -/
def twinBeam (x : ℝ) : MultiFock 2 :=
  if h : ∃ v : MultiFock 2,
      HasSum (fun n : ℕ => ((Real.sqrt (1 - x ^ 2) * x ^ n : ℝ) : ℂ) •
        multiKet (fun _ => n)) v then Classical.choose h else 0

example : gaussianDensity 4 0 0 = 4 := by simp [gaussianDensity]

example (v w : MultiFock 2) :
    jointQuadratureForm v w = (2 : ℂ) * star (diagonalFunctional (fockConcentration 1 v)) *
      diagonalFunctional (fockConcentration 1 w) := rfl

example (A : PhysicalOperator H) (h : IsTraceClass A) :
    ∃ u v : ℕ → H,
      QAlgorithms.Papers.Independent.Dependency50.P39.NuclearExpansion A u v := h

example : equalNumberFormula 0 = 2 := by norm_num [equalNumberFormula]

example (r : ℕ) : photonTotal (fun _ : Fin r => 0) = 0 := by simp [photonTotal]

example {N : ℕ} (n : Fin N → ℕ) : multiKet n n = 1 := by simp [multiKet]

end QAlgorithms.Papers.Independent.Renew46.P30


