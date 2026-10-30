-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09
-- name    : QAlgorithms_Papers_Independent_Extend50_P09
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T23:19:36.297026+00:00
-- url     : https://prove2.me/theorems/03ef8894-11ac-4904-afa5-b2f91acf1fc0
-- title:
--   Definitions for Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries
-- statement:
--   The objects the formalized statements of *Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries* (arXiv:2112.01498) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CovariantWord`: Computational basis for n d-level systems (§II, p.2).
--   - `pdist`: Root-fidelity purified distance, (1)–(2), p.2.
--   - `choiError`: Eq.(6), p.3: optimize over all CPTP decoders, normalized Choi input.
--   - `optimalWorstRecoveryError`: Eq.(8), p.3: one decoder is chosen before the reference-entangled input. A reference of dimension dim L suffices; pure unit inputs suffice.
--   - `selectedRecoveryError`: Select the source's two recovery criteria.
--   - `firstCoordinates`: First k tensor factors; the bound prevents a truncated physical register.
--   - `remainingCoordinates`: Remaining n-k tensor factors.
--   - `append`: Append the fixed ancillary density operator, Defs.1–2, pp.5,11.
--   - `appendUnitaryEncoder`: Unitary conjugation after appending the ancillary state.
--   - `RetainedConfigurations`: Configuration on retained sites S. Locations are fixed before U.
--   - `joinSites`: Join configurations on S and its complement, p.14.
--   - `retain`: Partial trace retaining precisely S, §§III B, IV C.
--   - `noisyEncoder`: Receiver retains the complement of the known erased set.
--   - `chargeHammingWeight`: Hamming weight of a binary computational word, p.5.
--   - `u1ChargeOperator`: Charge operator Q(n), p.5.
--   - `u1SectorProjector`: Charge eigenspace projector, including the zero projector on impossible sectors.
--   - `ChargeState`: Def.1, p.5: normalized pure ancilla of charge alpha.
--   - `chargeRotation`: U(1) action exp(-i theta Q), §III A, p.5.
--   - `U1Group`: Full charge commutant, with full U(binomial(n,j)) blocks, p.5.
--   - `collectiveQuditAction`: Collective single-qudit action, Eq.(71), p.10.
--   - `SUGroup`: Compact commutant as DEFINED on p.10, including determinant one. This is not the incorrect independent SU(r_lambda)-block reading on p.11.
--   - `FullGroup`: Full unconstrained unitary group (§VI, pp.13–14).
--   - `IsCommutantHaarLaw`: Probability law supported on the named compact matrix group, invariant under every left translation. This characterizes its normalized Haar measure.
--   - `PhysicalUnitaryLaws`: A family of laws, one for each physical register size.
--   - `sdp`: SDP value of (B14), p.17, for arbitrary PSD operators including zero. The feasible set is nonempty and bounded below for PSD input.
--   - `chooseZ`: Signed lower binomial index; negative indices contribute zero.
--   - `hyper`: Conditional probabilities in (C2), with all invalid sectors omitted.
--   - `choiMarginalCoefficient`: Beta of (C4), p.19, a coefficient per computational basis vector.
--   - `avgChoi`: Exact averaged environmental Choi state of (C2), p.19.
--   - `choiMarginalState`: Marginal zeta_0 of (C3)–(C5), p.19.
--   - `avgFullChoi`: Exact averaged full physical Choi state of (C1), p.19.
--   - `comparatorFidelity`: Exact (C6), interpreted as the fidelity of its constructed states.
--   - `comparatorDistance`: The symmetry/comparator distance, not optimized recovery error.
--   - `avgBasis`: Exact averaged basis environment state, (C20), p.21.
--   - `basisDistance`: Largest basis symmetry distance, using all logical basis words.
--   - `u1Leading`: Leading term in Thms.2–3, pp.5,7.
--   - `u1Ratio`: Relative remainder parameter: k²t²/n for Choi, kt²/n for worst case.
--   - `U1Performance`: Full Thm.2 or Thm.3 contract. Constants precede all admissible size subsequences, ancillas and erased sets; thresholds may depend on convergence. No integrality of a*n is demanded off the chosen unbounded subsequence.
--   - `rdim`: Actual Specht and Schur dimensions, pp.9–10.
--   - `ldim`: Actual Schur-module dimension, pp.9–10.
--   - `embeddedSchurSpechtVector`: Physical vector for one Schur basis coordinate and a fixed Specht unit vector, using the accepted constructed Schur transform, Def.2, p.11.
--   - `suAncilla`: Def.2's actual embedded mixed ancilla I_L/l tensor |psi><psi|. No arbitrary certified density matrix or dimension is supplied.
--   - `SUPerformance`: Full Thm.5/6 contract, pp.11–12. Constants are uniform over every partition with a FIXED separation eta, its Specht vector, and erased position. Uses the physical receiver and CPTP recovery even when the ancilla is mixed.
--   - `jointUnitaryEntryMoment`: Degree-(s,s) joint physical matrix-entry jointUnitaryEntryMoment. Cross-block phases are included; matching marginal block designs alone does not suffice (§V).
--   - `DesignLaw`: Exact symmetric 2-design, §V p.13: probability, group support and FULL first/second conjugation moments equal to the named Haar law.
--   - `concat`: Reassemble first t and last n-t coordinates in their physical order.
--   - `firstTrace`: Complementary erasure keeping the FIRST t qudits, (A9), (B8).
--   - `erasureChoi`: Normalized Choi state of the actual complementary partial trace.
--   - `initialChoi`: Initial normalized Choi ket, before U, (B6), p.17.
--   - `u1Xi`: The diagonal U(1) Xi of (B4), canonically embedded in A tensor Abar. Cross-charge sectors are zero. Zero padding the A* register preserves H_min.
--   - `u1Lambda`: Constructed Lambda=Xi(Psi tensor Choi(tau))Xi†, (B3)–(B4), p.16. Order is A*=(A,Abar), followed by (R,E); no entropy certificate is a field.
--   - `choiLambda`: Choi instance of the constructed Lambda.
--   - `simpleInitial`: An arbitrary normalized logical ket with the same fixed charge ancilla, and a one-dimensional reference, as in Appendix B2.
--   - `simpleLambda`: Basis or superposition instance of Lambda, with trivial reference.
--   - `sectorBell`: Normalized equal-weight-u1SectorProjector entangled vector, (B5), p.17. Impossible sectors return zero and are excluded from all normalized uses.
--   - `choiGammaCoefficient`: Actual Gamma_i of (B11)–(B12), with only physical j sectors.
--   - `choiKappaValue`: Kappa, (B25), p.18: NO square root on the two binomial factors in the inner sum. Signed indices omit every impossible u1SectorProjector.
--   - `FourPhase`: Four unit phases used for the normalized two-basis-state superpositions.
--   - `superposition`: (49)–(50), p.7; x!=y is carried at every normalized use.
--   - `SymmetryBlockCoordinates`: A direct-sum-product coordinate index, (26), p.4.
--   - `StarIndex`: The A* output coordinates, with the two multiplicity factors only.
--   - `blockProjector`: Physical projector onto a block of the actual unitary decomposition.
--   - `generalXi`: Xi of (26)/(A5), pp.4,15. In normalized Bell contraction the sqrt(l_j) cancels; the barred decomposition uses conjugate coordinates.
--   - `generalLambda`: Lambda of (25)/(A5), constructed from its input, normalized Choi state and the actual decomposition. No desired norm/entropy bound is assumed.
--   - `physicalSchurBlockCoordinates`: The actual accepted Schur transform reordered with L first and R second.
--   - `shapeEntropy`: Shannon entropy of the zero-padded normalized row vector, (A16), p.16.
--   - `constantCoeff11`: Coefficient in (C17), PDF p.20. The term -2 sqrt(2) alpha is LINEAR in alpha; it is not -2 sqrt(2 alpha).
--   - `constantCoeff22`: Coefficient in (C18), PDF p.20.
--   - `isotypicState`: Actual normalized lambda-isotypic projector in n-1 qudits, (D9).
--   - `removeSite`: Delete the j-th coordinate; t>=1 is supplied at every use.
--   - `insertAt`: rho on retained site j and tau on the other t-1 retained sites.
--   - `logicalMatrix`: Convert the one-qudit logical register to its single site.
--   - `suMarginalFormula`: (D10), including t=n. The last term is omitted at t=n rather than tracing a fictitious -1 qudits.
--   - `oneErasureMeanChannel`: Exact oneErasureMeanChannel averaged erased-qudit channel, (D13), p.22.
--   - `schmidtKet`: Schmidt probabilities (not amplitudes) give this normalized ket.
--   - `schmidtLeading`: Coefficient of 1/n in (D23); 0/0=0 is the continuous value for two zero Schmidt probabilities.
--   - `FlaggedIndex`: Classical location flag with its corresponding surviving register, p.14.
--   - `LocationLaw`: Arbitrary distribution over erased sets of exactly t sites, independent of the unknown logical state.
--   - `locationFlaggedErasureEncoder`: Flagged erasure after the appendUnitaryEncoder: the receiver learns S and gets S^c. Different location flags are orthogonal blocks.
--   - `locationFailure`: Failure means either one erased set violates the bound or one flagged mixture violates it. A single good appendUnitaryEncoder works simultaneously for all locations and all input-independent distributions of the fixed erasure size.
--   - `U1LocationPerformance`: U(1) main-bound extension to flagged random erasures, §VI p.14.
--   - `SULocationPerformance`: SU(d) extension to one flagged random erasure, §VI p.14.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, https://arxiv.org/abs/2112.01498v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02

/-!
Statements from Kong–Liu, arXiv:2112.01498v2. All page references are PDF pages.
Paper-local definitions have complete bodies. Error is always optimal CPTP
RECOVERY error; no erased-register relaxation is used for mixed encoders.
Compilation is pending the batch mechanical handoff.
-/
noncomputable section
-- Finite-matrix Bochner averages use the standard entrywise norm and topology.
open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder
open MeasureTheory Filter
namespace QAlgorithms.Papers.Independent.Extend50.P09
attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.
open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)
open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)
open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

/-- Borel sigma algebra of the finite-dimensional physical matrix space (§II A). -/
local instance covariantMatrixMeasurable (I : Type*) [Fintype I] :
    MeasurableSpace (Op I) := borel _

/-- The physical matrix sigma algebra is Borel (§II A). -/
local instance covariantMatrixBorel (I : Type*) [Fintype I] :
    BorelSpace (Op I) := ⟨rfl⟩

/-- Computational basis for n d-level systems (§II, p.2). -/
abbrev CovariantWord (d n : ℕ) := Fin n → Fin d

/-- Root-fidelity purified distance, (1)–(2), p.2. -/
def pdist {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Op I) : ℝ :=
  Real.sqrt (1 - rootFidelity rho sigma ^ 2)

/-- Eq.(6), p.3: optimize over all CPTP decoders, normalized Choi input. -/
def choiError {L B : Type*} [Fintype L] [DecidableEq L]
    [Fintype B] [DecidableEq B] (channel : Superop L B) : ℝ :=
  sInf {e : ℝ | ∃ D : Superop B L, IsChannel D ∧
    e = pdist (pureDensity (bell L))
      (idTensorSuperop (R := L) (D ∘ channel) (pureDensity (bell L)))}

/-- Eq.(8), p.3: one decoder is chosen before the reference-entangled input.
A reference of dimension dim L suffices; pure unit inputs suffice. -/
def optimalWorstRecoveryError {L B : Type*} [Fintype L] [DecidableEq L]
    [Fintype B] [DecidableEq B] (channel : Superop L B) : ℝ :=
  sInf {e : ℝ | ∃ D : Superop B L, IsChannel D ∧
    e = sSup {v : ℝ | ∃ psi : EuclideanSpace ℂ (L × L), IsState psi ∧
      v = pdist (pureDensity psi)
        (idTensorSuperop (R := L) (D ∘ channel) (pureDensity psi))}}

/-- Select the source's two recovery criteria. -/
def selectedRecoveryError {L B : Type*} [Fintype L] [DecidableEq L]
    [Fintype B] [DecidableEq B] (worst : Bool) (C : Superop L B) : ℝ :=
  if worst then optimalWorstRecoveryError C else choiError C

/-- First k tensor factors; the bound prevents a truncated physical register. -/
def firstCoordinates {d n k : ℕ} (h : k ≤ n) (x : CovariantWord d n) : CovariantWord d k :=
  fun i => x ⟨i.val, lt_of_lt_of_le i.isLt h⟩

/-- Remaining n-k tensor factors. -/
def remainingCoordinates {d n k : ℕ} (x : CovariantWord d n) : CovariantWord d (n-k) :=
  fun i => x ⟨k+i.val, by omega⟩

/-- Append the fixed ancillary density operator, Defs.1–2, pp.5,11. -/
def append {d n k : ℕ} (h : k ≤ n) (anc : Op (CovariantWord d (n-k))) :
    Superop (CovariantWord d k) (CovariantWord d n) :=
  fun rho a b => rho (firstCoordinates h a) (firstCoordinates h b) * anc (remainingCoordinates a) (remainingCoordinates b)

/-- Unitary conjugation after appending the ancillary state. -/
def appendUnitaryEncoder {d n k : ℕ} (h : k ≤ n) (anc : Op (CovariantWord d (n-k)))
    (U : Op (CovariantWord d n)) : Superop (CovariantWord d k) (CovariantWord d n) :=
  fun rho => U * append h anc rho * Uᴴ

/-- Configuration on retained sites S. Locations are fixed before U. -/
abbrev RetainedConfigurations (d n : ℕ) (S : Finset (Fin n)) := {i : Fin n // i ∈ S} → Fin d

/-- Join configurations on S and its complement, p.14. -/
def joinSites {d n : ℕ} (S : Finset (Fin n))
    (a : RetainedConfigurations d n S) (b : RetainedConfigurations d n Sᶜ) : CovariantWord d n :=
  fun i => if h : i ∈ S then a ⟨i,h⟩ else b ⟨i, by simpa using h⟩

/-- Partial trace retaining precisely S, §§III B, IV C. -/
def retain {d n : ℕ} (S : Finset (Fin n)) : Superop (CovariantWord d n) (RetainedConfigurations d n S) :=
  fun rho a b => ∑ z : RetainedConfigurations d n Sᶜ, rho (joinSites S a z) (joinSites S b z)

/-- Receiver retains the complement of the known erased set. -/
def noisyEncoder {d n k : ℕ} (h : k ≤ n) (anc : Op (CovariantWord d (n-k)))
    (S : Finset (Fin n)) (U : Op (CovariantWord d n)) :=
  retain Sᶜ ∘ appendUnitaryEncoder h anc U

/-- Hamming weight of a binary computational word, p.5. -/
def chargeHammingWeight {n : ℕ} (x : CovariantWord 2 n) : ℕ := ∑ i, (x i).val

/-- Charge operator Q(n), p.5. -/
def u1ChargeOperator (n : ℕ) : Op (CovariantWord 2 n) := Matrix.diagonal fun x => (chargeHammingWeight x : ℂ)

/-- Charge eigenspace projector, including the zero projector on impossible sectors. -/
def u1SectorProjector (n j : ℕ) : Op (CovariantWord 2 n) :=
  Matrix.diagonal fun x => if chargeHammingWeight x = j then 1 else 0

/-- Def.1, p.5: normalized pure ancilla of charge alpha. -/
def ChargeState {m : ℕ} (alpha : ℕ) (psi : EuclideanSpace ℂ (CovariantWord 2 m)) : Prop :=
  IsState psi ∧ ∀ x, chargeHammingWeight x ≠ alpha → psi x = 0

/-- U(1) action exp(-i theta Q), §III A, p.5. -/
def chargeRotation (n : ℕ) (theta : ℝ) : Op (CovariantWord 2 n) :=
  Matrix.diagonal fun x => Complex.exp (-Complex.I * (theta : ℂ) * (chargeHammingWeight x : ℂ))

/-- Full charge commutant, with full U(binomial(n,j)) blocks, p.5. -/
def U1Group (n : ℕ) (U : Op (CovariantWord 2 n)) : Prop :=
  Uᴴ * U = 1 ∧ U * u1ChargeOperator n = u1ChargeOperator n * U

/-- Collective single-qudit action, Eq.(71), p.10. -/
def collectiveQuditAction {d : ℕ} (n : ℕ) (U : Op (Fin d)) : Op (CovariantWord d n) :=
  fun a b => ∏ i, U (a i) (b i)

/-- Compact commutant as DEFINED on p.10, including determinant one.
This is not the incorrect independent SU(r_lambda)-block reading on p.11. -/
def SUGroup (d n : ℕ) (V : Op (CovariantWord d n)) : Prop :=
  Vᴴ * V = 1 ∧ V.det = 1 ∧ ∀ U : Op (Fin d), Uᴴ * U = 1 → U.det = 1 →
    V * collectiveQuditAction n U = collectiveQuditAction n U * V

/-- Full unconstrained unitary group (§VI, pp.13–14). -/
def FullGroup (d n : ℕ) (U : Op (CovariantWord d n)) : Prop := Uᴴ * U = 1

/-- Probability law supported on the named compact matrix group, invariant
under every left translation. This characterizes its normalized Haar measure. -/
def IsCommutantHaarLaw {I : Type*} [Fintype I] [DecidableEq I]
    (G : Op I → Prop) (mu : Measure (Op I)) : Prop :=
  IsProbabilityMeasure mu ∧ mu {U | ¬ G U} = 0 ∧
    ∀ V, G V → Measure.map (fun U => V * U) mu = mu

/-- A family of laws, one for each physical register size. -/
abbrev PhysicalUnitaryLaws (d : ℕ) := (n : ℕ) → Measure (Op (CovariantWord d n))

/-- SDP value of (B14), p.17, for arbitrary PSD operators including zero.
The feasible set is nonempty and bounded below for PSD input. -/
def sdp {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : Op (A × B)) : ℝ :=
  sInf {s : ℝ | ∃ sigma : Op B, sigma.PosSemidef ∧ s = sigma.trace.re ∧
    (Matrix.kronecker (1 : Op A) sigma - rho).PosSemidef}

/-- Signed lower binomial index; negative indices contribute zero. -/
def chooseZ (n : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j then (n.choose j.toNat : ℝ) else 0

/-- Conditional probabilities in (C2), with all invalid sectors omitted. -/
def hyper (n t q i : ℕ) : ℝ :=
  chooseZ (n-t) ((q : ℤ)-i) / (n.choose q : ℝ)

/-- Beta of (C4), p.19, a coefficient per computational basis vector. -/
def choiMarginalCoefficient (n k t alpha i : ℕ) : ℝ :=
  (2 : ℝ)^(- (k : ℤ)) * ∑ j ∈ Finset.range (k+1),
    (k.choose j : ℝ) * hyper n t (j+alpha) i

/-- Exact averaged environmental Choi state of (C2), p.19. -/
def avgChoi (n k t alpha : ℕ) : Op (CovariantWord 2 k × CovariantWord 2 t) :=
  fun x y => if x = y then
    ((2 : ℝ)^(- (k : ℤ)) * hyper n t (chargeHammingWeight x.1 + alpha) (chargeHammingWeight x.2) : ℂ) else 0

/-- Marginal zeta_0 of (C3)–(C5), p.19. -/
def choiMarginalState (n k t alpha : ℕ) : Op (CovariantWord 2 t) :=
  Matrix.diagonal fun x => (choiMarginalCoefficient n k t alpha (chargeHammingWeight x) : ℂ)

/-- Exact averaged full physical Choi state of (C1), p.19. -/
def avgFullChoi (n k alpha : ℕ) : Op (CovariantWord 2 k × CovariantWord 2 n) :=
  (2 : ℂ)^(- (k : ℤ)) • ∑ j ∈ Finset.range (k+1),
    (n.choose (j+alpha) : ℂ)⁻¹ • Matrix.kronecker (u1SectorProjector k j) (u1SectorProjector n (j+alpha))

/-- Exact (C6), interpreted as the fidelity of its constructed states. -/
def comparatorFidelity (n k t alpha : ℕ) : ℝ :=
  rootFidelity (avgChoi n k t alpha) (Matrix.kronecker (mixed (CovariantWord 2 k)) (choiMarginalState n k t alpha))

/-- The symmetry/comparator distance, not optimized recovery error. -/
def comparatorDistance (n k t alpha : ℕ) : ℝ :=
  pdist (avgChoi n k t alpha) (Matrix.kronecker (mixed (CovariantWord 2 k)) (choiMarginalState n k t alpha))

/-- Exact averaged basis environment state, (C20), p.21. -/
def avgBasis (n t q : ℕ) : Op (CovariantWord 2 t) :=
  Matrix.diagonal fun x => (hyper n t q (chargeHammingWeight x) : ℂ)

/-- Largest basis symmetry distance, using all logical basis words. -/
def basisDistance (n k t alpha : ℕ) : ℝ :=
  (Finset.univ : Finset (CovariantWord 2 k)).sup' Finset.univ_nonempty
    (fun x => pdist (avgBasis n t (chargeHammingWeight x+alpha)) (choiMarginalState n k t alpha))

/-- Leading term in Thms.2–3, pp.5,7. -/
def u1Leading (worst : Bool) (a : ℝ) (n k t : ℕ) : ℝ :=
  (if worst then (k : ℝ) * Real.sqrt t else Real.sqrt ((t : ℝ)*k)) /
    (4 * n * Real.sqrt (a*(1-a)))

/-- Relative remainder parameter: k²t²/n for Choi, kt²/n for worst case. -/
def u1Ratio (worst : Bool) (n k t : ℕ) : ℝ :=
  (k : ℝ)^(if worst then 1 else 2) * (t : ℝ)^2 / n

/-- Full Thm.2 or Thm.3 contract. Constants precede all admissible size
subsequences, ancillas and erased sets; thresholds may depend on convergence.
No integrality of a*n is demanded off the chosen unbounded subsequence. -/
def U1Performance (worst : Bool) (laws : PhysicalUnitaryLaws 2) : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ N k t alpha : ℕ → ℕ,
    Tendsto N atTop atTop →
    Tendsto (fun i => u1Ratio worst (N i) (k i) (t i)) atTop (nhds 0) →
    (∀ i, 0 < N i ∧ 0 < k i ∧ k i ≤ N i ∧ 0 < t i ∧ t i ≤ N i ∧
      alpha i ≤ N i-k i ∧ (alpha i : ℝ) = a * N i) →
    ∃ i0 : ℕ, ∀ i ≥ i0, ∀ h : k i ≤ N i,
    ∀ psi : EuclideanSpace ℂ (CovariantWord 2 (N i-k i)), ChargeState (alpha i) psi →
    ∀ S : Finset (Fin (N i)), S.card = t i →
    let err := fun U => selectedRecoveryError worst (noisyEncoder h (pureDensity psi) S U)
    let b := u1Leading worst a (N i) (k i) (t i) *
      (1 + C * u1Ratio worst (N i) (k i) (t i))
    (∫ U, err U ∂laws (N i)) ≤ b ∧
      (laws (N i)).real {U | b < err U} ≤ Real.exp (-c * N i)

/-- Actual Specht and Schur dimensions, pp.9–10. -/
def rdim {d n : ℕ} (lam : Schur.Partition d n) : ℕ :=
  Module.finrank ℂ (Schur.spechtSpace lam)

/-- Actual Schur-module dimension, pp.9–10. -/
def ldim {d n : ℕ} (lam : Schur.Partition d n) : ℕ :=
  Module.finrank ℂ (Schur.schurModule lam)

/-- Physical vector for one Schur basis coordinate and a fixed Specht unit
vector, using the accepted constructed Schur transform, Def.2, p.11. -/
def embeddedSchurSpechtVector {d m : ℕ} (lam : Schur.Partition d m)
    (psi : EuclideanSpace ℂ (Fin (rdim lam))) (l : Fin (ldim lam)) :
    EuclideanSpace ℂ (CovariantWord d m) :=
  WithLp.toLp 2 fun x => ∑ r, conj (Schur.decomposition d m ⟨lam,(r,l)⟩ x) * psi r

/-- Def.2's actual embedded mixed ancilla I_L/l tensor |psi><psi|.
No arbitrary certified density matrix or dimension is supplied. -/
def suAncilla {d m : ℕ} (lam : Schur.Partition d m)
    (psi : EuclideanSpace ℂ (Fin (rdim lam))) : Op (CovariantWord d m) :=
  (ldim lam : ℂ)⁻¹ • ∑ l : Fin (ldim lam), pureDensity (embeddedSchurSpechtVector lam psi l)

/-- Full Thm.5/6 contract, pp.11–12. Constants are uniform over every
partition with a FIXED separation eta, its Specht vector, and erased position.
Uses the physical receiver and CPTP recovery even when the ancilla is mixed. -/
def SUPerformance (worst : Bool) (d : ℕ) (laws : PhysicalUnitaryLaws d) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∃ n0 : ℕ, ∀ n ≥ n0, ∀ hn : 2 ≤ n,
    ∀ lam : Schur.Partition d (n-1),
    eta * n ≤ (n : ℝ) - lam.val.rowLen 0 →
    ∀ psi : EuclideanSpace ℂ (Fin (rdim lam)), IsState psi →
    ∀ S : Finset (Fin n), S.card = 1 →
    let err := fun V => selectedRecoveryError worst
      (noisyEncoder (show 1 ≤ n by omega) (suAncilla lam psi) S V)
    let b := Real.sqrt ((d : ℝ)^2-1)/(2*n) + C/(n : ℝ)^2
    (∫ V, err V ∂laws n) ≤ b ∧ (laws n).real {V | b < err V} ≤ Real.exp (-c*n)

/-- Degree-(s,s) joint physical matrix-entry jointUnitaryEntryMoment. Cross-block phases
are included; matching marginal block designs alone does not suffice (§V). -/
def jointUnitaryEntryMoment {I : Type*} [Fintype I] (s : ℕ)
    (a b c e : Fin s → I) (U : Op I) : ℂ :=
  (∏ i, U (a i) (b i)) * conj (∏ i, U (c i) (e i))

/-- Exact symmetric 2-design, §V p.13: probability, group support and
FULL first/second conjugation moments equal to the named Haar law. -/
def DesignLaw {I : Type*} [Fintype I] [DecidableEq I]
    (G : Op I → Prop) (mu nu : Measure (Op I)) : Prop :=
  IsProbabilityMeasure mu ∧ mu {U | ¬ G U} = 0 ∧ IsCommutantHaarLaw G nu ∧
    ∀ s ∈ ({1,2} : Finset ℕ), ∀ a b c e : Fin s → I,
      (∫ U, jointUnitaryEntryMoment s a b c e U ∂mu) = ∫ U, jointUnitaryEntryMoment s a b c e U ∂nu

example (n : ℕ) : chargeRotation n 0 = 1 := by simp [chargeRotation]

example (n : ℕ) : chargeHammingWeight (fun _ : Fin n => (0 : Fin 2)) = 0 := by simp [chargeHammingWeight]

example : chooseZ 3 (-1) = 0 := by norm_num [chooseZ]

example {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    negLog 0 = (⊤ : EReal) := by simp [negLog]

example (n k t alpha : ℕ) : selectedRecoveryError false
    (fun rho : Op (CovariantWord 2 k) => rho) = choiError (fun rho : Op (CovariantWord 2 k) => rho) := rfl

example {d n : ℕ} (S : Finset (Fin n)) (X : Op (CovariantWord d n)) :
    retain S X = fun a b => ∑ z : RetainedConfigurations d n Sᶜ, X (joinSites S a z) (joinSites S b z) := rfl

example (d n : ℕ) (U : Op (Fin d)) (a b : CovariantWord d n) :
    collectiveQuditAction n U a b = ∏ i, U (a i) (b i) := rfl

/-- Reassemble first t and last n-t coordinates in their physical order. -/
def concat {d n t : ℕ} (ht : t ≤ n) (x : CovariantWord d t) (z : CovariantWord d (n-t)) : CovariantWord d n :=
  fun i => if h : i.val < t then x ⟨i.val,h⟩ else z ⟨i.val-t,by omega⟩

/-- Complementary erasure keeping the FIRST t qudits, (A9), (B8). -/
def firstTrace {d n t : ℕ} (ht : t ≤ n) : Superop (CovariantWord d n) (CovariantWord d t) :=
  fun X x y => ∑ z : CovariantWord d (n-t), X (concat ht x z) (concat ht y z)

/-- Normalized Choi state of the actual complementary partial trace. -/
def erasureChoi {d n t : ℕ} (ht : t ≤ n) : Op (CovariantWord d n × CovariantWord d t) :=
  idTensorSuperop (R := CovariantWord d n) (firstTrace ht) (pureDensity (bell (CovariantWord d n)))

/-- Initial normalized Choi ket, before U, (B6), p.17. -/
def initialChoi {n k : ℕ} (hk : k ≤ n) (psi : EuclideanSpace ℂ (CovariantWord 2 (n-k))) :
    EuclideanSpace ℂ (CovariantWord 2 k × CovariantWord 2 n) :=
  WithLp.toLp 2 fun p => bell (CovariantWord 2 k) (p.1,firstCoordinates hk p.2) * psi (remainingCoordinates p.2)

/-- The diagonal U(1) Xi of (B4), canonically embedded in A tensor Abar.
Cross-charge sectors are zero. Zero padding the A* register preserves H_min. -/
def u1Xi (n : ℕ) (a b : CovariantWord 2 n) : ℂ :=
  if chargeHammingWeight a = chargeHammingWeight b then (Real.sqrt ((2 : ℝ)^n/(n.choose (chargeHammingWeight a) : ℝ)) : ℂ) else 0

/-- Constructed Lambda=Xi(Psi tensor Choi(tau))Xi†, (B3)–(B4), p.16.
Order is A*=(A,Abar), followed by (R,E); no entropy certificate is a field. -/
def u1Lambda {R : Type*} [Fintype R] {n t : ℕ} (ht : t ≤ n)
    (Psi : Op (R × CovariantWord 2 n)) : Op ((CovariantWord 2 n × CovariantWord 2 n) × (R × CovariantWord 2 t)) :=
  fun a b => u1Xi n a.1.1 a.1.2 * conj (u1Xi n b.1.1 b.1.2) *
    Psi (a.2.1,a.1.1) (b.2.1,b.1.1) * erasureChoi ht (a.1.2,a.2.2) (b.1.2,b.2.2)

/-- Choi instance of the constructed Lambda. -/
def choiLambda {n k t : ℕ} (hk : k ≤ n) (ht : t ≤ n)
    (psi : EuclideanSpace ℂ (CovariantWord 2 (n-k))) :=
  u1Lambda ht (pureDensity (initialChoi hk psi))

/-- An arbitrary normalized logical ket with the same fixed charge ancilla,
and a one-dimensional reference, as in Appendix B2. -/
def simpleInitial {n k : ℕ} (hk : k ≤ n)
    (psi : EuclideanSpace ℂ (CovariantWord 2 (n-k))) (v : EuclideanSpace ℂ (CovariantWord 2 k)) :
    EuclideanSpace ℂ (Unit × CovariantWord 2 n) :=
  WithLp.toLp 2 fun p => v (firstCoordinates hk p.2) * psi (remainingCoordinates p.2)

/-- Basis or superposition instance of Lambda, with trivial reference. -/
def simpleLambda {n k t : ℕ} (hk : k ≤ n) (ht : t ≤ n)
    (psi : EuclideanSpace ℂ (CovariantWord 2 (n-k))) (v : EuclideanSpace ℂ (CovariantWord 2 k)) :=
  u1Lambda ht (pureDensity (simpleInitial hk psi v))

/-- Normalized equal-weight-u1SectorProjector entangled vector, (B5), p.17.
Impossible sectors return zero and are excluded from all normalized uses. -/
def sectorBell (m q : ℕ) : EuclideanSpace ℂ (CovariantWord 2 m × CovariantWord 2 m) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 ∧ chargeHammingWeight p.1 = q then
    ((Real.sqrt (m.choose q : ℝ))⁻¹ : ℂ) else 0

/-- Actual Gamma_i of (B11)–(B12), with only physical j sectors. -/
def choiGammaCoefficient {n k t : ℕ} (hk : k ≤ n) (ht : t ≤ n) (alpha : ℕ)
    (psi : EuclideanSpace ℂ (CovariantWord 2 (n-k))) (i : ℕ)
    (a : CovariantWord 2 n) (b : CovariantWord 2 t) (r : CovariantWord 2 k) (e : CovariantWord 2 t) : ℂ :=
  ∑ j ∈ Finset.range (n+1),
    if i ≤ j ∧ j-i ≤ t ∧ alpha ≤ j ∧ j-alpha ≤ k then
      (Real.sqrt (((t.choose (j-i) : ℝ) * (k.choose (j-alpha) : ℝ)) /
        ((2 : ℝ)^k * (n.choose j : ℝ))) : ℂ) *
        sectorBell t (j-i) (b,e) * sectorBell k (j-alpha) (firstCoordinates hk a,r) * psi (remainingCoordinates a)
    else 0

/-- Kappa, (B25), p.18: NO square root on the two binomial factors
in the inner sum. Signed indices omit every impossible u1SectorProjector. -/
def choiKappaValue (n k t alpha : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n-t+1),
    (∑ j ∈ Finset.range (n+1),
      chooseZ t ((j : ℤ)-i) * chooseZ k ((j : ℤ)-alpha) /
        Real.sqrt ((2 : ℝ)^k * (n.choose j : ℝ)))^2

/-- Four unit phases used for the normalized two-basis-state superpositions. -/
def FourPhase (z : ℂ) : Prop := z = 1 ∨ z = -1 ∨ z = Complex.I ∨ z = -Complex.I

/-- (49)–(50), p.7; x!=y is carried at every normalized use. -/
def superposition {k : ℕ} (x y : CovariantWord 2 k) (z : ℂ) : EuclideanSpace ℂ (CovariantWord 2 k) :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (ket x + z • ket y)

/-- A direct-sum-product coordinate index, (26), p.4. -/
abbrev SymmetryBlockCoordinates {J : Type*} (l r : J → ℕ) := (j : J) × (Fin (l j) × Fin (r j))

/-- The A* output coordinates, with the two multiplicity factors only. -/
abbrev StarIndex {J : Type*} (r : J → ℕ) := (j : J) × (Fin (r j) × Fin (r j))

/-- Physical projector onto a block of the actual unitary decomposition. -/
def blockProjector {J : Type*} [Fintype J] {d n : ℕ} (l r : J → ℕ)
    (S : Matrix (SymmetryBlockCoordinates l r) (CovariantWord d n) ℂ) (j : J) : Op (CovariantWord d n) :=
  fun a b => ∑ u : Fin (l j), ∑ v : Fin (r j), conj (S ⟨j,(u,v)⟩ a) * S ⟨j,(u,v)⟩ b

/-- Xi of (26)/(A5), pp.4,15. In normalized Bell contraction the
sqrt(l_j) cancels; the barred decomposition uses conjugate coordinates. -/
def generalXi {J : Type*} [Fintype J] {d n : ℕ} (l r : J → ℕ)
    (S : Matrix (SymmetryBlockCoordinates l r) (CovariantWord d n) ℂ) (j : StarIndex r)
    (a b : CovariantWord d n) : ℂ :=
  (Real.sqrt ((d : ℝ)^n / r j.1) : ℂ) *
    ∑ u : Fin (l j.1), S ⟨j.1,(u,j.2.1)⟩ a * conj (S ⟨j.1,(u,j.2.2)⟩ b)

/-- Lambda of (25)/(A5), constructed from its input, normalized Choi
state and the actual decomposition. No desired norm/entropy bound is assumed. -/
def generalLambda {J R : Type*} [Fintype J] [Fintype R]
    {d n t : ℕ} (ht : t ≤ n) (l r : J → ℕ)
    (S : Matrix (SymmetryBlockCoordinates l r) (CovariantWord d n) ℂ) (Psi : Op (R × CovariantWord d n)) :
    Op (StarIndex r × (R × CovariantWord d t)) :=
  fun x y => ∑ a : CovariantWord d n, ∑ b : CovariantWord d n, ∑ c : CovariantWord d n, ∑ e : CovariantWord d n,
    generalXi l r S x.1 a b * conj (generalXi l r S y.1 c e) *
      Psi (x.2.1,a) (y.2.1,c) * erasureChoi ht (b,x.2.2) (e,y.2.2)

/-- The actual accepted Schur transform reordered with L first and R second. -/
def physicalSchurBlockCoordinates (d n : ℕ) :
    Matrix (SymmetryBlockCoordinates (fun lam : Schur.Partition d n => ldim lam) rdim) (CovariantWord d n) ℂ :=
  fun j a => Schur.decomposition d n ⟨j.1,(j.2.2,j.2.1)⟩ a

/-- Shannon entropy of the zero-padded normalized row vector, (A16), p.16. -/
def shapeEntropy {d m : ℕ} (lam : Schur.Partition d m) : ℝ :=
  -∑ i : Fin d, ((lam.val.rowLen i.val : ℝ)/m) * Real.logb 2 ((lam.val.rowLen i.val : ℝ)/m)

example {d n t : ℕ} (ht : t ≤ n) (x : CovariantWord d t) (z : CovariantWord d (n-t))
    (i : Fin n) (hi : i.val < t) : concat ht x z i = x ⟨i.val,hi⟩ := by
  simp [concat,hi]

example {R : Type*} [Fintype R] {n t : ℕ} (ht : t ≤ n) :
    u1Lambda (R := R) ht 0 = 0 := by ext a b; simp [u1Lambda]

example (m q : ℕ) (a b : CovariantWord 2 m) (h : a ≠ b) : sectorBell m q (a,b) = 0 := by
  simp [sectorBell,h]

/-- Coefficient in (C17), PDF p.20. The term -2 sqrt(2) alpha is LINEAR
in alpha; it is not -2 sqrt(2 alpha). -/
def constantCoeff11 (alpha : ℕ) : ℝ :=
  (-Real.sqrt 2-2*Real.sqrt 2*alpha+Real.sqrt ((alpha : ℝ)*(2*alpha+1))+
    Real.sqrt (((alpha : ℝ)+1)*(2*alpha+1)))/(2*Real.sqrt 2)

/-- Coefficient in (C18), PDF p.20. -/
def constantCoeff22 (alpha : ℕ) : ℝ :=
  (-2-2*(alpha : ℝ)+Real.sqrt ((alpha : ℝ)*(alpha+1))+
    Real.sqrt (((alpha : ℝ)+1)*(alpha+2)))/2

/-- Actual normalized lambda-isotypic projector in n-1 qudits, (D9). -/
def isotypicState {d m : ℕ} (lam : Schur.Partition d m) : Op (CovariantWord d m) :=
  ((ldim lam * rdim lam : ℕ) : ℂ)⁻¹ • Schur.isotypicProjector lam

/-- Delete the j-th coordinate; t>=1 is supplied at every use. -/
def removeSite {d t : ℕ} (j : Fin t) (x : CovariantWord d t) : CovariantWord d (t-1) :=
  fun i => x ⟨if i.val < j.val then i.val else i.val+1,by split_ifs <;> omega⟩

/-- rho on retained site j and tau on the other t-1 retained sites. -/
def insertAt {d t : ℕ} (j : Fin t) (rho : Op (Fin d)) (tau : Op (CovariantWord d (t-1))) :
    Op (CovariantWord d t) :=
  fun a b => rho (a j) (b j) * tau (removeSite j a) (removeSite j b)

/-- Convert the one-qudit logical register to its single site. -/
def logicalMatrix {d : ℕ} (rho : Op (Fin d)) : Op (CovariantWord d 1) :=
  fun a b => rho (a 0) (b 0)

/-- (D10), including t=n. The last term is omitted at t=n rather
than tracing a fictitious -1 qudits. -/
def suMarginalFormula {d n t : ℕ} (hn : 2 ≤ n) (ht0 : 1 ≤ t) (ht : t ≤ n)
    (lam : Schur.Partition d (n-1)) (rho : Op (Fin d)) : Op (CovariantWord d t) :=
  (n : ℂ)⁻¹ • ∑ j : Fin t,
    insertAt j rho (firstTrace (show t-1 ≤ n-1 by omega) (isotypicState lam)) +
  if h : t < n then (((n-t : ℕ) : ℂ)/(n : ℂ)) •
    firstTrace (show t ≤ n-1 by omega) (isotypicState lam) else 0

/-- Exact oneErasureMeanChannel averaged erased-qudit channel, (D13), p.22. -/
def oneErasureMeanChannel (d n : ℕ) : Superop (Fin d) (Fin d) :=
  fun X => (n : ℂ)⁻¹ • X + (((n : ℂ)-1)/(n : ℂ) * X.trace) • mixed (Fin d)

/-- Schmidt probabilities (not amplitudes) give this normalized ket. -/
def schmidtKet {d : ℕ} (p : Fin d → ℝ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun a => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0

/-- Coefficient of 1/n in (D23); 0/0=0 is the continuous value
for two zero Schmidt probabilities. -/
def schmidtLeading {d : ℕ} (p : Fin d → ℝ) : ℝ :=
  Real.sqrt ((d : ℝ)/2 * (∑ i, ∑ j, p i*p j/(p i+p j))-1/4)

example (d n : ℕ) : oneErasureMeanChannel d n 0 = 0 := by simp [oneErasureMeanChannel]

example (d : ℕ) (X : Op (Fin d)) : oneErasureMeanChannel d 1 X = X := by simp [oneErasureMeanChannel]

example (m : ℕ) (a : CovariantWord 2 m) : sectorBell m (chargeHammingWeight a) (a,a) =
    ((Real.sqrt (m.choose (chargeHammingWeight a) : ℝ))⁻¹ : ℂ) := by simp [sectorBell]

/-- Classical location flag with its corresponding surviving register, p.14. -/
abbrev FlaggedIndex (d n : ℕ) := (S : Finset (Fin n)) × RetainedConfigurations d n Sᶜ

/-- Arbitrary distribution over erased sets of exactly t sites, independent
of the unknown logical state. -/
def LocationLaw {n : ℕ} (t : ℕ) (p : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ p S) ∧ (∑ S, p S = 1) ∧ ∀ S, S.card ≠ t → p S = 0

/-- Flagged erasure after the appendUnitaryEncoder: the receiver learns S and gets S^c.
Different location flags are orthogonal blocks. -/
def locationFlaggedErasureEncoder {d n k : ℕ} (hk : k ≤ n) (anc : Op (CovariantWord d (n-k)))
    (p : Finset (Fin n) → ℝ) (U : Op (CovariantWord d n)) :
    Superop (CovariantWord d k) (FlaggedIndex d n) :=
  fun rho a b => if h : a.1 = b.1 then
    (p a.1 : ℂ) * noisyEncoder hk anc a.1 U rho a.2 (h.symm ▸ b.2) else 0

/-- Failure means either one erased set violates the bound or one flagged
mixture violates it. A single good appendUnitaryEncoder works simultaneously for all
locations and all input-independent distributions of the fixed erasure size. -/
def locationFailure {d n k : ℕ} (worst : Bool) (hk : k ≤ n)
    (anc : Op (CovariantWord d (n-k))) (t : ℕ) (b : ℝ) (U : Op (CovariantWord d n)) : Prop :=
  (∃ S : Finset (Fin n), S.card = t ∧ b < selectedRecoveryError worst (noisyEncoder hk anc S U)) ∨
  (∃ p : Finset (Fin n) → ℝ, LocationLaw t p ∧
    b < selectedRecoveryError worst (locationFlaggedErasureEncoder hk anc p U))

/-- U(1) main-bound extension to flagged random erasures, §VI p.14. -/
def U1LocationPerformance (worst : Bool) (laws : PhysicalUnitaryLaws 2) : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ N k t alpha : ℕ → ℕ, Tendsto N atTop atTop →
    Tendsto (fun i => u1Ratio worst (N i) (k i) (t i)) atTop (nhds 0) →
    (∀ i, 0 < N i ∧ 0 < k i ∧ k i ≤ N i ∧ 0 < t i ∧ t i ≤ N i ∧
      alpha i ≤ N i-k i ∧ (alpha i : ℝ) = a*N i) →
    ∃ i0 : ℕ, ∀ i ≥ i0, ∀ hk : k i ≤ N i,
    ∀ psi : EuclideanSpace ℂ (CovariantWord 2 (N i-k i)), ChargeState (alpha i) psi →
    let b := u1Leading worst a (N i) (k i) (t i) *
      (1+C*u1Ratio worst (N i) (k i) (t i))
    (laws (N i)).real {U | locationFailure worst hk (pureDensity psi) (t i) b U} ≤
      Real.exp (-c*N i) ∧
    ∀ p : Finset (Fin (N i)) → ℝ, LocationLaw (t i) p →
      (∫ U, selectedRecoveryError worst (locationFlaggedErasureEncoder hk (pureDensity psi) p U) ∂laws (N i)) ≤ b

/-- SU(d) extension to one flagged random erasure, §VI p.14. -/
def SULocationPerformance (worst : Bool) (d : ℕ) (laws : PhysicalUnitaryLaws d) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∃ n0 : ℕ, ∀ n ≥ n0, ∀ hn : 2 ≤ n, ∀ lam : Schur.Partition d (n-1),
    eta*n ≤ (n : ℝ)-lam.val.rowLen 0 →
    ∀ psi : EuclideanSpace ℂ (Fin (rdim lam)), IsState psi →
    let b := Real.sqrt ((d : ℝ)^2-1)/(2*n)+C/(n : ℝ)^2
    (laws n).real {U | locationFailure worst (show 1 ≤ n by omega) (suAncilla lam psi) 1 b U} ≤
      Real.exp (-c*n) ∧
    ∀ p : Finset (Fin n) → ℝ, LocationLaw 1 p →
      (∫ U, selectedRecoveryError worst
        (locationFlaggedErasureEncoder (show 1 ≤ n by omega) (suAncilla lam psi) p U) ∂laws n) ≤ b

example {n : ℕ} (p : Finset (Fin n) → ℝ) (hp : LocationLaw 0 p)
    (S : Finset (Fin n)) (hS : S.card ≠ 0) : p S = 0 := hp.2.2 S hS

example {d n k : ℕ} (hk : k ≤ n) (anc : Op (CovariantWord d (n-k)))
    (p : Finset (Fin n) → ℝ) (U : Op (CovariantWord d n)) (rho : Op (CovariantWord d k))
    (a b : FlaggedIndex d n) (h : a.1 ≠ b.1) :
    locationFlaggedErasureEncoder hk anc p U rho a b = 0 := by simp [locationFlaggedErasureEncoder,h]

end QAlgorithms.Papers.Independent.Extend50.P09


