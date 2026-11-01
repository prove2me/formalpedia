-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P53
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T06:24:48.999807+00:00
-- url     : https://prove2.me/theorems/726b94fd-1f7c-4fa3-8b84-a4d1599cfc97
-- title:
--   Definitions for Some remarks on port-based teleportation
-- statement:
--   The objects the formalized statements of *Some remarks on port-based teleportation* (arXiv:1506.01555) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Ports`
--   - `AC`
--   - `PortComplement`
--   - `spinSinglet`: PDF p.2, Eq.(2): normalized physical spin-zero singlet. The printed second spin label m is corrected to -m, as forced by the stated spin-zero convention and the physical angular-momentum decomposition on the same page.
--   - `singletDensity`: PDF p.2, Eq.(2): singlet projector.
--   - `insertPort`: Ordered insertion of one port into its complement.
--   - `singletInsert`: PDF p.2, Eq.(4): isometric insertion of the A_i,C singlet.
--   - `portProjector`: PDF p.2, Eq.(4): P^-_(A_i,C) tensor I_rest.
--   - `pbtSignal`: PDF p.2, Eq.(4): normalized signal; used with N>=1,d>=2.
--   - `pbtRho`: PDF p.2, Eq.(5): physical signal sum.
--   - `liftA`: PDF p.2: O acts on Alice's ports and leaves C unchanged.
--   - `resource`: PDF p.2, Eq.(1): resource amplitude after applying O to A.
--   - `NormalizedResource`: PDF p.2, Eq.(1): exact resource normalization.
--   - `DeterministicPOVM`: PDF p.2: Alice's deterministic measurement on AC.
--   - `ProbabilisticPOVM`: PDF p.3: none is failure, some i is successful port i.
--   - `pbtChannelBranch`: PDF pp.2,4: induced unnormalized reference-B branch for input T on R,C. The effect determines the branch after Alice's registers are discarded.
--   - `pbtBranch`: PDF pp.3-4: normalized reference-singlet experiment.
--   - `selectPort`: Physical marginal retaining the reference and selected output port.
--   - `pbtBranchProbability`: PDF p.4: outcome probability in the reference-singlet experiment.
--   - `pbtFidelity`: PDF p.2, Eq.(3): operational entanglement fidelity of port selection.
--   - `codingState`: PDF p.4, Eq.(20): state measured when Bob sends B_k, renamed C.
--   - `codingProbability`: PDF p.4: actual coding outcome probability.
--   - `ExactProbabilistic`: PDF p.4: Choi equation for faithful successful branches, including zero probabilities without division. For these CP branches it characterizes p_i times the identity channel, also on inputs entangled with a reference.
--   - `pbtSuccessProbability`: PDF p.4: total exact-teleportation success probability.
--   - `srm`: PDF p.3, Eq.(12): SRM on the support.
--   - `completedSRM`: PDF p.3, Eqs.(12)-(13): deterministic completion.
--   - `probabilisticSRM`: PDF p.3: separate probabilistic failure effect.
--   - `conditionalFidelity`: PDF pp.4-5, Eq.(23): normalized conditional singlet overlap. Uses below have strictly positive branch probability.
--   - `SymmetricPorts`: PDF pp.4-5: symmetry conditions imposed on the actual protocol.
--   - `maximumSpinVector`: PDF p.6, A7: equal-port sum with every complementary spin at its highest weight; normalization uses its actual Euclidean norm.
--   - `quditSpinZ`: PDF p.2: physical spin-s z component, s=(d-1)/2.
--   - `quditSpinRaise`: PDF p.2: raising matrix in the m=s-r convention.
--   - `spinX`: Physical Cartesian x component.
--   - `quditSpinY`: Physical Cartesian y component.
--   - `quditOnWire`: A spin operator on a named wire of an ordered finite register.
--   - `quditCollective`: PDF p.2: physical collective angular momentum on any complement or port register.
--   - `quditCasimir`: PDF p.2: the actual squared total angular momentum.
--   - `totalComponent`: PDF p.2: addition of the C spin to all A spins.
--   - `totalCasimir`: PDF p.2: actual squared angular momentum on AC.
--   - `casimirProjector`: PDF p.2, Eqs.(7)-(8): spectral projector for twice-spin t. Impossible sectors have zero projector; no abstract decomposition is assumed.
--   - `magneticProjector`: Physical z-component slice; r=0,...,t corresponds to m=t/2-r.
--   - `rhoSpinBlock`: PDF p.2, Eq.(8): spin block constructed by singlet insertion of the actual complementary-register spin projectors.
--   - `rhoSpinMagnetic`: PDF p.6, Eq.(A2): physical total-spin and magnetic block.
--   - `qubitSpins`: PDF p.3: parity-correct twice-spin labels for N qubits.
--   - `qubitSectorDimension`: PDF p.3, Eq.(14): intrinsic physical sector dimension h_N(t/2).
--   - `deterministicResource`: PDF p.3, Eq.(14), normalized correction: numerator 2^(N+2), not the printed 2^(N+1). The intrinsic sector dimension fixes this uniquely already at N=1. The malformed printed combinatorial shorthand is not used.
--   - `probabilisticResource`: PDF p.3, Eq.(15): explicit probabilistic resource, including the parity-correct minimum spin. No optimality is built into this definition.
--   - `transformedSRM`: The SRM for the actual transformed signals O sigma_i O†.
--   - `qutritResourceSquare`: PDF p.7, Eq.(B3): actual qutrit two-port resource square.
--   - `qutritResource`: PDF p.7: the positive square root of X, not an arbitrary filter.
--   - `qutritTransformedEffect`: PDF p.7, Eq.(B5): transformed success effects with corrected factor 9/10.
--   - `qutritPairKet`: Computational ket of the two physical qutrit A ports, highest spin label first.
--   - `qutritHighest`: PDF p.6, B1: the three highest-weight total-spin-one vectors, with the phase convention in which the A_1,C singlet matrix carries (-1)^(J+J'). J=0,1,2 is the physical A-spin. Lower magnetic vectors are generated below.
--   - `qutritCoupled`: PDF p.6, B1: actual coupled basis; r=0,1,2 represents m=1,0,-1.
--   - `qutritFrame`: PDF p.6: the physical three-column block frame at one magnetic number.
--   - `qutritFullFrame`: All nine coupled vectors, not a postulated abstract matrix basis.
--   - `qutritBlock`: PDF p.6, Eq.(B2): the exact spin-one magnetic block.
--   - `qutritKernelVector`: PDF p.7, Eq.(B7), corrected: sqrt(5), not 5, in the normalized null vector.
--   - `RealSpinBasis`: PDF p.6, A1-A4: a real orthonormal basis of the actual complementary spin/magnetic slice. Completeness refers to spectral projectors of the physical angular momenta, not to a postulated abstract block.
--   - `swapPorts`: PDF p.6, A4: the physical port swap, leaving C untouched.
--   - `gramFrame`: PDF p.6, A1,A4: all xi vectors are constructed from one basis by swaps.
--   - `pbtGram`: PDF p.6, A3: actual Gram matrix.
--   - `complementSwap`: PDF p.6, A5: swap of two wires inside the base complement. Used only when neither swapped wire is i0, so the complement is invariant.
--   - `gramSynthesis`: PDF p.6, A6: synthesized physical vector. No coefficient is divided by its port norm, so zero-norm port components remain harmless.
--   - `acDicke`: PDF p.3, Eqs.(17)-(18): maximal-spin Dicke vectors on A,C.
--   - `bdDicke`: PDF p.3, Eq.(16): same symmetric spin vector on D,B.
--   - `Refinement`: PDF p.3, Eq.(18): e0 and the two signs for each positive integer m. This is a full refinement precisely in the odd-N regime used below.
--   - `refinementVector`: PDF p.3, Eq.(18): explicit e_m^+, e_m^-, e0, with false denoting +.
--   - `refinementEffect`: PDF pp.3-4: sequential failure then rank-one refinement effect on AC.
--   - `recoveryMeasurement`: PDF p.4: the same complete Alice measurement for both of Bob's choices.
--   - `recoverBranch`: PDF p.4: B-only unitary action, with an inert arbitrary reference.
--   - `onePortBell`: One-port coordinates for the N=1 Bell-measurement specialization.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, https://arxiv.org/abs/1506.01555v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P39

/-!
Ishizaka, arXiv:1506.01555v2. Locators are PDF pages.
Registers are ordered A,C and D,B. A spin label r means m=(d-1)/2-r.
Local definitions have complete bodies; compilation is pending batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

abbrev Ports (d N : ℕ) := Fin N → Fin d

abbrev AC (d N : ℕ) := Ports d N × Fin d

abbrev PortComplement (d N : ℕ) (i : Fin N) := {j : Fin N // j ≠ i} → Fin d

/-- PDF p.2, Eq.(2): normalized physical spin-zero singlet. The printed
second spin label m is corrected to -m, as forced by the stated spin-zero
convention and the physical angular-momentum decomposition on the same page. -/
def spinSinglet (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun x => if x.2 = Fin.rev x.1 then
    (-1 : ℂ) ^ x.1.val / (Real.sqrt d : ℂ) else 0

/-- PDF p.2, Eq.(2): singlet projector. -/
def singletDensity (d : ℕ) : Op (Fin d × Fin d) := QAlgorithms.pureDensity (spinSinglet d)

/-- Ordered insertion of one port into its complement. -/
def insertPort {d N : ℕ} (i : Fin N) (a : Fin d) (r : PortComplement d N i) : Ports d N :=
  fun j => if h : j = i then a else r ⟨j, h⟩

/-- PDF p.2, Eq.(4): isometric insertion of the A_i,C singlet. -/
def singletInsert {d N : ℕ} (i : Fin N) : Matrix (AC d N) (PortComplement d N i) ℂ :=
  fun x r => spinSinglet d (x.1 i, x.2) *
    if (fun j : {j : Fin N // j ≠ i} => x.1 j.val) = r then 1 else 0

/-- PDF p.2, Eq.(4): P^-_(A_i,C) tensor I_rest. -/
def portProjector {d N : ℕ} (i : Fin N) : Op (AC d N) :=
  singletInsert i * (singletInsert i)ᴴ

/-- PDF p.2, Eq.(4): normalized signal; used with N>=1,d>=2. -/
def pbtSignal (d N : ℕ) (i : Fin N) : Op (AC d N) :=
  ((d : ℂ) ^ (N - 1))⁻¹ • portProjector i

/-- PDF p.2, Eq.(5): physical signal sum. -/
def pbtRho (d N : ℕ) : Op (AC d N) := ∑ i, pbtSignal d N i

/-- PDF p.2: O acts on Alice's ports and leaves C unchanged. -/
def liftA {d N : ℕ} (O : Op (Ports d N)) : Op (AC d N) :=
  Matrix.kronecker O (1 : Op (Fin d))

/-- PDF p.2, Eq.(1): resource amplitude after applying O to A. -/
def resource {d N : ℕ} (O : Op (Ports d N)) :
    EuclideanSpace ℂ (Ports d N × Ports d N) :=
  WithLp.toLp 2 fun x => ∑ a : Ports d N, O x.1 a * ∏ i, spinSinglet d (a i, x.2 i)

/-- PDF p.2, Eq.(1): exact resource normalization. -/
def NormalizedResource {d N : ℕ} (O : Op (Ports d N)) : Prop :=
  Matrix.trace (Oᴴ * O) = (d : ℂ) ^ N

/-- PDF p.2: Alice's deterministic measurement on AC. -/
def DeterministicPOVM {d N : ℕ} (E : Fin N → Op (AC d N)) : Prop :=
  (∀ i, (E i).PosSemidef) ∧ ∑ i, E i = 1

/-- PDF p.3: none is failure, some i is successful port i. -/
def ProbabilisticPOVM {d N : ℕ} (E : Option (Fin N) → Op (AC d N)) : Prop :=
  (∀ i, (E i).PosSemidef) ∧ ∑ i, E i = 1

/-- PDF pp.2,4: induced unnormalized reference-B branch for input T on R,C.
The effect determines the branch after Alice's registers are discarded. -/
def pbtChannelBranch {d N : ℕ} {R : Type*} [Fintype R]
    (O : Op (Ports d N)) (E : Op (AC d N)) (T : Op (R × Fin d)) :
    Op (R × Ports d N) :=
  fun x y => ∑ a : Ports d N, ∑ b : Ports d N, ∑ c : Fin d, ∑ e : Fin d,
    E (b, e) (a, c) * resource O (a, x.2) * conj (resource O (b, y.2)) *
      T (x.1, c) (y.1, e)

/-- PDF pp.3-4: normalized reference-singlet experiment. -/
def pbtBranch {d N : ℕ} (O : Op (Ports d N)) (E : Op (AC d N)) :
    Op (Fin d × Ports d N) := pbtChannelBranch O E (singletDensity d)

/-- Physical marginal retaining the reference and selected output port. -/
def selectPort {d N : ℕ} {R : Type*} [Fintype R]
    (i : Fin N) (T : Op (R × Ports d N)) : Op (R × Fin d) :=
  fun x y => ∑ r : PortComplement d N i, T (x.1, insertPort i x.2 r) (y.1, insertPort i y.2 r)

/-- PDF p.4: outcome probability in the reference-singlet experiment. -/
def pbtBranchProbability {d N : ℕ} (O : Op (Ports d N)) (E : Op (AC d N)) : ℝ :=
  (Matrix.trace (pbtBranch O E)).re

/-- PDF p.2, Eq.(3): operational entanglement fidelity of port selection. -/
def pbtFidelity {d N : ℕ} (O : Op (Ports d N)) (E : Fin N → Op (AC d N)) : ℝ :=
  ∑ i, (Matrix.trace (singletDensity d * selectPort i (pbtBranch O (E i)))).re

/-- PDF p.4, Eq.(20): state measured when Bob sends B_k, renamed C. -/
def codingState {d N : ℕ} (O : Op (Ports d N)) (k : Fin N) : Op (AC d N) :=
  fun x y => ∑ r : PortComplement d N k,
    resource O (x.1, insertPort k x.2 r) * conj (resource O (y.1, insertPort k y.2 r))

/-- PDF p.4: actual coding outcome probability. -/
def codingProbability {d N : ℕ} (O : Op (Ports d N))
    (E : Op (AC d N)) (k : Fin N) : ℝ := QAlgorithms.effectProb E (codingState O k)

/-- PDF p.4: Choi equation for faithful successful branches, including zero
probabilities without division. For these CP branches it characterizes p_i
times the identity channel, also on inputs entangled with a reference. -/
def ExactProbabilistic {d N : ℕ} (O : Op (Ports d N))
    (E : Option (Fin N) → Op (AC d N)) : Prop :=
  NormalizedResource O ∧ ProbabilisticPOVM E ∧
    ∀ i, selectPort i (pbtBranch O (E (some i))) =
      (pbtBranchProbability O (E (some i)) : ℂ) • singletDensity d

/-- PDF p.4: total exact-teleportation success probability. -/
def pbtSuccessProbability {d N : ℕ} (O : Op (Ports d N))
    (E : Option (Fin N) → Op (AC d N)) : ℝ :=
  ∑ i, pbtBranchProbability O (E (some i))

/-- PDF p.3, Eq.(12): SRM on the support. -/
def srm (d N : ℕ) (i : Fin N) : Op (AC d N) :=
  inverseSqrt (pbtRho d N) * pbtSignal d N i * inverseSqrt (pbtRho d N)

/-- PDF p.3, Eqs.(12)-(13): deterministic completion. -/
def completedSRM (d N : ℕ) (i : Fin N) : Op (AC d N) :=
  srm d N i + (N : ℂ)⁻¹ • (1 - support (pbtRho d N))

/-- PDF p.3: separate probabilistic failure effect. -/
def probabilisticSRM (d N : ℕ) : Option (Fin N) → Op (AC d N)
  | none => 1 - support (pbtRho d N)
  | some i => srm d N i

/-- PDF pp.4-5, Eq.(23): normalized conditional singlet overlap.
Uses below have strictly positive branch probability. -/
def conditionalFidelity {d N : ℕ} (O : Op (Ports d N))
    (E : Op (AC d N)) (k : Fin N) : ℝ :=
  (Matrix.trace (singletDensity d * selectPort k (pbtBranch O E))).re /
    pbtBranchProbability O E

/-- PDF pp.4-5: symmetry conditions imposed on the actual protocol. -/
def SymmetricPorts {d N : ℕ} (O : Op (Ports d N))
    (E : Fin N → Op (AC d N)) (Fother : ℝ) : Prop :=
  (∀ i, pbtBranchProbability O (E i) = (N : ℝ)⁻¹) ∧
  (∀ i, conditionalFidelity O (E i) i = pbtFidelity O E) ∧
  ∀ i k, i ≠ k → conditionalFidelity O (E i) k = Fother

example : spinSinglet 2 (0, 0) = 0 := by simp [spinSinglet, Fin.rev]

example : spinSinglet 2 (0, 1) = (Real.sqrt 2 : ℂ)⁻¹ := by simp [spinSinglet, Fin.rev]

example : spinSinglet 2 (1, 0) = -(Real.sqrt 2 : ℂ)⁻¹ := by simp [spinSinglet, Fin.rev, div_eq_mul_inv]

example {d N : ℕ} (i : Fin N) (a : Fin d) (r : PortComplement d N i) :
    insertPort i a r i = a := by simp [insertPort]

example {I : Type*} [Fintype I] [DecidableEq I] : inverseSqrt (0 : Op I) = 0 := by
  simp [inverseSqrt, cfc_zero]

example (d N : ℕ) : probabilisticSRM d N none = 1 - support (pbtRho d N) := rfl

/-- PDF p.6, A7: equal-port sum with every complementary spin at its
highest weight; normalization uses its actual Euclidean norm. -/
def maximumSpinVector (d N : ℕ) : EuclideanSpace ℂ (AC d N) :=
  let v : EuclideanSpace ℂ (AC d N) := ∑ i : Fin N,
    WithLp.toLp 2 fun x => ∑ r : PortComplement d N i,
      singletInsert i x r * (if ∀ j, (r j).val = 0 then 1 else 0)
  (‖v‖⁻¹ : ℂ) • v

/-- PDF p.2: physical spin-s z component, s=(d-1)/2. -/
def quditSpinZ (d : ℕ) : Op (Fin d) :=
  Matrix.diagonal fun r => ((((d : ℝ) - 1) / 2 - r.val : ℝ) : ℂ)

/-- PDF p.2: raising matrix in the m=s-r convention. -/
def quditSpinRaise (d : ℕ) : Op (Fin d) :=
  fun r t => if t.val = r.val + 1 then
    (Real.sqrt (((r.val : ℝ) + 1) * ((d : ℝ) - 1 - r.val)) : ℂ) else 0

/-- Physical Cartesian x component. -/
def spinX (d : ℕ) : Op (Fin d) := (1 / 2 : ℂ) • (quditSpinRaise d + (quditSpinRaise d)ᴴ)

/-- Physical Cartesian y component. -/
def quditSpinY (d : ℕ) : Op (Fin d) :=
  (1 / (2 * Complex.I) : ℂ) • (quditSpinRaise d - (quditSpinRaise d)ᴴ)

/-- A spin operator on a named wire of an ordered finite register. -/
def quditOnWire (d : ℕ) {W : Type*} [Fintype W] [DecidableEq W]
    (q : W) (M : Op (Fin d)) : Op (W → Fin d) :=
  fun x y => M (x q) (y q) * ∏ r ∈ Finset.univ.erase q, if x r = y r then 1 else 0

/-- PDF p.2: physical collective angular momentum on any complement or port register. -/
def quditCollective (d : ℕ) (W : Type*) [Fintype W] [DecidableEq W]
    (M : Op (Fin d)) : Op (W → Fin d) := ∑ q, quditOnWire d q M

/-- PDF p.2: the actual squared total angular momentum. -/
def quditCasimir (d : ℕ) (W : Type*) [Fintype W] [DecidableEq W] : Op (W → Fin d) :=
  quditCollective d W (spinX d) ^ 2 + quditCollective d W (quditSpinY d) ^ 2 +
    quditCollective d W (quditSpinZ d) ^ 2

/-- PDF p.2: addition of the C spin to all A spins. -/
def totalComponent (d N : ℕ) (M : Op (Fin d)) : Op (AC d N) :=
  Matrix.kronecker (quditCollective d (Fin N) M) (1 : Op (Fin d)) +
    Matrix.kronecker (1 : Op (Ports d N)) M

/-- PDF p.2: actual squared angular momentum on AC. -/
def totalCasimir (d N : ℕ) : Op (AC d N) :=
  totalComponent d N (spinX d) ^ 2 + totalComponent d N (quditSpinY d) ^ 2 +
    totalComponent d N (quditSpinZ d) ^ 2

/-- PDF p.2, Eqs.(7)-(8): spectral projector for twice-spin t. Impossible
sectors have zero projector; no abstract decomposition is assumed. -/
def casimirProjector {I : Type*} [Fintype I] [DecidableEq I] (K : Op I) (t : ℕ) : Op I :=
  cfc (fun x : ℝ => if x = (t : ℝ) / 2 * ((t : ℝ) / 2 + 1) then 1 else 0) K

/-- Physical z-component slice; r=0,...,t corresponds to m=t/2-r. -/
def magneticProjector {I : Type*} [Fintype I] [DecidableEq I]
    (Z : Op I) (t r : ℕ) : Op I :=
  cfc (fun x : ℝ => if x = (t : ℝ) / 2 - r then 1 else 0) Z

/-- PDF p.2, Eq.(8): spin block constructed by singlet insertion of the
actual complementary-register spin projectors. -/
def rhoSpinBlock (d N t : ℕ) : Op (AC d N) :=
  ((d : ℂ) ^ (N - 1))⁻¹ • ∑ i : Fin N,
    singletInsert (d := d) i *
      casimirProjector (quditCasimir d {j : Fin N // j ≠ i}) t *
      (singletInsert (d := d) i)ᴴ

/-- PDF p.6, Eq.(A2): physical total-spin and magnetic block. -/
def rhoSpinMagnetic (d N t r : ℕ) : Op (AC d N) :=
  rhoSpinBlock d N t * magneticProjector (totalComponent d N (quditSpinZ d)) t r

/-- PDF p.3: parity-correct twice-spin labels for N qubits. -/
def qubitSpins (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun t => t % 2 = N % 2

/-- PDF p.3, Eq.(14): intrinsic physical sector dimension h_N(t/2). -/
def qubitSectorDimension (N t : ℕ) : ℝ :=
  (Matrix.trace (casimirProjector (quditCasimir 2 (Fin N)) t)).re

/-- PDF p.3, Eq.(14), normalized correction: numerator 2^(N+2), not the
printed 2^(N+1). The intrinsic sector dimension fixes this uniquely already
at N=1. The malformed printed combinatorial shorthand is not used. -/
def deterministicResource (N : ℕ) : Op (Ports 2 N) :=
  ∑ t ∈ qubitSpins N,
    ((Real.sqrt ((2 : ℝ) ^ (N + 2) / (qubitSectorDimension N t * ((N : ℝ) + 2))) *
      Real.sin (Real.pi * ((t : ℝ) + 1) / ((N : ℝ) + 2)) : ℝ) : ℂ) •
      casimirProjector (quditCasimir 2 (Fin N)) t

/-- PDF p.3, Eq.(15): explicit probabilistic resource, including the
parity-correct minimum spin. No optimality is built into this definition. -/
def probabilisticResource (N : ℕ) : Op (Ports 2 N) :=
  (Real.sqrt ((2 : ℝ) ^ N / (∑ t ∈ qubitSpins N, ((t : ℝ) + 1) ^ 2)) : ℂ) •
    ∑ t ∈ qubitSpins N,
      (Real.sqrt (((t : ℝ) + 1) ^ 2 / qubitSectorDimension N t) : ℂ) •
        casimirProjector (quditCasimir 2 (Fin N)) t

/-- The SRM for the actual transformed signals O sigma_i O†. -/
def transformedSRM {d N : ℕ} (O : Op (Ports d N)) (i : Fin N) : Op (AC d N) :=
  let A := liftA O
  let R := A * pbtRho d N * Aᴴ
  inverseSqrt R * (A * pbtSignal d N i * Aᴴ) * inverseSqrt R

example (d : ℕ) : quditCollective d (Fin 0) (quditSpinZ d) = 0 := by simp [quditCollective]

example : qubitSpins 1 = {1} := by decide

/-- PDF p.7, Eq.(B3): actual qutrit two-port resource square. -/
def qutritResourceSquare : Op (Ports 3 2) :=
  (6 / 5 : ℂ) • casimirProjector (quditCasimir 3 (Fin 2)) 0 +
  (3 / 5 : ℂ) • casimirProjector (quditCasimir 3 (Fin 2)) 2 +
  (6 / 5 : ℂ) • casimirProjector (quditCasimir 3 (Fin 2)) 4

/-- PDF p.7: the positive square root of X, not an arbitrary filter. -/
def qutritResource : Op (Ports 3 2) := cfc Real.sqrt qutritResourceSquare

/-- PDF p.7, Eq.(B5): transformed success effects with corrected factor 9/10. -/
def qutritTransformedEffect (i : Fin 2) : Op (AC 3 2) := (9 / 10 : ℂ) • portProjector i

/-- Computational ket of the two physical qutrit A ports, highest spin label first. -/
def qutritPairKet (a b : Fin 3) : EuclideanSpace ℂ (Ports 3 2) :=
  QAlgorithms.ket (![a, b] : Ports 3 2)

/-- PDF p.6, B1: the three highest-weight total-spin-one vectors, with the
phase convention in which the A_1,C singlet matrix carries (-1)^(J+J').
J=0,1,2 is the physical A-spin. Lower magnetic vectors are generated below. -/
def qutritHighest (J : Fin 3) : EuclideanSpace ℂ (AC 3 2) :=
  match J.val with
  | 0 => (Real.sqrt 3 : ℂ)⁻¹ • QAlgorithms.tensorVec
      (qutritPairKet 0 2 - qutritPairKet 1 1 + qutritPairKet 2 0) (QAlgorithms.ket 0)
  | 1 => (- (1 / 2 : ℂ)) •
      (QAlgorithms.tensorVec (qutritPairKet 0 1 - qutritPairKet 1 0) (QAlgorithms.ket 1) -
       QAlgorithms.tensorVec (qutritPairKet 0 2 - qutritPairKet 2 0) (QAlgorithms.ket 0))
  | _ => (Real.sqrt (3 / 5 : ℝ) : ℂ) •
      QAlgorithms.tensorVec (qutritPairKet 0 0) (QAlgorithms.ket 2) -
      (Real.sqrt (3 / 20 : ℝ) : ℂ) •
      QAlgorithms.tensorVec (qutritPairKet 0 1 + qutritPairKet 1 0) (QAlgorithms.ket 1) +
      (Real.sqrt (1 / 60 : ℝ) : ℂ) •
      QAlgorithms.tensorVec (qutritPairKet 0 2 + qutritPairKet 2 0 +
        (2 : ℂ) • qutritPairKet 1 1) (QAlgorithms.ket 0)

/-- PDF p.6, B1: actual coupled basis; r=0,1,2 represents m=1,0,-1. -/
def qutritCoupled (r J : Fin 3) : EuclideanSpace ℂ (AC 3 2) :=
  ((Real.sqrt 2 : ℂ) ^ r.val)⁻¹ •
    QAlgorithms.act ((totalComponent 3 2 ((quditSpinRaise 3)ᴴ)) ^ r.val) (qutritHighest J)

/-- PDF p.6: the physical three-column block frame at one magnetic number. -/
def qutritFrame (r : Fin 3) : Matrix (AC 3 2) (Fin 3) ℂ :=
  fun x J => qutritCoupled r J x

/-- All nine coupled vectors, not a postulated abstract matrix basis. -/
def qutritFullFrame : Matrix (AC 3 2) (Fin 3 × Fin 3) ℂ :=
  fun x rJ => qutritCoupled rJ.1 rJ.2 x

/-- PDF p.6, Eq.(B2): the exact spin-one magnetic block. -/
def qutritBlock : Op (Fin 3) :=
  (2 / 27 : ℂ) • !![1, 0, (Real.sqrt 5 : ℂ); 0, 3, 0; (Real.sqrt 5 : ℂ), 0, 5]

/-- PDF p.7, Eq.(B7), corrected: sqrt(5), not 5, in the normalized null vector. -/
def qutritKernelVector (r : Fin 3) : EuclideanSpace ℂ (AC 3 2) :=
  (Real.sqrt 6 : ℂ)⁻¹ •
    ((Real.sqrt 5 : ℂ) • qutritCoupled r 0 - qutritCoupled r 2)

example : qutritHighest 0 = (Real.sqrt 3 : ℂ)⁻¹ • QAlgorithms.tensorVec
    (qutritPairKet 0 2 - qutritPairKet 1 1 + qutritPairKet 2 0) (QAlgorithms.ket 0) := rfl

/-- PDF p.6, A1-A4: a real orthonormal basis of the actual complementary
spin/magnetic slice. Completeness refers to spectral projectors of the
physical angular momenta, not to a postulated abstract block. -/
structure RealSpinBasis (d N t r : ℕ) (i0 : Fin N) (A : Type*)
    [Fintype A] [DecidableEq A] where
  frame : Matrix (PortComplement d N i0) A ℂ
  real_entries : ∀ x a, (frame x a).im = 0
  orthonormal : frameᴴ * frame = 1
  complete : frame * frameᴴ =
    casimirProjector (quditCasimir d {j : Fin N // j ≠ i0}) t *
      magneticProjector (quditCollective d {j : Fin N // j ≠ i0} (quditSpinZ d)) t r

/-- PDF p.6, A4: the physical port swap, leaving C untouched. -/
def swapPorts {d N : ℕ} (i k : Fin N) : Op (Ports d N) :=
  fun x y => if x = (fun j => y (Equiv.swap i k j)) then 1 else 0

/-- PDF p.6, A1,A4: all xi vectors are constructed from one basis by swaps. -/
def gramFrame {d N t r : ℕ} {i0 : Fin N} {A : Type*} [Fintype A] [DecidableEq A]
    (B : RealSpinBasis d N t r i0 A) : Matrix (AC d N) (Fin N × A) ℂ :=
  fun x ia => (liftA (swapPorts (d := d) i0 ia.1) *
    singletInsert (d := d) i0 * B.frame) x ia.2

/-- PDF p.6, A3: actual Gram matrix. -/
def pbtGram {d N t r : ℕ} {i0 : Fin N} {A : Type*} [Fintype A] [DecidableEq A]
    (B : RealSpinBasis d N t r i0 A) : Op (Fin N × A) :=
  (gramFrame B)ᴴ * gramFrame B

/-- PDF p.6, A5: swap of two wires inside the base complement. Used only
when neither swapped wire is i0, so the complement is invariant. -/
def complementSwap {d N : ℕ} (i0 i k : Fin N) : Op (PortComplement d N i0) :=
  fun x y => ∏ j : {j : Fin N // j ≠ i0},
    if h : Equiv.swap i k j.val ≠ i0 then
      if x j = y ⟨Equiv.swap i k j.val, h⟩ then 1 else 0
    else 0

/-- PDF p.6, A6: synthesized physical vector. No coefficient is divided by
its port norm, so zero-norm port components remain harmless. -/
def gramSynthesis {d N t r : ℕ} {i0 : Fin N} {A : Type*} [Fintype A] [DecidableEq A]
    (B : RealSpinBasis d N t r i0 A) (c : EuclideanSpace ℂ (Fin N × A)) :
    EuclideanSpace ℂ (AC d N) :=
  WithLp.toLp 2 (Matrix.mulVec (gramFrame B) (WithLp.ofLp c))

example {d N t r : ℕ} {i0 : Fin N} {A : Type*} [Fintype A] [DecidableEq A]
    (B : RealSpinBasis d N t r i0 A) : gramSynthesis B 0 = 0 := by
  simp [gramSynthesis]

/-- PDF p.3, Eqs.(17)-(18): maximal-spin Dicke vectors on A,C. -/
def acDicke (N k : ℕ) : EuclideanSpace ℂ (AC 2 N) :=
  WithLp.toLp 2 fun x =>
    if (∑ i : Fin N, (x.1 i).val) + x.2.val = k then
      (Real.sqrt (Nat.choose (N + 1) k) : ℂ)⁻¹ else 0

/-- PDF p.3, Eq.(16): same symmetric spin vector on D,B. -/
def bdDicke (N k : ℕ) : EuclideanSpace ℂ (Fin 2 × Ports 2 N) :=
  WithLp.toLp 2 fun x => acDicke N k (x.2, x.1)

/-- PDF p.3, Eq.(18): e0 and the two signs for each positive integer m.
This is a full refinement precisely in the odd-N regime used below. -/
abbrev Refinement (N : ℕ) := Unit ⊕ (Fin ((N + 1) / 2) × Bool)

/-- PDF p.3, Eq.(18): explicit e_m^+, e_m^-, e0, with false denoting +. -/
def refinementVector (N : ℕ) : Refinement N → EuclideanSpace ℂ (AC 2 N)
  | Sum.inl _ => acDicke N ((N + 1) / 2)
  | Sum.inr (m, sign) => (Real.sqrt 2 : ℂ)⁻¹ •
      (acDicke N ((N + 1) / 2 - (m.val + 1)) +
        (if sign then (-1 : ℂ) else 1) • acDicke N ((N + 1) / 2 + (m.val + 1)))

/-- PDF pp.3-4: sequential failure then rank-one refinement effect on AC. -/
def refinementEffect (N : ℕ) (z : Refinement N) : Op (AC 2 N) :=
  let P0 := probabilisticSRM 2 N none
  P0 * QAlgorithms.pureDensity (refinementVector N z) * P0

/-- PDF p.4: the same complete Alice measurement for both of Bob's choices. -/
def recoveryMeasurement (N : ℕ) : Fin N ⊕ Refinement N → Op (AC 2 N)
  | Sum.inl i => srm 2 N i
  | Sum.inr z => refinementEffect N z

/-- PDF p.4: B-only unitary action, with an inert arbitrary reference. -/
def recoverBranch {N : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (U : Op (Ports 2 N)) (T : Op (R × Ports 2 N)) : Op (R × Ports 2 N) :=
  let V := Matrix.kronecker (1 : Op R) U
  V * T * Vᴴ

/-- One-port coordinates for the N=1 Bell-measurement specialization. -/
def onePortBell (sign : Bool) (parallel : Bool) : EuclideanSpace ℂ (AC 2 1) :=
  WithLp.toLp 2 fun x =>
    if (if parallel then x.2 = x.1 0 else x.2 = Fin.rev (x.1 0)) then
      (if sign then (-1 : ℂ) ^ (x.1 0).val else 1) / (Real.sqrt 2 : ℂ) else 0

example (N : ℕ) : refinementVector N (Sum.inl ()) = acDicke N ((N + 1) / 2) := rfl

end QAlgorithms.Papers.Independent.Intakenext100.P53


