-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P33
-- name    : QAlgorithms_Papers_Independent_Advance50_P33
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T13:29:41.19742+00:00
-- url     : https://prove2.me/theorems/f4d3381c-8cd8-4812-a9d0-952d7a066c84
-- title:
--   Definitions for Quantum bit commitment under Gaussian constraints
-- statement:
--   The objects the formalized statements of *Quantum bit commitment under Gaussian constraints* (arXiv:1105.2140) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `branchSign`: PDF pp.2--3, Eqs.(3)--(5): the relative coherent-branch sign.
--   - `fockTensorPair`: PDF p.2: tensor product in the complete two-mode number basis. The orthogonal Hilbert series converges for every pair of l2 vectors.
--   - `cat`: PDF p.3, Eq.(4): normalized odd/even cat. The odd branch requires A≠0.
--   - `commitmentEncoding`: PDF p.2, Eq.(3): the token--proof encoding; the odd branch requires a≠0.
--   - `IsBalanced`: PDF p.3: a balanced lossless beam splitter with phases fixed so that (z,w)↦((z-w)/sqrt(2),(z+w)/sqrt(2)). This is a device definition on all coherent products, not a promise about a particular cat or attack.
--   - `balancedInterferometer`: PDF p.3: the fixed physical interferometer, chosen by its action on ALL coherent products. The identity fallback is excluded by the IsBalanced conclusion in each interferometric theorem. This definition never refers to a committed bit.
--   - `firstParity`: PDF p.3, Eq.(5): mean parity of the first output; the other is discarded. All uses have norm-one vectors, so the real series is absolutely summable.
--   - `oppositeProbability`: PDF p.3: probability of the opposite-bit parity outcome at unveiling. For b=0 this is even parity; for b=1 it is odd parity.
--   - `attackedChi`: PDF pp.3--4: apply a fixed bounded operation only to the proof of Eq.(3). This finite branch expression is exactly (I tensor U)chi, with no token action.
--   - `vacuumReflection`: PDF p.3, Eq.(6): bounded vacuum reflection exp(i*pi*|0><0|).
--   - `nonGaussianFlip`: PDF p.3, Eq.(6): D(-a)(I-2|0><0|)D(a); no unbounded exponential.
--   - `pShift`: PDF pp.4--6: D(i*t/sqrt(2)) shifts the physical p quadrature by t, with hbar=1. Thus the proof shift sqrt(2)*d is D(i*d).
--   - `displacedOutput`: PDF pp.5--6: cat shift -d and vacuum shift +d at Bob's two outputs.
--   - `photonParityMean`: PDF p.5: single-mode mean photon parity, on normalized states.
--   - `catOppositeProbability`: PDF p.5: opposite-bit acceptance in the displayed p-displacement family.
--   - `displacementControl`: PDF pp.5--6: direction-specific control is one HALF of changing-bit success. This denotes the specified displacement, without claiming global optimality.
--   - `arbitraryDisplacementControl`: PDF p.5: direction-specific half-success for an ARBITRARY complex cat-mode displacement. This supplies the full displacement-only optimization domain; displacementControl parameterizes its momentum-axis maximizer.
--   - `oddParityFormula`: PDF p.5, Eqs.(9)--(10): pi*W_odd(0,d), for positive real cat amplitude A.
--   - `stationaryDisplacement`: PDF p.5, Eq.(10), CORRECTED: printed sqrt(2)*alpha*sin(...) is changed to sqrt(2)*alpha_prime*sin(...), as differentiating the same cat Wigner function requires. Here A denotes alpha_prime, throughout this equation.
--   - `vacuumJointProbability`: PDF p.6: the vacuum event in the second output, jointly with opposite parity.
--   - `vacuumProbability`: PDF p.6: probability of vacuum in output two, with output one ignored.
--   - `tokenReducedMatrix`: PDF p.6, Eq.(13): actual partial-trace coefficients of Eq.(3), proof discarded. Every scalar environment sum is guarded by Summable in the result.
--   - `tokenState`: PDF p.6: bounded realization of the CONSTRUCTED token partial trace. The results conclude IsDensity and HasFockMatrix, excluding a zero fallback.
--   - `tokenDifference`: PDF pp.6--7: H is rho_0-rho_1, fixing the sign in Eq.(14).
--   - `tokenEigenvalue`: PDF p.7, Eqs.(14)--(16): positive magnitude of the two nonzero eigenvalues.
--   - `bobGain`: PDF p.7, Eq.(16): G_max=D/2=||H||_1/4, an advantage, not success probability.
--   - `IsOscillatorEffect`: PDF pp.6--7: arbitrary binary POVM effect on the ENTIRE oscillator space. Self-adjointness plus quadratic forms gives 0<=E<=I. Outcome E guesses bit 1.
--   - `tokenGuessProbability`: PDF pp.6--7: equal-prior guessing probability for the binary POVM (I-E,E). The theorem supplies trace-product summability for EVERY effect.
--   - `catPhotonMean`: PDF p.8: mean photon number on the full oscillator number distribution. Finiteness/Summable is a conclusion, rather than a hidden default for divergent tsum.
-- source:
--   Quantum bit commitment under Gaussian constraints, arXiv:1105.2140v2, https://arxiv.org/abs/1105.2140v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

/-!
Mandilara and Cerf, arXiv:1105.2140v2, PDF pp.2--8.
The accepted countable Fock space, coherent vectors, Weyl displacements and
nuclear trace norm are reused without a photon cutoff. New objects are local
to this paper. `false` encodes b=0 (odd); `true` encodes b=1 (even).
Token is the first factor; proof is the second. The balanced interferometer is
fixed on all coherent products, independently of the committed bit and amplitude.
The false global Gaussian-optimality/security assertions are deferred in HARD.md.
Eq.(10)'s unprimed sine coefficient and Eq.(14)'s eigenvalue labels are corrected
explicitly below; their printed forms remain in items.json and HARD.md.
The accepted homonyms pair, chi, balanced, parity, tokenMatrix, IsEffect and
guessProbability have incompatible types or conventions; the distinct local names
below are justified declaration by declaration in ASSESSMENT.json. No equivalent
frozen definition is redeclared. Compilation is pending the mechanical batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P33

open Filter
open scoped BigOperators Topology
open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator BipartiteFock fockKet bipartiteKet coherentKet
   coherentCoefficient CoherentRealized displacement displacementMatrix
   DisplacementRealized HasFockMatrix operatorOfMatrix IsDensity IsTraceClass
   nuclearTraceNorm fockTrace)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2--3, Eqs.(3)--(5): the relative coherent-branch sign. -/
def branchSign (b : Bool) : ℝ := if b then 1 else -1

/-- PDF p.2: tensor product in the complete two-mode number basis. The
orthogonal Hilbert series converges for every pair of l2 vectors. -/
def fockTensorPair (u v : Fock) : BipartiteFock :=
  ∑' p : ℕ × ℕ, (u p.1 * v p.2) • bipartiteKet p

/-- PDF p.3, Eq.(4): normalized odd/even cat. The odd branch requires A≠0. -/
def cat (A : ℂ) (b : Bool) : Fock :=
  ((Real.sqrt (2 * (1 + branchSign b * Real.exp (-2 * Complex.normSq A))))⁻¹ : ℂ) •
    (coherentKet A + (branchSign b : ℂ) • coherentKet (-A))

/-- PDF p.2, Eq.(3): the token--proof encoding; the odd branch requires a≠0. -/
def commitmentEncoding (a : ℂ) (b : Bool) : BipartiteFock :=
  ((Real.sqrt (2 * (1 + branchSign b * Real.exp (-4 * Complex.normSq a))))⁻¹ : ℂ) •
    (fockTensorPair (coherentKet a) (coherentKet (-a)) +
      (branchSign b : ℂ) • fockTensorPair (coherentKet (-a)) (coherentKet a))

/-- PDF p.3: a balanced lossless beam splitter with phases fixed so that
(z,w)↦((z-w)/sqrt(2),(z+w)/sqrt(2)). This is a device definition on all
coherent products, not a promise about a particular cat or attack. -/
def IsBalanced (B : BipartiteFock ≃ₗᵢ[ℂ] BipartiteFock) : Prop :=
  ∀ z w : ℂ, B (fockTensorPair (coherentKet z) (coherentKet w)) =
    fockTensorPair (coherentKet ((z - w) / (Real.sqrt 2 : ℂ)))
      (coherentKet ((z + w) / (Real.sqrt 2 : ℂ)))

/-- PDF p.3: the fixed physical interferometer, chosen by its action on ALL
coherent products. The identity fallback is excluded by the IsBalanced conclusion
in each interferometric theorem. This definition never refers to a committed bit. -/
def balancedInterferometer : BipartiteFock ≃ₗᵢ[ℂ] BipartiteFock :=
  if h : ∃ B : BipartiteFock ≃ₗᵢ[ℂ] BipartiteFock, IsBalanced B then
    Classical.choose h else LinearIsometryEquiv.refl ℂ BipartiteFock

/-- PDF p.3, Eq.(5): mean parity of the first output; the other is discarded.
All uses have norm-one vectors, so the real series is absolutely summable. -/
def firstParity (psi : BipartiteFock) : ℝ :=
  ∑' p : ℕ × ℕ, (-1 : ℝ) ^ p.1 * ‖psi p‖ ^ 2

/-- PDF p.3: probability of the opposite-bit parity outcome at unveiling.
For b=0 this is even parity; for b=1 it is odd parity. -/
def oppositeProbability (b : Bool) (psi : BipartiteFock) : ℝ :=
  ∑' p : ℕ × ℕ, if (if b then Odd p.1 else Even p.1) then ‖psi p‖ ^ 2 else 0

/-- PDF pp.3--4: apply a fixed bounded operation only to the proof of Eq.(3).
This finite branch expression is exactly (I tensor U)chi, with no token action. -/
def attackedChi (a : ℂ) (b : Bool) (U : FockOperator) : BipartiteFock :=
  ((Real.sqrt (2 * (1 + branchSign b * Real.exp (-4 * Complex.normSq a))))⁻¹ : ℂ) •
    (fockTensorPair (coherentKet a) (U (coherentKet (-a))) +
      (branchSign b : ℂ) • fockTensorPair (coherentKet (-a)) (U (coherentKet a)))

/-- PDF p.3, Eq.(6): bounded vacuum reflection exp(i*pi*|0><0|). -/
def vacuumReflection : FockOperator :=
  1 - (2 : ℂ) • InnerProductSpace.rankOne ℂ (fockKet 0) (fockKet 0)

/-- PDF p.3, Eq.(6): D(-a)(I-2|0><0|)D(a); no unbounded exponential. -/
def nonGaussianFlip (a : ℂ) : FockOperator :=
  (displacement (-a)).comp (vacuumReflection.comp (displacement a))

/-- PDF pp.4--6: D(i*t/sqrt(2)) shifts the physical p quadrature by t,
with hbar=1. Thus the proof shift sqrt(2)*d is D(i*d). -/
def pShift (t : ℝ) : FockOperator :=
  displacement (Complex.I * (t / Real.sqrt 2 : ℝ))

/-- PDF pp.5--6: cat shift -d and vacuum shift +d at Bob's two outputs. -/
def displacedOutput (A : ℂ) (b : Bool) (d : ℝ) : BipartiteFock :=
  fockTensorPair (pShift (-d) (cat A b)) (coherentKet (Complex.I * (d / Real.sqrt 2 : ℝ)))

/-- PDF p.5: single-mode mean photon parity, on normalized states. -/
def photonParityMean (psi : Fock) : ℝ := ∑' n : ℕ, (-1 : ℝ) ^ n * ‖psi n‖ ^ 2

/-- PDF p.5: opposite-bit acceptance in the displayed p-displacement family. -/
def catOppositeProbability (A : ℂ) (b : Bool) (d : ℝ) : ℝ :=
  ∑' n : ℕ, if (if b then Odd n else Even n) then ‖pShift (-d) (cat A b) n‖ ^ 2 else 0

/-- PDF pp.5--6: direction-specific control is one HALF of changing-bit success.
This denotes the specified displacement, without claiming global optimality. -/
def displacementControl (A : ℂ) (b : Bool) (d : ℝ) : ℝ :=
  catOppositeProbability A b d / 2

/-- PDF p.5: direction-specific half-success for an ARBITRARY complex
cat-mode displacement. This supplies the full displacement-only optimization
domain; displacementControl parameterizes its momentum-axis maximizer. -/
def arbitraryDisplacementControl (A : ℂ) (b : Bool) (z : ℂ) : ℝ :=
  (∑' n : ℕ, if (if b then Odd n else Even n) then
    ‖displacement z (cat A b) n‖ ^ 2 else 0) / 2

/-- PDF p.5, Eqs.(9)--(10): pi*W_odd(0,d), for positive real cat amplitude A. -/
def oddParityFormula (A d : ℝ) : ℝ :=
  Real.exp (-d ^ 2) * (Real.exp (-2 * A ^ 2) - Real.cos (2 * Real.sqrt 2 * d * A)) /
    (1 - Real.exp (-2 * A ^ 2))

/-- PDF p.5, Eq.(10), CORRECTED: printed sqrt(2)*alpha*sin(...) is changed
to sqrt(2)*alpha_prime*sin(...), as differentiating the same cat Wigner
function requires. Here A denotes alpha_prime, throughout this equation. -/
def stationaryDisplacement (A d : ℝ) : Prop :=
  d * Real.cos (2 * Real.sqrt 2 * d * A) +
    Real.sqrt 2 * A * Real.sin (2 * Real.sqrt 2 * d * A) = d * Real.exp (-2 * A ^ 2)

/-- PDF p.6: the vacuum event in the second output, jointly with opposite parity. -/
def vacuumJointProbability (b : Bool) (psi : BipartiteFock) : ℝ :=
  ∑' n : ℕ, if (if b then Odd n else Even n) then ‖psi (n, 0)‖ ^ 2 else 0

/-- PDF p.6: probability of vacuum in output two, with output one ignored. -/
def vacuumProbability (psi : BipartiteFock) : ℝ := ∑' n : ℕ, ‖psi (n, 0)‖ ^ 2

/-- PDF p.6, Eq.(13): actual partial-trace coefficients of Eq.(3), proof discarded.
Every scalar environment sum is guarded by Summable in the result. -/
def tokenReducedMatrix (a : ℂ) (b : Bool) (m n : ℕ) : ℂ :=
  ∑' k : ℕ, commitmentEncoding a b (m, k) * star (commitmentEncoding a b (n, k))

/-- PDF p.6: bounded realization of the CONSTRUCTED token partial trace.
The results conclude IsDensity and HasFockMatrix, excluding a zero fallback. -/
def tokenState (a : ℂ) (b : Bool) : FockOperator := operatorOfMatrix (tokenReducedMatrix a b)

/-- PDF pp.6--7: H is rho_0-rho_1, fixing the sign in Eq.(14). -/
def tokenDifference (a : ℂ) : FockOperator := tokenState a false - tokenState a true

/-- PDF p.7, Eqs.(14)--(16): positive magnitude of the two nonzero eigenvalues. -/
def tokenEigenvalue (a : ℂ) : ℝ :=
  Real.exp (-2 * Complex.normSq a) / (1 + Real.exp (-4 * Complex.normSq a))

/-- PDF p.7, Eq.(16): G_max=D/2=||H||_1/4, an advantage, not success probability. -/
def bobGain (a : ℂ) : ℝ := nuclearTraceNorm (tokenDifference a) / 4

/-- PDF pp.6--7: arbitrary binary POVM effect on the ENTIRE oscillator space.
Self-adjointness plus quadratic forms gives 0<=E<=I. Outcome E guesses bit 1. -/
def IsOscillatorEffect (E : FockOperator) : Prop :=
  E.adjoint = E ∧ ∀ psi : Fock,
    0 ≤ (inner ℂ psi (E psi)).re ∧ (inner ℂ psi (E psi)).re ≤ ‖psi‖ ^ 2

/-- PDF pp.6--7: equal-prior guessing probability for the binary POVM (I-E,E).
The theorem supplies trace-product summability for EVERY effect. -/
def tokenGuessProbability (a : ℂ) (E : FockOperator) : ℝ :=
  ((fockTrace ((1 - E).comp (tokenState a false))).re +
    (fockTrace (E.comp (tokenState a true))).re) / 2

/-- PDF p.8: mean photon number on the full oscillator number distribution.
Finiteness/Summable is a conclusion, rather than a hidden default for divergent tsum. -/
def catPhotonMean (A : ℂ) (b : Bool) : ℝ :=
  ∑' n : ℕ, (n : ℝ) * ‖cat A b n‖ ^ 2

example : branchSign false = -1 := rfl

example : branchSign true = 1 := rfl

example (u : Fock) : fockTensorPair 0 u = 0 := by simp [fockTensorPair]

example : stationaryDisplacement 1 0 := by simp [stationaryDisplacement]

example : vacuumJointProbability false (0 : BipartiteFock) = 0 := by
  simp [vacuumJointProbability]

end QAlgorithms.Papers.Independent.Advance50.P33


