-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
-- name    : QAlgorithms_Papers_Independent_Frontier18_P14
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:01:49.323208+00:00
-- url     : https://prove2.me/theorems/62d3a976-4440-43b3-8665-7a9781ae0468
-- title:
--   Definitions for Quantum Physics of Simple Optical Instruments
-- statement:
--   The objects the formalized statements of *Quantum Physics of Simple Optical Instruments* (arXiv:quant-ph/0305007) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Fock`
--   - `occupationOutput`
--   - `normalizedInput`: PDF p.10: arbitrary normalized input constructed from raw occupation coefficients and their actual l² witness. Normalization is input data, never a hypothesis on the output of the optical instrument.
--   - `passiveCoefficients`: PDF pp.20–21, (4.12),(4.18)–(4.20): finite sum within each total-number sector. No infinite coefficient-product sum occurs at a fixed output coordinate.
--   - `passiveApply`: PDF pp.10,20–21: concrete full Fock extension of the occupation transform. The fallback makes this a total definition for arbitrary matrices. The theorem below asserts square summability for every input whenever B is unitary, so the fallback is never taken in the physical regime. No norm or convergence conclusion is assumed in this definition.
--   - `coherentCoefficient`: PDF p.20, (4.14): coefficients of a normalized one-mode coherent state.
--   - `coherentPairCoefficients`: PDF p.21, (4.15): tensor-product coherent coefficients.
--   - `coherentPair`: PDF pp.20–21: coherent input in full l², with total fallback off the square-summable regime. The headline asserts membership and norm one for all a,b.
--   - `displacementEntry`: PDF pp.20–21, coherent displacement in the occupation basis. These are matrix coefficients of D(z)=exp(z a†-conj(z) a), obtained from normal ordering. The k range guards both factorial subtractions. This defines entries, without assuming an operator extension or any coefficient-product summability.
--   - `displacedCoefficients`: Full two-mode Weyl displacement coefficients, with the double series indexed by pairs. The extension theorem asserts actual summability, not a default tsum value, for all l² inputs.
--   - `displace`: Full l² displacement, with a total fallback excluded by the theorem on all complex displacements and arbitrary l² inputs.
--   - `pureOperator`: PDF p.10: rank-one operator of a full Fock vector, reusing the accepted nuclear trace-class model; density requires norm one.
--   - `fockReducedFirst`: PDF pp.21,35: partial trace of a rank-one two-mode operator, retaining mode one. Cauchy–Schwarz supplies summability for all l² inputs.
--   - `reducedSecond`: Partial trace retaining mode two, with no occupation cutoff.
--   - `displacedOperator`: Conjugation by a one-mode displacement on operator coefficients. The stated reduced-state laws assert the summability of this series on their actual trace-class arguments; no absolute sum of arbitrary input products is postulated.
--   - `rectangularOutput`: Rectangular occupation truncation of the output, before taking either partial trace. Both input cutoffs tend independently to infinity.
--   - `balanced`: PDF p.22, (4.23): the paper's real balanced splitter, fixing reflection sign.
--   - `relativeModePhase`: PDF p.17, (4.4): relative phase matrix.
--   - `realModeRotation`: PDF p.12, (3.16): real passive mixing matrix.
--   - `boost`: PDF p.29, (6.5): real two-mode hyperbolic mixing on (a1,a2†).
--   - `beamEuler`: PDF p.17, (4.3): the complete U(2) parametrization, in printed phase order.
--   - `amplifierEuler`: PDF p.29, (6.4): complete U(1,1) parametrization on (a1,a2†).
--   - `pairMetric`: PDF pp.9,29: commutator metric on an annihilator/creator pair.
--   - `Core`: PDF pp.4–5,17,30: common invariant core of n-mode Fock space. Finite support is a domain for polynomial operator identities, not a restriction on states in any full-Hilbert-space assertion.
--   - `coreKet`: PDF p.21, (4.17): occupation ket on the algebraic Fock core.
--   - `annihilate`: PDF pp.5,21: annihilation with sqrt occupation weight, explicitly zero on an unoccupied mode, including the natural-subtraction boundary.
--   - `create`: PDF pp.5,21: creation with sqrt(n+1) occupation weight.
--   - `commutator`: Operator commutator; multiplication in Module.End is composition.
--   - `outputAnnihilator`: PDF p.9, (3.1): output annihilators from conjugate-paired B,C blocks.
--   - `outputCreator`: PDF p.9, (3.1): actual adjoint partners on the common core.
--   - `doubled`: PDF p.9, (3.1): all annihilators followed by all creators, as Sum indices.
--   - `modeMetric`: PDF p.9, (3.3): the indefinite doubled commutator metric.
--   - `stokesT`: PDF p.17, (4.6): total photon number divided by two.
--   - `stokesX`: PDF p.17, (4.6): x Stokes generator.
--   - `stokesY`: PDF p.17, (4.6): y Stokes generator, fixing the paper's sign.
--   - `stokesZ`: PDF p.17, (4.6): photon-number difference divided by two.
--   - `lorentzT`: PDF p.30, (6.10): Kt retains the a2 a2† vacuum shift.
--   - `lorentzX`: PDF p.30, (6.10): pair creation/annihilation x generator.
--   - `lorentzY`: PDF p.30, (6.10): pair creation/annihilation y generator.
--   - `lorentzZ`: PDF p.30, (6.10): Kz retains the negative half-vacuum shift.
--   - `quadratureQ`: PDF p.5, (2.10): q from an annihilator and its creator partner.
--   - `quadratureP`: PDF p.5, (2.10): p from an annihilator and its creator partner.
--   - `amplifierDoubled`: PDF pp.29–30: real amplifier on the full doubled mode column.
--   - `balancedDoubled`: PDF p.29, (6.7): same balanced mixing on annihilators and creators.
--   - `oppositeSqueezes`: PDF p.29, (6.6): opposite squeezes in the rotated modes.
--   - `pauliDirection`: PDF p.17, (4.5): a real direction contracted with the three Pauli matrices.
--   - `singlet`: PDF p.32, (6.17): normalized singlet in the two-polarization-qubit sector.
--   - `singletCorrelation`: PDF p.33, (6.19): actual singlet matrix expectation, not a prescribed dot product.
--   - `chsh`: PDF p.33, (6.20): CHSH sign order used in the source.
--   - `unitDirection`: Unit direction on the Poincare sphere (PDF p.33).
-- source:
--   Quantum Physics of Simple Optical Instruments, arXiv:quant-ph/0305007v2, https://arxiv.org/abs/quant-ph/0305007v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

/-!
Statements from U. Leonhardt, arXiv:quant-ph/0305007v2.
The accepted Dependency50.P34 module supplies the finite occupation polynomial
only. The sector construction here extends it to arbitrary square-summable inputs.
All polynomial operator equalities are on the common finite-occupation core.
Deferred analytic and source-ambiguous nodes are recorded in this unit's HARD.md.
-/

noncomputable section

open scoped Matrix ComplexConjugate
open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P14

abbrev Fock := QAlgorithms.Papers.Independent.Dependency50.P34.TwoModeFock

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet)

abbrev occupationOutput := QAlgorithms.Papers.Independent.Dependency50.P34.fockOutput

/-- PDF p.10: arbitrary normalized input constructed from raw occupation
coefficients and their actual l² witness. Normalization is input data, never a
hypothesis on the output of the optical instrument. -/
def normalizedInput (c : (ℕ × ℕ) → ℂ) (hc : Memℓp c 2)
    (hn : ‖(⟨c, hc⟩ : Fock)‖ = 1) : {psi : Fock // ‖psi‖ = 1} :=
  ⟨⟨c, hc⟩, hn⟩

example (c : (ℕ × ℕ) → ℂ) (hc : Memℓp c 2)
    (hn : ‖(⟨c, hc⟩ : Fock)‖ = 1) (mn : ℕ × ℕ) :
    (normalizedInput c hc hn).val mn = c mn := rfl

/-- PDF pp.20–21, (4.12),(4.18)–(4.20): finite sum within each total-number
sector. No infinite coefficient-product sum occurs at a fixed output coordinate. -/
def passiveCoefficients (B : Matrix (Fin 2) (Fin 2) ℂ) (psi : Fock)
    (pq : ℕ × ℕ) : ℂ :=
  ∑ m ∈ Finset.range (pq.1 + pq.2 + 1),
    psi (m, pq.1 + pq.2 - m) *
      occupationOutput B m (pq.1 + pq.2 - m) pq

/-- PDF pp.10,20–21: concrete full Fock extension of the occupation transform.
The fallback makes this a total definition for arbitrary matrices. The theorem
below asserts square summability for every input whenever B is unitary, so the
fallback is never taken in the physical regime. No norm or convergence conclusion
is assumed in this definition. -/
def passiveApply (B : Matrix (Fin 2) (Fin 2) ℂ) (psi : Fock) : Fock :=
  if h : Memℓp (passiveCoefficients B psi) 2 then
    ⟨passiveCoefficients B psi, h⟩ else 0

/-- PDF p.20, (4.14): coefficients of a normalized one-mode coherent state. -/
def coherentCoefficient (a : ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-Complex.normSq a / 2) : ℂ) * a ^ n /
    (Real.sqrt (Nat.factorial n : ℝ) : ℂ)

/-- PDF p.21, (4.15): tensor-product coherent coefficients. -/
def coherentPairCoefficients (a b : ℂ) (mn : ℕ × ℕ) : ℂ :=
  coherentCoefficient a mn.1 * coherentCoefficient b mn.2

/-- PDF pp.20–21: coherent input in full l², with total fallback off the
square-summable regime. The headline asserts membership and norm one for all a,b. -/
def coherentPair (a b : ℂ) : Fock :=
  if h : Memℓp (coherentPairCoefficients a b) 2 then
    ⟨coherentPairCoefficients a b, h⟩ else 0

/-- PDF pp.20–21, coherent displacement in the occupation basis. These are
matrix coefficients of D(z)=exp(z a†-conj(z) a), obtained from normal ordering.
The k range guards both factorial subtractions. This defines entries, without
assuming an operator extension or any coefficient-product summability. -/
def displacementEntry (z : ℂ) (m n : ℕ) : ℂ :=
  (Real.exp (-Complex.normSq z / 2) : ℂ) *
    (Real.sqrt ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ)) : ℂ) *
    ∑ k ∈ Finset.range (min m n + 1),
      z ^ (m - k) * (-star z) ^ (n - k) /
        ((Nat.factorial (m - k) : ℂ) *
         (Nat.factorial (n - k) : ℂ) * (Nat.factorial k : ℂ))

/-- Full two-mode Weyl displacement coefficients, with the double series indexed
by pairs. The extension theorem asserts actual summability, not a default tsum
value, for all l² inputs. -/
def displacedCoefficients (z : Fin 2 → ℂ) (psi : Fock) (pq : ℕ × ℕ) : ℂ :=
  ∑' mn : ℕ × ℕ,
    displacementEntry (z 0) pq.1 mn.1 * displacementEntry (z 1) pq.2 mn.2 * psi mn

/-- Full l² displacement, with a total fallback excluded by the theorem on all
complex displacements and arbitrary l² inputs. -/
def displace (z : Fin 2 → ℂ) (psi : Fock) : Fock :=
  if h : Memℓp (displacedCoefficients z psi) 2 then
    ⟨displacedCoefficients z psi, h⟩ else 0

/-- PDF p.10: rank-one operator of a full Fock vector, reusing the accepted
nuclear trace-class model; density requires norm one. -/
abbrev pureOperator (psi : Fock) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  QAlgorithms.Papers.Independent.Dependency50.P33.rankOne psi

/-- PDF pp.21,35: partial trace of a rank-one two-mode operator, retaining mode
one. Cauchy–Schwarz supplies summability for all l² inputs. -/
def fockReducedFirst (psi : Fock) : Matrix ℕ ℕ ℂ :=
  fun i j => ∑' k : ℕ, psi (i, k) * star (psi (j, k))

/-- Partial trace retaining mode two, with no occupation cutoff. -/
def reducedSecond (psi : Fock) : Matrix ℕ ℕ ℂ :=
  fun i j => ∑' k : ℕ, psi (k, i) * star (psi (k, j))

/-- Conjugation by a one-mode displacement on operator coefficients.
The stated reduced-state laws assert the summability of this series on their
actual trace-class arguments; no absolute sum of arbitrary input products is
postulated. -/
def displacedOperator (z : ℂ) (rho : Matrix ℕ ℕ ℂ) : Matrix ℕ ℕ ℂ :=
  fun i j => ∑' mn : ℕ × ℕ,
    displacementEntry z i mn.1 * rho mn.1 mn.2 * star (displacementEntry z j mn.2)

/-- Rectangular occupation truncation of the output, before taking either
partial trace. Both input cutoffs tend independently to infinity. -/
def rectangularOutput (B : Matrix (Fin 2) (Fin 2) ℂ) (psi : Fock)
    (MN : ℕ × ℕ) : Fock :=
  ∑ m ∈ Finset.range MN.1, ∑ n ∈ Finset.range MN.2,
    psi (m, n) • occupationOutput B m n

/-- PDF p.22, (4.23): the paper's real balanced splitter, fixing reflection sign. -/
def balanced : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / (Real.sqrt 2 : ℂ), 1 / (Real.sqrt 2 : ℂ);
     -(1 / (Real.sqrt 2 : ℂ)), 1 / (Real.sqrt 2 : ℂ)]

/-- PDF p.17, (4.4): relative phase matrix. -/
def relativeModePhase (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (Complex.I * (theta / 2 : ℝ)), 0;
     0, Complex.exp (-Complex.I * (theta / 2 : ℝ))]

/-- PDF p.12, (3.16): real passive mixing matrix. -/
def realModeRotation (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos theta : ℂ), (Real.sin theta : ℂ);
     -(Real.sin theta : ℂ), (Real.cos theta : ℂ)]

/-- PDF p.29, (6.5): real two-mode hyperbolic mixing on (a1,a2†). -/
def boost (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cosh theta : ℂ), (Real.sinh theta : ℂ);
     (Real.sinh theta : ℂ), (Real.cosh theta : ℂ)]

/-- PDF p.17, (4.3): the complete U(2) parametrization, in printed phase order. -/
def beamEuler (phi theta psi lam : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.exp (Complex.I * (lam / 2 : ℝ)) •
    !![(Real.cos (theta / 2) : ℂ) * Complex.exp (Complex.I * ((psi + phi) / 2 : ℝ)),
       (Real.sin (theta / 2) : ℂ) * Complex.exp (Complex.I * ((psi - phi) / 2 : ℝ));
       -(Real.sin (theta / 2) : ℂ) * Complex.exp (Complex.I * ((phi - psi) / 2 : ℝ)),
       (Real.cos (theta / 2) : ℂ) * Complex.exp (-Complex.I * ((psi + phi) / 2 : ℝ))]

/-- PDF p.29, (6.4): complete U(1,1) parametrization on (a1,a2†). -/
def amplifierEuler (phi theta psi lam : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.exp (Complex.I * (lam / 2 : ℝ)) •
    !![(Real.cosh (theta / 2) : ℂ) * Complex.exp (Complex.I * ((psi + phi) / 2 : ℝ)),
       (Real.sinh (theta / 2) : ℂ) * Complex.exp (Complex.I * ((psi - phi) / 2 : ℝ));
       (Real.sinh (theta / 2) : ℂ) * Complex.exp (Complex.I * ((phi - psi) / 2 : ℝ)),
       (Real.cosh (theta / 2) : ℂ) * Complex.exp (-Complex.I * ((psi + phi) / 2 : ℝ))]

/-- PDF pp.9,29: commutator metric on an annihilator/creator pair. -/
def pairMetric : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- PDF pp.4–5,17,30: common invariant core of n-mode Fock space.
Finite support is a domain for polynomial operator identities, not a restriction
on states in any full-Hilbert-space assertion. -/
abbrev Core (n : ℕ) := (Fin n → ℕ) →₀ ℂ

/-- PDF p.21, (4.17): occupation ket on the algebraic Fock core. -/
def coreKet {n : ℕ} (m : Fin n → ℕ) : Core n := Finsupp.single m 1

/-- PDF pp.5,21: annihilation with sqrt occupation weight, explicitly zero on
an unoccupied mode, including the natural-subtraction boundary. -/
def annihilate (n : ℕ) (j : Fin n) : Module.End ℂ (Core n) :=
  Finsupp.lsum ℂ (fun m => LinearMap.toSpanSingleton ℂ (Core n)
    (if m j = 0 then 0 else
      (Real.sqrt (m j : ℝ) : ℂ) • coreKet (Function.update m j (m j - 1))))

/-- PDF pp.5,21: creation with sqrt(n+1) occupation weight. -/
def create (n : ℕ) (j : Fin n) : Module.End ℂ (Core n) :=
  Finsupp.lsum ℂ (fun m => LinearMap.toSpanSingleton ℂ (Core n)
    ((Real.sqrt ((m j : ℝ) + 1) : ℂ) • coreKet (Function.update m j (m j + 1))))

/-- Operator commutator; multiplication in Module.End is composition. -/
def commutator {n : ℕ} (A B : Module.End ℂ (Core n)) := A * B - B * A

/-- PDF p.9, (3.1): output annihilators from conjugate-paired B,C blocks. -/
def outputAnnihilator {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    Module.End ℂ (Core n) :=
  ∑ k, (B j k • annihilate n k + C j k • create n k)

/-- PDF p.9, (3.1): actual adjoint partners on the common core. -/
def outputCreator {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    Module.End ℂ (Core n) :=
  ∑ k, (star (B j k) • create n k + star (C j k) • annihilate n k)

/-- PDF p.9, (3.1): all annihilators followed by all creators, as Sum indices. -/
def doubled {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks B C (C.map star) (B.map star)

/-- PDF p.9, (3.3): the indefinite doubled commutator metric. -/
def modeMetric (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- PDF p.17, (4.6): total photon number divided by two. -/
def stokesT : Module.End ℂ (Core 2) :=
  (1 / 2 : ℂ) • (create 2 0 * annihilate 2 0 + create 2 1 * annihilate 2 1)

/-- PDF p.17, (4.6): x Stokes generator. -/
def stokesX : Module.End ℂ (Core 2) :=
  (1 / 2 : ℂ) • (create 2 0 * annihilate 2 1 + create 2 1 * annihilate 2 0)

/-- PDF p.17, (4.6): y Stokes generator, fixing the paper's sign. -/
def stokesY : Module.End ℂ (Core 2) :=
  (Complex.I / 2) • (create 2 1 * annihilate 2 0 - create 2 0 * annihilate 2 1)

/-- PDF p.17, (4.6): photon-number difference divided by two. -/
def stokesZ : Module.End ℂ (Core 2) :=
  (1 / 2 : ℂ) • (create 2 0 * annihilate 2 0 - create 2 1 * annihilate 2 1)

/-- PDF p.30, (6.10): Kt retains the a2 a2† vacuum shift. -/
def lorentzT : Module.End ℂ (Core 2) :=
  (1 / 2 : ℂ) • (create 2 0 * annihilate 2 0 + annihilate 2 1 * create 2 1)

/-- PDF p.30, (6.10): pair creation/annihilation x generator. -/
def lorentzX : Module.End ℂ (Core 2) :=
  (1 / 2 : ℂ) • (annihilate 2 0 * annihilate 2 1 + create 2 0 * create 2 1)

/-- PDF p.30, (6.10): pair creation/annihilation y generator. -/
def lorentzY : Module.End ℂ (Core 2) :=
  (Complex.I / 2) • (annihilate 2 0 * annihilate 2 1 - create 2 0 * create 2 1)

/-- PDF p.30, (6.10): Kz retains the negative half-vacuum shift. -/
def lorentzZ : Module.End ℂ (Core 2) :=
  (1 / 2 : ℂ) • (create 2 0 * annihilate 2 0 - annihilate 2 1 * create 2 1)

/-- PDF p.5, (2.10): q from an annihilator and its creator partner. -/
def quadratureQ (a ad : Module.End ℂ (Core 2)) : Module.End ℂ (Core 2) :=
  (1 / (Real.sqrt 2 : ℂ)) • (ad + a)

/-- PDF p.5, (2.10): p from an annihilator and its creator partner. -/
def quadratureP (a ad : Module.End ℂ (Core 2)) : Module.End ℂ (Core 2) :=
  (Complex.I / (Real.sqrt 2 : ℂ)) • (ad - a)

/-- PDF pp.29–30: real amplifier on the full doubled mode column. -/
def amplifierDoubled (z : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(Real.cosh z : ℂ), 0, 0, (Real.sinh z : ℂ);
     0, (Real.cosh z : ℂ), (Real.sinh z : ℂ), 0;
     0, (Real.sinh z : ℂ), (Real.cosh z : ℂ), 0;
     (Real.sinh z : ℂ), 0, 0, (Real.cosh z : ℂ)]

/-- PDF p.29, (6.7): same balanced mixing on annihilators and creators. -/
def balancedDoubled : Matrix (Fin 4) (Fin 4) ℂ :=
  !![balanced 0 0, balanced 0 1, 0, 0;
     balanced 1 0, balanced 1 1, 0, 0;
     0, 0, balanced 0 0, balanced 0 1;
     0, 0, balanced 1 0, balanced 1 1]

/-- PDF p.29, (6.6): opposite squeezes in the rotated modes. -/
def oppositeSqueezes (z : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(Real.cosh z : ℂ), 0, (Real.sinh z : ℂ), 0;
     0, (Real.cosh z : ℂ), 0, -(Real.sinh z : ℂ);
     (Real.sinh z : ℂ), 0, (Real.cosh z : ℂ), 0;
     0, -(Real.sinh z : ℂ), 0, (Real.cosh z : ℂ)]

/-- PDF p.17, (4.5): a real direction contracted with the three Pauli matrices. -/
def pauliDirection (a : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a 2 : ℂ), (a 0 : ℂ) - Complex.I * (a 1 : ℂ);
     (a 0 : ℂ) + Complex.I * (a 1 : ℂ), -(a 2 : ℂ)]

/-- PDF p.32, (6.17): normalized singlet in the two-polarization-qubit sector. -/
def singlet : (Fin 2 × Fin 2) → ℂ :=
  fun ij => if ij = (0, 1) then 1 / (Real.sqrt 2 : ℂ)
    else if ij = (1, 0) then -(1 / (Real.sqrt 2 : ℂ)) else 0

/-- PDF p.33, (6.19): actual singlet matrix expectation, not a prescribed dot product. -/
def singletCorrelation (a b : Fin 3 → ℝ) : ℝ :=
  (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    star (singlet i) * (pauliDirection a i.1 j.1 * pauliDirection b i.2 j.2) *
      singlet j).re

/-- PDF p.33, (6.20): CHSH sign order used in the source. -/
def chsh (a ap b bp : Fin 3 → ℝ) : ℝ :=
  singletCorrelation a b + singletCorrelation a bp +
    singletCorrelation ap b - singletCorrelation ap bp

/-- Unit direction on the Poincare sphere (PDF p.33). -/
def unitDirection (a : Fin 3 → ℝ) : Prop := ∑ i, a i ^ 2 = 1

example (B : Matrix (Fin 2) (Fin 2) ℂ) (pq : ℕ × ℕ) :
    passiveCoefficients B 0 pq = 0 := by simp [passiveCoefficients]

example (B : Matrix (Fin 2) (Fin 2) ℂ) : passiveApply B 0 = 0 := by
  classical
  ext pq
  unfold passiveApply
  split_ifs <;> simp [passiveCoefficients]

example : coherentCoefficient 0 0 = 1 := by simp [coherentCoefficient]

example : coherentPairCoefficients 0 0 (0, 0) = 1 := by
  simp [coherentPairCoefficients, coherentCoefficient]

example : displacementEntry 0 0 0 = 1 := by simp [displacementEntry]

example (i j : ℕ) : fockReducedFirst 0 i j = 0 := by simp [fockReducedFirst]

example (i j : ℕ) : reducedSecond 0 i j = 0 := by simp [reducedSecond]

example (z : ℂ) : displacedOperator z 0 = 0 := by
  funext i j
  simp [displacedOperator]

example (B : Matrix (Fin 2) (Fin 2) ℂ) (psi : Fock) :
    rectangularOutput B psi (0, 0) = 0 := by simp [rectangularOutput]

example : balanced 1 0 = -(1 / (Real.sqrt 2 : ℂ)) := rfl

example : relativeModePhase 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [relativeModePhase]

example : realModeRotation 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realModeRotation]

example : boost 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boost]

example (n : ℕ) (j : Fin n) : annihilate n j (coreKet (fun _ => 0)) = 0 := by
  classical
  simp [annihilate, coreKet, Finsupp.lsum, LinearMap.toSpanSingleton]

example : commutator stokesT stokesT = 0 := by
  exact sub_self (stokesT * stokesT)

example : lorentzZ = (1 / 2 : ℂ) •
    (create 2 0 * annihilate 2 0 - annihilate 2 1 * create 2 1) := rfl

example : singlet (0, 0) = 0 := by simp [singlet]

example : pauliDirection (fun _ => 0) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliDirection]

end QAlgorithms.Papers.Independent.Frontier18.P14


