-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
-- name    : QAlgorithms_Papers_Independent_Frontier30_P14
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:17:05.930003+00:00
-- url     : https://prove2.me/theorems/2de32173-c45c-4048-864a-9ca7334acacc
-- title:
--   Definitions for Degradability of Bosonic Gaussian channels
-- statement:
--   The objects the formalized statements of *Degradability of Bosonic Gaussian channels* (arXiv:quant-ph/0603257) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Operation`
--   - `isometryCoeff`: Section II, PDF p.2: coefficients of a bounded isometry on complete spaces.
--   - `unitaryCoeff`: Section II, PDF p.2: a bounded unitary, not a formal matrix of unbounded ladders.
--   - `conjugateKernel`: Section II, PDF p.2: coefficients of K X K-adjoint. For trace-class X and bounded K the iterated sums are genuine operator products, without truncation. The same expression applies to the bounded Weyl operators used below.
--   - `boundedUnitaryConjugation`: Section II, PDF p.2: conjugation by a fixed bounded unitary.
--   - `partialRight`: Section II, PDF p.2: the genuine environmental partial trace, on trace class. The coefficient formula is total on arrays, but every theorem uses a nuclear trace-class argument or a bounded-unitary image of a product of densities.
--   - `partialLeft`: Section II, PDF p.2: trace over the carrier, with the environment retained.
--   - `dilationReceiver`: Equation (1), PDF p.2, on all trace-class inputs; the environment is fixed.
--   - `weakComplement`: Equation (2), PDF p.2: SAME U and sigma as the receiver, including mixed sigma.
--   - `WeaklyDegradable`: Equation (3), PDF p.2. One full-space CPTP recovery works for every density. The two supplied maps are themselves full trace-class channels.
--   - `AntiDegradable`: Equation (4), PDF p.2, in the opposite recovery direction.
--   - `pureReceiver`: Section II, PDF p.2: receiver of a pure Stinespring isometry.
--   - `pureComplement`: Section II, PDF p.2: true complement of that same pure isometry.
--   - `OrdinarilyDegradable`: Section II, PDF p.2, ordinary degradability: some true Stinespring complement is recovered by a CPTP map. The auxiliary complete Hilbert space is unrestricted; no mixed-environment weak complement is called a true complement.
--   - `PureDensity`: Section II, PDF p.2: normalized rank-one environmental density.
--   - `identityCoeff`: Identity coefficients, also for the non-trace-class identity in (A14).
--   - `composeKernel`: Coefficients of a product of bounded operators; never a finite matrix product.
--   - `swapCoefficients`: The vacuum-preserving self-adjoint swap Xi of Appendix A.3, PDF p.6. This is its conjugation action on operator coefficients on the completed product.
--   - `weylCharacteristic`: Equations (5),(16), PDF pp.2,4: Tr(rho D(z)); the order of the nested sums is matrix multiplication first, diagonal trace second. On a density this is a trace-class/bounded pairing, including infinite-entropy and non-Gaussian states.
--   - `GaussianDensity`: Equation (6), PDF p.2: Gaussian densities, with arbitrary real first moments. Positivity of the covariance is already forced by the density and this formula.
--   - `CenteredGaussian`: Sections III-IV, PDF pp.3-4: zero first moments, with no purity assumption.
--   - `daggerIndex`: Dagger partner in the ordered list (a,a-adjoint,b,b-adjoint), (7), PDF p.2.
--   - `commutatorMatrix`: Full commutator matrix, not merely the selected constraints (8)-(9).
--   - `Canonical`: Equation (7), PDF pp.2-3, in the equivalent bounded Weyl form. Conjugate rows and all canonical commutators are included. The fixed Fock Weyl operators avoid multiplying unbounded annihilation operators on unspecified domains.
--   - `characteristicQ`: Equation (10), PDF p.3, zero-based matrix indices.
--   - `standardMatrix`: Exactly (11),(12), PDF p.3. k is intensity transmissivity/gain.
--   - `GaussianUnitary`: Appendix A, PDF pp.5-6: single-mode squeezings with the phase rotations explicitly allowed before (A1),(A7). No displacement is hidden in this predicate.
--   - `traceClassTensorPower`: Memoryless n-use channel on complete tensor powers, for the operational Q in Section II, PDF p.2. Each recursion applies the original channel to one coordinate and leaves all off-diagonal blocks intact.
--   - `codeFidelity`: Entanglement-transmission fidelity for m logical qubits; squared fidelity with the normalized maximally entangled vector. No real supremum is used. Operational convention: Section II, PDF p.2, unknown-state transmission; the standard equivalent code convention is [16], PDF p.2, Scenario Ib, (1)-(2).
--   - `traceClassAchievableRate`: Section II, PDF p.2, unassisted achievable rates, without energy constraints. Encoding and decoding are arbitrary full trace-class CPTP maps, including across all n uses. Rate and code choices precede all transmitted states, which are covered by entanglement fidelity. The threshold N is positive.
--   - `operationalTraceClassCapacity`: Operational quantum capacity, Section II, PDF p.2, valued in [0,infinity]. An unbounded set has supremum infinity, and an empty set has supremum zero.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, https://arxiv.org/abs/quant-ph/0603257v4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

/-!
Statements from Caruso and Giovannetti, arXiv:quant-ph/0603257v4.
Completed Hilbert spaces are l2 of their orthonormal-basis labels; the two-mode
space is l2(N x N), without a photon-number cutoff. The accepted P33 nuclear
trace-class, state and CPTP definitions are reused, not finite-matrix channels.
The Fock displacement matrix is reused from the accepted P39 module.
All local definitions have complete bodies. Source theorems alone are admitted.
Coherent-information additivity is deferred because its infinite-entropy domain
is not specified by this source. Compilation is pending the batch handoff.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

/-! Accepted-library names were checked by type, not by spelling. P19.Coeff is
a partition-coefficient space; P26.Unitary is finite-dimensional; P21.conjugate
is vector conjugation; P48.receiver uses finite Stinespring matrices; P34.weyl
is a cyclic finite-dimensional matrix. None substitutes for the full Fock-space
objects here. Matrix and LinearIsometryEquiv are used directly. The fixed Fock
Weyl matrix is imported as P39.displacementMatrix, and Matrix.single supplies
logical matrix units. Finite-dimensional channelPower/AchievableRate/capacity
interfaces do not cover unrestricted trace-class bosonic channels; the distinct
local names below make that domain explicit. -/

namespace QAlgorithms.Papers.Independent.Frontier30.P14

abbrev Operation (I J : Type) := (Matrix I I ℂ) → (Matrix J J ℂ)

/-- Section II, PDF p.2: coefficients of a bounded isometry on complete spaces. -/
def isometryCoeff {I J : Type} (V : Hilbert I →ₗᵢ[ℂ] Hilbert J) : Matrix J I ℂ :=
  fun i j => V (lp.single 2 j 1) i

/-- Section II, PDF p.2: a bounded unitary, not a formal matrix of unbounded ladders. -/
def unitaryCoeff {I : Type} (U : (Hilbert I ≃ₗᵢ[ℂ] Hilbert I)) : (Matrix I I ℂ) :=
  isometryCoeff U.toLinearIsometry

/-- Section II, PDF p.2: coefficients of K X K-adjoint. For trace-class X and
bounded K the iterated sums are genuine operator products, without truncation.
The same expression applies to the bounded Weyl operators used below. -/
def conjugateKernel {I J : Type} (K : Matrix J I ℂ) (X : (Matrix I I ℂ)) : (Matrix J J ℂ) :=
  fun i j => ∑' a, K i a * (∑' b, X a b * star (K j b))

/-- Section II, PDF p.2: conjugation by a fixed bounded unitary. -/
def boundedUnitaryConjugation {I : Type} (U : (Hilbert I ≃ₗᵢ[ℂ] Hilbert I)) : Operation I I :=
  conjugateKernel (unitaryCoeff U)

/-- Section II, PDF p.2: the genuine environmental partial trace, on trace class.
The coefficient formula is total on arrays, but every theorem uses a nuclear
trace-class argument or a bounded-unitary image of a product of densities. -/
def partialRight {I J : Type} (X : (Matrix (I × J) (I × J) ℂ)) : (Matrix I I ℂ) :=
  fun i j => ∑' b, X (i, b) (j, b)

/-- Section II, PDF p.2: trace over the carrier, with the environment retained. -/
def partialLeft {I J : Type} (X : (Matrix (I × J) (I × J) ℂ)) : (Matrix J J ℂ) :=
  fun i j => ∑' a, X (a, i) (a, j)

/-- Equation (1), PDF p.2, on all trace-class inputs; the environment is fixed. -/
def dilationReceiver {I J : Type} (U : (Hilbert (I × J) ≃ₗᵢ[ℂ] Hilbert (I × J))) (sigma : (Matrix J J ℂ)) : Operation I I :=
  fun X => partialRight (boundedUnitaryConjugation U (productCoeff X sigma))

/-- Equation (2), PDF p.2: SAME U and sigma as the receiver, including mixed sigma. -/
def weakComplement {I J : Type} (U : (Hilbert (I × J) ≃ₗᵢ[ℂ] Hilbert (I × J))) (sigma : (Matrix J J ℂ)) : Operation I J :=
  fun X => partialLeft (boundedUnitaryConjugation U (productCoeff X sigma))

/-- Equation (3), PDF p.2. One full-space CPTP recovery works for every density.
The two supplied maps are themselves full trace-class channels. -/
def WeaklyDegradable {I J K : Type} (E : Operation I J) (F : Operation I K) : Prop :=
  IsTraceClassChannel E ∧ IsTraceClassChannel F ∧
    ∃ T : Operation J K, IsTraceClassChannel T ∧
      ∀ rho : State I, T (E rho.coefficients) = F rho.coefficients

/-- Equation (4), PDF p.2, in the opposite recovery direction. -/
def AntiDegradable {I J K : Type} (E : Operation I J) (F : Operation I K) : Prop :=
  IsTraceClassChannel E ∧ IsTraceClassChannel F ∧
    ∃ T : Operation K J, IsTraceClassChannel T ∧
      ∀ rho : State I, T (F rho.coefficients) = E rho.coefficients

/-- Section II, PDF p.2: receiver of a pure Stinespring isometry. -/
def pureReceiver {I J : Type} (V : Hilbert I →ₗᵢ[ℂ] Hilbert (I × J)) : Operation I I :=
  fun X => partialRight (conjugateKernel (isometryCoeff V) X)

/-- Section II, PDF p.2: true complement of that same pure isometry. -/
def pureComplement {I J : Type} (V : Hilbert I →ₗᵢ[ℂ] Hilbert (I × J)) : Operation I J :=
  fun X => partialLeft (conjugateKernel (isometryCoeff V) X)

/-- Section II, PDF p.2, ordinary degradability: some true Stinespring complement
is recovered by a CPTP map. The auxiliary complete Hilbert space is unrestricted;
no mixed-environment weak complement is called a true complement. -/
def OrdinarilyDegradable {I : Type} (E : Operation I I) : Prop :=
  IsTraceClassChannel E ∧ ∃ J : Type,
    ∃ V : Hilbert I →ₗᵢ[ℂ] Hilbert (I × J),
      (∀ rho : State I, pureReceiver V rho.coefficients = E rho.coefficients) ∧
      WeaklyDegradable (pureReceiver V) (pureComplement V)

/-- Section II, PDF p.2: normalized rank-one environmental density. -/
def PureDensity {I : Type} (sigma : (Matrix I I ℂ)) : Prop :=
  IsDensity sigma ∧ ∃ v : Hilbert I, ‖v‖ = 1 ∧ sigma = rankOne v

/-- Identity coefficients, also for the non-trace-class identity in (A14). -/
def identityCoeff (I : Type) : (Matrix I I ℂ) := fun i j => if i = j then 1 else 0

/-- Coefficients of a product of bounded operators; never a finite matrix product. -/
def composeKernel {I J K : Type} (A : Matrix K J ℂ) (B : Matrix J I ℂ) : Matrix K I ℂ :=
  fun i j => ∑' k, A i k * B k j

/-- The vacuum-preserving self-adjoint swap Xi of Appendix A.3, PDF p.6.
This is its conjugation action on operator coefficients on the completed product. -/
def swapCoefficients {I : Type} (X : (Matrix (I × I) (I × I) ℂ)) : (Matrix (I × I) (I × I) ℂ) :=
  fun p q => X (p.2, p.1) (q.2, q.1)

/-- Equations (5),(16), PDF pp.2,4: Tr(rho D(z)); the order of the nested sums
is matrix multiplication first, diagonal trace second. On a density this is a
trace-class/bounded pairing, including infinite-entropy and non-Gaussian states. -/
def weylCharacteristic (rho : (Matrix ℕ ℕ ℂ)) (z : ℂ) : ℂ :=
  ∑' m, ∑' n, rho m n * displacementMatrix z n m

/-- Equation (6), PDF p.2: Gaussian densities, with arbitrary real first moments.
Positivity of the covariance is already forced by the density and this formula. -/
def GaussianDensity (rho : (Matrix ℕ ℕ ℂ)) : Prop :=
  IsDensity rho ∧ ∃ a b c u v : ℝ, ∀ z : ℂ,
    weylCharacteristic rho z = Complex.exp
      (((-(a * z.re ^ 2 + 2 * b * z.re * z.im + c * z.im ^ 2) / 2 : ℝ) : ℂ) +
        Complex.I * ((u * z.re + v * z.im : ℝ) : ℂ))

/-- Sections III-IV, PDF pp.3-4: zero first moments, with no purity assumption. -/
def CenteredGaussian (rho : (Matrix ℕ ℕ ℂ)) : Prop :=
  IsDensity rho ∧ ∃ a b c : ℝ, ∀ z : ℂ,
    weylCharacteristic rho z = Complex.exp
      ((-(a * z.re ^ 2 + 2 * b * z.re * z.im + c * z.im ^ 2) / 2 : ℝ) : ℂ)

/-- Dagger partner in the ordered list (a,a-adjoint,b,b-adjoint), (7), PDF p.2. -/
def daggerIndex (i : Fin 4) : Fin 4 :=
  if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 3 else 2

/-- Full commutator matrix, not merely the selected constraints (8)-(9). -/
def commutatorMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => if i = j then (if i = 0 ∨ i = 2 then 1 else -1) else 0

/-- Equation (7), PDF pp.2-3, in the equivalent bounded Weyl form. Conjugate
rows and all canonical commutators are included. The fixed Fock Weyl operators
avoid multiplying unbounded annihilation operators on unspecified domains. -/
def Canonical (U : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ))) (A : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  (∀ i j, A (daggerIndex i) (daggerIndex j) = star (A i j)) ∧
  A * commutatorMatrix * A.conjTranspose = commutatorMatrix ∧
  ∀ z w : ℂ, boundedUnitaryConjugation U (productCoeff (displacementMatrix z) (displacementMatrix w)) =
    productCoeff
      (displacementMatrix (∑ i : Fin 4, (![-star z, z, -star w, w] : Fin 4 → ℂ) i * A i 1))
      (displacementMatrix (∑ i : Fin 4, (![-star z, z, -star w, w] : Fin 4 → ℂ) i * A i 3))

/-- Equation (10), PDF p.3, zero-based matrix indices. -/
def characteristicQ (A : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  Complex.normSq (A 0 0) - Complex.normSq (A 0 1)

/-- Exactly (11),(12), PDF p.3. k is intensity transmissivity/gain. -/
def standardMatrix (k : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let t : ℂ := (Real.sqrt k : ℂ)
  if k ≤ 1 then
    let r : ℂ := (Real.sqrt (1 - k) : ℂ)
    ![![t, 0, -r, 0], ![0, t, 0, -r], ![r, 0, t, 0], ![0, r, 0, t]]
  else
    let r : ℂ := (Real.sqrt (k - 1) : ℂ)
    ![![t, 0, 0, -r], ![0, t, -r, 0], ![0, -r, t, 0], ![-r, 0, 0, t]]

/-- Appendix A, PDF pp.5-6: single-mode squeezings with the phase rotations
explicitly allowed before (A1),(A7). No displacement is hidden in this predicate. -/
def GaussianUnitary (S : (Hilbert ℕ ≃ₗᵢ[ℂ] Hilbert ℕ)) : Prop :=
  ∃ alpha beta : ℂ, Complex.normSq alpha - Complex.normSq beta = 1 ∧
    ∀ z : ℂ, boundedUnitaryConjugation S (displacementMatrix z) = displacementMatrix (z * star alpha - star z * beta)

/-- Memoryless n-use channel on complete tensor powers, for the operational Q
in Section II, PDF p.2. Each recursion applies the original channel to one
coordinate and leaves all off-diagonal blocks intact. -/
def traceClassTensorPower {I : Type} (E : Operation I I) :
    (n : ℕ) → Operation (Fin n → I) (Fin n → I)
  | 0 => fun X => X
  | n + 1 => fun X a b =>
      traceClassTensorPower E n
        (fun s t => E (fun i j => X (Fin.cons i s) (Fin.cons j t)) (a 0) (b 0))
        (Fin.tail a) (Fin.tail b)

/-- Entanglement-transmission fidelity for m logical qubits; squared fidelity
with the normalized maximally entangled vector. No real supremum is used.
Operational convention: Section II, PDF p.2, unknown-state transmission; the
standard equivalent code convention is [16], PDF p.2, Scenario Ib, (1)-(2). -/
def codeFidelity (m : ℕ) (E : Operation (Fin (2 ^ m)) (Fin (2 ^ m))) : ℝ :=
  ((∑ a : Fin (2 ^ m), ∑ b : Fin (2 ^ m), E (Matrix.single a b 1) a b).re) /
    ((2 : ℝ) ^ m) ^ 2

/-- Section II, PDF p.2, unassisted achievable rates, without energy constraints.
Encoding and decoding are arbitrary full trace-class CPTP maps, including across
all n uses. Rate and code choices precede all transmitted states, which are
covered by entanglement fidelity. The threshold N is positive. -/
def traceClassAchievableRate {I : Type} (E : Operation I I) (R : ℝ≥0) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∃ m : ℕ,
      ∃ Enc : Operation (Fin (2 ^ m)) (Fin n → I),
      ∃ Dec : Operation (Fin n → I) (Fin (2 ^ m)),
        IsTraceClassChannel Enc ∧ IsTraceClassChannel Dec ∧
        ((R : ℝ) - delta) * (n : ℝ) ≤ (m : ℝ) ∧
        1 - epsilon ≤ codeFidelity m (Dec ∘ traceClassTensorPower E n ∘ Enc)

/-- Operational quantum capacity, Section II, PDF p.2, valued in [0,infinity].
An unbounded set has supremum infinity, and an empty set has supremum zero. -/
def operationalTraceClassCapacity {I : Type} (E : Operation I I) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ≥0 // traceClassAchievableRate E R}, (R.val : ℝ≥0∞)

/-! Sanity examples pin definitions, not proofs of source results. -/

example {I : Type} (X : (Matrix (I × I) (I × I) ℂ)) :
    swapCoefficients (swapCoefficients X) = X := by rfl

example {I J : Type} : partialRight (0 : (Matrix (I × J) (I × J) ℂ)) = 0 := by
  funext i j
  simp [partialRight]

example (z : ℂ) : displacementMatrix z 0 0 = (Real.exp (-Complex.normSq z / 2) : ℂ) := by
  simp [displacementMatrix]

example : characteristicQ (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
  norm_num [characteristicQ]

example {I : Type} (E : Operation I I) : traceClassTensorPower E 0 = id := by rfl

example {I : Type} :
    (⨆ R : (∅ : Set ℝ≥0), (R.val : ℝ≥0∞)) = 0 := by simp

end QAlgorithms.Papers.Independent.Frontier30.P14


