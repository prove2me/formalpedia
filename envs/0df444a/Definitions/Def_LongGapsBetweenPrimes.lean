-- Prove2me | Definitions.Def_LongGapsBetweenPrimes
-- name    : LongGapsBetweenPrimes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:29:13.268496+00:00
-- url     : https://prove2.me/theorems/eb5de178-291e-4a47-82fa-6187ba38b384
-- title:
--   Long Gaps Between Primes
-- statement:
--   Definitions and structural lemmas for Long Gaps Between Primes, from OpenAI's pinned Large gaps between consecutive primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean

import Mathlib
set_option autoImplicit true
namespace LongGapsBetweenPrimes
noncomputable section
def iteratedLog (j : ℕ) (x : ℝ) : ℝ := (Real.log^[j]) x
def gapScale (x : ℝ) : ℝ :=
  Real.log x * (iteratedLog 2 x) ^ 2 * iteratedLog 4 x / (iteratedLog 3 x) ^ 2
def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬r.Prime
def LongGapTheorem : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in Filter.atTop,
    ∃ p q : ℕ, ConsecutivePrimes p q ∧ (q : ℝ) ≤ X ∧ c * gapScale X ≤ (q - p : ℕ)
def ShortTranslates : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x < H → (H : ℝ) ≤ x * (Real.log x) ^ 2 →
    ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H → (S.card : ℝ) ≤ δ * x →
    ∀ b : ℕ, b < primorial ⌊x⌋₊ →
    ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ Real.exp x ∧
      ∀ s ∈ S, ¬Nat.Prime (b + primorial ⌊x⌋₊ * t + s)
def normalizer (P : ℕ) : ℝ :=
  ∑ d ∈ P.divisors.erase 1, 1 / ((d.totient : ℝ) * Real.log d)
def coefficient (P d : ℕ) : ℝ :=
  if d = 1 then 1 else -1 / (normalizer P * Real.log d)
def residueFactor {p : ℕ} (a t : Fin p) : ℝ :=
  if t = a then -1 else 1 / ((p : ℝ) - 1)
def coefficientMoment (P : ℕ) (γ : ℝ) : ℝ :=
  ∑ d ∈ P.divisors, coefficient P d ^ 2 * (d : ℝ) ^ γ / d.totient
def coefficientAbsMoment (P : ℕ) (γ : ℝ) : ℝ :=
  ∑ d ∈ P.divisors.erase 1, |coefficient P d| * (d : ℝ) ^ γ / d.totient
abbrev DivisorIndex (P : ℕ) := {d : ℕ // d ∈ P.divisors}
abbrev DivisorTuple (P k : ℕ) := Fin k → DivisorIndex P
def tupleProduct {P k : ℕ} (r : DivisorTuple P k) : ℕ := ∏ i, (r i).val
def tupleRegion (P k : ℕ) (D : ℝ) : Finset (DivisorTuple P k) := by
  classical
  exact Finset.univ.filter fun r =>
    (∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) ∧ (tupleProduct r : ℝ) ≤ D
def tupleMass {P k : ℕ} (r : DivisorTuple P k) : ℝ :=
  ∏ i, coefficient P (r i).val ^ 2 / ((r i).val.totient : ℝ)
def survivors (S ps : Finset ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  S.filter fun n => ∀ p ∈ ps, n % p ≠ a p
def productBasis {α : Type*} [Fintype α] {Ω J : α → Type*}
    (f : (p : α) → J p → Ω p → ℝ) (σ : (p : α) → J p) (t : (p : α) → Ω p) : ℝ :=
  ∏ p, f p (σ p) (t p)
def localBasis {p k : ℕ} (root : Fin k → Fin p) (i : Option (Fin k)) (t : Fin p) : ℝ :=
  match i with
  | none => 1
  | some j => Real.sqrt ((p : ℝ) - 1) * residueFactor (root j) t
def localKernel (p : ℕ) {k : ℕ} (i j : Option (Fin k)) : ℝ :=
  match i, j with
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some a, some b => if a = b then 1 else -1 / ((p : ℝ) - 1)
def localRow (p k : ℕ) (i : Option (Fin k)) : ℝ :=
  match i with
  | none => 1
  | some _ => 1 + ((k : ℝ) - 1) / ((p : ℝ) - 1)
def productKernel {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ τ : α → Option (Fin k)) : ℝ := ∏ p, localKernel (size p) (σ p) (τ p)
def assignmentSupport {α : Type*} [Fintype α] {k : ℕ}
    (σ : α → Option (Fin k)) : Finset α := Finset.univ.filter fun p => (σ p).isSome
def assignmentProduct {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : ℕ := ∏ p ∈ assignmentSupport σ, size p
def residueIndicator (m a n : ℕ) : ℝ := if n % m = a then 1 else 0
def eulerProduct (N : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-σ))⁻¹
def natPowerHom (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' a b := by
    simp only [Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)
def divisorEulerMoment (P : ℕ) (γ : ℝ) : ℝ :=
  ∑ d ∈ P.divisors, (d : ℝ) ^ γ / d.totient
def auxiliaryPrimes (Z Y : ℕ) : Finset ℕ := Y.primesLE \ Z.primesLE
def auxiliaryProduct (Z Y : ℕ) : ℕ := ∏ p ∈ auxiliaryPrimes Z Y, p
def absoluteMomentBound (b : ℝ) : ℝ :=
  Real.exp 2 + 2 * Real.exp 6 * Real.exp (6 * Real.exp 2) / b
def coefficientControl (b : ℝ) : ℝ := absoluteMomentBound b / b
def sieveZ (x : ℝ) : ℕ := ⌊x ^ 6⌋₊
def sieveUpperLog (x : ℝ) : ℝ := x / (Real.log x) ^ 5
def sieveY (x : ℝ) : ℕ := ⌊Real.exp (sieveUpperLog x)⌋₊
def sieveP (x : ℝ) : ℕ := auxiliaryProduct (sieveZ x) (sieveY x)
def normalizerLower : ℝ := 1 / (100 * Real.exp 6)
def sieveBeta (x : ℝ) : ℝ := 1 / sieveUpperLog x
def weightConstant : ℝ :=
  1 + absoluteMomentBound normalizerLower + coefficientControl normalizerLower
structure CoefficientEstimates (P : ℕ) (β C : ℝ) : Prop where
  /-- The sieve modulus exceeds one. -/
  one_lt : 1 < P
  /-- The sieve modulus is squarefree. -/
  squarefree : Squarefree P
  /-- Every divisor coefficient has absolute value at most one. -/
  abs_le_one : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1
  /-- The absolute moment is uniformly bounded for tilts up to `2 * β`. -/
  absMoment_le : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 2 * β → coefficientAbsMoment P γ ≤ C
  /-- The absolute moment is also controlled relative to the normalizer. -/
  moment_control : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 2 * β →
    coefficientAbsMoment P γ ≤ C * normalizer P
def divisorProbability (P : ℕ) (d : DivisorIndex P) : ℝ :=
  (coefficient P d.val ^ 2 / d.val.totient) / coefficientMoment P 0
def diagonalMass (P k : ℕ) (D : ℝ) : ℝ := ∑ r ∈ tupleRegion P k D, tupleMass r
abbrev PrimeIndex (P : ℕ) := {p : ℕ // p ∈ P.primeFactors}
def tupleAssignment {P k : ℕ} (r : DivisorTuple P k) : PrimeIndex P → Option (Fin k) := by
  classical
  exact fun p => if h : ∃ i, p.val ∣ (r i).val then some (Classical.choose h) else none
def rawLocalBasis {p k : ℕ} (root : Fin k → Fin p) (i : Option (Fin k)) (t : Fin p) : ℝ :=
  match i with
  | none => 1
  | some j => residueFactor (root j) t
def assignmentNormalizer {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : ℝ :=
  ∏ p, match σ p with | none => 1 | some _ => (Real.sqrt ((size p : ℝ) - 1))⁻¹
def assignmentVariance {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : ℝ :=
  ∏ p, match σ p with | none => 1 | some _ => 1 / ((size p : ℝ) - 1)
def tupleAmplitude {P k : ℕ} (r : DivisorTuple P k) : ℝ := ∏ i, coefficient P (r i).val
def tupleNormalizedCoefficient {P k : ℕ} (r : DivisorTuple P k) : ℝ :=
  tupleAmplitude r * assignmentNormalizer (fun p : PrimeIndex P => p.val) (tupleAssignment r)
def residueWeight (P k : ℕ) (D : ℝ) (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  ∑ r : tupleRegion P k D,
    tupleAmplitude r.val * productBasis (fun p => rawLocalBasis (root p)) (tupleAssignment r.val) t
def integerAverage (T : ℕ) (f : ℕ → ℝ) : ℝ := (∑ n ∈ Finset.range T, f n) / T
def assignmentPrimes {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) : Finset ℕ :=
  (assignmentSupport σ).image Subtype.val
def assignedRoot {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) (p : PrimeIndex P) : Fin p.val :=
  match σ p with
  | none => ⟨0, (Nat.mem_primeFactors.mp p.property).1.pos⟩
  | some i => root p i
lemma exists_assignment_residue {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) :
    ∃ a : ℕ, a < assignmentProduct (fun p : PrimeIndex P => p.val) σ ∧
      ∀ p : PrimeIndex P, (σ p).isSome → a % p.val = (assignedRoot root σ p).val := by
  classical
  have hcop : (↑(assignmentSupport σ) : Set (PrimeIndex P)).Pairwise
      (fun p q => Nat.Coprime p.val q.val) := by
    intro p _ q _ hpq
    exact (Nat.coprime_primes (Nat.mem_primeFactors.mp p.property).1
      (Nat.mem_primeFactors.mp q.property).1).mpr (fun h => hpq (Subtype.ext h))
  let a := Nat.chineseRemainderOfFinset (fun p => (assignedRoot root σ p).val)
    (fun p : PrimeIndex P => p.val) (assignmentSupport σ)
    (fun p _ => (Nat.mem_primeFactors.mp p.property).1.ne_zero) hcop
  refine ⟨a.val, Nat.chineseRemainderOfFinset_lt_prod _ _ _ _, ?_⟩
  intro p hp
  have h := a.property p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (assignedRoot root σ p).isLt] using h
def assignmentCode {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) : ℕ := Classical.choose (exists_assignment_residue root σ)
def residueVector (P n : ℕ) : (p : PrimeIndex P) → Fin p.val :=
  fun p => ⟨n % p.val, Nat.mod_lt n (Nat.mem_primeFactors.mp p.property).1.pos⟩
def basisWeight (P k : ℕ) (D : ℝ)
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  ∑ r : tupleRegion P k D, tupleAmplitude r.val * productBasis f (tupleAssignment r.val) t
def coefficientRemainder (P m : ℕ) (D : ℝ) : ℝ :=
  ∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) ≤ D / m ∧ d.Coprime m), coefficient P d / d.totient
def coordinateBasis {P k : ℕ}
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (d : DivisorIndex P) (i : Fin k) (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  ∏ p : PrimeIndex P, if p.val ∣ d.val then f p (some i) (t p) else 1
def replacedLocalBasis {p k : ℕ} (root : Fin k → Fin p) (i : Fin k)
    (j : Option (Fin k)) (t : Fin p) : ℝ :=
  match j with
  | none => 1
  | some j => if j = i then 1 / ((p : ℝ) - 1) else residueFactor (root j) t
def replacedResidueWeight (P k : ℕ) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (i : Fin k)
    (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  basisWeight P k D (fun p => replacedLocalBasis (root p) i) t
def weightedResidueWeight (P k : ℕ) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (b : DivisorTuple P k → ℝ)
    (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  ∑ r : tupleRegion P k D, b r.val * tupleAmplitude r.val *
    productBasis (fun p => rawLocalBasis (root p)) (tupleAssignment r.val) t
def gramBound (k : ℕ) (M D : ℝ) : ℝ :=
  Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M))
def uncoveredBound (k : ℕ) (β C M D : ℝ) : ℝ :=
  gramBound k M D * (2 * C ^ 2 * D ^ (-(2 * β)) * Real.exp ((k : ℝ) * C * (2 * β)) +
    2 * (4 * Real.log D / (M * Real.log 2)) ^ 2)
def sieveD (x : ℝ) : ℝ := Real.exp (x / 8)
def sieveT (x : ℝ) : ℕ := ⌊Real.exp x⌋₊
def sieveDelta : ℝ := 1 / (64 * weightConstant)
def smoothEulerConstant : ℝ := (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹
def smoothScaleConstant : ℝ := 3 * smoothEulerConstant + 10
def coverLogZ (x : ℝ) : ℝ :=
  Real.log x * Real.log (Real.log (Real.log x)) /
    (smoothScaleConstant * Real.log (Real.log x))
def coverZ (x : ℝ) : ℕ := ⌊Real.exp (coverLogZ x)⌋₊
def coverW (x : ℝ) : ℕ := ⌊(Real.log x) ^ 4⌋₊
def coverTilt (x : ℝ) : ℝ := smoothScaleConstant * Real.log (Real.log x) / Real.log x
def coverLength (η x : ℝ) : ℕ :=
  ⌊η * x * Real.log x ^ 2 * Real.log (Real.log (Real.log x)) / Real.log (Real.log x) ^ 2⌋₊
def zeroCoverPrimes (x : ℝ) : Finset ℕ :=
  (coverW x).primesLE ∪ (⌊x / 2⌋₊.primesLE \ (coverZ x).primesLE)
def zeroSurvivors (x : ℝ) (H : ℕ) : Finset ℕ :=
  survivors (Finset.Icc 1 H) (zeroCoverPrimes x) (fun _ => 0)
def coverScale (x : ℝ) : ℝ :=
  x * Real.log x ^ 2 * Real.log (Real.log (Real.log x)) / Real.log (Real.log x) ^ 2
def coveringConstant : ℝ :=
  10 * smoothScaleConstant * Real.exp 6 * (Real.log 4 + 2)
def coverEta : ℝ := sieveDelta / (2 * (1 + coveringConstant))
end
end LongGapsBetweenPrimes


