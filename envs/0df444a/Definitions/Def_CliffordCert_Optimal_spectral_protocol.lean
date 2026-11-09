-- Prove2me | Definitions.Def_CliffordCert_Optimal_spectral_protocol
-- name    : CliffordCert_Optimal_spectral_protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:42:09.532025+00:00
-- url     : https://prove2.me/theorems/b2438dce-fe1f-4e3d-a0e4-203aa659379a
-- title:
--   The actual swap observable and block acceptance effect
-- statement:
--   For a reference state $\tau$ on a finite basis and $s\ge2$, define the swap matrices $F_{ij}$, the single-register lifts $\tau^{(i)}$, and the matrix
--   $$T_s(\tau)=\binom{s}{2}^{-1}\sum_{i<j}F_{ij}-\frac2s\sum_i\tau^{(i)}+\operatorname{Tr}(\tau^2)I.$$
--   An orthonormal eigenbasis refines its spectral projections. Each basis outcome has its actual Born weight and reports its real eigenvalue. Equal-eigenvalue outcomes are indistinguishable to the test and sum to the corresponding eigenspace probability. Mean and variance are finite sums of these weights, rather than assumed moment properties.
--
--   For a fixed family with $L$ settings put $s=\lceil128d/\varepsilon^2\rceil$, $m=Ls$, $\tau_i=\Phi_i(\sigma)$ and $\beta=\varepsilon^2/(rL)$. The acceptance effect is the sum of tensor spectral projections over precisely those tuples satisfying
--   $$\widehat D=L^{-1}\sum_i Z_i<\beta/2.$$
--   Equality is rejected. The sender schedule is flattened in block-major order. The same acceptance probability is computed explicitly as the sum of independent block Born products. Effect validity, exact agreement with this model, the constants 6 and 774, and success under both promises occur directly in the upper-bound and goal theorem conclusions.
--
--   Outside the Hermitian domain the spectral helpers return zero. The estimator and upper-bound theorems must establish Hermiticity on every use, preventing this default from satisfying the target vacuously.
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 6, Eqs. (4)–(6); §A.1 p. 9, §E pp. 15–17 (PDF pp. 16–18) (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_pauli_compression
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

def swapRegisters {I : Type} [DecidableEq I] {s : ℕ} (i j : Fin s) : Mat (Fin s → I) :=
  fun x y => if x = y ∘ Equiv.swap i j then 1 else 0

def onRegister {I : Type} [DecidableEq I] {s : ℕ} (i : Fin s) (A : Mat I) :
    Mat (Fin s → I) := fun x y =>
  A (x i) (y i) * if ∀ j, j ≠ i → x j = y j then 1 else 0

/-- Eq. (4), with binomial normalization; theorem domain is s ≥ 2. -/
def distanceObservable {I : Type} [Fintype I] [DecidableEq I] (τ : Mat I) (s : ℕ) :
    Mat (Fin s → I) :=
  ((s.choose 2 : ℂ)⁻¹) •
    (∑ i : Fin s, ∑ j : Fin s with i < j, swapRegisters i j) -
  (2 / (s : ℂ)) • (∑ i : Fin s, onRegister i τ) + Matrix.trace (τ * τ) • 1

/-- A rank-one refinement of the spectral measurement. Equal eigenvalues are reported
    identically, so their probabilities add to the full eigenspace Born probability. -/
def spectralValue {I : Type} [Fintype I] [DecidableEq I] (A : Mat I) (j : I) : ℝ :=
  if h : A.IsHermitian then h.eigenvalues j else 0

def spectralProjection {I : Type} [Fintype I] [DecidableEq I] (A : Mat I) (j : I) : Mat I :=
  if h : A.IsHermitian then
    fun a b => (h.eigenvectorBasis j) a * star ((h.eigenvectorBasis j) b)
  else 0

def spectralWeight {I : Type} [Fintype I] [DecidableEq I] (A ρ : Mat I) (j : I) : ℝ :=
  born ρ (spectralProjection A j)

def spectralMean {I : Type} [Fintype I] [DecidableEq I] (A ρ : Mat I) : ℝ :=
  ∑ j, spectralWeight A ρ j * spectralValue A j

def spectralVariance {I : Type} [Fintype I] [DecidableEq I] (A ρ : Mat I) : ℝ :=
  ∑ j, spectralWeight A ρ j * (spectralValue A j - spectralMean A ρ)^2

def blockSize (n : ℕ) (ε : ℝ) : ℕ := ⌈128 * (2 : ℝ)^n / ε^2⌉₊

def blockObservable {n q : ℕ} (hqn : q ≤ n) (C : EncoderFamily n q)
    (σ : Mat (Bits n)) (ε : ℝ) (i : Fin C.length) :=
  distanceObservable (compression hqn (C.unitary i) σ) (blockSize n ε)

abbrev BlockOutcome (q s L : ℕ) := Fin L → (Fin s → Bits q)

def averageReported {n q : ℕ} (hqn : q ≤ n) (C : EncoderFamily n q)
    (σ : Mat (Bits n)) (ε : ℝ)
    (z : BlockOutcome q (blockSize n ε) C.length) : ℝ :=
  (∑ i, spectralValue (blockObservable hqn C σ ε i) (z i)) / C.length

def acceptsOutcome {n q : ℕ} (hqn : q ≤ n) (C : EncoderFamily n q)
    (σ : Mat (Bits n)) (ε : ℝ)
    (z : BlockOutcome q (blockSize n ε) C.length) : Prop :=
  averageReported hqn C σ ε z < ε^2 / ((2 : ℝ)^q * C.length) / 2

/-- Independent block Born probabilities, rather than free moment variables. -/
def blockAcceptance {n q : ℕ} (hqn : q ≤ n) (C : EncoderFamily n q)
    (σ ρ : Mat (Bits n)) (ε : ℝ) : ℝ :=
  ∑ z : BlockOutcome q (blockSize n ε) C.length,
    if acceptsOutcome hqn C σ ε z then
      ∏ i, spectralWeight (blockObservable hqn C σ ε i)
        (tensorPower (compression hqn (C.unitary i) ρ) (blockSize n ε)) (z i)
    else 0

/-- Flattened sender schedule: block i then within-block copy j. -/
def blockSchedule {n q : ℕ} (hqn : q ≤ n) (C : EncoderFamily n q) (ε : ℝ)
    (j : Fin (C.length * blockSize n ε)) : Mat (Bits n) →ₗ[ℂ] Mat (Bits q) :=
  if h : 0 < blockSize n ε then
    compression hqn (C.unitary ⟨j.val / blockSize n ε, by
      exact (Nat.div_lt_iff_lt_mul h).mpr (by simpa [Nat.mul_comm] using j.isLt)⟩)
  else 0

def regroup {q s L : ℕ} (x : Fin (L*s) → Bits q) (i : Fin L) (j : Fin s) : Bits q :=
  x ⟨i.val*s+j.val, by
    calc i.val*s+j.val < i.val*s+s := Nat.add_lt_add_left j.isLt _
         _ = (i.val+1)*s := by ring
         _ ≤ L*s := Nat.mul_le_mul_right s (Nat.succ_le_of_lt i.isLt)⟩

/-- Sum of tensor spectral projections over EXACTLY the accepting outcome tuples. -/
def blockEffect {n q : ℕ} (hqn : q ≤ n) (C : EncoderFamily n q)
    (σ : Mat (Bits n)) (ε : ℝ) : Mat (Fin (C.length * blockSize n ε) → Bits q) :=
  fun x y => ∑ z : BlockOutcome q (blockSize n ε) C.length,
    if acceptsOutcome hqn C σ ε z then
      ∏ i, spectralProjection (blockObservable hqn C σ ε i) (z i)
        (regroup x i) (regroup y i)
    else 0

end CliffordCert.Optimal


