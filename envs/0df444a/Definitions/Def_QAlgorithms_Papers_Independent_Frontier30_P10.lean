-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P10
-- name    : QAlgorithms_Papers_Independent_Frontier30_P10
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:13:26.778677+00:00
-- url     : https://prove2.me/theorems/80e6c066-a92e-41a6-957b-0fd3d9f7d662
-- title:
--   Definitions for Entanglement-breaking channels in infinite dimensions
-- statement:
--   The objects the formalized statements of *Entanglement-breaking channels in infinite dimensions* (arXiv:0802.0235) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HilbertPOVM`: PDF pp.2–3: a normalized positive operator measure on the Borel outcome space. The scalar measures are the quadratic-form measures, not a bounded density. Their finite mass is the squared vector norm, including unnormalized vectors. Countable additivity in these matrix elements is weak operator additivity.
--   - `symplecticPair`: PDF p.7: Delta(w,z) = sum_j (w_y z_x - w_x z_y), with no sign reversal.
--   - `fourierCharacter`: PDF pp.7–8: the positive-phase symplectic Fourier character.
--   - `HasCharacteristic`: PDF p.8: the actual operator characteristic-function law, specified on all quadratic forms. Polarization recovers all off-diagonal matrix elements.
--   - `OperatorPositiveDefinite`: PDF p.8, condition 3: positivity of the operator block matrix. Each block is tested on an independently chosen Hilbert vector; scalar positive definiteness on a single vector is not substituted. Repeated points are allowed.
--   - `WeylSystem`: PDF p.7, (20), with its Weyl cocycle: a strongly continuous irreducible Weyl system. The cocycle sign gives W(z)* W(w) W(z) = exp(i Delta(w,z)) W(w). Nonzero Hilbert spaces are required when this structure is used below.
--   - `gaussianCharacteristic`: PDF p.8, (22): a candidate Gaussian observable characteristic function. No existence or uncertainty inequality is built into this definition.
--   - `observableNoiseMatrix`: PDF p.8, (23): the Hermitian difference mu - (i/2) K^T Delta_A K, computed by pairing columns of K. There is no inverse, rank or strictness guard.
-- source:
--   Entanglement-breaking channels in infinite dimensions, arXiv:0802.0235v1, https://arxiv.org/abs/0802.0235v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

/-!
Statements from Holevo, arXiv:0802.0235v1. Only the observable results with
completed paper-local interfaces are stated. Channel, dilation and capacity
interfaces and source ambiguities are recorded in the assigned HARD.md/GAPS.json.
All operator integrals below are weak integrals, tested on Hilbert vectors.
Compilation is pending the batch handoff.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P10

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- PDF pp.2–3: a normalized positive operator measure on the Borel outcome space.
The scalar measures are the quadratic-form measures, not a bounded density.
Their finite mass is the squared vector norm, including unnormalized vectors.
Countable additivity in these matrix elements is weak operator additivity. -/
structure HilbertPOVM (H X : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [MeasurableSpace X] where
  effect : Set X → H →L[ℂ] H
  total : effect Set.univ = ContinuousLinearMap.id ℂ H
  positive : ∀ S, MeasurableSet S → ∀ u : H,
    (inner ℂ u (effect S u)).im = 0 ∧ 0 ≤ (inner ℂ u (effect S u)).re
  law : H → Measure X
  finite : ∀ u, IsFiniteMeasure (law u)
  law_apply : ∀ u S, MeasurableSet S →
    law u S = ENNReal.ofReal (inner ℂ u (effect S u)).re

/-! Reuse the accepted finite coordinate index `Dependency50.P10.Phase n`.
Real phase vectors are `Phase n → ℝ`, ordered (x_1,...,x_n;y_1,...,y_n).
Only the index is reused: the symplectic form below retains this paper's sign,
which is opposite to the imported covariance paper's `sigma`. -/

/-- PDF p.7: Delta(w,z) = sum_j (w_y z_x - w_x z_y), with no sign reversal. -/
def symplecticPair {n : ℕ} (w z : Phase n → ℝ) : ℝ :=
  ∑ j : Fin n, (w (Sum.inr j) * z (Sum.inl j) - w (Sum.inl j) * z (Sum.inr j))

/-- PDF pp.7–8: the positive-phase symplectic Fourier character. -/
def fourierCharacter {n : ℕ} (w z : Phase n → ℝ) : ℂ :=
  Complex.exp (Complex.I * (symplecticPair w z : ℂ))

/-- PDF p.8: the actual operator characteristic-function law, specified on
all quadratic forms. Polarization recovers all off-diagonal matrix elements. -/
def HasCharacteristic {n : ℕ} (M : HilbertPOVM H (Phase n → ℝ))
    (phi : (Phase n → ℝ) → H →L[ℂ] H) : Prop :=
  ∀ w u, Integrable (fun z => fourierCharacter w z) (M.law u) ∧
    inner ℂ u (phi w u) = ∫ z, fourierCharacter w z ∂M.law u

/-- PDF p.8, condition 3: positivity of the operator block matrix. Each
block is tested on an independently chosen Hilbert vector; scalar positive
definiteness on a single vector is not substituted. Repeated points are allowed. -/
def OperatorPositiveDefinite {n : ℕ} (phi : (Phase n → ℝ) → H →L[ℂ] H) : Prop :=
  ∀ (m : ℕ) (w : Fin m → (Phase n → ℝ)) (v : Fin m → H),
    let q := ∑ j : Fin m, ∑ k : Fin m, inner ℂ (v j) (phi (w j - w k) (v k))
    q.im = 0 ∧ 0 ≤ q.re

/-- PDF p.7, (20), with its Weyl cocycle: a strongly continuous irreducible
Weyl system. The cocycle sign gives W(z)* W(w) W(z) = exp(i Delta(w,z)) W(w).
Nonzero Hilbert spaces are required when this structure is used below. -/
structure WeylSystem (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (n : ℕ) where
  operator : (Phase n → ℝ) → H ≃ₗᵢ[ℂ] H
  zero : operator 0 = LinearIsometryEquiv.refl ℂ H
  multiply : ∀ z w u, operator z (operator w u) =
    Complex.exp (Complex.I * (symplecticPair z w : ℂ) / 2) • operator (z + w) u
  continuous : ∀ u, Continuous (fun z => operator z u)
  irreducible : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
    (∀ z u, u ∈ S → operator z u ∈ S) → S = ⊥ ∨ S = ⊤

/-- PDF p.8, (22): a candidate Gaussian observable characteristic function.
No existence or uncertainty inequality is built into this definition. -/
def gaussianCharacteristic {a b : ℕ} (W : WeylSystem H a)
    (K : Matrix (Phase a) (Phase b) ℝ)
    (mu : Matrix (Phase b) (Phase b) ℝ)
    (w : Phase b → ℝ) : H →L[ℂ] H :=
  (Real.exp (-(∑ i, ∑ j, w i * mu i j * w j) / 2) : ℂ) •
    (W.operator (K.mulVec w)).toLinearIsometry.toContinuousLinearMap

/-- PDF p.8, (23): the Hermitian difference mu - (i/2) K^T Delta_A K,
computed by pairing columns of K. There is no inverse, rank or strictness guard. -/
def observableNoiseMatrix {a b : ℕ}
    (K : Matrix (Phase a) (Phase b) ℝ)
    (mu : Matrix (Phase b) (Phase b) ℝ) :
    Matrix (Phase b) (Phase b) ℂ :=
  fun i j => (mu i j : ℂ) - (Complex.I / 2) *
    (symplecticPair (fun r => K r i) (fun r => K r j) : ℂ)

/-! Sanity examples: normalization, phase sign boundaries and zero input coupling. -/

example {X : Type*} [MeasurableSpace X] (M : HilbertPOVM H X) (u : H) :
    M.law u Set.univ = ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [M.law_apply u Set.univ MeasurableSet.univ, M.total]
  change ENNReal.ofReal (inner ℂ u u).re = ENNReal.ofReal (‖u‖ ^ 2)
  exact congrArg ENNReal.ofReal (inner_self_eq_norm_sq (𝕜 := ℂ) u)

example {n : ℕ} (z : Phase n → ℝ) : fourierCharacter 0 z = 1 := by
  simp [fourierCharacter, symplecticPair]

example {n : ℕ} (W : WeylSystem H n) (u : H) : W.operator 0 u = u := by
  rw [W.zero]
  rfl

example {b : ℕ} (mu : Matrix (Phase b) (Phase b) ℝ) :
    observableNoiseMatrix (0 : Matrix (Phase 0) (Phase b) ℝ) mu =
      fun i j => (mu i j : ℂ) := by
  funext i j
  simp [observableNoiseMatrix, symplecticPair]

end QAlgorithms.Papers.Independent.Frontier30.P10


