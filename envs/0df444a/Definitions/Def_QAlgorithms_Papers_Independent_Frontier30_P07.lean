-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P07
-- name    : QAlgorithms_Papers_Independent_Frontier30_P07
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:35:28.996841+00:00
-- url     : https://prove2.me/theorems/9359ab7c-29a3-4b70-b975-8974a93d4de6
-- title:
--   Definitions for One-mode quantum Gaussian channels
-- statement:
--   The objects the formalized statements of *One-mode quantum Gaussian channels* (arXiv:quant-ph/0607051) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PhaseSpace`: Real phase space Z, PDF p.1, (2).
--   - `Oscillator`: The full one-mode separable oscillator Hilbert space, PDF p.1. Reuse the frozen countable Hilbert-space definition, with no energy cutoff.
--   - `Observable`: Bounded observables on the genuine oscillator, PDF pp.1–2.
--   - `symplecticForm`: Paper's argument symplectic form, PDF p.1, (2). In particular Delta((1,0),(0,1))=-1.
--   - `WeylRepresentation`: Regular irreducible Weyl representation with hbar=1, PDF p.1, (1)–(2). Strong continuity is regularity. Closed invariant complex subspaces are trivial, so reducible or trivial representations cannot satisfy the standing assumptions. The Weyl CCR is the bounded-operator formulation of the source's canonical self-adjoint generators, in countable orthonormal coordinates.
--   - `IsBlockPositive`: Positivity of an arbitrary finite operator matrix on H tensor C^n, PDF p.2, channel standing convention. This tests all vectors in each factor.
--   - `NormalChannel`: Normal unital completely positive Heisenberg maps, PDF pp.1–2. Normality is expressed by preservation of strong limits of increasing positive sequences. On B(H) for this separable H this is equivalent to normality. Complete positivity uses every finite matrix amplification, not scalar positivity alone. The bounded linear map acts on all observables, not just Weyl symbols.
--   - `CovarianceForm`: Real covariance bilinear forms, PDF p.2, (5). Symmetry is required below.
--   - `AdmissibleNoise`: The non-strict positive-type condition (5), PDF p.2, for every finite list. Zero noise at the identity endpoint is permitted.
--   - `HasGaussianAction`: Actual Gaussian action (3), allowing the preliminary linear displacement mentioned on PDF p.2. No unrestricted characteristic symbols substitute for a normal channel. The centered multiplier is exp(-alpha(z,z)/2).
--   - `IsSymplectic`: Linear symplectic changes of coordinates, PDF p.1.
--   - `Implements`: Canonical unitary implementing T in this actual Weyl representation, PDF p.1: U_T* V(z) U_T = V(Tz).
--   - `CanonicalForm`: The six printed canonical forms, PDF p.3. Parameters are unrestricted real numbers here, with their physical domains specified by ValidCanonical.
--   - `ValidCanonical`: Physical parameter domains, PDF pp.3–4. The proof supplies N0>=0 also for A2, C and D. B2 includes the identity Nc=0.
--   - `canonicalLinear`: The canonical K maps, PDF p.3.
--   - `canonicalNoise`: Canonical alpha(z,z), PDF p.3; its multiplier is exp(-this/2). B1 therefore has exactly the printed exp(-x^2/4), rather than the quarter-turned representation used in the open-system discussion.
--   - `noiseDensity`: Complex Gaussian probability density in the complex coordinate z=(x+iy)/sqrt(2), PDF p.7. It is used only when Nc>0.
--   - `noiseMeasure`: The actual Gaussian measure mu_Nc on the complex plane, PDF p.7. Lebesgue measure here is complex-plane area, not dx dy in physical coordinates.
--   - `Environment`: The source's infinite-dimensional environmental Hilbert space, PDF pp.7–8.
--   - `EnvironmentOperator`: Bounded environmental operators on weighted L2, PDF p.8.
--   - `HasEnvironmentWeylAction`: Pointwise formula (12), PDF p.8. Both conjugation bars and the negative real weight are as printed. Equality is almost everywhere on L2 representatives.
--   - `environmentWeyl`: The unique bounded realization of (12), PDF p.8, when it exists. The fallback is explicitly excluded by the realization conclusion below; existence/unitarity is never assumed as a hypothesis of the result.
--   - `environmentVacuum`: The actual constant environment vector, PDF pp.7–9, if it lies in L2. The theorem concludes its representative and normalization, avoiding a fallback or a hypothesized pure state standing in for the source's constructed vector.
--   - `environmentSymplecticForm`: Four-coordinate argument symplectic form in complex notation, PDF p.8, (13), with coordinate order (q1,q2,p1,p2).
--   - `EnvironmentWeylRealized`: Realization and Weyl CCR of the environmental operators (12)–(13), PDF p.8. These are bounded Weyl operators; no bounded canonical generators are asserted.
--   - `environmentCovariance`: Environmental covariance in physical coordinates (q1,q2,p1,p2), PDF p.9. Diagonal entries are Nc,Nc,1/(4Nc),1/(4Nc); all mixed covariances vanish.
--   - `complexCoordinate`: Complex coordinate conversion z=(x+iy)/sqrt(2), PDF pp.7–8.
--   - `HasEnvironmentGaussianCovariance`: Centered Gaussian covariance defined through the actual pure-state characteristic function, PDF p.9. This encodes zero means and the symmetrized covariance without undefined products of unbounded canonical operators.
-- source:
--   One-mode quantum Gaussian channels, arXiv:quant-ph/0607051v2, https://arxiv.org/abs/quant-ph/0607051v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters

/-!
# One-mode quantum Gaussian channels

Source: A. S. Holevo, arXiv:quant-ph/0607051v2, PDF pp.1–4.
The oscillator is the full countable Hilbert space, without a Fock cutoff.
The Weyl formulation encodes the regular irreducible CCR representation;
unbounded Q and P are not replaced by bounded matrices.
Other planned results are explicitly deferred in this unit's HARD.md/GAPS.json.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Frontier30.P07

/-- Real phase space Z, PDF p.1, (2). -/
abbrev PhaseSpace := ℝ × ℝ

/-- The full one-mode separable oscillator Hilbert space, PDF p.1.
Reuse the frozen countable Hilbert-space definition, with no energy cutoff. -/
abbrev Oscillator := QAlgorithms.RealRegisters.Hilbert ℕ

/-- Bounded observables on the genuine oscillator, PDF pp.1–2. -/
abbrev Observable := Oscillator →L[ℂ] Oscillator

/-- Paper's argument symplectic form, PDF p.1, (2).
In particular Delta((1,0),(0,1))=-1. -/
def symplecticForm (z w : PhaseSpace) : ℝ := w.1 * z.2 - z.1 * w.2

/-- Regular irreducible Weyl representation with hbar=1, PDF p.1, (1)–(2).
Strong continuity is regularity. Closed invariant complex subspaces are trivial,
so reducible or trivial representations cannot satisfy the standing assumptions.
The Weyl CCR is the bounded-operator formulation of the source's canonical
self-adjoint generators, in countable orthonormal coordinates. -/
structure WeylRepresentation where
  operator : PhaseSpace → Observable
  unitary : ∀ z, operator z ∈ unitary Observable
  zero : operator 0 = 1
  ccr : ∀ z w, (operator z).comp (operator w) =
    Complex.exp (Complex.I * ((symplecticForm z w / 2 : ℝ) : ℂ)) • operator (z + w)
  regular : ∀ v : Oscillator, Continuous (fun z => operator z v)
  irreducible : ∀ S : Submodule ℂ Oscillator, IsClosed (S : Set Oscillator) →
    (∀ z v, v ∈ S → operator z v ∈ S) → S = ⊥ ∨ S = ⊤

/-- Positivity of an arbitrary finite operator matrix on H tensor C^n,
PDF p.2, channel standing convention. This tests all vectors in each factor. -/
def IsBlockPositive {n : ℕ} (A : Fin n → Fin n → Observable) : Prop :=
  ∀ v : Fin n → Oscillator,
    (∑ i, ∑ j, inner (𝕜 := ℂ) (v i) (A i j (v j))).im = 0 ∧
    0 ≤ (∑ i, ∑ j, inner (𝕜 := ℂ) (v i) (A i j (v j))).re

/-- Normal unital completely positive Heisenberg maps, PDF pp.1–2.
Normality is expressed by preservation of strong limits of increasing positive
sequences. On B(H) for this separable H this is equivalent to normality.
Complete positivity uses every finite matrix amplification, not scalar positivity
alone. The bounded linear map acts on all observables, not just Weyl symbols. -/
structure NormalChannel where
  action : Observable →L[ℂ] Observable
  unital : action 1 = 1
  completelyPositive : ∀ (n : ℕ) (A : Fin n → Fin n → Observable),
    IsBlockPositive A → IsBlockPositive (fun i j => action (A i j))
  normal : ∀ (A : ℕ → Observable) (X : Observable),
    (∀ n, (A n).IsPositive) →
    (∀ n, (A (n + 1) - A n).IsPositive) →
    (∀ v : Oscillator, Tendsto (fun n => A n v) atTop (𝓝 (X v))) →
    ∀ v : Oscillator, Tendsto (fun n => action (A n) v) atTop (𝓝 (action X v))

/-- Sanity check: the B2 zero-noise endpoint is an actual normal CP unital map. -/
example : ∃ Phi : NormalChannel, ∀ A : Observable, Phi.action A = A := by
  refine ⟨{
    action := ContinuousLinearMap.id ℂ Observable
    unital := rfl
    completelyPositive := ?_
    normal := ?_
  }, ?_⟩
  · intro n A hA
    exact hA
  · intro A X hpositive hincreasing hlimit v
    exact hlimit v
  · intro A
    rfl

/-- Real covariance bilinear forms, PDF p.2, (5). Symmetry is required below. -/
abbrev CovarianceForm := PhaseSpace →ₗ[ℝ] PhaseSpace →ₗ[ℝ] ℝ

/-- The non-strict positive-type condition (5), PDF p.2, for every finite list.
Zero noise at the identity endpoint is permitted. -/
def AdmissibleNoise (K : PhaseSpace →ₗ[ℝ] PhaseSpace) (alpha : CovarianceForm) : Prop :=
  (∀ z w, alpha z w = alpha w z) ∧
    ∀ (n : ℕ) (z : Fin n → PhaseSpace),
      Matrix.PosSemidef (fun r s =>
        (alpha (z r) (z s) : ℂ) -
          Complex.I * ((symplecticForm (z r) (z s) / 2 : ℝ) : ℂ) +
          Complex.I * ((symplecticForm (K (z r)) (K (z s)) / 2 : ℝ) : ℂ))

/-- Actual Gaussian action (3), allowing the preliminary linear displacement
mentioned on PDF p.2. No unrestricted characteristic symbols substitute for a
normal channel. The centered multiplier is exp(-alpha(z,z)/2). -/
def HasGaussianAction (W : WeylRepresentation) (Phi : NormalChannel)
    (K : PhaseSpace →ₗ[ℝ] PhaseSpace) (alpha : CovarianceForm)
    (mean : PhaseSpace →ₗ[ℝ] ℝ) : Prop :=
  ∀ z, Phi.action (W.operator z) =
    Complex.exp (((-alpha z z / 2 : ℝ) : ℂ) + Complex.I * (mean z : ℂ)) •
      W.operator (K z)

/-- Linear symplectic changes of coordinates, PDF p.1. -/
def IsSymplectic (T : PhaseSpace ≃ₗ[ℝ] PhaseSpace) : Prop :=
  ∀ z w, symplecticForm (T z) (T w) = symplecticForm z w

/-- Canonical unitary implementing T in this actual Weyl representation,
PDF p.1: U_T* V(z) U_T = V(Tz). -/
def Implements (W : WeylRepresentation) (T : PhaseSpace ≃ₗ[ℝ] PhaseSpace)
    (U : Observable) : Prop :=
  U ∈ unitary Observable ∧ ∀ z, star U * W.operator z * U = W.operator (T z)

/-- The six printed canonical forms, PDF p.3. Parameters are unrestricted
real numbers here, with their physical domains specified by ValidCanonical. -/
inductive CanonicalForm where
  | a1 (N0 : ℝ)
  | a2 (N0 : ℝ)
  | b1
  | b2 (Nc : ℝ)
  | c (k N0 : ℝ)
  | d (k N0 : ℝ)

/-- Physical parameter domains, PDF pp.3–4. The proof supplies N0>=0
also for A2, C and D. B2 includes the identity Nc=0. -/
def ValidCanonical : CanonicalForm → Prop
  | .a1 N0 => 0 ≤ N0
  | .a2 N0 => 0 ≤ N0
  | .b1 => True
  | .b2 Nc => 0 ≤ Nc
  | .c k N0 => 0 < k ∧ k ≠ 1 ∧ 0 ≤ N0
  | .d k N0 => 0 < k ∧ 0 ≤ N0

/-- The canonical K maps, PDF p.3. -/
def canonicalLinear : CanonicalForm → PhaseSpace → PhaseSpace
  | .a1 _, _ => (0, 0)
  | .a2 _, z => (z.1, 0)
  | .b1, z => z
  | .b2 _, z => z
  | .c k _, z => (k * z.1, k * z.2)
  | .d k _, z => (k * z.1, -k * z.2)

/-- Canonical alpha(z,z), PDF p.3; its multiplier is exp(-this/2).
B1 therefore has exactly the printed exp(-x^2/4), rather than the
quarter-turned representation used in the open-system discussion. -/
def canonicalNoise : CanonicalForm → PhaseSpace → ℝ
  | .a1 N0, z => (N0 + 1 / 2) * (z.1 ^ 2 + z.2 ^ 2)
  | .a2 N0, z => (N0 + 1 / 2) * (z.1 ^ 2 + z.2 ^ 2)
  | .b1, z => z.1 ^ 2 / 2
  | .b2 Nc, z => Nc * (z.1 ^ 2 + z.2 ^ 2)
  | .c k N0, z => |k ^ 2 - 1| * (N0 + 1 / 2) * (z.1 ^ 2 + z.2 ^ 2)
  | .d k N0, z => (k ^ 2 + 1) * (N0 + 1 / 2) * (z.1 ^ 2 + z.2 ^ 2)

example : symplecticForm (1, 0) (0, 1) = -1 := by
  norm_num [symplecticForm]

example : symplecticForm (0, 1) (1, 0) = 1 := by
  norm_num [symplecticForm]

example : ValidCanonical (.b2 0) := by
  norm_num [ValidCanonical]

example : canonicalLinear (.b2 0) = id := by
  rfl

example (z : PhaseSpace) : canonicalNoise (.b2 0) z = 0 := by
  simp [canonicalNoise]

example : canonicalNoise .b1 (2, 0) = 2 := by
  norm_num [canonicalNoise]

example : canonicalNoise (.a1 0) (1, 0) = 1 / 2 := by
  norm_num [canonicalNoise]

/-- Complex Gaussian probability density in the complex coordinate
z=(x+iy)/sqrt(2), PDF p.7. It is used only when Nc>0. -/
def noiseDensity (Nc : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.pi * Nc)⁻¹ * Real.exp (-Complex.normSq z / Nc))

/-- The actual Gaussian measure mu_Nc on the complex plane, PDF p.7.
Lebesgue measure here is complex-plane area, not dx dy in physical coordinates. -/
def noiseMeasure (Nc : ℝ) : Measure ℂ :=
  volume.withDensity (noiseDensity Nc)

/-- The source's infinite-dimensional environmental Hilbert space, PDF pp.7–8. -/
abbrev Environment (Nc : ℝ) := MeasureTheory.Lp ℂ 2 (noiseMeasure Nc)

/-- Bounded environmental operators on weighted L2, PDF p.8. -/
abbrev EnvironmentOperator (Nc : ℝ) := Environment Nc →L[ℂ] Environment Nc

/-- Pointwise formula (12), PDF p.8. Both conjugation bars and the negative
real weight are as printed. Equality is almost everywhere on L2 representatives. -/
def HasEnvironmentWeylAction (Nc : ℝ) (z1 z2 : ℂ)
    (A : EnvironmentOperator Nc) : Prop :=
  ∀ psi : Environment Nc, ∀ᵐ z ∂noiseMeasure Nc,
    (A psi) z = psi (z + z2) *
      Complex.exp (Complex.I * ((2 * (star z1 * (z + z2 / 2)).re : ℝ) : ℂ) -
        (((star z2 * (z + z2 / 2)).re / Nc : ℝ) : ℂ))

/-- The unique bounded realization of (12), PDF p.8, when it exists.
The fallback is explicitly excluded by the realization conclusion below;
existence/unitarity is never assumed as a hypothesis of the result. -/
def environmentWeyl (Nc : ℝ) (z1 z2 : ℂ) : EnvironmentOperator Nc := by
  classical
  exact if h : ∃ A : EnvironmentOperator Nc, HasEnvironmentWeylAction Nc z1 z2 A
    then Classical.choose h else 0

/-- The actual constant environment vector, PDF pp.7–9, if it lies in L2.
The theorem concludes its representative and normalization, avoiding a fallback
or a hypothesized pure state standing in for the source's constructed vector. -/
def environmentVacuum (Nc : ℝ) : Environment Nc := by
  classical
  exact if h : ∃ psi : Environment Nc, ∀ᵐ z ∂noiseMeasure Nc, psi z = 1
    then Classical.choose h else 0

/-- Four-coordinate argument symplectic form in complex notation, PDF p.8,
(13), with coordinate order (q1,q2,p1,p2). -/
def environmentSymplecticForm (z1 z2 w1 w2 : ℂ) : ℝ :=
  2 * (star w1 * z2 - star z1 * w2).re

/-- Realization and Weyl CCR of the environmental operators (12)–(13), PDF p.8.
These are bounded Weyl operators; no bounded canonical generators are asserted. -/
def EnvironmentWeylRealized (Nc : ℝ) : Prop :=
  (∀ z1 z2, HasEnvironmentWeylAction Nc z1 z2 (environmentWeyl Nc z1 z2) ∧
    environmentWeyl Nc z1 z2 ∈ unitary (EnvironmentOperator Nc)) ∧
  (∀ z1 z2 w1 w2,
    (environmentWeyl Nc z1 z2).comp (environmentWeyl Nc w1 w2) =
      Complex.exp (Complex.I * ((environmentSymplecticForm z1 z2 w1 w2 / 2 : ℝ) : ℂ)) •
        environmentWeyl Nc (z1 + w1) (z2 + w2)) ∧
  (∀ psi : Environment Nc,
    Continuous (fun z : ℂ × ℂ => environmentWeyl Nc z.1 z.2 psi))

/-- Environmental covariance in physical coordinates (q1,q2,p1,p2), PDF p.9.
Diagonal entries are Nc,Nc,1/(4Nc),1/(4Nc); all mixed covariances vanish. -/
def environmentCovariance (Nc : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![Nc, Nc, 1 / (4 * Nc), 1 / (4 * Nc)]

/-- Complex coordinate conversion z=(x+iy)/sqrt(2), PDF pp.7–8. -/
def complexCoordinate (x y : ℝ) : ℂ :=
  ((x : ℂ) + Complex.I * (y : ℂ)) / (Real.sqrt 2 : ℂ)

/-- Centered Gaussian covariance defined through the actual pure-state
characteristic function, PDF p.9. This encodes zero means and the symmetrized
covariance without undefined products of unbounded canonical operators. -/
def HasEnvironmentGaussianCovariance (Nc : ℝ) (psi : Environment Nc)
    (alpha : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ r : Fin 4 → ℝ,
    inner (𝕜 := ℂ) psi
      (environmentWeyl Nc (complexCoordinate (r 0) (r 1))
        (complexCoordinate (r 2) (r 3)) psi) =
      Complex.exp (((-(∑ i, ∑ j, r i * alpha i j * r j) / 2 : ℝ) : ℂ))

example (z : ℂ) : noiseDensity 0 z = 0 := by
  simp [noiseDensity]

example (Nc : ℝ) : environmentCovariance Nc 0 0 = Nc := by
  simp [environmentCovariance]

example (Nc : ℝ) : environmentCovariance Nc 0 2 = 0 := by
  simp [environmentCovariance]

example : complexCoordinate 0 0 = 0 := by
  simp [complexCoordinate]

example : environmentSymplecticForm 0 1 1 0 = 2 := by
  norm_num [environmentSymplecticForm]

end QAlgorithms.Papers.Independent.Frontier30.P07


