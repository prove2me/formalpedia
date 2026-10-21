-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P19
-- name    : QAlgorithms_Papers_Independent_Renew46_P19
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:20:52.875654+00:00
-- url     : https://prove2.me/theorems/5bbd3f26-3157-42e6-bf52-6ed4381df6ed
-- title:
--   Definitions for A new approach to the star-genvalue equation
-- statement:
--   The objects the formalized statements of *A new approach to the star-genvalue equation* (arXiv:0808.0489) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `radiusSquared`: PDF pp.5,12: Euclidean squared radius, independent of the product sup norm.
--   - `windowFactor`: PDF p.5, (13): normalization of the window transform.
--   - `windowFormula`: PDF p.5, (13): independently defined normalized cross-Wigner integral. For L2 inputs the product in y is integrable by Cauchy--Schwarz and affine changes of variables. The conjugation is on the window, not on psi.
--   - `RealizesWindow`: PDF p.5: a bounded realization is specified solely by the a.e. integral formula; it does not assume isometry, closed range, or an intertwiner.
--   - `windowMap`: PDF p.5: the continuous extension of (13), selected by its a.e. formula. The fallback totalizes selection and is ruled out by realization conclusions; no desired norm or spectral property is built into the selection predicate.
--   - `windowRange`: PDF p.5: the actual linear range, with inherited norm and inner product.
--   - `adjointFormula`: PDF p.5, (14): adjoint formula on Schwartz inputs; both y and p are integrated using the phase Lebesgue measure. The printed output z is x.
--   - `phaseShift`: PDF p.4, (8): phase displacement, before passage to L2 classes.
--   - `configurationShift`: PDF p.4, after (9): the configuration-space Heisenberg displacement.
--   - `RealizesPhaseShift`: PDF pp.4–6: a.e. specification of the phase displacement on L2.
--   - `phaseOperator`: PDF pp.4–6: bounded realization of the independent half-shift formula.
--   - `RealizesConfigurationShift`: PDF pp.4–6: a.e. specification of the configuration displacement on L2.
--   - `configurationOperator`: PDF pp.4–6: bounded realization of the configuration shift formula.
--   - `heisenbergOperator`: PDF p.5: central character exp(it/hbar) fixes the Heisenberg sign.
--   - `coordinateStar`: PDF p.6: coordinate Moyal multiplication is the Bopp differential expression; these unbounded expressions are used on Schwartz functions only. a=0 is position, a=1 is momentum.
--   - `configurationTranspose`: PDF pp.6,10–11: transposed configuration quadrature on test functions. Complex-linear distribution duality sends -i d/dx to +i d/dx.
--   - `quadraticConfigurationTest`: PDF pp.10–11: transpose of the Weyl-ordered quadratic Hamiltonian, hbar=1. Symmetrization retains both mixed orders.
--   - `quadraticConfigurationGraph`: PDF pp.10–11: maximal weak L2 graph of quadratic Weyl quantization. Both pairings must be integrable; there is no total-integral loophole.
--   - `phaseTranspose`: PDF pp.10–11: formal transpose of each Bopp coordinate, hbar=1.
--   - `quadraticPhaseGraph`: PDF pp.10–11: maximal weak L2 graph of polynomial star multiplication. This differential construction does not purport to define generic-symbol star.
--   - `symplecticMatrix`: PDF p.11: J in interleaved x,p coordinates, with blocks [[0,1],[-1,0]].
--   - `HasFrequencies`: PDF p.11: frequencies with their full algebraic multiplicities, without an ordering choice or rational independence assumption.
--   - `quadraticLevels`: PDF p.11: the spectral set; hbar=1 is inherited from (18)–(19).
--   - `physicistsHermite`: PDF p.10, (19): physicists' Hermite polynomial by Rodrigues' formula. The printed unexplained m in (-1)^(km) is removed as recorded in the audit.
--   - `hermiteFunction`: PDF p.10, (19): the explicitly normalized configuration eigenfunction.
-- source:
--   A new approach to the star-genvalue equation, arXiv:0808.0489v1, https://arxiv.org/abs/0808.0489v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P10

/-!
arXiv:0808.0489v1, A new approach to the star-genvalue equation.
Only the explicitly pinned accepted library is imported. All new definitions
are paper-local. General tempered-symbol calculus and defective source results
are deferred in this unit's HARD.md. Compilation is pending the batch handoff.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Renew46.P19

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)
open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates Quadrature)
open QAlgorithms.Papers.Independent.Next46.P20
  (ConfigurationL2 PhaseL2 phasePosition phaseMomentum phasePoint)
open QAlgorithms.Papers.Independent.Claimed50.P05 (spectrumOf pointSpectrum)

open QAlgorithms.Papers.Independent.Frontier30.P10 (symplecticPair)

/- PDF p.2: reuse the accepted p*x' - x*p' pairing after the explicit
interleaved-to-grouped coordinate reindexing. This notation introduces no
new declaration or second definition of the symplectic form. -/
local notation "sigma" => fun {n : ℕ} (z w : PhaseCoordinates n) =>
  symplecticPair (Sum.elim (phasePosition z) (phaseMomentum z))
    (Sum.elim (phasePosition w) (phaseMomentum w))

/-- PDF pp.5,12: Euclidean squared radius, independent of the product sup norm. -/
def radiusSquared {n : ℕ} (z : PhaseCoordinates n) : ℝ :=
  coordinateDot (phasePosition z) (phasePosition z) +
    coordinateDot (phaseMomentum z) (phaseMomentum z)

/-- PDF p.5, (13): normalization of the window transform. -/
def windowFactor (n : ℕ) (hbar : ℝ) : ℂ :=
  (Real.rpow (2 * Real.pi * hbar) (-(n : ℝ) / 2) : ℂ)

/-- PDF p.5, (13): independently defined normalized cross-Wigner integral.
For L2 inputs the product in y is integrable by Cauchy--Schwarz and affine
changes of variables. The conjugation is on the window, not on psi. -/
def windowFormula {n : ℕ} (hbar : ℝ)
    (psi phi : Configuration n → ℂ) (z : PhaseCoordinates n) : ℂ :=
  windowFactor n hbar * ∫ y : Configuration n,
    Complex.exp (-Complex.I * ((coordinateDot (phaseMomentum z) y / hbar : ℝ) : ℂ)) *
      psi (phasePosition z + (1 / 2 : ℝ) • y) *
      star (phi (phasePosition z - (1 / 2 : ℝ) • y))

/-- PDF p.5: a bounded realization is specified solely by the a.e. integral
formula; it does not assume isometry, closed range, or an intertwiner. -/
def RealizesWindow {n : ℕ} (hbar : ℝ) (phi : ConfigurationL2 n)
    (T : ConfigurationL2 n →L[ℂ] PhaseL2 n) : Prop :=
  ∀ psi, ∀ᵐ z : PhaseCoordinates n,
    T psi z = windowFormula hbar (psi : Configuration n → ℂ) phi z

/-- PDF p.5: the continuous extension of (13), selected by its a.e. formula.
The fallback totalizes selection and is ruled out by realization conclusions;
no desired norm or spectral property is built into the selection predicate. -/
def windowMap {n : ℕ} (hbar : ℝ) (phi : ConfigurationL2 n) :
    ConfigurationL2 n →L[ℂ] PhaseL2 n :=
  if h : ∃ T : ConfigurationL2 n →L[ℂ] PhaseL2 n, RealizesWindow hbar phi T
  then Classical.choose h else 0

/-- PDF p.5: the actual linear range, with inherited norm and inner product. -/
def windowRange {n : ℕ} (hbar : ℝ) (phi : ConfigurationL2 n) :
    Submodule ℂ (PhaseL2 n) := (windowMap hbar phi).toLinearMap.range

/-- PDF p.5, (14): adjoint formula on Schwartz inputs; both y and p are
integrated using the phase Lebesgue measure. The printed output z is x. -/
def adjointFormula {n : ℕ} (hbar : ℝ) (phi : Configuration n → ℂ)
    (Psi : PhaseCoordinates n → ℂ) (x : Configuration n) : ℂ :=
  (Real.rpow (2 / (Real.pi * hbar)) ((n : ℝ) / 2) : ℂ) *
    ∫ z : PhaseCoordinates n,
      Complex.exp (Complex.I * ((2 * coordinateDot (phaseMomentum z)
        (x - phasePosition z) / hbar : ℝ) : ℂ)) *
        phi (2 • phasePosition z - x) * Psi z

/-- PDF p.4, (8): phase displacement, before passage to L2 classes. -/
def phaseShift {n : ℕ} (hbar : ℝ) (d : PhaseCoordinates n)
    (f : PhaseCoordinates n → ℂ) (z : PhaseCoordinates n) : ℂ :=
  Complex.exp (-Complex.I * ((sigma z d / hbar : ℝ) : ℂ)) *
    f (z - (1 / 2 : ℝ) • d)

/-- PDF p.4, after (9): the configuration-space Heisenberg displacement. -/
def configurationShift {n : ℕ} (hbar : ℝ) (d : PhaseCoordinates n)
    (f : Configuration n → ℂ) (x : Configuration n) : ℂ :=
  Complex.exp (Complex.I * (((coordinateDot (phaseMomentum d) x -
    coordinateDot (phaseMomentum d) (phasePosition d) / 2) / hbar : ℝ) : ℂ)) *
      f (x - phasePosition d)

/-- PDF pp.4–6: a.e. specification of the phase displacement on L2. -/
def RealizesPhaseShift {n : ℕ} (hbar : ℝ) (d : PhaseCoordinates n)
    (T : PhaseL2 n →L[ℂ] PhaseL2 n) : Prop :=
  ∀ f, ∀ᵐ z : PhaseCoordinates n, T f z = phaseShift hbar d f z

/-- PDF pp.4–6: bounded realization of the independent half-shift formula. -/
def phaseOperator {n : ℕ} (hbar : ℝ) (d : PhaseCoordinates n) :
    PhaseL2 n →L[ℂ] PhaseL2 n :=
  if h : ∃ T : PhaseL2 n →L[ℂ] PhaseL2 n, RealizesPhaseShift hbar d T
  then Classical.choose h else 0

/-- PDF pp.4–6: a.e. specification of the configuration displacement on L2. -/
def RealizesConfigurationShift {n : ℕ} (hbar : ℝ) (d : PhaseCoordinates n)
    (T : ConfigurationL2 n →L[ℂ] ConfigurationL2 n) : Prop :=
  ∀ f, ∀ᵐ x : Configuration n, T f x = configurationShift hbar d f x

/-- PDF pp.4–6: bounded realization of the configuration shift formula. -/
def configurationOperator {n : ℕ} (hbar : ℝ) (d : PhaseCoordinates n) :
    ConfigurationL2 n →L[ℂ] ConfigurationL2 n :=
  if h : ∃ T : ConfigurationL2 n →L[ℂ] ConfigurationL2 n,
      RealizesConfigurationShift hbar d T
  then Classical.choose h else 0

/-- PDF p.5: central character exp(it/hbar) fixes the Heisenberg sign. -/
def heisenbergOperator {n : ℕ} (hbar : ℝ) (d : PhaseCoordinates n) (t : ℝ) :
    PhaseL2 n →L[ℂ] PhaseL2 n :=
  Complex.exp (Complex.I * ((t / hbar : ℝ) : ℂ)) • phaseOperator hbar d

/-- PDF p.6: coordinate Moyal multiplication is the Bopp differential
expression; these unbounded expressions are used on Schwartz functions only.
a=0 is position, a=1 is momentum. -/
def coordinateStar {n : ℕ} (hbar : ℝ) (a : Fin 2) (j : Fin n)
    (f : PhaseCoordinates n → ℂ) (z : PhaseCoordinates n) : ℂ :=
  if a = 0 then
    ((phasePosition z) j : ℂ) * f z + (Complex.I * (hbar : ℂ) / 2) *
      (fderiv ℝ f z) (phasePoint 0 (Pi.single j 1))
  else
    ((phaseMomentum z) j : ℂ) * f z - (Complex.I * (hbar : ℂ) / 2) *
      (fderiv ℝ f z) (phasePoint (Pi.single j 1) 0)

/-- PDF pp.6,10–11: transposed configuration quadrature on test functions.
Complex-linear distribution duality sends -i d/dx to +i d/dx. -/
def configurationTranspose {n : ℕ} (a : Quadrature n)
    (f : Configuration n → ℂ) (x : Configuration n) : ℂ :=
  if a.2 = 0 then (x a.1 : ℂ) * f x
  else Complex.I * (fderiv ℝ f x) (Pi.single a.1 1)

/-- PDF pp.10–11: transpose of the Weyl-ordered quadratic Hamiltonian,
hbar=1. Symmetrization retains both mixed orders. -/
def quadraticConfigurationTest {n : ℕ} (M : Matrix (Quadrature n) (Quadrature n) ℝ)
    (f : Configuration n → ℂ) : Configuration n → ℂ :=
  fun x => (1 / 4 : ℂ) * ∑ a, ∑ b, (M a b : ℂ) *
    (configurationTranspose b (configurationTranspose a f) x +
      configurationTranspose a (configurationTranspose b f) x)

/-- PDF pp.10–11: maximal weak L2 graph of quadratic Weyl quantization.
Both pairings must be integrable; there is no total-integral loophole. -/
def quadraticConfigurationGraph {n : ℕ} (M : Matrix (Quadrature n) (Quadrature n) ℝ) :
    Set (ConfigurationL2 n × ConfigurationL2 n) :=
  {q | ∀ f : SchwartzMap (Configuration n) ℂ,
    Integrable (fun x => q.2 x * f x) ∧
    Integrable (fun x => q.1 x * quadraticConfigurationTest M f x) ∧
    (∫ x, q.2 x * f x) = ∫ x, q.1 x * quadraticConfigurationTest M f x}

/-- PDF pp.10–11: formal transpose of each Bopp coordinate, hbar=1. -/
def phaseTranspose {n : ℕ} (a : Quadrature n)
    (f : PhaseCoordinates n → ℂ) (z : PhaseCoordinates n) : ℂ :=
  coordinateStar (-1) a.2 a.1 f z

/-- PDF pp.10–11: maximal weak L2 graph of polynomial star multiplication.
This differential construction does not purport to define generic-symbol star. -/
def quadraticPhaseGraph {n : ℕ} (M : Matrix (Quadrature n) (Quadrature n) ℝ) :
    Set (PhaseL2 n × PhaseL2 n) :=
  {q | ∀ f : SchwartzMap (PhaseCoordinates n) ℂ,
    let Tf : PhaseCoordinates n → ℂ := fun z => (1 / 4 : ℂ) * ∑ a, ∑ b,
      (M a b : ℂ) * (phaseTranspose b (phaseTranspose a f) z +
        phaseTranspose a (phaseTranspose b f) z)
    Integrable (fun z => q.2 z * f z) ∧ Integrable (fun z => q.1 z * Tf z) ∧
    (∫ z, q.2 z * f z) = ∫ z, q.1 z * Tf z}

/-- PDF p.11: J in interleaved x,p coordinates, with blocks [[0,1],[-1,0]]. -/
def symplecticMatrix (n : ℕ) : Matrix (Quadrature n) (Quadrature n) ℝ :=
  fun a b => if a.1 = b.1 then
    if a.2 = 0 ∧ b.2 = 1 then 1 else if a.2 = 1 ∧ b.2 = 0 then -1 else 0
  else 0

/-- PDF p.11: frequencies with their full algebraic multiplicities, without
an ordering choice or rational independence assumption. -/
def HasFrequencies {n : ℕ} (M : Matrix (Quadrature n) (Quadrature n) ℝ)
    (omega : Fin n → ℝ) : Prop :=
  (∀ j, 0 < omega j) ∧ (symplecticMatrix n * M).charpoly =
    ∏ j : Fin n, (Polynomial.X ^ 2 + Polynomial.C (omega j ^ 2))

/-- PDF p.11: the spectral set; hbar=1 is inherited from (18)–(19). -/
def quadraticLevels {n : ℕ} (omega : Fin n → ℝ) : Set ℂ :=
  {lambda | ∃ N : Fin n → ℕ,
    lambda = ((∑ j, ((N j : ℝ) + 1 / 2) * omega j : ℝ) : ℂ)}

/-- PDF p.10, (19): physicists' Hermite polynomial by Rodrigues' formula.
The printed unexplained m in (-1)^(km) is removed as recorded in the audit. -/
def physicistsHermite (k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * Real.exp (x ^ 2) * iteratedDeriv k (fun y : ℝ => Real.exp (-(y ^ 2))) x

/-- PDF p.10, (19): the explicitly normalized configuration eigenfunction. -/
def hermiteFunction (k : ℕ) (x : Configuration 1) : ℂ :=
  ((Real.sqrt ((2 : ℝ) ^ k * (Nat.factorial k : ℝ) * Real.sqrt Real.pi))⁻¹ *
    Real.exp (-(x 0 ^ 2) / 2) * physicistsHermite k (x 0) : ℝ)

example {n : ℕ} (z : PhaseCoordinates n) : sigma z 0 = 0 := by
  simp [symplecticPair, phasePosition, phaseMomentum, coordinateDot]

example {n : ℕ} (hbar : ℝ) (phi : ConfigurationL2 n) : windowMap hbar phi 0 = 0 := by
  exact map_zero _

example {n : ℕ} (hbar : ℝ) (d : PhaseCoordinates n) : phaseOperator hbar d 0 = 0 := by
  exact map_zero _

example {n : ℕ} (hbar : ℝ) (d : PhaseCoordinates n) : configurationOperator hbar d 0 = 0 := by
  exact map_zero _

example {n : ℕ} (hbar : ℝ) (phi : Configuration n → ℂ) (z : PhaseCoordinates n) :
    windowFormula hbar 0 phi z = 0 := by
  simp [windowFormula]

example {n : ℕ} (z : PhaseCoordinates n) : radiusSquared z =
    (∑ j, (phasePosition z j) ^ 2) + ∑ j, (phaseMomentum z j) ^ 2 := by
  simp [radiusSquared, coordinateDot, pow_two]

example : physicistsHermite 0 0 = 1 := by
  simp [physicistsHermite]

example {n : ℕ} (hbar : ℝ) (f : PhaseCoordinates n → ℂ) (z : PhaseCoordinates n) :
    phaseShift hbar 0 f z = f z := by
  simp [phaseShift, symplecticPair, phasePosition, phaseMomentum, coordinateDot]

example {n : ℕ} (hbar : ℝ) (f : Configuration n → ℂ) (x : Configuration n) :
    configurationShift hbar 0 f x = f x := by
  have hpos : phasePosition (0 : PhaseCoordinates n) = (0 : Configuration n) := rfl
  have hmom : phaseMomentum (0 : PhaseCoordinates n) = (0 : Configuration n) := rfl
  simp only [configurationShift, hpos, hmom]
  simp [coordinateDot]

example {n : ℕ} (hbar : ℝ) (phi : Configuration n → ℂ) (x : Configuration n) :
    adjointFormula hbar phi 0 x = 0 := by
  simp [adjointFormula]

example : symplecticMatrix 1 (0, 0) (0, 1) = 1 := by
  rfl

end QAlgorithms.Papers.Independent.Renew46.P19


