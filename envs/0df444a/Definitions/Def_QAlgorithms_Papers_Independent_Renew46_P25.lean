-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25
-- name    : QAlgorithms_Papers_Independent_Renew46_P25
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:37:46.104717+00:00
-- url     : https://prove2.me/theorems/71ea4e7c-5795-4ceb-88dd-f762d4d583cf
-- title:
--   Definitions for A Weyl Calculus on Symplectic Phase Space
-- statement:
--   The objects the formalized statements of *A Weyl Calculus on Symplectic Phase Space* (arXiv:math-ph/0508024) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ConfigurationEuclidean`: PDF p.5: real configuration space, with its Euclidean Lebesgue measure.
--   - `PhaseSpaceGrouped`: PDF p.5: grouped real position/momentum coordinates on the full phase space.
--   - `ConfigurationEuclideanL2`: PDF pp.21,33: genuine Lebesgue L2, without a finite Hilbert truncation.
--   - `PhaseGroupedL2`: PDF pp.31,33: genuine phase-space Lebesgue L2.
--   - `positionPart`: PDF p.5: position projection in grouped coordinates.
--   - `momentumPart`: PDF p.5: momentum projection in grouped coordinates.
--   - `groupedSymplecticPairing`: PDF p.5: sigma(z,w)=p.xprime-pprime.x, consistent with the accepted J.
--   - `phaseFactor`: The real-coordinate phase exp(i t); PDF pp.21-22.
--   - `phaseTranslation`: PDF p.33, (80): the concrete phase-space Weyl translation. No integrals or choices of representatives enter this pointwise definition.
--   - `phaseHeisenberg`: PDF p.33, (87): the source's positive central character.
--   - `heisenbergProduct`: PDF p.33: multiplication in H_n, in the source's sigma convention.
--   - `fourierConstant`: PDF pp.21-22: (2 pi)^(-n/2) exp(-i pi n/4), fixing the branch of i^(-n/2).
--   - `admissiblePhase`: PDF p.21: the parity of admissible m, without choosing a single opposite lift.
--   - `generatingQuadratic`: PDF p.21, (45): the source's quadratic generating function.
--   - `quadraticChirp`: PDF p.21: V_P, with the printed negative exponent.
--   - `quadraticDilation`: PDF p.21: M_{L,m}. Actual theorems require det L nonzero and admissible m.
--   - `quadraticFourier`: PDF p.22: Jhat, initially on Schwartz input. The integral is Lebesgue.
--   - `quadraticGenerator`: PDF pp.21-22,28, (45)-(46): quadratic Fourier generator. Printed: p.21 has exp(-i W). Changed: exp(+i W), as on p.28. Why: multiplying the four explicit factors in (46) gives this positive sign. This source correction requires the separate independent moderation round.
--   - `realizesConfiguration`: A concrete function formula has this L2 realization if it agrees on every Schwartz input. This is a predicate, never an assumed operator existence result.
--   - `windowTransform`: PDF pp.31,34, (71),(92): the actual kernel of U_phi. The window is phi, without a conjugate in this kernel: equivalently this is (pi/2)^(n/2) W(f,conj(phi))(z/2). Only Schwartz inputs are used below.
--   - `configurationPosition`: PDF p.32, (78): ordinary position on its Schwartz domain.
--   - `configurationMomentum`: PDF p.32, (78): ordinary momentum, -i d/dx_j, on Schwartz input.
--   - `groupedBoppPosition`: PDF pp.3,32, (2),(77): x_j/2+i d/dp_j, on the Schwartz domain.
--   - `groupedBoppMomentum`: PDF pp.3,32, (2),(77): p_j/2-i d/dx_j. The repeated xhat in (77) and (78) is the printed label error; the differential formula fixes momentum.
--   - `phaseOscillator`: PDF p.33, (82): Weyl quantization of H=(|x|^2+|p|^2)/2 by (2). There are no mixed monomials and hence no ordering choice: each coordinate square is the square of the corresponding phase-space coordinate operator.
--   - `phaseLaplacian`: PDF p.33, (83): the full Euclidean Laplacian in all 2n variables.
--   - `phaseAngularDerivative`: PDF p.33, (83): sigma(z,partial_z)=p.partial_x-x.partial_p.
--   - `configurationTranslation`: PDF pp.3,6-7: ordinary Weyl translation at zero central coordinate.
--   - `configurationWeylFromTwisted`: PDF p.7: ordinary Weyl operator from its twisted symbol. Only Schwartz twisted symbols and Schwartz inputs occur in the theorem below; this integral is never used to model a general tempered-symbol integral.
--   - `phaseWeylFromTwisted`: PDF p.33, (81): phase-space Weyl operator from a Schwartz twisted symbol.
--   - `twistedConvolution`: PDF pp.7,35: normalized twisted convolution, on Schwartz symbols. The integration variable is zprime, correcting the dummy dz printed on p.35.
-- source:
--   A Weyl Calculus on Symplectic Phase Space, arXiv:math-ph/0508024v2, https://arxiv.org/abs/math-ph/0508024v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P37

/-!
# A Weyl Calculus on Symplectic Phase Space

Source: arXiv:math-ph/0508024v2. Statements only; compilation is pending.
The accepted Cayley and diagonal-Hessian definitions are reused verbatim.
The remaining definitions are concrete functions on real Euclidean spaces,
with Lebesgue measure. Deferred nodes are individually recorded in HARD.md.
-/

noncomputable section

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
open QAlgorithms.Papers.Independent.Next46.P37 (cayley inverseCayley diagonalHessian)

namespace QAlgorithms.Papers.Independent.Renew46.P25

/-- PDF p.5: real configuration space, with its Euclidean Lebesgue measure. -/
abbrev ConfigurationEuclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- PDF p.5: grouped real position/momentum coordinates on the full phase space. -/
abbrev PhaseSpaceGrouped (n : ℕ) := EuclideanSpace ℝ (Phase n)

/-- PDF pp.21,33: genuine Lebesgue L2, without a finite Hilbert truncation. -/
abbrev ConfigurationEuclideanL2 (n : ℕ) :=
  Lp ℂ 2 (volume : Measure (ConfigurationEuclidean n))

/-- PDF pp.31,33: genuine phase-space Lebesgue L2. -/
abbrev PhaseGroupedL2 (n : ℕ) := Lp ℂ 2 (volume : Measure (PhaseSpaceGrouped n))

/-- PDF p.5: position projection in grouped coordinates. -/
def positionPart {n : ℕ} (z : PhaseSpaceGrouped n) : ConfigurationEuclidean n :=
  WithLp.toLp 2 (fun j => z (Sum.inl j))

/-- PDF p.5: momentum projection in grouped coordinates. -/
def momentumPart {n : ℕ} (z : PhaseSpaceGrouped n) : ConfigurationEuclidean n :=
  WithLp.toLp 2 (fun j => z (Sum.inr j))

/-- PDF p.5: sigma(z,w)=p.xprime-pprime.x, consistent with the accepted J. -/
def groupedSymplecticPairing {n : ℕ} (z w : PhaseSpaceGrouped n) : ℝ :=
  ∑ j, (z (Sum.inr j) * w (Sum.inl j) - w (Sum.inr j) * z (Sum.inl j))

/-- The real-coordinate phase exp(i t); PDF pp.21-22. -/
def phaseFactor (t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ))

/-- PDF p.33, (80): the concrete phase-space Weyl translation.
No integrals or choices of representatives enter this pointwise definition. -/
def phaseTranslation {n : ℕ} (z0 : PhaseSpaceGrouped n)
    (F : PhaseSpaceGrouped n → ℂ) (z : PhaseSpaceGrouped n) : ℂ :=
  phaseFactor (-groupedSymplecticPairing z z0 / 2) * F (z - z0)

/-- PDF p.33, (87): the source's positive central character. -/
def phaseHeisenberg {n : ℕ} (g : PhaseSpaceGrouped n × ℝ)
    (F : PhaseSpaceGrouped n → ℂ) (z : PhaseSpaceGrouped n) : ℂ :=
  phaseFactor g.2 * phaseTranslation g.1 F z

/-- PDF p.33: multiplication in H_n, in the source's sigma convention. -/
def heisenbergProduct {n : ℕ} (g h : PhaseSpaceGrouped n × ℝ) : PhaseSpaceGrouped n × ℝ :=
  (g.1 + h.1, g.2 + h.2 + groupedSymplecticPairing g.1 h.1 / 2)

/-- PDF pp.21-22: (2 pi)^(-n/2) exp(-i pi n/4), fixing the branch of i^(-n/2). -/
def fourierConstant (n : ℕ) : ℂ :=
  (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) : ℂ) *
    phaseFactor (-Real.pi * (n : ℝ) / 4)

/-- PDF p.21: the parity of admissible m, without choosing a single opposite lift. -/
def admissiblePhase {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (m : ℤ) : Prop :=
  phaseFactor (Real.pi * (m : ℝ)) = (Real.sign L.det : ℂ)

/-- PDF p.21, (45): the source's quadratic generating function. -/
def generatingQuadratic {n : ℕ} (P L Q : Matrix (Fin n) (Fin n) ℝ)
    (x y : ConfigurationEuclidean n) : ℝ :=
  (∑ i, (∑ j, P i j * x j) * x i) / 2 -
    (∑ i, (∑ j, L i j * x j) * y i) +
    (∑ i, (∑ j, Q i j * y j) * y i) / 2

/-- PDF p.21: V_P, with the printed negative exponent. -/
def quadraticChirp {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (f : ConfigurationEuclidean n → ℂ) (x : ConfigurationEuclidean n) : ℂ :=
  phaseFactor (-(∑ i, (∑ j, P i j * x j) * x i) / 2) * f x

/-- PDF p.21: M_{L,m}. Actual theorems require det L nonzero and admissible m. -/
def quadraticDilation {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (m : ℤ)
    (f : ConfigurationEuclidean n → ℂ) (x : ConfigurationEuclidean n) : ℂ :=
  phaseFactor (Real.pi * (m : ℝ) / 2) * (Real.sqrt |L.det| : ℂ) *
    f (WithLp.toLp 2 (fun i => ∑ j, L i j * x j))

/-- PDF p.22: Jhat, initially on Schwartz input. The integral is Lebesgue. -/
def quadraticFourier {n : ℕ} (f : ConfigurationEuclidean n → ℂ) (x : ConfigurationEuclidean n) : ℂ :=
  fourierConstant n * ∫ y : ConfigurationEuclidean n,
    phaseFactor (-(∑ j, x j * y j)) * f y

/-- PDF pp.21-22,28, (45)-(46): quadratic Fourier generator.
Printed: p.21 has exp(-i W). Changed: exp(+i W), as on p.28.
Why: multiplying the four explicit factors in (46) gives this positive sign.
This source correction requires the separate independent moderation round. -/
def quadraticGenerator {n : ℕ} (P L Q : Matrix (Fin n) (Fin n) ℝ) (m : ℤ)
    (f : ConfigurationEuclidean n → ℂ) (x : ConfigurationEuclidean n) : ℂ :=
  (fourierConstant n * phaseFactor (Real.pi * (m : ℝ) / 2) *
      (Real.sqrt |L.det| : ℂ)) *
    ∫ y : ConfigurationEuclidean n, phaseFactor (generatingQuadratic P L Q x y) * f y

/-- A concrete function formula has this L2 realization if it agrees on every
Schwartz input. This is a predicate, never an assumed operator existence result. -/
def realizesConfiguration {n : ℕ}
    (A : (ConfigurationEuclidean n → ℂ) → ConfigurationEuclidean n → ℂ)
    (U : ConfigurationEuclideanL2 n ≃ₗᵢ[ℂ] ConfigurationEuclideanL2 n) : Prop :=
  ∀ f : SchwartzMap (ConfigurationEuclidean n) ℂ,
    (fun x => U (f.toLp 2 volume) x) =ᵐ[volume] A f

/-- PDF pp.31,34, (71),(92): the actual kernel of U_phi.
The window is phi, without a conjugate in this kernel: equivalently this is
(pi/2)^(n/2) W(f,conj(phi))(z/2). Only Schwartz inputs are used below. -/
def windowTransform {n : ℕ} (phi f : ConfigurationEuclidean n → ℂ) (z : PhaseSpaceGrouped n) : ℂ :=
  (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) : ℂ) *
    phaseFactor ((∑ j, momentumPart z j * positionPart z j) / 2) *
    ∫ y : ConfigurationEuclidean n,
      phaseFactor (-(∑ j, momentumPart z j * y j)) *
        phi (positionPart z - y) * f y

/-- PDF p.32, (78): ordinary position on its Schwartz domain. -/
def configurationPosition {n : ℕ} (j : Fin n)
    (f : ConfigurationEuclidean n → ℂ) (x : ConfigurationEuclidean n) : ℂ := (x j : ℂ) * f x

/-- PDF p.32, (78): ordinary momentum, -i d/dx_j, on Schwartz input. -/
def configurationMomentum {n : ℕ} (j : Fin n)
    (f : ConfigurationEuclidean n → ℂ) (x : ConfigurationEuclidean n) : ℂ :=
  -Complex.I * fderiv ℝ f x (EuclideanSpace.single j 1)

/-- PDF pp.3,32, (2),(77): x_j/2+i d/dp_j, on the Schwartz domain. -/
def groupedBoppPosition {n : ℕ} (j : Fin n)
    (F : PhaseSpaceGrouped n → ℂ) (z : PhaseSpaceGrouped n) : ℂ :=
  ((z (Sum.inl j) / 2 : ℝ) : ℂ) * F z +
    Complex.I * fderiv ℝ F z (EuclideanSpace.single (Sum.inr j) 1)

/-- PDF pp.3,32, (2),(77): p_j/2-i d/dx_j. The repeated xhat in (77)
and (78) is the printed label error; the differential formula fixes momentum. -/
def groupedBoppMomentum {n : ℕ} (j : Fin n)
    (F : PhaseSpaceGrouped n → ℂ) (z : PhaseSpaceGrouped n) : ℂ :=
  ((z (Sum.inr j) / 2 : ℝ) : ℂ) * F z -
    Complex.I * fderiv ℝ F z (EuclideanSpace.single (Sum.inl j) 1)

/-- PDF p.33, (82): Weyl quantization of H=(|x|^2+|p|^2)/2 by (2).
There are no mixed monomials and hence no ordering choice: each coordinate
square is the square of the corresponding phase-space coordinate operator. -/
def phaseOscillator {n : ℕ} (F : PhaseSpaceGrouped n → ℂ) (z : PhaseSpaceGrouped n) : ℂ :=
  (1 / 2 : ℂ) * ∑ j,
    (groupedBoppPosition j (groupedBoppPosition j F) z + groupedBoppMomentum j (groupedBoppMomentum j F) z)

/-- PDF p.33, (83): the full Euclidean Laplacian in all 2n variables. -/
def phaseLaplacian {n : ℕ} (F : PhaseSpaceGrouped n → ℂ) (z : PhaseSpaceGrouped n) : ℂ :=
  ∑ k : Phase n, fderiv ℝ
    (fun w => fderiv ℝ F w (EuclideanSpace.single k 1)) z
    (EuclideanSpace.single k 1)

/-- PDF p.33, (83): sigma(z,partial_z)=p.partial_x-x.partial_p. -/
def phaseAngularDerivative {n : ℕ} (F : PhaseSpaceGrouped n → ℂ) (z : PhaseSpaceGrouped n) : ℂ :=
  ∑ j, ((z (Sum.inr j) : ℂ) *
      fderiv ℝ F z (EuclideanSpace.single (Sum.inl j) 1) -
    (z (Sum.inl j) : ℂ) * fderiv ℝ F z (EuclideanSpace.single (Sum.inr j) 1))

/-- PDF pp.3,6-7: ordinary Weyl translation at zero central coordinate. -/
def configurationTranslation {n : ℕ} (z0 : PhaseSpaceGrouped n)
    (f : ConfigurationEuclidean n → ℂ) (x : ConfigurationEuclidean n) : ℂ :=
  phaseFactor ((∑ j, momentumPart z0 j * x j) -
    (∑ j, momentumPart z0 j * positionPart z0 j) / 2) * f (x - positionPart z0)

/-- PDF p.7: ordinary Weyl operator from its twisted symbol.
Only Schwartz twisted symbols and Schwartz inputs occur in the theorem below;
this integral is never used to model a general tempered-symbol integral. -/
def configurationWeylFromTwisted {n : ℕ} (a : PhaseSpaceGrouped n → ℂ)
    (f : ConfigurationEuclidean n → ℂ) (x : ConfigurationEuclidean n) : ℂ :=
  (((2 * Real.pi)⁻¹ ^ n : ℝ) : ℂ) *
    ∫ z0 : PhaseSpaceGrouped n, a z0 * configurationTranslation z0 f x

/-- PDF p.33, (81): phase-space Weyl operator from a Schwartz twisted symbol. -/
def phaseWeylFromTwisted {n : ℕ} (a : PhaseSpaceGrouped n → ℂ)
    (F : PhaseSpaceGrouped n → ℂ) (z : PhaseSpaceGrouped n) : ℂ :=
  (((2 * Real.pi)⁻¹ ^ n : ℝ) : ℂ) *
    ∫ z0 : PhaseSpaceGrouped n, a z0 * phaseTranslation z0 F z

/-- PDF pp.7,35: normalized twisted convolution, on Schwartz symbols.
The integration variable is zprime, correcting the dummy dz printed on p.35. -/
def twistedConvolution {n : ℕ} (a b : PhaseSpaceGrouped n → ℂ) (z : PhaseSpaceGrouped n) : ℂ :=
  (((2 * Real.pi)⁻¹ ^ n : ℝ) : ℂ) * ∫ w : PhaseSpaceGrouped n,
    phaseFactor (groupedSymplecticPairing z w / 2) * a (z - w) * b w

/-- Sanity: both Schwartz-symbol Weyl constructions give zero for symbol zero. -/
example {n : ℕ} (f : ConfigurationEuclidean n → ℂ) : configurationWeylFromTwisted 0 f = 0 := by
  funext x
  simp [configurationWeylFromTwisted]

/-- Sanity: a unit momentum paired with a unit position has the positive sign. -/
example : groupedSymplecticPairing (n := 1) (EuclideanSpace.single (Sum.inr 0) 1)
    (EuclideanSpace.single (Sum.inl 0) 1) = 1 := by
  simp [groupedSymplecticPairing, EuclideanSpace.single_apply]

/-- Sanity: the phase-space Weyl translation at the origin is the identity. -/
example {n : ℕ} (F : PhaseSpaceGrouped n → ℂ) : phaseTranslation 0 F = F := by
  funext z
  simp [phaseTranslation, groupedSymplecticPairing, phaseFactor]

/-- Sanity: the zero quadratic has zero generating phase. -/
example {n : ℕ} (x y : ConfigurationEuclidean n) : generatingQuadratic 0 0 0 x y = 0 := by
  simp [generatingQuadratic]

/-- Sanity: the zero chirp is the identity. -/
example {n : ℕ} (f : ConfigurationEuclidean n → ℂ) : quadraticChirp 0 f = f := by
  funext x
  simp [quadraticChirp, phaseFactor]

/-- Sanity: window-transform linear zero input gives the zero function. -/
example {n : ℕ} (phi : ConfigurationEuclidean n → ℂ) : windowTransform phi 0 = 0 := by
  funext z
  simp [windowTransform]

end QAlgorithms.Papers.Independent.Renew46.P25


