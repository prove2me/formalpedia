-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P11
-- name    : QAlgorithms_Papers_Independent_Intake100_P11
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:50:53.801001+00:00
-- url     : https://prove2.me/theorems/7013f204-46af-4878-bcc3-ba3375849365
-- title:
--   Definitions for Universal linear Bogoliubov transformations through one-way quantum computation
-- statement:
--   The objects the formalized statements of *Universal linear Bogoliubov transformations through one-way quantum computation* (arXiv:0910.0660) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Mat2`: PDF p.4: one mode's ordered coordinates (x,p).
--   - `Mat4`: PDF p.8: grouped coordinates (x1,x2,p1,p2).
--   - `IsOneModeSymplectic`: PDF p.4: the source's characterization of Sp(2,R) by ad-bc=1.
--   - `elementary`: PDF p.4: elementary homodyne teleportation matrix FO(kappa).
--   - `elementaryWord`: PDF pp.3--4: chronological settings; last gate acts on the left. Every entry is one source elementary module, and the empty word is identity.
--   - `elementaryAncillas`: PDF p.4, Fig.2: one ancilla per elementary step, with external input.
--   - `quadratureRotationMatrix`: PDF p.4: positive phase-space rotation; F=R(pi/2). This real quadrature matrix differs from EquatorialQSP.rotation, a two-angle complex qubit unitary. Its descriptive name distinguishes these concepts.
--   - `quadratureSqueezeMatrix`: PDF p.6, Eq.(10): positive r means p-squeezing. This real quadrature matrix differs from Gap48.P30.squeezing, a Fock-space vacuum amplifier dilation from one mode to two modes.
--   - `teleportationMatrix`: PDF p.6, corrected Eq.(8). Printed lower-right denominator: cos(thetaPlus). Changed: cos(thetaMinus), as required by Eqs.(9)--(13), determinant one, and Bell linear elimination. All uses below guard nonsingular angles. This source correction requires independent moderation.
--   - `teleportationHyperbolic`: PDF p.7, Eq.(13): fixed optical coupling, with r any finite real number.
--   - `bellOutputMatrix`: PDF p.6, Eq.(7): coefficients of ideal port output (x2,p2) in sqrt(2) times the homodyne readings, using x2=p1,p2=x1. This is linear Heisenberg algebra, not a normalized resource state or a Bell instrument.
--   - `bellInputMatrix`: PDF p.6, Eq.(7): coefficients of input (x0,p0) in the same readings.
--   - `teleportationAncillas`: PDF p.7, Fig.4: two cluster-port ancillas plus one ancilla per extra step.
--   - `cotAngle`: PDF p.7, Eq.(14): cotangent chart; the theorem requires nonzero sine.
--   - `connectionQuadratic`: PDF p.8, Eq.(16): position-quadratic shear coefficients. Printed prose: +i*eta*(x1+x2)^2. Changed: -i*eta*(x1+x2)^2, because x3+eta*p3, Eq.(16), and Eq.(19) agree on this sign. The general quadratic exponential in the prose also omits i. Independent moderation is required.
--   - `fourierTwo`: PDF p.8, Eq.(16): two-mode Fourier matrix in grouped coordinates.
--   - `positionShear`: PDF p.8: ideal position-quadratic phase matrix.
--   - `connectionMatrix`: PDF p.8, Eq.(16): ideal connection matrix; no finite-resource semantics.
--   - `ConnectionSettings`: PDF p.8, Fig.6: one source module's independent measurement settings.
--   - `connectionWord`: PDF pp.8--9: matrix of a finite chronological source-module sequence.
--   - `connectionAncillas`: PDF pp.8--9, Fig.6: three ancillas per source module, not an optimal count.
--   - `phaseFreeBeamMatrix`: PDF p.9, Eq.(17): phase-free beam splitter, with intensity reflectivity R. This real quadrature matrix differs from Next46.P17.beamSplitter, which acts on full Fock-density coefficients and traces the second output port.
--   - `beamSplitterGrouped`: PDF p.9, Eq.(17): the same beam splitter acts on x and p.
--   - `beamSettings`: PDF p.9, Eq.(19): source programming for each of three identical modules.
-- source:
--   Universal linear Bogoliubov transformations through one-way quantum computation, arXiv:0910.0660v1, https://arxiv.org/abs/0910.0660v1

import Mathlib

/-!
Ukai et al., arXiv:0910.0660v1, PDF pp.4--9.
Exact ideal Heisenberg matrices, grouped quadratures, hbar=1/2. Displacements
and global phases are omitted as on p.4. All settings depend on the target,
never on input states or measurement outcomes. There is no photon cutoff or
infinitely squeezed normal state. HARD.md defers operational normal-state
claims and finite-resource limits; the two supporting matrix identities below
do not replace their deferred operational headlines.
-/

noncomputable section

open scoped Matrix BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P11

/-- PDF p.4: one mode's ordered coordinates (x,p). -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-- PDF p.8: grouped coordinates (x1,x2,p1,p2). -/
abbrev Mat4 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ

/-- PDF p.4: the source's characterization of Sp(2,R) by ad-bc=1. -/
def IsOneModeSymplectic (A : Mat2) : Prop :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1

/-- PDF p.4: elementary homodyne teleportation matrix FO(kappa). -/
def elementary (kappa : ℝ) : Mat2 := !![-kappa, -1; 1, 0]

/-- PDF pp.3--4: chronological settings; last gate acts on the left.
Every entry is one source elementary module, and the empty word is identity. -/
def elementaryWord (settings : List ℝ) : Mat2 :=
  settings.foldl (fun A kappa => elementary kappa * A) 1

/-- PDF p.4, Fig.2: one ancilla per elementary step, with external input. -/
def elementaryAncillas (settings : List ℝ) : ℕ := settings.length

/-- PDF p.4: positive phase-space rotation; F=R(pi/2).
This real quadrature matrix differs from EquatorialQSP.rotation, a two-angle
complex qubit unitary. Its descriptive name distinguishes these concepts. -/
def quadratureRotationMatrix (theta : ℝ) : Mat2 :=
  !![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta]

/-- PDF p.6, Eq.(10): positive r means p-squeezing.
This real quadrature matrix differs from Gap48.P30.squeezing, a Fock-space
vacuum amplifier dilation from one mode to two modes. -/
def quadratureSqueezeMatrix (r : ℝ) : Mat2 := !![Real.exp r, 0; 0, Real.exp (-r)]

/-- PDF p.6, corrected Eq.(8). Printed lower-right denominator: cos(thetaPlus).
Changed: cos(thetaMinus), as required by Eqs.(9)--(13), determinant one, and
Bell linear elimination. All uses below guard nonsingular angles.
This source correction requires independent moderation. -/
def teleportationMatrix (thetaPlus thetaMinus : ℝ) : Mat2 :=
  !![Real.cos thetaPlus / Real.cos thetaMinus,
      (Real.sin thetaMinus + Real.sin thetaPlus) / Real.cos thetaMinus;
      (Real.sin thetaMinus - Real.sin thetaPlus) / Real.cos thetaMinus,
      Real.cos thetaPlus / Real.cos thetaMinus]

/-- PDF p.7, Eq.(13): fixed optical coupling, with r any finite real number. -/
def teleportationHyperbolic (theta r : ℝ) : Mat2 :=
  !![Real.cos theta * Real.cosh r, Real.sin theta * Real.cosh r + Real.sinh r;
      -Real.sin theta * Real.cosh r + Real.sinh r, Real.cos theta * Real.cosh r]

/-- PDF p.6, Eq.(7): coefficients of ideal port output (x2,p2) in sqrt(2)
times the homodyne readings, using x2=p1,p2=x1. This is linear Heisenberg
algebra, not a normalized resource state or a Bell instrument. -/
def bellOutputMatrix (theta0 theta1 : ℝ) : Mat2 :=
  !![-Real.cos theta0, Real.sin theta0; Real.sin theta1, Real.cos theta1]

/-- PDF p.6, Eq.(7): coefficients of input (x0,p0) in the same readings. -/
def bellInputMatrix (theta0 theta1 : ℝ) : Mat2 :=
  !![Real.cos theta0, Real.sin theta0; Real.sin theta1, -Real.cos theta1]

/-- PDF p.7, Fig.4: two cluster-port ancillas plus one ancilla per extra step. -/
def teleportationAncillas (extra : List ℝ) : ℕ := 2 + extra.length

/-- PDF p.7, Eq.(14): cotangent chart; the theorem requires nonzero sine. -/
def cotAngle (theta : ℝ) : ℝ := Real.cos theta / Real.sin theta

/-- PDF p.8, Eq.(16): position-quadratic shear coefficients.
Printed prose: +i*eta*(x1+x2)^2. Changed: -i*eta*(x1+x2)^2, because
x3+eta*p3, Eq.(16), and Eq.(19) agree on this sign. The general quadratic
exponential in the prose also omits i. Independent moderation is required. -/
def connectionQuadratic (kappa1 kappa2 eta : ℝ) : Mat2 :=
  !![kappa1 - eta, -eta; -eta, kappa2 - eta]

/-- PDF p.8, Eq.(16): two-mode Fourier matrix in grouped coordinates. -/
def fourierTwo : Mat4 := Matrix.fromBlocks 0 (-1 : Mat2) 1 0

/-- PDF p.8: ideal position-quadratic phase matrix. -/
def positionShear (K : Mat2) : Mat4 := Matrix.fromBlocks 1 0 K 1

/-- PDF p.8, Eq.(16): ideal connection matrix; no finite-resource semantics. -/
def connectionMatrix (kappa1 kappa2 eta : ℝ) : Mat4 :=
  fourierTwo * positionShear (connectionQuadratic kappa1 kappa2 eta)

/-- PDF p.8, Fig.6: one source module's independent measurement settings. -/
structure ConnectionSettings where
  kappa1 : ℝ
  kappa2 : ℝ
  eta : ℝ

/-- PDF pp.8--9: matrix of a finite chronological source-module sequence. -/
def connectionWord (settings : List ConnectionSettings) : Mat4 :=
  settings.foldl (fun A s => connectionMatrix s.kappa1 s.kappa2 s.eta * A) 1

/-- PDF pp.8--9, Fig.6: three ancillas per source module, not an optimal count. -/
def connectionAncillas (settings : List ConnectionSettings) : ℕ :=
  3 * settings.length

/-- PDF p.9, Eq.(17): phase-free beam splitter, with intensity reflectivity R.
This real quadrature matrix differs from Next46.P17.beamSplitter, which acts
on full Fock-density coefficients and traces the second output port. -/
def phaseFreeBeamMatrix (R : ℝ) : Mat2 :=
  !![Real.sqrt R, Real.sqrt (1 - R); Real.sqrt (1 - R), -Real.sqrt R]

/-- PDF p.9, Eq.(17): the same beam splitter acts on x and p. -/
def beamSplitterGrouped (R : ℝ) : Mat4 :=
  Matrix.fromBlocks (phaseFreeBeamMatrix R) 0 0 (phaseFreeBeamMatrix R)

/-- PDF p.9, Eq.(19): source programming for each of three identical modules. -/
def beamSettings (R : ℝ) : ConnectionSettings where
  kappa1 := Real.sqrt R - Real.sqrt (1 - R)
  kappa2 := -Real.sqrt R - Real.sqrt (1 - R)
  eta := -Real.sqrt (1 - R)

example : IsOneModeSymplectic (1 : Mat2) := by
  norm_num [IsOneModeSymplectic]

example : elementary 0 = (!![0, -1; 1, 0] : Mat2) := by
  norm_num [elementary]

example : elementaryWord [] = 1 := rfl

example : elementaryAncillas [0, 0, 0, 0] = 4 := rfl

example : quadratureRotationMatrix 0 0 0 = 1 := by
  norm_num [quadratureRotationMatrix]

example : quadratureSqueezeMatrix 0 1 1 = 1 := by
  norm_num [quadratureSqueezeMatrix]

example : teleportationMatrix 0 0 0 0 = 1 := by
  norm_num [teleportationMatrix]

example : teleportationHyperbolic 0 0 1 0 = 0 := by
  norm_num [teleportationHyperbolic]

example : bellOutputMatrix 0 0 0 0 = -1 := by
  norm_num [bellOutputMatrix]

example : bellInputMatrix 0 0 1 1 = -1 := by
  norm_num [bellInputMatrix]

example : teleportationAncillas [0, 0] = 4 := rfl

example : cotAngle (Real.pi / 2) = 0 := by
  simp [cotAngle]

example : connectionQuadratic 2 3 0 0 1 = 0 := by
  norm_num [connectionQuadratic]

example : fourierTwo = Matrix.fromBlocks 0 (-1 : Mat2) 1 0 := rfl

example : positionShear (0 : Mat2) = Matrix.fromBlocks (1 : Mat2) 0 0 1 := rfl

example : connectionMatrix 0 0 0 =
    fourierTwo * positionShear (connectionQuadratic 0 0 0) := rfl

example : (beamSettings 1).eta = 0 := by
  norm_num [beamSettings]

example : connectionWord [] = 1 := rfl

example : connectionAncillas (List.replicate 3 (beamSettings 0)) = 9 := rfl

example : phaseFreeBeamMatrix 0 0 1 = 1 := by
  norm_num [phaseFreeBeamMatrix]

example : beamSplitterGrouped 1 =
    Matrix.fromBlocks (phaseFreeBeamMatrix 1) 0 0 (phaseFreeBeamMatrix 1) := rfl

end QAlgorithms.Papers.Independent.Intake100.P11


