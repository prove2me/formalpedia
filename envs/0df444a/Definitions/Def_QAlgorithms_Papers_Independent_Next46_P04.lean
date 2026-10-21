-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P04
-- name    : QAlgorithms_Papers_Independent_Next46_P04
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T12:36:39.015996+00:00
-- url     : https://prove2.me/theorems/ed537d46-8b9f-4fc5-8e05-474c319e9548
-- title:
--   Definitions for Ramp-up of Hawking radiation in Bose-Einstein condensate analogue black holes
-- statement:
--   The objects the formalized statements of *Ramp-up of Hawking radiation in Bose-Einstein condensate analogue black holes* (arXiv:2005.04443) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `AcousticModel`: PDF pp. 1--2: constant negative flow, initial subsonic speed, and positive physical constants. The transverse densityObservable reduction is n1 = n * lperp^2.
--   - `a`: PDF p. 2: magnitude of the left-directed flow.
--   - `n1`: PDF p. 2, (3): reduced one-dimensional condensate densityObservable.
--   - `z`: PDF p. 2, (4): dimensionless spatial coordinate.
--   - `soundSpeed`: PDF p. 2, (4): the post-quench speed, used only in the post-quench regime.
--   - `initialU`: PDF p. 2, (9): initial outgoing coordinate.
--   - `initialW`: PDF p. 2, (9): initial incoming coordinate.
--   - `u`: PDF p. 2, (10): outgoing coordinate, with physical domain x != 0.
--   - `v`: PDF p. 2, (10): incoming coordinate. The artanh is INSIDE cosh.
--   - `acousticForm`: PDF p. 2, (6): conformal acoustic metric applied to a tangent vector.
--   - `A`: PDF p. 2, (11): negative retarded matching scale.
--   - `B`: PDF p. 3, (13): positive advanced matching scale.
--   - `side`: PDF pp. 2--3: real half-line sign. Only x != 0 is used.
--   - `retardedIn`: PDF p. 2, (12): signed inverse, s = +1 outside and s = -1 inside.
--   - `advancedPrinted`: PDF p. 3, (13), literally printed; it differs from the inverse of (10) by an additive constant, which cancels in differentiated correlators.
--   - `advancedOffset`: PDF pp. 2--3, correction to (13): printed minus shell-normalized inverse.
--   - `advancedIn`: PDF pp. 2--3: inverse of the actual advanced shell map, retaining (10)'s integration constant. Printed (13) omits subtraction of `advancedOffset`.
--   - `retardedShell`: PDF p. 2: outgoing shell map constructed by eliminating shell position.
--   - `advancedShell`: PDF pp. 2--3: incoming shell map constructed by eliminating shell position.
--   - `mappedU`: PDF p. 2: matched initial outgoing coordinate on each half-line.
--   - `mappedW`: PDF pp. 2--3: matched initial incoming coordinate.
--   - `FieldKernel`: PDF pp. 2,4: two-point real kernel, with independent primed coordinates.
--   - `flowFirst`: PDF p. 2, (5): convective derivative in the first point.
--   - `flowSecond`: PDF p. 2, (5): convective derivative in the second point.
--   - `densityObservable`: PDF p. 2, (5): densityObservable correlator obtained by differentiating a field kernel BEFORE equating times; the dimensional reduction factor is outside D.
--   - `vacuumSector`: PDF p. 2, (8): real off-null representative for one vacuum sector.
--   - `vacuumDensity`: PDF pp. 2--3, (5),(8): post-quench vacuum densityObservable observable.
--   - `initialDensity`: PDF p. 3, sentence after (14): pre-quench vacuum densityObservable observable.
--   - `correlatorScale`: PDF pp. 3--5: common positive normalization.
--   - `uFactor`: PDF p. 3, (14): outgoing matching-derivative and speed factors.
--   - `vFactor`: PDF p. 3, (14): incoming matching-derivative and speed factors.
--   - `advancedDistance`: PDF p. 3, (16): stationary incoming-coordinate separation.
--   - `lateU`: PDF p. 3, outgoing part of (15), for x > 0 and xp < 0.
--   - `lateVacuumV`: PDF p. 3, corrected incoming part of (15): product of the two (c+a) factors, rather than the square root printed in (15); follows from (14).
--   - `hawkingTemperature`: PDF p. 4: Hawking temperature.
--   - `Au`: PDF p. 4, (19): outgoing thermal scale, used only for T > 0.
--   - `Av`: PDF p. 4, (19): incoming thermal scale, used only for T > 0.
--   - `occupation`: PDF p. 4, (17)--(18): initial comoving occupation at lab frequency omega; s = +1 is outgoing, s = -1 incoming. Physical use requires omega,T > 0.
--   - `thermalSector`: PDF p. 4, (19): real off-null thermal sector; initial equilibrium is encoded by this kernel, not quantified over arbitrary states.
--   - `thermalUDensity`: PDF p. 4, (5),(19): thermal outgoing densityObservable contribution, defined by D.
--   - `thermalVDensity`: PDF p. 4, (5),(19): thermal incoming densityObservable contribution, defined by D.
--   - `thermalDensityObservable`: PDF p. 4, (5),(19): complete thermal densityObservable observable, defined by D.
--   - `rho0`: PDF p. 4: scalar vacuum late-time control parameter, not a peak length.
--   - `rhoT`: PDF p. 5: scalar thermal late-time control parameter.
--   - `incomingThermalScale`: PDF p. 5, from (13),(20): surviving incoming thermal scale.
--   - `lateThermalV`: PDF p. 5: signed stationary incoming thermal contribution.
-- source:
--   Ramp-up of Hawking radiation in Bose-Einstein condensate analogue black holes, arXiv:2005.04443v3, https://arxiv.org/abs/2005.04443v3

import Mathlib

/-!
Fabbri--Balbinot, arXiv:2005.04443v3, PDF pp. 1--5.
All statements concern the exact reduced, dispersionless conformal model (5)--(7),
with no backscattering and an instantaneous shell. They do not assert an error
bound relative to the microscopic condensate. The two time regimes are separate;
no physical value at the quench is assigned. Shell evaluations use the smooth
coordinate formulas extended to t = 0 for matching only.

The real off-null kernels below represent (8) and (19) only for the differentiated
observable. No Wightman distribution or imaginary-branch prescription is asserted.
Two source corrections require independent moderation: (13) needs the additive
constant specified in `advancedOffset` to invert (10) with its printed constant;
the advanced denominator in (15) must be a product rather than a square root.
-/

namespace QAlgorithms.Papers.Independent.Next46.P04

noncomputable section

open Filter

/-- PDF pp. 1--2: constant negative flow, initial subsonic speed, and positive
physical constants. The transverse densityObservable reduction is n1 = n * lperp^2. -/
structure AcousticModel where
  V : ℝ
  cin : ℝ
  kappa : ℝ
  n : ℝ
  lperp : ℝ
  m : ℝ
  hbar : ℝ
  kB : ℝ
  V_neg : V < 0
  cin_gt : |V| < cin
  kappa_pos : 0 < kappa
  n_pos : 0 < n
  lperp_pos : 0 < lperp
  m_pos : 0 < m
  hbar_pos : 0 < hbar
  kB_pos : 0 < kB

/-- PDF p. 2: magnitude of the left-directed flow. -/
def a (p : AcousticModel) : ℝ := |p.V|

/-- PDF p. 2, (3): reduced one-dimensional condensate densityObservable. -/
def n1 (p : AcousticModel) : ℝ := p.n * p.lperp ^ 2

/-- PDF p. 2, (4): dimensionless spatial coordinate. -/
def z (p : AcousticModel) (x : ℝ) : ℝ := 3 * p.kappa * x / (2 * a p)

/-- PDF p. 2, (4): the post-quench speed, used only in the post-quench regime. -/
def soundSpeed (p : AcousticModel) (x : ℝ) : ℝ :=
  a p * (1 + (2 / 3 : ℝ) * Real.tanh (z p x))

/-- PDF p. 2, (9): initial outgoing coordinate. -/
def initialU (p : AcousticModel) (t x : ℝ) : ℝ := t - x / (p.cin - a p)

/-- PDF p. 2, (9): initial incoming coordinate. -/
def initialW (p : AcousticModel) (t x : ℝ) : ℝ := t + x / (p.cin + a p)

/-- PDF p. 2, (10): outgoing coordinate, with physical domain x != 0. -/
def u (p : AcousticModel) (t x : ℝ) : ℝ :=
  t - Real.log (Real.sinh (z p |x|)) / p.kappa

/-- PDF p. 2, (10): incoming coordinate. The artanh is INSIDE cosh. -/
def v (p : AcousticModel) (t x : ℝ) : ℝ :=
  t + (9 * p.kappa * x / (2 * a p) -
    Real.log (Real.cosh (z p x + Real.artanh (1 / 3 : ℝ)))) / (8 * p.kappa)

/-- PDF p. 2, (6): conformal acoustic metric applied to a tangent vector. -/
def acousticForm (p : AcousticModel) (x dt dx : ℝ) : ℝ :=
  -((soundSpeed p x) ^ 2 - (a p) ^ 2) * dt ^ 2 + 2 * a p * dt * dx + dx ^ 2

/-- PDF p. 2, (11): negative retarded matching scale. -/
def A (p : AcousticModel) : ℝ := 3 * p.kappa * (a p - p.cin) / (2 * a p)

/-- PDF p. 3, (13): positive advanced matching scale. -/
def B (p : AcousticModel) : ℝ := 3 * p.kappa * (p.cin + a p) / (2 * a p)

/-- PDF pp. 2--3: real half-line sign. Only x != 0 is used. -/
def side (x : ℝ) : ℝ := if 0 < x then 1 else -1

/-- PDF p. 2, (12): signed inverse, s = +1 outside and s = -1 inside. -/
def retardedIn (p : AcousticModel) (s r : ℝ) : ℝ :=
  (s / A p) * Real.log (Real.sqrt (1 + Real.exp (-2 * p.kappa * r)) +
    Real.exp (-p.kappa * r))

/-- PDF p. 3, (13), literally printed; it differs from the inverse of (10)
by an additive constant, which cancels in differentiated correlators. -/
def advancedPrinted (p : AcousticModel) (r : ℝ) : ℝ :=
  4 * p.kappa * r / B p + Real.log (1 +
    Real.sqrt (1 + 2 * Real.sqrt 2 * Real.exp (-8 * p.kappa * r))) / (2 * B p)

/-- PDF pp. 2--3, correction to (13): printed minus shell-normalized inverse. -/
def advancedOffset (p : AcousticModel) : ℝ := Real.log (2 * Real.sqrt 2) / (2 * B p)

/-- PDF pp. 2--3: inverse of the actual advanced shell map, retaining (10)'s
integration constant. Printed (13) omits subtraction of `advancedOffset`. -/
def advancedIn (p : AcousticModel) (r : ℝ) : ℝ := advancedPrinted p r - advancedOffset p

/-- PDF p. 2: outgoing shell map constructed by eliminating shell position. -/
def retardedShell (p : AcousticModel) (r : ℝ) : ℝ := u p 0 (-(p.cin - a p) * r)

/-- PDF pp. 2--3: incoming shell map constructed by eliminating shell position. -/
def advancedShell (p : AcousticModel) (r : ℝ) : ℝ := v p 0 ((p.cin + a p) * r)

/-- PDF p. 2: matched initial outgoing coordinate on each half-line. -/
def mappedU (p : AcousticModel) (t x : ℝ) : ℝ := retardedIn p (side x) (u p t x)

/-- PDF pp. 2--3: matched initial incoming coordinate. -/
def mappedW (p : AcousticModel) (t x : ℝ) : ℝ := advancedIn p (v p t x)

/-- PDF pp. 2,4: two-point real kernel, with independent primed coordinates. -/
abbrev FieldKernel := ℝ → ℝ → ℝ → ℝ → ℝ

/-- PDF p. 2, (5): convective derivative in the first point. -/
def flowFirst (p : AcousticModel) (K : FieldKernel) (t x tp xp : ℝ) : ℝ :=
  deriv (fun s => K s x tp xp) t + p.V * deriv (fun y => K t y tp xp) x

/-- PDF p. 2, (5): convective derivative in the second point. -/
def flowSecond (p : AcousticModel) (K : FieldKernel) (t x tp xp : ℝ) : ℝ :=
  deriv (fun s => K t x s xp) tp + p.V * deriv (fun y => K t x tp y) xp

/-- PDF p. 2, (5): densityObservable correlator obtained by differentiating a field kernel
BEFORE equating times; the dimensional reduction factor is outside D. -/
def densityObservable (p : AcousticModel) (c : ℝ → ℝ) (K : FieldKernel) (t x xp : ℝ) : ℝ :=
  (n1 p) ^ 2 / (p.m ^ 2 * (c x) ^ 2 * (c xp) ^ 2) *
    Real.sqrt (p.m ^ 2 * c x * c xp / (n1 p) ^ 2) *
    flowFirst p (flowSecond p K) t x t xp

/-- PDF p. 2, (8): real off-null representative for one vacuum sector. -/
def vacuumSector (p : AcousticModel) (q : ℝ → ℝ → ℝ) : FieldKernel :=
  fun t x tp xp => -p.hbar / (4 * Real.pi) * Real.log |q t x - q tp xp|

/-- PDF pp. 2--3, (5),(8): post-quench vacuum densityObservable observable. -/
def vacuumDensity (p : AcousticModel) (t x xp : ℝ) : ℝ :=
  densityObservable p (soundSpeed p) (fun t x tp xp =>
    vacuumSector p (mappedU p) t x tp xp +
    vacuumSector p (mappedW p) t x tp xp) t x xp

/-- PDF p. 3, sentence after (14): pre-quench vacuum densityObservable observable. -/
def initialDensity (p : AcousticModel) (t x xp : ℝ) : ℝ :=
  densityObservable p (fun _ => p.cin) (fun t x tp xp =>
    vacuumSector p (initialU p) t x tp xp +
    vacuumSector p (initialW p) t x tp xp) t x xp

/-- PDF pp. 3--5: common positive normalization. -/
def correlatorScale (p : AcousticModel) : ℝ := p.hbar * n1 p / (4 * Real.pi * p.m)

/-- PDF p. 3, (14): outgoing matching-derivative and speed factors. -/
def uFactor (p : AcousticModel) (t x xp : ℝ) : ℝ :=
  deriv (retardedIn p (side x)) (u p t x) *
    deriv (retardedIn p (side xp)) (u p t xp) /
    ((soundSpeed p x - a p) * (soundSpeed p xp - a p))

/-- PDF p. 3, (14): incoming matching-derivative and speed factors. -/
def vFactor (p : AcousticModel) (t x xp : ℝ) : ℝ :=
  deriv (advancedIn p) (v p t x) * deriv (advancedIn p) (v p t xp) /
    ((soundSpeed p x + a p) * (soundSpeed p xp + a p))

/-- PDF p. 3, (16): stationary incoming-coordinate separation. -/
def advancedDistance (p : AcousticModel) (x xp : ℝ) : ℝ :=
  9 * (x - xp) / (16 * a p) - Real.log
    ((2 * Real.exp (z p x) + Real.exp (-z p x)) /
      (2 * Real.exp (z p xp) + Real.exp (-z p xp))) / (8 * p.kappa)

/-- PDF p. 3, outgoing part of (15), for x > 0 and xp < 0. -/
def lateU (p : AcousticModel) (x xp : ℝ) : ℝ :=
  correlatorScale p * p.kappa ^ 2 /
    (4 * Real.sqrt (soundSpeed p x * soundSpeed p xp) *
      (soundSpeed p x - a p) * (soundSpeed p xp - a p) *
      (Real.cosh (Real.log (Real.sinh (z p x) / Real.sinh (z p |xp|)) / 2)) ^ 2)

/-- PDF p. 3, corrected incoming part of (15): product of the two (c+a)
factors, rather than the square root printed in (15); follows from (14). -/
def lateVacuumV (p : AcousticModel) (x xp : ℝ) : ℝ :=
  -correlatorScale p / (Real.sqrt (soundSpeed p x * soundSpeed p xp) *
    (soundSpeed p x + a p) * (soundSpeed p xp + a p) *
    (advancedDistance p x xp) ^ 2)

/-- PDF p. 4: Hawking temperature. -/
def hawkingTemperature (p : AcousticModel) : ℝ := p.hbar * p.kappa / (2 * Real.pi * p.kB)

/-- PDF p. 4, (19): outgoing thermal scale, used only for T > 0. -/
def Au (p : AcousticModel) (T : ℝ) : ℝ :=
  Real.pi * p.kB * T * (p.cin - a p) / (p.hbar * p.cin)

/-- PDF p. 4, (19): incoming thermal scale, used only for T > 0. -/
def Av (p : AcousticModel) (T : ℝ) : ℝ :=
  Real.pi * p.kB * T * (p.cin + a p) / (p.hbar * p.cin)

/-- PDF p. 4, (17)--(18): initial comoving occupation at lab frequency omega;
s = +1 is outgoing, s = -1 incoming. Physical use requires omega,T > 0. -/
def occupation (p : AcousticModel) (T s omega : ℝ) : ℝ :=
  1 / (Real.exp (p.hbar * (omega * p.cin / (p.cin - s * a p)) / (p.kB * T)) - 1)

/-- PDF p. 4, (19): real off-null thermal sector; initial equilibrium is
encoded by this kernel, not quantified over arbitrary states. -/
def thermalSector (p : AcousticModel) (scale : ℝ) (q : ℝ → ℝ → ℝ) : FieldKernel :=
  fun t x tp xp => -p.hbar / (4 * Real.pi) *
    Real.log |Real.sinh (scale * (q t x - q tp xp)) / scale|

/-- PDF p. 4, (5),(19): thermal outgoing densityObservable contribution, defined by D. -/
def thermalUDensity (p : AcousticModel) (T t x xp : ℝ) : ℝ :=
  densityObservable p (soundSpeed p) (thermalSector p (Au p T) (mappedU p)) t x xp

/-- PDF p. 4, (5),(19): thermal incoming densityObservable contribution, defined by D. -/
def thermalVDensity (p : AcousticModel) (T t x xp : ℝ) : ℝ :=
  densityObservable p (soundSpeed p) (thermalSector p (Av p T) (mappedW p)) t x xp

/-- PDF p. 4, (5),(19): complete thermal densityObservable observable, defined by D. -/
def thermalDensityObservable (p : AcousticModel) (T t x xp : ℝ) : ℝ :=
  densityObservable p (soundSpeed p) (fun t x tp xp =>
    thermalSector p (Au p T) (mappedU p) t x tp xp +
    thermalSector p (Av p T) (mappedW p) t x tp xp) t x xp

/-- PDF p. 4: scalar vacuum late-time control parameter, not a peak length. -/
def rho0 (p : AcousticModel) (t x : ℝ) : ℝ :=
  Real.exp (-p.kappa * t) * Real.sinh (z p |x|)

/-- PDF p. 5: scalar thermal late-time control parameter. -/
def rhoT (p : AcousticModel) (T t x : ℝ) : ℝ :=
  Real.pi * p.kB * T * (p.cin - a p) / (|A p| * p.hbar * p.cin) * rho0 p t x

/-- PDF p. 5, from (13),(20): surviving incoming thermal scale. -/
def incomingThermalScale (p : AcousticModel) (T : ℝ) : ℝ := (4 * p.kappa / B p) * Av p T

/-- PDF p. 5: signed stationary incoming thermal contribution. -/
def lateThermalV (p : AcousticModel) (T x xp : ℝ) : ℝ :=
  -correlatorScale p * (incomingThermalScale p T) ^ 2 /
    (Real.sqrt (soundSpeed p x * soundSpeed p xp) *
      (soundSpeed p x + a p) * (soundSpeed p xp + a p) *
      (Real.sinh (incomingThermalScale p T * advancedDistance p x xp)) ^ 2)

/-- Sanity: the two initial coordinate origins agree on the shell. -/
example (p : AcousticModel) : initialU p 0 0 = 0 ∧ initialW p 0 0 = 0 := by
  simp [initialU, initialW]

/-- Sanity: the profile fixes the horizon sound speed. -/
example (p : AcousticModel) : soundSpeed p 0 = a p := by
  simp [soundSpeed, z]

/-- Sanity: a constant kernel has zero first convective derivative. -/
example (p : AcousticModel) (r t x tp xp : ℝ) :
    flowFirst p (fun _ _ _ _ => r) t x tp xp = 0 := by
  simp [flowFirst]

/-- Sanity: signed outgoing branches have opposite signs algebraically. -/
example (p : AcousticModel) (r : ℝ) : retardedIn p (-1) r = -retardedIn p 1 r := by
  simp [retardedIn, div_eq_mul_inv]

end

end QAlgorithms.Papers.Independent.Next46.P04


