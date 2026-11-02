-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P58
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P58
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:54:37.116311+00:00
-- url     : https://prove2.me/theorems/25feeae1-a953-47c0-994f-815124414393
-- title:
--   Definitions for Topological Entanglement Entropy and Holography
-- statement:
--   The objects the formalized statements of *Topological Entanglement Entropy and Holography* (arXiv:0805.1891) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RotationalModel`: The three reduced actions: (3.13), (3.17), and (4.8), PDF pp.9,10,15.
--   - `radialDegree`: Radius power from the round angular factor; PDF pp.7,15.
--   - `warp`: Coefficient multiplying the squared inverse-profile derivative; PDF pp.9,11,15.
--   - `warpDerivative`: Derivative of the warp coefficient, used in the direct-profile equation.
--   - `profileDensity`: Actual inverse-profile action density, with the source's z parametrization.
--   - `InverseEquation`: Euler--Lagrange equation of the reduced inverse-profile action. This is (3.20) for D3 and the undivided variational form of (4.9) for D4.
--   - `DirectEquation`: Direct-profile Euler--Lagrange equation, (3.7), (3.18), or (4.12). It also applies to annular graphs, whose inverse is not a single-valued function.
--   - `height`: Invert the actual strictly decreasing radius graph on its physical interval. On that graph's range the defining set is a nonempty bounded singleton. Values outside the range are unused. This definition does not introduce a free inverse.
--   - `RegularGraph`: Common regularity, anchoring, stationarity, and finite regulated area conditions. The ODE is imposed only at positive z strictly before the endpoint. A smooth extension through z=0 fixes total derivatives there without prescribing UV coefficients. The disk endpoint may have a singular inverse derivative.
--   - `IsDisk`: Regular disk cap, with the direct profile constructed by inversion. The physical compactified disks have b<1; the singular joining limit is excluded. The zero axis slope is a one-sided derivative, not the derivative of a default extension. Source: PDF pp.7--10,16.
--   - `IsCylinder`: Regular compactified cylinder, with positive endpoint radius and smooth inverse profile at z=1. This does not assume the endpoint expansion. Source: PDF pp.10--11,16.
--   - `IsProfile`: The two regular source topologies, without claiming exactly two solutions.
--   - `regulatedAction`: Unnormalized regulated action integral. Only positive cutoffs below b are used.
--   - `uv`: UV subtraction in the inverse-profile integral; (3.15), (3.23), (4.17). For D3 the dimensionless compactification radius is 1/2.
--   - `conformalEntropy`: Conformal reduced entropy, no end-cap term; (3.13), PDF p.9.
--   - `d3Entropy`: Compactified D3 reduced entropy in the (3.17)/(3.23) normalization. The extra pi in (3.19) is not used.
--   - `D4Parameters`: Independent positive D4 scales with alpha-prime=1; PDF pp.14,20.
--   - `d4U0`: D4 tip scale U0=4*pi*lambda/(9*R4^2), (4.2).
--   - `d4Newton`: Ten-dimensional Newton constant from (4.26); used only for N>=1.
--   - `d4Prefactor`: The explicitly reduced (4.8) prefactor, with R^6=(pi*lambda)^2. No incorrect round-sphere volume is assumed to derive this expression.
--   - `d4Entropy`: D4 entropy for the source's reduced action (4.8).
--   - `conformalF`: Corrected conformal variable x=1-r/R in (3.9). The printed x=1-R/r on PDF p.7 has the wrong sign in the physical interior.
--   - `FirstD4Coefficient`: The first D4 large-radius coefficient equation (4.19), with regular endpoint and boundary data only. Its vanishing is a theorem conclusion, not a hypothesis.
--   - `SecondD4Coefficient`: The next regular coefficient problem (4.20), after the leading coefficient vanishes.
--   - `d4G`: The explicit regular coefficient (4.23), PDF p.20.
--   - `d4GPrime`: Simplified derivative (4.22), including its regular value at z=1.
--   - `d4ConstantDensity`: Radius-independent integrand of (4.24), before its disputed printed evaluation.
--   - `ShrinkingOscillations`: Usual qualitative diminishing-envelope oscillation: a finite limit, with values strictly on both sides in every punctured neighborhood. No rate, exact decimal, or monotonicity of successive numerical extrema is added.
--   - `IsAnnulus`: Nontrivial stationary annular surface, PDF pp.11,22--25 (and conformal pp.8--9). There is no global-minimality field.
-- source:
--   Topological Entanglement Entropy and Holography, arXiv:0805.1891v2, https://arxiv.org/abs/0805.1891v2

import Mathlib

/-!
Reduced rotational profile problems in Pakman--Parnachev, arXiv:0805.1891v2.
The actions below are the paper's explicitly chosen reduced actions, not a derivation
of their disputed absolute geometric normalization. All lengths in the compactified
models are dimensionless. Logarithms are natural. No claim identifies arbitrary
stationary profiles with global entropy minimizers.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P58

open Set Filter MeasureTheory
open scoped Topology

/-- The three reduced actions: (3.13), (3.17), and (4.8), PDF pp.9,10,15. -/
inductive RotationalModel where
  | conformal
  | d3
  | d4
  deriving DecidableEq

/-- Radius power from the round angular factor; PDF pp.7,15. -/
def radialDegree : RotationalModel → ℕ
  | .conformal => 1
  | .d3 => 1
  | .d4 => 2

/-- Coefficient multiplying the squared inverse-profile derivative; PDF pp.9,11,15. -/
def warp : RotationalModel → ℝ → ℝ
  | .conformal, _ => 1
  | .d3, z => 1 - z ^ 4
  | .d4, z => z * (1 - z ^ 3)

/-- Derivative of the warp coefficient, used in the direct-profile equation. -/
def warpDerivative : RotationalModel → ℝ → ℝ
  | .conformal, _ => 0
  | .d3, z => -4 * z ^ 3
  | .d4, z => 1 - 4 * z ^ 3

example : warp .d3 1 = 0 ∧ warp .d4 1 = 0 := by
  norm_num [warp]

example : radialDegree .d4 = 2 := by
  rfl

example : warpDerivative .d4 1 = -3 := by
  norm_num [warpDerivative]

/-- Actual inverse-profile action density, with the source's z parametrization. -/
def profileDensity (m : RotationalModel) (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  r z ^ radialDegree m / z ^ 3 * Real.sqrt (1 + warp m z * deriv r z ^ 2)

example (c z : ℝ) : profileDensity .d3 (fun _ => c) z = c / z ^ 3 := by
  simp [profileDensity, radialDegree]

/-- Euler--Lagrange equation of the reduced inverse-profile action.
This is (3.20) for D3 and the undivided variational form of (4.9) for D4. -/
def InverseEquation (m : RotationalModel) (r : ℝ → ℝ) (z : ℝ) : Prop :=
  deriv (fun u => r u ^ radialDegree m * warp m u * deriv r u /
    (u ^ 3 * Real.sqrt (1 + warp m u * deriv r u ^ 2))) z =
  (radialDegree m : ℝ) * r z ^ (radialDegree m - 1) /
    z ^ 3 * Real.sqrt (1 + warp m z * deriv r z ^ 2)

/-- Direct-profile Euler--Lagrange equation, (3.7), (3.18), or (4.12).
It also applies to annular graphs, whose inverse is not a single-valued function. -/
def DirectEquation (m : RotationalModel) (Z : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv (fun u => u ^ radialDegree m * deriv Z u /
    (Z u ^ 3 * Real.sqrt (warp m (Z u) + deriv Z u ^ 2))) t =
  t ^ radialDegree m *
    (warpDerivative m (Z t) /
      (2 * Z t ^ 3 * Real.sqrt (warp m (Z t) + deriv Z t ^ 2)) -
      3 * Real.sqrt (warp m (Z t) + deriv Z t ^ 2) / Z t ^ 4)

/-- Invert the actual strictly decreasing radius graph on its physical interval.
On that graph's range the defining set is a nonempty bounded singleton. Values
outside the range are unused. This definition does not introduce a free inverse. -/
def height (r : ℝ → ℝ) (b t : ℝ) : ℝ :=
  sInf {z : ℝ | z ∈ Icc 0 b ∧ r z = t}

/-- Common regularity, anchoring, stationarity, and finite regulated area conditions.
The ODE is imposed only at positive z strictly before the endpoint. A smooth
extension through z=0 fixes total derivatives there without prescribing UV coefficients.
The disk endpoint may have a singular inverse derivative. -/
def RegularGraph (m : RotationalModel) (R b : ℝ) (r : ℝ → ℝ) : Prop :=
  0 < R ∧ 0 < b ∧ r 0 = R ∧ ContinuousOn r (Icc 0 b) ∧
  StrictAntiOn r (Icc 0 b) ∧
  (∀ z ∈ Ico 0 b, ContDiffAt ℝ 2 r z) ∧
  (∀ z ∈ Ioo 0 b, 0 < r z ∧ InverseEquation m r z) ∧
  (∀ a : ℝ, 0 < a → a < b → IntervalIntegrable (profileDensity m r) volume a b)

/-- Regular disk cap, with the direct profile constructed by inversion.
The physical compactified disks have b<1; the singular joining limit is excluded.
The zero axis slope is a one-sided derivative, not the derivative of a default extension.
Source: PDF pp.7--10,16. -/
def IsDisk (m : RotationalModel) (R b : ℝ) (r : ℝ → ℝ) : Prop :=
  RegularGraph m R b r ∧ r b = 0 ∧ (m = .conformal ∨ b < 1) ∧
  ContDiffOn ℝ 2 (height r b) (Ico 0 R) ∧
  HasDerivWithinAt (height r b) 0 (Ici 0) 0

/-- Regular compactified cylinder, with positive endpoint radius and smooth inverse
profile at z=1. This does not assume the endpoint expansion. Source: PDF pp.10--11,16. -/
def IsCylinder (m : RotationalModel) (R : ℝ) (r : ℝ → ℝ) : Prop :=
  (m = .d3 ∨ m = .d4) ∧ RegularGraph m R 1 r ∧
  0 < r 1 ∧ ContDiffAt ℝ 2 r 1

example : ¬ IsCylinder .conformal 1 (fun _ => 1) := by
  simp [IsCylinder]

/-- The two regular source topologies, without claiming exactly two solutions. -/
def IsProfile (m : RotationalModel) (R b : ℝ) (r : ℝ → ℝ) : Prop :=
  IsDisk m R b r ∨ (b = 1 ∧ IsCylinder m R r)

/-- Unnormalized regulated action integral. Only positive cutoffs below b are used. -/
def regulatedAction (m : RotationalModel) (r : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ z in a..b, profileDensity m r z

/-- UV subtraction in the inverse-profile integral; (3.15), (3.23), (4.17).
For D3 the dimensionless compactification radius is 1/2. -/
def uv (m : RotationalModel) (R a : ℝ) : ℝ :=
  match m with
  | .conformal => R / (2 * a ^ 2) + Real.log (a / R) / (8 * R)
  | .d3 => R / (2 * a ^ 2) + Real.log (a / R) / (8 * R)
  | .d4 => R ^ 2 / (2 * a ^ 2) - 3 / (2 * a) + Real.log a / (8 * R ^ 2)

example : uv .d4 1 1 = -1 := by
  norm_num [uv]

/-- Conformal reduced entropy, no end-cap term; (3.13), PDF p.9. -/
def conformalEntropy (N : ℕ) (l : ℝ) (r : ℝ → ℝ) (a b : ℝ) : ℝ :=
  4 * (N : ℝ) ^ 2 * l / (15 * Real.pi) * regulatedAction .conformal r a b

/-- Compactified D3 reduced entropy in the (3.17)/(3.23) normalization.
The extra pi in (3.19) is not used. -/
def d3Entropy (N : ℕ) (r : ℝ → ℝ) (a b : ℝ) : ℝ :=
  4 * (N : ℝ) ^ 2 / 15 * regulatedAction .d3 r a b

/-- Independent positive D4 scales with alpha-prime=1; PDF pp.14,20. -/
structure D4Parameters where
  coupling : ℝ
  circleRadius : ℝ
  coupling_pos : 0 < coupling
  circleRadius_pos : 0 < circleRadius

/-- D4 tip scale U0=4*pi*lambda/(9*R4^2), (4.2). -/
def d4U0 (P : D4Parameters) : ℝ :=
  4 * Real.pi * P.coupling / (9 * P.circleRadius ^ 2)

/-- Ten-dimensional Newton constant from (4.26); used only for N>=1. -/
def d4Newton (P : D4Parameters) (N : ℕ) : ℝ :=
  8 * Real.pi ^ 6 * P.coupling ^ 2 / (N : ℝ) ^ 2

/-- The explicitly reduced (4.8) prefactor, with R^6=(pi*lambda)^2.
No incorrect round-sphere volume is assumed to derive this expression. -/
def d4Prefactor (P : D4Parameters) (N : ℕ) : ℝ :=
  Real.pi ^ 3 * (Real.pi * P.coupling) ^ 2 * d4U0 P * P.circleRadius /
    (2 * d4Newton P N)

/-- D4 entropy for the source's reduced action (4.8). -/
def d4Entropy (P : D4Parameters) (N : ℕ) (r : ℝ → ℝ) (a b : ℝ) : ℝ :=
  d4Prefactor P N * regulatedAction .d4 r a b

example (P : D4Parameters) : d4Newton P 0 = 0 := by
  simp [d4Newton]

/-- Corrected conformal variable x=1-r/R in (3.9).
The printed x=1-R/r on PDF p.7 has the wrong sign in the physical interior. -/
def conformalF (R b : ℝ) (r : ℝ → ℝ) (x : ℝ) : ℝ :=
  height r b (R * (1 - x)) / (2 * R * Real.sqrt x)

/-- The first D4 large-radius coefficient equation (4.19), with regular endpoint
and boundary data only. Its vanishing is a theorem conclusion, not a hypothesis. -/
def FirstD4Coefficient (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧ (∀ z ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f z) ∧
  ∀ z ∈ Ioo (0 : ℝ) 1,
    4 * deriv f z + 2 * z ^ 3 * deriv f z + 5 * z * deriv f z ^ 3 -
      7 * z ^ 4 * deriv f z ^ 3 + 2 * z ^ 7 * deriv f z ^ 3 -
      2 * z * deriv (deriv f) z + 2 * z ^ 4 * deriv (deriv f) z = 0

/-- The next regular coefficient problem (4.20), after the leading coefficient vanishes. -/
def SecondD4Coefficient (g : ℝ → ℝ) : Prop :=
  g 0 = 0 ∧ (∀ z ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 g z) ∧
  ∀ z ∈ Ioo (0 : ℝ) 1,
    4 + 4 * deriv g z + 2 * z ^ 3 * deriv g z -
      2 * z * deriv (deriv g) z + 2 * z ^ 4 * deriv (deriv g) z = 0

/-- The explicit regular coefficient (4.23), PDF p.20. -/
def d4G (z : ℝ) : ℝ :=
  -Real.arctan ((1 + 2 * z) / Real.sqrt 3) / Real.sqrt 3 -
    Real.log (1 + z + z ^ 2) / 2 + Real.pi / (6 * Real.sqrt 3)

/-- Simplified derivative (4.22), including its regular value at z=1. -/
def d4GPrime (z : ℝ) : ℝ :=
  -(1 + z) / (1 + z + z ^ 2)

example : d4GPrime 1 = -(2 : ℝ) / 3 := by
  norm_num [d4GPrime]

/-- Radius-independent integrand of (4.24), before its disputed printed evaluation. -/
def d4ConstantDensity (z : ℝ) : ℝ :=
  (4 * d4G z + z * (1 - z ^ 3) * d4GPrime z ^ 2) / (2 * z ^ 3)

/-- Usual qualitative diminishing-envelope oscillation: a finite limit, with
values strictly on both sides in every punctured neighborhood. No rate, exact
decimal, or monotonicity of successive numerical extrema is added. -/
def ShrinkingOscillations (f : ℝ → ℝ) (side : Set ℝ) (endpoint limit : ℝ) : Prop :=
  Tendsto f (nhdsWithin endpoint side) (nhds limit) ∧
  ∀ delta : ℝ, 0 < delta →
    (∃ x ∈ side, 0 < |x - endpoint| ∧ |x - endpoint| < delta ∧ f x < limit) ∧
    (∃ x ∈ side, 0 < |x - endpoint| ∧ |x - endpoint| < delta ∧ limit < f x)

/-- Nontrivial stationary annular surface, PDF pp.11,22--25 (and conformal pp.8--9).
There is no global-minimality field. -/
def IsAnnulus (m : RotationalModel) (Ri Re : ℝ) (Z : ℝ → ℝ) : Prop :=
  0 < Ri ∧ Ri < Re ∧ ContinuousOn Z (Icc Ri Re) ∧ Z Ri = 0 ∧ Z Re = 0 ∧
  ∀ t ∈ Ioo Ri Re, ContDiffAt ℝ 2 Z t ∧ 0 < Z t ∧
    (m = .conformal ∨ Z t < 1) ∧ DirectEquation m Z t

end QAlgorithms.Papers.Independent.Intakethird100.P58


