-- Prove2me | Definitions.Def_NoHair_staticConformalCompletion
-- name    : NoHair_staticConformalCompletion
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T10:06:55.626018+00:00
-- url     : https://prove2.me/theorems/2d0d78d3-1526-4669-b001-95aee06c0e26
-- title:
--   Complete Riemannian data of the static conformal double
-- statement:
--   A complete scalar-flat Riemannian three-manifold with one zero-mass end, a distinguished filled point, a physical chart identifying the positive conformal metric, and a signed lapse solving the Riemannian weighted divergence equation.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

noncomputable section

open Set Filter Bundle
open scoped Bundle Topology Manifold ContDiff

namespace NoHair

/-- Weighted lapse divergence in local coordinates for a Riemannian metric. -/
def staticWeightedLapseDivergence (g : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (f : ADMPoint → ℝ) (x : ADMPoint) : ℝ :=
  ∑ i : Fin 3, spatialADMPartial i (fun y => Real.sqrt (g y).det * (2 / (1 + f y))^2 *
    (∑ j : Fin 3, (g y)⁻¹ i j * spatialADMPartial j f y)) x

/-- A complete Riemannian conformal double with its filled point, physical region,
and signed lapse. The geometry and the lapse equation are expressed intrinsically
or in arbitrary smooth charts, before applying positive-mass rigidity. -/
structure StaticConformalCompletion (Ω : Set ADMPoint) (N : ADMPoint → ℝ)
    (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) where
  carrier : Type
  [metric : MetricSpace carrier]
  [charts : ChartedSpace ADMPoint carrier]
  [manifold : IsManifold 𝓘(ℝ,ADMPoint) ∞ carrier]
  [bundle : RiemannianBundle (fun q : carrier => TangentSpace 𝓘(ℝ,ADMPoint) q)]
  [smoothMetric : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint
    (fun q : carrier => TangentSpace 𝓘(ℝ,ADMPoint) q)]
  [riemannian : IsRiemannianManifold 𝓘(ℝ,ADMPoint) carrier]
  [complete : CompleteSpace carrier]
  [connected : ConnectedSpace carrier]
  [countable : SecondCountableTopology carrier]
  zeroMassEnd : HasScalarFlatZeroADMEnd carrier
  pole : carrier
  lapse : carrier → ℝ
  smoothLapse : ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ℝ) 2 lapse ({pole}ᶜ)
  lower : ∀ q, q ≠ pole → -1 < lapse q
  asymptote : ∀ ε : ℝ, 0 < ε → ∃ K : Set carrier, IsCompact K ∧
    ∀ q, q ∉ K → |lapse q - 1| ≤ ε
  horizon : ∃ q : carrier, q ≠ pole ∧ lapse q = 0
  physical : OpenPartialHomeomorph carrier ADMPoint
  source : physical.source = {q | q ≠ pole ∧ 0 < lapse q}
  target : physical.target = Ω
  smoothPhysical : ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ physical physical.source
  smoothInverse : ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ physical.symm physical.target
  physicalMetric : ∀ q ∈ physical.source, N (physical q) = lapse q ∧
    ∀ v w : TangentSpace 𝓘(ℝ,ADMPoint) q, (∑ i : Fin 3, ∑ j : Fin 3,
      staticPositiveMetric N h (physical q) i j *
        (fun z : ADMPoint => z i) (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) physical q v) *
        (fun z : ADMPoint => z j) (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) physical q w)) = inner ℝ v w
  lapseEquation : ∀ e : OpenPartialHomeomorph ADMPoint carrier,
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e e.source →
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e.symm e.target →
    ∀ x ∈ e.source, e x ≠ pole → lapse (e x) ≠ 0 →
      staticWeightedLapseDivergence (riemannianEndCoeffs e) (lapse ∘ e) x = 0

attribute [instance] StaticConformalCompletion.metric StaticConformalCompletion.charts
  StaticConformalCompletion.manifold StaticConformalCompletion.bundle
  StaticConformalCompletion.smoothMetric StaticConformalCompletion.riemannian
  StaticConformalCompletion.complete StaticConformalCompletion.connected StaticConformalCompletion.countable

end NoHair


