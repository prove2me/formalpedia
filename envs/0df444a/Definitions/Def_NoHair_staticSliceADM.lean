-- Prove2me | Definitions.Def_NoHair_staticSliceADM
-- name    : NoHair_staticSliceADM
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T07:34:47.140668+00:00
-- url     : https://prove2.me/theorems/fe975f74-5887-4899-ab3f-9975b8a37379
-- title:
--   Cartesian ADM flux, lapse flux, and regular static coordinates
-- statement:
--   On large coordinate spheres the ADM integrand is $(\partial_jh_{ij}-\partial_ih_{jj})n^i$ with normalization $1/(16\pi)$, and the lapse flux integrand is $\partial_iN\,n^i$ with normalization $1/(4\pi)$. Integration uses Euclidean surface measure. The positive conformal metric is $((1+N)/2)^4h$. The coordinate bundle names the existing regular static slice's domain, chart, lapse, and spatial metric so that statements about their fluxes refer to the same end.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, section 2, equations (2.1)–(2.4), and proof of Theorem 1.1 in section 5, equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of Multiple Black Holes in Asymptotically Euclidean Static Vacuum Space-Time, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326. In the proof of Theorem 1.1, pp. 23–24 of the preprint, the rescaled end has zero mass by the ADM–Komar identity. R. Beig, Arnowitt–Deser–Misner energy and g00, Phys. Lett. A 69 (1978) 153–155, https://doi.org/10.1016/0375-9601(78)90198-6.

import Definitions.Def_NoHair_regularStaticVacuumSlice
import Mathlib.MeasureTheory.Constructions.HaarToSphere

noncomputable section

open Metric Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace NoHair

abbrev ADMPoint := EuclideanSpace ℝ (Fin 3)
abbrev ADMSphere := sphere (0 : ADMPoint) 1
abbrev admSurfaceMeasure : Measure ADMSphere := (volume : Measure ADMPoint).toSphere

/-- The Cartesian coordinate derivative in a spatial end. -/
def spatialADMPartial (i : Fin 3) (f : ADMPoint → ℝ) (x : ADMPoint) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The ADM density on the unit sphere parameterizing a coordinate sphere of radius r. -/
def staticADMDensity (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) (n : ADMSphere) : ℝ :=
  let x := r • (n : ADMPoint)
  ∑ i : Fin 3, ∑ j : Fin 3,
    (r^2 * spatialADMPartial j (fun y => h y i j) x -
     r^2 * spatialADMPartial i (fun y => h y j j) x) * (n : ADMPoint) i

/-- The radial derivative of the lapse with the coordinate sphere area factor. -/
def staticLapseDensity (N : ADMPoint → ℝ) (r : ℝ) (n : ADMSphere) : ℝ :=
  ∑ i : Fin 3, r^2 * spatialADMPartial i N (r • (n : ADMPoint)) * (n : ADMPoint) i

def staticADMFlux (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) : ℝ :=
  (∫ n : ADMSphere, staticADMDensity h r n ∂admSurfaceMeasure) / (16 * Real.pi)

def staticLapseFlux (N : ADMPoint → ℝ) (r : ℝ) : ℝ :=
  (∫ n : ADMSphere, staticLapseDensity N r n ∂admSurfaceMeasure) / (4 * Real.pi)

def staticPositiveMetric (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (x : ADMPoint) (i j : Fin 3) : ℝ := ((1 + N x) / 2)^4 * h x i j

/-- Cartesian falloff of the metric and lapse, through their first derivatives. -/
def HasStaticFirstOrderFalloff (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ x : ADMPoint, R < ‖x‖ →
    ContDiffAt ℝ 1 N x ∧ (∀ i j, ContDiffAt ℝ 1 (fun y => h y i j) x) ∧
    |N x - 1| ≤ C / ‖x‖ ∧
    (∀ i j, |h x i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C / ‖x‖) ∧
    (∀ i, |‖x‖^2 * spatialADMPartial i N x| ≤ C) ∧
    (∀ i j k, |‖x‖^2 * spatialADMPartial k (fun y => h y i j) x| ≤ C)

/-- The coordinate witnesses of HasRegularStaticVacuumSlice, retained for flux calculations. -/
structure RegularStaticSliceCoordinates {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M) where
  openExterior : IsOpen D
  Ω : Set ADMPoint
  W : Set ADMPoint
  N : ADMPoint → ℝ
  h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ
  ψ : E4 → M
  openSlice : IsOpen Ω
  connectedSlice : IsConnected Ω
  compactComplement : IsCompact Ωᶜ
  hasBoundary : (frontier Ω).Nonempty
  connectedBoundary : IsConnected (frontier Ω)
  openExtension : IsOpen W
  extendsAcross : closure Ω ⊆ W
  positiveSide : ∀ x ∈ W, x ∈ Ω ↔ 0 < N x
  horizon : ∀ x ∈ frontier Ω, N x = 0 ∧ fderiv ℝ N x ≠ 0
  smoothLapse : ContDiffOn ℝ ∞ N W
  smoothMetric : ∀ i j, ContDiffOn ℝ ∞ (fun x => h x i j) W
  positiveMetric : ∀ x ∈ W, (h x).PosDef
  falloff : ∀ k : ℕ, ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ x : ADMPoint, R < ‖x‖ →
    ‖iteratedFDeriv ℝ k (fun y => N y - 1) x‖ ≤ C / ‖x‖^(k+1) ∧
    ∀ i j, ‖iteratedFDeriv ℝ k (fun y => h y i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) x‖
      ≤ C / ‖x‖^(k+1)
  exteriorChart : IsDiffeoOnto ψ (conformalSpatialPoint ⁻¹' Ω) D
  timeTranslation : ∀ t : ℝ, ∀ z ∈ conformalSpatialPoint ⁻¹' Ω, ψ (z + t • coordBasis 0) = φ t (ψ z)
  staticMetric : ∀ z ∈ conformalSpatialPoint ⁻¹' Ω, ∀ v w : E4,
    g (ψ z) (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) ψ z v) (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) ψ z w) =
    -(N (conformalSpatialPoint z)) ^ 2 * v 0 * w 0 +
      ∑ i : Fin 3, ∑ j : Fin 3, h (conformalSpatialPoint z) i j * v i.succ * w j.succ
  vacuum : ∀ z ∈ conformalSpatialPoint ⁻¹' Ω, ∀ i j, ricci (pullbackCoeffs g ψ) z i j = 0

end NoHair


