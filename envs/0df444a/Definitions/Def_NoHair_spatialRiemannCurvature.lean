-- Prove2me | Definitions.Def_NoHair_spatialRiemannCurvature
-- name    : NoHair_spatialRiemannCurvature
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T11:46:00.450366+00:00
-- url     : https://prove2.me/theorems/a81a373c-f0b1-4d50-8965-cff4df9fdf26
-- title:
--   Spatial coordinate curvature and vanishing Riemann tensor in an atlas
-- statement:
--   The spatial Riemann curvature operator is formed from the published spatial Levi-Civita connection. Its contraction over the output and first differential index is the published spatial Ricci tensor. Flatness means that each component vanishes in all supplied smooth coordinate charts.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation

noncomputable section
open Set Filter Bundle
open scoped ContDiff Manifold
namespace NoHair

/-- Curvature of the spatial Levi-Civita connection, with the first output index raised. -/
def spatialRiemannCurvature (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (x : ADMPoint) (a b i j : Fin 3) : ℝ :=
  spatialADMPartial i (fun y => spatialLeviCivita h y a j b) x -
    spatialADMPartial j (fun y => spatialLeviCivita h y a i b) x +
    ∑ l : Fin 3, (spatialLeviCivita h x a i l * spatialLeviCivita h x l j b -
      spatialLeviCivita h x a j l * spatialLeviCivita h x l i b)

/-- All coordinate components of the Riemann tensor vanish throughout the given atlas. -/
def FlatInADMCharts (Q : Type*) [MetricSpace Q] [ChartedSpace ADMPoint Q]
    [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q] [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)] : Prop :=
  ∀ e ∈ atlas ADMPoint Q, ∀ x ∈ e.target, ∀ a b i j : Fin 3,
    spatialRiemannCurvature (riemannianEndCoeffs e.symm) x a b i j = 0

end NoHair


