-- Prove2me | Definitions.Def_NoHair_staticCartesianRicci
-- name    : NoHair_staticCartesianRicci
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T08:19:32.793655+00:00
-- url     : https://prove2.me/theorems/c4017745-bb38-490b-a23e-13253f5efc70
-- title:
--   Static Cartesian block metric and the principal Ricci terms
-- statement:
--   The full four-dimensional block metric $-N^2dt^2+h$, the embedding at time zero, the spatial coordinate Laplacian of $N$, and the spatial principal Ricci term $\mathrm{Ric}'_\delta(h)-\partial^2N$ specify the comparison between the exact four-dimensional field equation and the ADM surface current.
-- source:
--   P. Miao and L.-F. Tam, Evaluation of the ADM mass and center of mass via the Ricci tensor, Proc. Amer. Math. Soc. 144 (2016), pp. 753–761, Theorem 1.1(a) and the Euclidean integration-by-parts identity in the proof of Theorem 2.1, equations (2.2)–(2.8), https://arxiv.org/abs/1408.3893, https://doi.org/10.1090/proc12726. For the time and spatial Ricci equations, see equations (5.4) and (5.5) of P. T. Chruściel, https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf.

import Definitions.Def_NoHair_linearADMFlux

noncomputable section

namespace NoHair

/-- The static block metric in spacetime coordinates. -/
def staticCartesianBlock (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (z : E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => Fin.cases (Fin.cases (-(N (conformalSpatialPoint z))^2) (fun _ => 0) j)
    (fun a => Fin.cases 0 (fun b => h (conformalSpatialPoint z) a b) j) i

/-- The time-zero event above the spatial point. -/
def staticTimeZero (x : ADMPoint) : E4 := WithLp.toLp 2 (Fin.cons 0 (fun i => x i))

/-- Flat coordinate Laplacian of the lapse. -/
def flatLapseLaplacian (N : ADMPoint → ℝ) (x : ADMPoint) : ℝ :=
  ∑ l : Fin 3, spatialADMPartial l (spatialADMPartial l N) x

/-- The spatial Ricci linearization at the Euclidean metric minus the coordinate Hessian of the lapse. -/
def staticPrincipalRicci (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (i j : Fin 3) (x : ADMPoint) : ℝ :=
  (∑ l : Fin 3, (spatialADMPartial l (spatialADMPartial j (fun z => h z l i)) x +
    spatialADMPartial i (spatialADMPartial l (fun z => h z j l)) x -
    spatialADMPartial l (spatialADMPartial l (fun z => h z j i)) x -
    spatialADMPartial i (spatialADMPartial j (fun z => h z l l)) x)) / 2 -
    spatialADMPartial i (spatialADMPartial j N) x

end NoHair


