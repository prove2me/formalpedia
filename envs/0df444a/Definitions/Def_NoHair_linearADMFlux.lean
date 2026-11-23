-- Prove2me | Definitions.Def_NoHair_linearADMFlux
-- name    : NoHair_linearADMFlux
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T07:49:58.632172+00:00
-- url     : https://prove2.me/theorems/350b64c4-0dc4-413d-9c69-a8778a9fc350
-- title:
--   Linearized Einstein tensor in the ADM surface identity
-- statement:
--   For a spatial tensor $k$ define $A_j=\partial_i k_{ji}-\partial_j k_{ii}$ and $T_{ijl}=\partial_l k_{ji}-\partial_j k_{li}+\delta_{ij}A_l-\delta_{il}A_j$. The last two slots of $T$ are antisymmetric. For symmetric $k$, $\partial_l T_{ijl}$ is $-2$ times the Euclidean linearized Einstein tensor. The lapse-corrected perturbation $k=h+2(N-1)\delta$ is used in the static mass calculation.
-- source:
--   P. Miao and L.-F. Tam, Evaluation of the ADM mass and center of mass via the Ricci tensor, Proc. Amer. Math. Soc. 144 (2016), pp. 753–761, Theorem 1.1(a) and the Euclidean integration-by-parts identity in the proof of Theorem 2.1, equations (2.2)–(2.8), https://arxiv.org/abs/1408.3893, https://doi.org/10.1090/proc12726.

import Definitions.Def_NoHair_staticSliceADM

noncomputable section
namespace NoHair

/-- The coefficient of the outward normal in the Cartesian ADM flux integrand. -/
def admVector (k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) (x : ADMPoint) : ℝ :=
  ∑ i : Fin 3, (spatialADMPartial i (fun z => k z j i) x -
    spatialADMPartial j (fun z => k z i i) x)

/-- The antisymmetric potential for the Euclidean linearization of the Einstein tensor. -/
def admSuperpotential (k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (i j l : Fin 3) (x : ADMPoint) : ℝ :=
  spatialADMPartial l (fun z => k z j i) x - spatialADMPartial j (fun z => k z l i) x +
    (1 : Matrix (Fin 3) (Fin 3) ℝ) i j * admVector k l x -
    (1 : Matrix (Fin 3) (Fin 3) ℝ) i l * admVector k j x

/-- For a symmetric tensor k this is minus twice the flat linearized Einstein tensor. -/
def negativeTwiceLinearEinstein (k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) (x : ADMPoint) : ℝ :=
  ∑ l : Fin 3, spatialADMPartial l (admSuperpotential k i j l) x

/-- Adding the lapse perturbation to the spatial tensor subtracts its normalized flux from the ADM energy. -/
def lapseCorrectedADMMetric (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (x : ADMPoint) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => h x i j + 2 * (N x - 1) * (1 : Matrix (Fin 3) (Fin 3) ℝ) i j

end NoHair


