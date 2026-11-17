-- Prove2me | Definitions.Def_N25_UnitAnalytic
-- name    : N25_UnitAnalytic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:24.804827+00:00
-- url     : https://prove2.me/theorems/833e1568-8730-4813-8544-e6e1e3ea8cd3
-- title:
--   Analytic level-$25$ modular units
-- statement:
--   Defines the matrix subgroup attached to the level-$25$ congruence condition, a normalized residue factor evaluated at the dilation $25τ$, and five unpowered analytic Siegel ratios on the upper half-plane. These analytic functions are the modular units whose expansions and divisors generate the plane model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_SiegelFunction
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
namespace N25

abbrev GammaH25GL : Subgroup (GL (Fin 2) ℝ) :=
  (CohCarrier.GammaH 25 N25.H25 : Subgroup (GL (Fin 2) ℝ))

/-- The normalized residue factor evaluated at the level-25 dilation. -/
def etaAnalytic25 (g : ℕ) (τ : UpperHalfPlane) : ℂ :=
  -ModularCurve.siegelFun 25 (g : ℤ) 0 (25 * (τ : ℂ))

/-- The five unpowered analytic Siegel ratios. -/
def unitAnalytic25 (i : Fin 5) (τ : UpperHalfPlane) : ℂ :=
  (etaAnalytic25 (unitResidues25 i).1 τ *
      etaAnalytic25 (unitResidues25 i).2 τ) /
    (etaAnalytic25 (unitResidues25 (i + 1)).1 τ *
      etaAnalytic25 (unitResidues25 (i + 1)).2 τ)

end N25


