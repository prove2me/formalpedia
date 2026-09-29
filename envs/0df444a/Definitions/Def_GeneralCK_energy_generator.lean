-- Prove2me | Definitions.Def_GeneralCK_energy_generator
-- name    : GeneralCK_energy_generator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T22:20:48.274978+00:00
-- url     : https://prove2.me/theorems/27025976-c11e-49f1-8e00-8d597cb36b51
-- title:
--   The entropy pairing with the cube generator
-- statement:
--   For a real-valued array $v$ on the $n$-dimensional Boolean cube and a point $x$, write $x^{(i)}$ for the point with coordinate $i$ flipped. The generator density is $$D_v(x)=J(v(x))\sum_{i=1}^n(v(x^{(i)})-v(x)).$$ This bundle defines the coordinate flip and the density; the equality between its uniform mean and the recursive energy is proved separately.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EnergyIdentity.lean#L7-L26

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_cube_analysis
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.Energy
open scoped BigOperators
open CubeAnalysis

def flip {n : ℕ} (x : Cube n) (i : Fin n) : Cube n :=
  Function.update x i (!(x i))





noncomputable def generatorDensity {n : ℕ} (v : Cube n → ℝ) (x : Cube n) : ℝ :=
  J (v x) * ∑ i, (v (flip x i) - v x)







end GeneralCK.Energy


