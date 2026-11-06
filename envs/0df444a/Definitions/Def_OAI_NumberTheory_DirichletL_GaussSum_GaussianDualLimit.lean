-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
-- name    : OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:44:35.398876+00:00
-- url     : https://prove2.me/theorems/870eaa7f-dbbc-4ca0-8653-4603b08d26b6
-- title:
--   Gaussian Dual Limit
-- statement:
--   Definitions and structural lemmas for Gaussian Dual Limit, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GaussianDualLimit.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace OscillatoryDeterminant
open Complex
def q (a b : ℂ) : ℂ := a*a-a*b+b*b
noncomputable def A (t a b : ℂ) : ℂ := t + 2*Complex.I*b/q a b
noncomputable def B (t a b : ℂ) : ℂ := -t/2-2*Complex.I*a/q a b
noncomputable def D (t a b : ℂ) : ℂ := t + 2*Complex.I*(a-b)/q a b
end OscillatoryDeterminant
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace EisensteinFiberShift
def Q (x y : ℝ) : ℝ := x*x-x*y+y*y
def q (a b : ℝ) : ℝ := Q a b
noncomputable def shiftX (a b x y : ℝ) : ℝ := ((a-b)*x+b*y)/q a b
noncomputable def shiftY (a b x y : ℝ) : ℝ := (-b*x+a*y)/q a b
end EisensteinFiberShift
namespace ShortDraftLatticeCount
open ActualEisensteinCoordinates
noncomputable def rowNormBall (H : ℕ) : Finset O := by
  classical
  let I : Finset ℤ := Finset.Icc (-((H : ℤ) + 1)) ((H : ℤ) + 1)
  exact (I.product I).image (fun v => eval v.1 v.2)
end ShortDraftLatticeCount
namespace EisensteinGaussianPrefactor
end EisensteinGaussianPrefactor
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace EisensteinGaussianPrefactor
end EisensteinGaussianPrefactor
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace OscillatoryDeterminant
open Complex
noncomputable def r (t a b : ℂ) : ℂ := 1 + 3 * q a b * t^2 / 16
end OscillatoryDeterminant
open Filter Real Asymptotics
namespace RankTwoLimit
section
open scoped Topology
open RankTwoPoisson RankTwoEisShift Filter
noncomputable def dualTerm (T : ℝ) (x y : ℝ) (z : ℤ × ℤ) : ℂ :=
  RankTwoPoisson.eisGauss T (z.1,-z.2) * RankTwoEisShift.dualPhase z.1 z.2 x y
noncomputable def limitTerm (z : ℤ × ℤ) : ℂ :=
  if z = (0,0) then 1 else 0
end
open scoped Topology
open Filter
end RankTwoLimit
end
end OAI


