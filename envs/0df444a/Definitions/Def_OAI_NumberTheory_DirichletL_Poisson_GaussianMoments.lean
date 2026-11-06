-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
-- name    : OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:46:50.35561+00:00
-- url     : https://prove2.me/theorems/5be33ddf-aa17-47da-9504-06d0f2b37334
-- title:
--   Gaussian Moments
-- statement:
--   Definitions and structural lemmas for Gaussian Moments, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
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
open Filter Real Asymptotics
namespace GaussianMoment
end GaussianMoment
namespace ActualEisensteinCubic
section
open ShortDraftLatticeCount
end
end ActualEisensteinCubic
open ActualEisensteinCubic
namespace RationalPrimeExtraction
noncomputable def selected (Y : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime
end RationalPrimeExtraction
namespace OscSpecial
noncomputable def middleForm (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  a⁻¹ * (z.1 : ℂ) ^ 2 -
    2 * (Complex.I * b / a) * (z.1 : ℂ) * (z.2 : ℂ) +
    RankTwoComplex.schur a b d * (z.2 : ℂ) ^ 2
noncomputable def originalForm (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2
noncomputable def inverseForm (a b d : ℂ) (R : ℝ) (z : ℤ × ℤ) : ℂ :=
  (d * (z.1 : ℂ) ^ 2 - 2 * b * (z.1 : ℂ) * (z.2 : ℂ) +
    a * (z.2 : ℂ) ^ 2) / (R : ℂ)
noncomputable def q (a b : ℝ) : ℝ := a ^ 2 - a * b + b ^ 2
noncomputable def A (η a b : ℝ) : ℂ :=
  (η : ℂ) + 2 * Complex.I * (b : ℂ) / (q a b : ℂ)
noncomputable def B (η a b : ℝ) : ℂ :=
  -(η : ℂ) / 2 - 2 * Complex.I * (a : ℂ) / (q a b : ℂ)
noncomputable def D (η a b : ℝ) : ℂ :=
  (η : ℂ) + 2 * Complex.I * ((a-b : ℝ) : ℂ) / (q a b : ℂ)
noncomputable def R (η a b : ℝ) : ℝ := 4 / q a b + 3 * η ^ 2 / 4
end OscSpecial
end
end OAI


