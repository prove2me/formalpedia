-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
-- name    : OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:44:04.893989+00:00
-- url     : https://prove2.me/theorems/65959895-30ac-4669-9b4e-80e2416268ea
-- title:
--   Binary Gaussian
-- statement:
--   Definitions and structural lemmas for Binary Gaussian, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
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
namespace RankTwoComplex
open Real
noncomputable def schur (a b d : ℂ) : ℂ := d - b ^ 2 / a
noncomputable def binaryGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2))
noncomputable def firstGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * (z.1 : ℂ) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * schur a b d * (z.2 : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * (Complex.I * b / a * (z.1 : ℂ)) * (z.2 : ℂ))
noncomputable def dualGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * (z.1 : ℂ) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) / (schur a b d) *
      ((z.2 : ℂ) - b / a * (z.1 : ℂ)) ^ 2)
end RankTwoComplex
namespace GaussianShiftedPartition
open ActualEisensteinCubic ConcreteTraceCRT ConcreteBreveE
noncomputable def representative (c : O) (r : O ⧸ Ideal.span {c}) : O :=
  Classical.choose (Ideal.Quotient.mk_surjective r)
end GaussianShiftedPartition
namespace RankTwoAffine
open RankTwoComplex
noncomputable def binaryGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2) +
    2 * (Real.pi : ℂ) * (u * (z.1 : ℂ) + v * (z.2 : ℂ)))
noncomputable def firstGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * ((z.1 : ℂ) + Complex.I * u) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * schur a b d * (z.2 : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) *
        (v + Complex.I * b / a * ((z.1 : ℂ) + Complex.I * u)) * (z.2 : ℂ))
noncomputable def dualGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * ((z.1 : ℂ) + Complex.I * u) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) / (schur a b d) *
      ((z.2 : ℂ) + Complex.I *
        (v + Complex.I * b / a * ((z.1 : ℂ) + Complex.I * u))) ^ 2)
end RankTwoAffine
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace RankTwoEisShift
noncomputable def Q (x y : ℝ) : ℝ := x ^ 2 - x * y + y ^ 2
noncomputable def shifted (t x y : ℝ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (((-Real.pi * t * Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) : ℝ) : ℂ))
noncomputable def A (t : ℝ) : ℂ := (t : ℂ)
noncomputable def B (t : ℝ) : ℂ := ((-t / 2 : ℝ) : ℂ)
noncomputable def D (t : ℝ) : ℂ := (t : ℂ)
noncomputable def U (t x y : ℝ) : ℂ := ((-t * (x - y / 2) : ℝ) : ℂ)
noncomputable def V (t x y : ℝ) : ℂ := ((-t * (y - x / 2) : ℝ) : ℂ)
noncomputable def C (t x y : ℝ) : ℂ :=
  Complex.exp (((-Real.pi * t * Q x y : ℝ) : ℂ))
noncomputable def dualPhase (k l : ℤ) (x y : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * ((k : ℝ) * x + (l : ℝ) * y) : ℝ) : ℂ)) * Complex.I)
noncomputable def middlePhase (k n : ℤ) (x y : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * (k : ℝ) * (x - ((n : ℝ) + y) / 2) : ℝ) : ℂ)) * Complex.I)
end RankTwoEisShift
end
end OAI


