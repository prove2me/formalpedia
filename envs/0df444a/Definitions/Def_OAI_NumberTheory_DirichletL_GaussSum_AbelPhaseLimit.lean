-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
-- name    : OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:27:55.780487+00:00
-- url     : https://prove2.me/theorems/f06e7727-8dcd-4ac2-921e-928cbacee647
-- title:
--   Abel Phase Limit
-- statement:
--   Definitions and structural lemmas for Abel Phase Limit, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/AbelPhaseLimit.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
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
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace OscSpecial
noncomputable def dualQ (z : ℤ × ℤ) : ℝ :=
  (z.1 : ℝ) ^ 2 + (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2
noncomputable def dualTrace (a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  (a - b) * (z.1 : ℝ) ^ 2 + 2 * a * (z.1 : ℝ) * (z.2 : ℝ) +
    b * (z.2 : ℝ) ^ 2
noncomputable def phaseA (a b : ℝ) : ℝ := 3 * q a b / 16
noncomputable def phaseAngle (a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  -(Real.pi / 2) * dualTrace a b z
noncomputable def dualAmp (η a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * (η * q a b / (4 * r η a b)) * dualQ z)
noncomputable def dualVarTerm (η a b : ℝ) (z : ℤ × ℤ) : ℂ :=
  (dualAmp η a b z : ℂ) *
    Complex.exp (Complex.I * ((phaseAngle a b z / r η a b : ℝ) : ℂ))
noncomputable def dualFixedTerm (η a b : ℝ) (z : ℤ × ℤ) : ℂ :=
  (dualAmp η a b z : ℂ) *
    Complex.exp (Complex.I * (phaseAngle a b z : ℂ))
noncomputable def dualRealGauss (t : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * t * dualQ z)
noncomputable def phaseErrorConstant (a b : ℝ) : ℝ :=
  (Real.pi / 2) * phaseBoundConstant a b * phaseA a b
open scoped Topology
open Filter
end OscSpecial
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT
end ActualEisensteinCubic
open Filter
open scoped Topology
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
end
end OAI


