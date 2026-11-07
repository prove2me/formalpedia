-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
-- name    : OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:48:04.845294+00:00
-- url     : https://prove2.me/theorems/0c00c60b-da8c-4bcc-ac51-044234b4193b
-- title:
--   Norm Fiber Mellin
-- statement:
--   Definitions and structural lemmas for Norm Fiber Mellin, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/NormFiberMellin.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
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
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
namespace ShortDraftLocal
end ShortDraftLocal
open MulChar AddChar
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace ShortDraftHeckeBridge
noncomputable def chiMinusThree : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)
noncomputable def baseChangeWeight {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) * χ (Ideal.absNorm I)
noncomputable def invCharAF {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  (toArithmeticFunction (χ ·)).pmul (ArithmeticFunction.moebius : ArithmeticFunction ℂ)
noncomputable def pairAF {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  invCharAF χ * invCharAF ψ
end ShortDraftHeckeBridge
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace ShortDraftHeckeBridge
noncomputable def normFiberExpSum (weight : Ideal O → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)
noncomputable def normFiberMellin (weight : Ideal O → ℂ) (s : ℂ) : ℂ :=
  mellin (fun D : ℝ => normFiberExpSum weight D⁻¹) (-s) / Complex.Gamma s
end ShortDraftHeckeBridge
end
end OAI


