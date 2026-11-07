-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
-- name    : OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:51:15.889458+00:00
-- url     : https://prove2.me/theorems/6e997f0c-2a2b-4cd6-949e-04b8a264d54f
-- title:
--   Norm Fiber Characters
-- statement:
--   Definitions and structural lemmas for Norm Fiber Characters, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/NormFiberCharacters.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
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
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace ShortDraftHeckeBridge
noncomputable def baseChangeChar {q : ℕ} (χ : DirichletCharacter ℂ q) :
    DirichletCharacter ℂ (q * 3) :=
  χ.changeLevel (Nat.dvd_mul_right q 3) *
    chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q)
end ShortDraftHeckeBridge
namespace ActualEisensteinCubic
open MulChar AddChar
end ActualEisensteinCubic
namespace ShortDraftHeckeBridge
abbrev K := CyclotomicField 3 ℚ
instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
instance : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
end ShortDraftHeckeBridge
end
end OAI


