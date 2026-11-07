-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
-- name    : OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:44:46.971843+00:00
-- url     : https://prove2.me/theorems/62333168-8c67-481d-96a4-07160fca7e57
-- title:
--   Local Nonvanishing
-- statement:
--   Definitions and structural lemmas for Local Nonvanishing, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
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
namespace TargetLocalReduction
def LocalExponentialMobiusBound : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
      ∃ σ : ℝ, 0 < σ ∧ σ < ρ.re ∧ σ < 1 ∧
        (fun D : ℝ => ShortDraftMellin.mobiusExpSum χ D⁻¹) =O[atTop]
          (fun D : ℝ => D ^ σ)
end TargetLocalReduction
namespace ActualEisensteinCubic
open AddChar MulChar
end ActualEisensteinCubic
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
namespace ShortDraftHeckeBridge
abbrev O := ActualEisensteinSieve.O
noncomputable def normFiberCoeff (weight : Ideal O → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset, weight I
noncomputable def pairInverseCoeff
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ℕ → ℂ :=
  (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) ⍟
    (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ))
end ShortDraftHeckeBridge
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
open scoped ComplexConjugate
end ActualEisensteinCubic
open MulChar AddChar
namespace ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end ShortDraftLocal
end
end OAI


