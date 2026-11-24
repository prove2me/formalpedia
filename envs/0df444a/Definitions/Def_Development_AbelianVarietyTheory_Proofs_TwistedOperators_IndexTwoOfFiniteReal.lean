-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:19:58.719751+00:00
-- url     : https://prove2.me/theorems/5c03fdff-be58-40d7-a3f2-064b04d7670d
-- title:
--   Index Two Of Finite Real
-- statement:
--   Definitions and structural lemmas for Index Two Of Finite Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IndexTwoOfFiniteReal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
namespace GlobalTheory.QuadSymbol
namespace NormBaseChange
open NormIndex
def IndexTwo (B : Type) [Field B] : Prop :=
  ∀ d : B, ¬ IsSquare d → (∃ c : B, c ≠ 0 ∧ ¬ Nm d c) ∧
    ∀ x y : B, x ≠ 0 → y ≠ 0 → ¬ Nm d x → ¬ Nm d y → Nm d (x * y)
def NormsEscape (A B : Type) [Field A] [Field B] [Algebra A B] : Prop :=
  ∀ d : A, ¬ IsSquare (algebraMap A B d) → ∃ x : B, x ≠ 0 ∧ ¬ Nm d (Algebra.norm A x)
section Tower
variable {A B C : Type} [Field A] [Field B] [Field C]
end Tower
section Galois
variable {A : Type} [Field A] [CharZero A]
  (hA : ∀ (B : Type) [Field B] [Algebra A B] [FiniteDimensional A B], IndexTwo B)
include hA
end Galois
section Finite
open GlobalTheory.CNorm
end Finite
end NormBaseChange
end GlobalTheory.QuadSymbol


