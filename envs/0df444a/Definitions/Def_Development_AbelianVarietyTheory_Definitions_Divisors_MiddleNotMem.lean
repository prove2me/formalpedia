-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MiddleNotMem
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_MiddleNotMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:52.099769+00:00
-- url     : https://prove2.me/theorems/ae871b45-d0d5-4b06-b26c-dafe5b9a5d67
-- title:
--   Middle Not Mem
-- statement:
--   Definitions and structural lemmas for Middle Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MiddleNotMem.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
namespace GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
section Alg
variable {k : Type*} [Field k] {n n' n'' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  [Fintype n''] [DecidableEq n'']
def twoPhase (x : Matrix (n ⊕ Fin 2) (n' ⊕ Fin 3) k) (x' : Matrix (n'' ⊕ Fin 1) (n ⊕ Fin 2) k) : k :=
  ch x + ch x' + ∑ r, x' (.inr 0) (.inl r) * x (.inl r) (.inr 1)
end Alg
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {G : Grid k} (hs : 1 ≤ G.s) [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
end GlobalTheory.FunObj.UnfModel


