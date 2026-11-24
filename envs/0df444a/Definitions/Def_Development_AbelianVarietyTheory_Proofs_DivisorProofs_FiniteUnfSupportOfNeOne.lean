-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:58.264507+00:00
-- url     : https://prove2.me/theorems/d4dafe48-d015-4018-b161-e9e3f68ba18f
-- title:
--   Finite Unf Support Of Ne One
-- statement:
--   Definitions and structural lemmas for Finite Unf Support Of Ne One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
namespace GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
section Vertex
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def symLev (c : ℕ) : n ⊕ Fin c → ℕ := if Even c then midLev (c / 2) else lev (c / 2 + 1)
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Vertex
section Shift
variable {k : Type} [Field k] {G : Grid k} (hs : 1 ≤ G.s)
abbrev Shifts (G : Grid k) : Type := ∀ j : Fin (G.m - 1),
  Matrix (Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)) (Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1)) k
def IsAuxiliaryHeckeCharacter (d : Shifts G) : Prop :=
  ∀ j, (∀ r s, ¬ Free ((G.m - 2 - j.val) / 2 + 1) (r, s) → d j r s = 0) ∧ ∀ r s, d j r (Sum.inl s) = 0
def shiftVars (d : Shifts G) : Vars G := fun j rs => d j rs.1.1 rs.1.2
end Shift
section Frame
variable {k : Type} [Field k] {a c b : ℕ}
variable [ValuativeRel k]
end Frame
section Step
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {G : Grid k} (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
  [ν.IsAddHaarMeasure]
end Step
section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] {G : Grid k} {hs : 1 ≤ G.s} {ψ : AddChar k Circle} (ν : Measure k)
  [ν.IsAddHaarMeasure]
end Main
end GlobalTheory.FunObj.FiniteSupport


