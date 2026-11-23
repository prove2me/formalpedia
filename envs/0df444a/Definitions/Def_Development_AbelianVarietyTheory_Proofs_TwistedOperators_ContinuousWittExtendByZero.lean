-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:32.81563+00:00
-- url     : https://prove2.me/theorems/69059174-da52-4db0-8a3c-b5781e9cb9fa
-- title:
--   Continuous Witt Extend By Zero
-- statement:
--   Definitions and structural lemmas for Continuous Witt Extend By Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
namespace GlobalTheory.RootEx.Exchange
section General
variable {k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k] [T2Space k]
  [SecondCountableTopology k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]
open Classical in

def ext0 {I : Type} (P : I → Prop) (e : {i // P i} → k) : I → k :=
  fun i => if h : P i then e ⟨i, h⟩ else 0
end General
section Entries
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def mat (x₀ : Matrix n n' k) (y : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k) :
    Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k := basePt c x₀ + Matrix.of fun r s => y (r, s)
def gRow (q : Fin c) (u : n' → k) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k :=
  fun i => if i.1 = Sum.inr q then Sum.elim u 0 i.2 else 0
def gCol (q : Fin c) (β : n → k) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k :=
  fun i => if i.2 = Sum.inr q.castSucc then Sum.elim β 0 i.1 else 0
def sRow (q : Fin c) (u : n' → k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k :=
  fun i => Sum.elim (fun s' => ext0 (Free (q.val + 1)) e (i.1.1, Sum.inr q.castSucc) * u s') 0 i.1.2
def sCol (q : Fin c) (β : n → k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k :=
  fun i => Sum.elim (fun r' => -(β r' * ext0 (Free (q.val + 1)) e (Sum.inr q, i.1.2))) 0 i.1.1
end Entries
section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def big (ψ : AddChar k Circle) (q : Fin c) (χ : (n' → k) → ℂ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ℂ :=
  χ (fun s => x (Sum.inr q) (Sum.inl s)) * Φ x * (ψ (-ch x) : ℂ)
variable [MeasurableSpace k] [BorelSpace k]
end Main
end GlobalTheory.RootEx.Exchange


