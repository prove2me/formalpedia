-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:18:22.134904+00:00
-- url     : https://prove2.me/theorems/07a74f4d-a107-4e39-bc3f-ecca830335ea
-- title:
--   Flat Maps Preserve Schwartz Bruhat And Surjective
-- statement:
--   Definitions and structural lemmas for Flat Maps Preserve Schwartz Bruhat And Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open Filter Topology
noncomputable section
namespace GlobalTheory.LocFlat
section Gen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open Classical in

def freeMat (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => if h : Free p (r, s) then e ⟨(r, s), h⟩ else 0
end Gen
end GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat
open Filter Topology
section Gen2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
end Gen2
end GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat
section Spec
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def restOf (rd : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => if rd r s then 0 else z r s - basePt c (0 : Matrix n n' k) r s
def glue {X : Type} (rd : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool) (E : X → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (q : X × Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => if rd r s then E q.1 r s else q.2 r s + basePt c (0 : Matrix n n' k) r s
def rdCol (p : ℕ) : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool
  | .inl _, .inl _ => true
  | .inl _, .inr i => decide (i.val + 1 = p)
  | .inr _, _ => false
def readCol (p : ℕ) (hp : p - 1 < c + 1) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : Matrix n (n' ⊕ Unit) k :=
  Matrix.of fun r s => Sum.elim (fun s => z (.inl r) (.inl s)) (fun _ => z (.inl r) (.inr ⟨p - 1, hp⟩)) s
def extCol (x : Matrix n (n' ⊕ Unit) k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => match r, s with
    | .inl r, .inl s => x r (.inl s)
    | .inl r, .inr _ => x r (.inr ())
    | .inr _, _ => 0
def ptCol (p : ℕ) (x : Matrix n (n' ⊕ Unit) k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  affPt p x.toCols₁ e + colAt n' c p fun r => x r (Sum.inr ())
end Spec
end GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat
section SpecRow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def rdRow (p : ℕ) : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool
  | .inl _, .inl _ => true
  | .inr l, .inl _ => decide (l.val + 1 = p)
  | _, .inr _ => false
def readRow (p : ℕ) (hp : p - 1 < c) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : Matrix (n ⊕ Unit) n' k :=
  Matrix.of fun r s => Sum.elim (fun r => z (.inl r) (.inl s)) (fun _ => z (.inr ⟨p - 1, hp⟩) (.inl s)) r
def extRow (x : Matrix (n ⊕ Unit) n' k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => match r, s with
    | .inl r, .inl s => x (.inl r) s
    | .inr _, .inl s => x (.inr ()) s
    | _, .inr _ => 0
def ptRow (p : ℕ) (x : Matrix (n ⊕ Unit) n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  affPt p x.toRows₁ e + rowAt n c p (x (Sum.inr ()))
end SpecRow
end GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat
section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
end Main
end GlobalTheory.LocFlat


