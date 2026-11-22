-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ReaderMonad
-- name    : LeanPool_FormalLearningTheory_PureMath_ReaderMonad
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:25.870636+00:00
-- url     : https://prove2.me/theorems/62c02553-d1de-45b8-82c3-5ccb3dfae1c1
-- title:
--   Reader Monad
-- statement:
--   Definitions and structural lemmas for Reader Monad, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ReaderMonad.lean

module
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v w
structure ReaderSel (ι : Type u) (α : Type v) (γ : Type w) where
  /-- Family of functions available to the selector. -/
  family : ι → α → γ
  /-- Data-dependent selector for the family index. -/
  sel : α → ι
def ReaderSel.eval {ι : Type u} {α : Type v} {γ : Type w}
    (r : ReaderSel ι α γ) (a : α) : γ :=
  r.family (r.sel a) a
def ReaderSel.pure {ι : Type u} {α : Type v} {γ : Type w}
    (i₀ : ι) (f : α → γ) : ReaderSel ι α γ where
  family := fun _ => f
  sel := fun _ => i₀
def ReaderSel.bind {ι : Type u} {α : Type v} {γ : Type w}
    (r : ReaderSel ι α γ) (f : γ → ReaderSel ι α γ) :
    ReaderSel ι α γ where
  family := fun i a => (f (r.family (r.sel a) a)).family i a
  sel := fun a => (f (r.family (r.sel a) a)).sel a


