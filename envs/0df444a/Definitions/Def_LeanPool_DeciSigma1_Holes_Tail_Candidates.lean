-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
-- name    : LeanPool_DeciSigma1_Holes_Tail_Candidates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:54:47.982854+00:00
-- url     : https://prove2.me/theorems/1ab6d858-0ce6-4fe3-8171-fadae2205ece
-- title:
--   Candidates
-- statement:
--   Definitions and structural lemmas for Candidates, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
structure RayCandidate [DecidableEq α] (M : StructuralReader α S k) (W : Fin k → List α)
    (ts : List (List α)) (v : Fin k) where
  /-- Maximum suffix length in the ray's dictionary. -/
  windowLength : ℕ
  /-- Cut where the ray segment starts. -/
  startCut : ℕ
  /-- Cut where the ray segment ends. -/
  endCut : ℕ
  closed : NodeClosedAt M.toTable (M.start v) (suffixDictionary ts windowLength) (W v) startCut
    endCut
  windowLength_lt : windowLength < endCut - startCut
namespace RayCandidate
variable [DecidableEq α] {M : StructuralReader α S k} {W : Fin k → List α} {ts : List (List α)}
  {v : Fin k}
def ray (x : RayCandidate M W ts v) :
    Ray α := repeatFactorRay (W v) x.startCut x.endCut x.closed.1 x.closed.2.1
end RayCandidate
section Selection
variable [DecidableEq α] [Fintype α] [Fintype S] [DecidableEq S]
end Selection
end DeciSigma1.Holes.Tail


