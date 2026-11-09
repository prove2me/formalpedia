-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_Bubbles
-- name    : DeletionHash_MixedEdit_Bubbles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:16.360735+00:00
-- url     : https://prove2.me/theorems/34d37458-c155-4992-9e26-a79a6c2b1b8b
-- title:
--   Oriented local bubbles with complete path geometry
-- statement:
--   For $m=L-1$, a bubble is an oriented pair of local words $P=AUB$ and $P'=AVB$ satisfying $U\ne V$, $|U|,|V|\le b$, and $m-k-b\le |A|,|B|\le m$. Each local word has length between $L$ and $2m+b$, their first and last $m$ letters agree, and their actual de Bruijn paths are simple and meet only at those endpoints. The order of the pair specifies the negative and positive paths. Their vertex set is the union of the two path-vertex sets. These are precisely the geometry conditions of equation (4) and Definition 2.5; existence of bubbles for actual interior edits remains a theorem.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), §2.3, equation (4), printed p. 7 (PDF p. 9); Definition 2.5, printed p. 8 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Paths

namespace DeletionHash.MixedEdit

universe u

/-- Equation (4) and the complete geometric conditions of Definition 2.5. -/
def Bubble {α : Type u} [DecidableEq α] (k L b : ℕ) (P P' : List α) : Prop :=
  let m := L-1
  (∃ A U V B : List α, P = A ++ U ++ B ∧ P' = A ++ V ++ B ∧ U ≠ V ∧
    U.length ≤ b ∧ V.length ≤ b ∧ m-k-b ≤ A.length ∧ A.length ≤ m ∧
    m-k-b ≤ B.length ∧ B.length ≤ m) ∧
  L ≤ P.length ∧ P.length ≤ 2*m+b ∧ L ≤ P'.length ∧ P'.length ≤ 2*m+b ∧
  P.take m = P'.take m ∧ P.drop (P.length-m) = P'.drop (P'.length-m) ∧
  SpellsSimplePath L P ∧ SpellsSimplePath L P' ∧
  (∀ v, v ∈ PathVertices L P → v ∈ PathVertices L P' →
    List.ofFn v = P.take m ∨ List.ofFn v = P.drop (P.length-m))

def bubbleVertices {α : Type u} (L : ℕ) (P P' : List α) : Set (Gram α (L-1)) :=
  PathVertices L P ∪ PathVertices L P'

end DeletionHash.MixedEdit


