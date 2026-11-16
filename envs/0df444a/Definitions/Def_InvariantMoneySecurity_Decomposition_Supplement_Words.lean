-- Prove2me | Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_Words
-- name    : InvariantMoneySecurity_Decomposition_Supplement_Words
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:29:11.787564+00:00
-- url     : https://prove2.me/theorems/9aae2b29-fd70-4df2-b678-72a0e880e9fb
-- title:
--   Definition 2.3 — words, paths and decoded path-finder outputs
-- statement:
--   Let $(X,S,I)$ be an invariant money scheme with moves $s_1,\dots,s_{|S|}$, permutations of the ground set $X\subseteq\{0,1\}^n$. A **word** is a finite sequence of moves $w=s_\ell\cdots s_1$, acting on $X$ by
--   $$w\cdot x=s_\ell(\cdots s_1(x)\cdots),$$
--   so $s_1$ is applied first. The empty word acts as the identity. A word $w$ is a **path from $x$ to $y$** if $w\cdot x=y$. A word is stored as the list $[s_1,\dots,s_\ell]$ of move indices in the order of application.
--
--   For a map $g$ from moves to a group (or monoid) $W$, the **product along the word** is $g_{s_\ell}\cdots g_{s_1}$, with the factor of the first-applied move on the right; this is the convention of Lemma 4.6(ii). In a non-abelian group the reversed product is a different element.
--
--   A path-finder's answer is classical. Its measured output string is decoded as a unary length $\ell$ (that many ones, then a zero) followed by $\ell$ consecutive move indices, each written in the scheme's published binary index encoding at width $\lceil\log_2(|S|+1)\rceil$; bits after the last index are ignored. A string that does not decode, or contains a block that is not the code of a move, is malformed and is never a path.
--
--   **Formalization Note** A move is also extended to arbitrary bit strings, as the identity outside $X$; every use applies it to an element of an orbit, where it is the genuine move.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), pp. 7–8, §2.1 (words) and Definition 2.3

import Definitions.Def_InvariantMoneySecurity_Decomposition_Scheme
set_option autoImplicit false
noncomputable section

namespace InvariantMoneySecurity.Decomposition.Supplement

open InvariantMoneySecurity.Decomposition

/-- Definition 2.3 convention: a word is a list of move indices in application order, so the
list `[s₁, …, s_ℓ]` is the source's word `s_ℓ ⋯ s₁`, with `s₁` applied first. -/
def applyWord {n : ℕ} (D : FiniteScheme n) (w : List (Fin D.moveCount)) (x : D.Object) :
    D.Object :=
  w.foldl (fun y j => D.move j y) x

/-- A move on raw bit strings: the indexed permutation on the ground set, the identity off it.
Every use below applies it to an element of an orbit, where it is the genuine move. -/
def moveBits {n : ℕ} (D : FiniteScheme n) (j : Fin D.moveCount) (y : Bits n) : Bits n :=
  if h : y ∈ D.ground then (D.move j ⟨y, h⟩).val else y

/-- The group product `g_{s_ℓ} ⋯ g_{s₁}` along a word stored in application order. -/
def wordProduct {W : Type} [Monoid W] {m : ℕ} (g : Fin m → W) (w : List (Fin m)) : W :=
  w.foldl (fun h j => g j * h) 1

/-- Decode `k` consecutive binary move indices (each in the published index encoding at width
`D.indexBits n`); a block that is not the code of a move is malformed. -/
def readMoves (D : Scheme) (n : ℕ) : ℕ → List Bool → Option (List (Fin (D.data n).moveCount))
  | 0, _ => some []
  | k + 1, bs => do
      let j ← (Finset.univ : Finset (Fin (D.data n).moveCount)).toList.find?
        (fun j => List.ofFn (D.index n j) == bs.take (D.indexBits n))
      let js ← readMoves D n k (bs.drop (D.indexBits n))
      return j :: js

/-- A path-finder's measured output string decoded as a word: a unary length `ℓ`, then `ℓ`
binary move indices, first-applied move first. Bits after the last index are ignored.
A string that does not decode is malformed and is never a path. -/
def decodeWord (D : Scheme) (n : ℕ) (z : List Bool) : Option (List (Fin (D.data n).moveCount)) := do
  let (ℓ, rest) ← readNat z
  readMoves D n ℓ rest

/-- `z` decodes to a path from `x` to `y` (Definition 2.3). -/
def OutputsPath (D : Scheme) (n : ℕ) (x : (D.data n).Object) (y : Bits n) (z : List Bool) : Prop :=
  ∃ w, decodeWord D n z = some w ∧ (applyWord (D.data n) w x).val = y

end InvariantMoneySecurity.Decomposition.Supplement


