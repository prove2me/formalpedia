-- Prove2me | Definitions.Def_CellProbeTree_Matching_LRBlock
-- name    : CellProbeTree_Matching_LRBlock
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:34:42.707428+00:00
-- url     : https://prove2.me/theorems/d8f4c447-ef35-42e2-8170-9781531e721e
-- title:
--   The LR encoding of binary trees, the interleaved LR block, and the forest count $F_u(b)$
-- statement:
--   The **LR encoding** of an ordered binary tree $T$ is the bracket word
--   $$\mathrm{LR}(T) = (\,\mathrm{LR}(T_{\mathrm{left}})\,)\,\mathrm{LR}(T_{\mathrm{right}}), \qquad \mathrm{LR}(\emptyset) = \varepsilon,$$
--   a Dyck word with one pair per node.
--
--   An **LR block** with parameters $u \ge 1$, $a, b \ge 0$ and $B = a + b + 2u$ (29) is given by ordered forests $A_1,\dots,A_u$ and $B_1,\dots,B_u$ of binary trees (atoms may be empty) of total node sizes $a$ and $b$, and a word $\sigma$ with $u$ letters $R$ and $u$ letters $L$ (no prefix condition). Number the occurrences of each letter from left to right (root-to-terminal order). Starting from the terminal empty word $D = \varepsilon$, process $\sigma$ backwards with (30)
--   $$R_i : D \mapsto (A_i)\,D, \qquad L_j : D \mapsto (D)\,B_j ,$$
--   where an atom stands for its LR encoding. The result is the **block word**; the **terminal gap** is the place where the initial $D = \varepsilon$ ends up. The **openings created by the spine steps** are the opening brackets introduced by the steps $R_i$ and $L_j$. Write $\alpha_i = \sum_{v \le i} |A_v|$, $\beta_j = \sum_{v \le j} |B_v|$ ($\alpha_0 = \beta_0 = 0$), $k_L(i)$ for the number of $L$-steps preceding $R_i$ and $k_R(j)$ for the number of $R$-steps preceding $L_j$.
--
--   $F_u(b)$ is the number of ordered $u$-tuples of binary trees with total node size $b$ (67), and $\mathcal F_{\mathrm{block}}$ is the family of all block words with parameters $u, a, b$.
--
--   **Formalization Note.** Trees are Mathlib's `BinaryTree Unit` (`numNodes` = size); forests are `Fin u → BinaryTree Unit`; $\sigma$ is `Fin (2 * u) → Bool` (`true` = $R$) read left to right, and `sigmaWords u` holds those with exactly $u$ letters $R$. `spine` returns the tagged parts of the word before and after the terminal gap; a letter is tagged `some (true, i)` if it is the opening created by $R_i$, `some (false, j)` if created by $L_j$ (1-based $i, j$), `none` otherwise. `blockPre` is the part before the gap. `precCount σ true i` $= k_L(i)$, `precCount σ false j` $= k_R(j)$, `prefixSize A i` $= \alpha_i$. `forestCount u b` $= F_u(b)$, `blockFamily u a b` $= \mathcal F_{\mathrm{block}}$ (the image of all block inputs, a set of words). `spine` returns an empty junk result when an atom list runs out, which never happens for $\sigma$ in `sigmaWords u`.
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), pp. 17–19, §4.1.1–4.1.2, equations (29), (30), (36); p. 41, Appendix A.1, equation (67)

import Mathlib

/-!
# The LR encoding of binary trees and the interleaved LR block

Liang, Liu, *Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality*,
STOC 2027 submission, §4.1.1 (pp. 17–18, equations (29), (30)), §4.1.2 (p. 19, equation (36)) and
Appendix A.1 (p. 41, equation (67)).

* `LR(T) = ( LR(T_left) ) LR(T_right)`, `LR(∅) = ε`.
* A block is given by forests `A_1, …, A_u` and `B_1, …, B_u` of binary trees (atoms may be empty)
  and a word `σ` with `u` letters `R` (`true`) and `u` letters `L` (`false`). Starting from the
  terminal empty word `D = ε`, `σ` is processed backwards with `R_i : D ↦ (A_i)D` and
  `L_j : D ↦ (D)B_j`, where `R_i` is the `i`-th `R` of `σ` and `L_j` the `j`-th `L`, counted in
  root-to-terminal order (left to right in `σ`).
* `spine` records the part of the final word before the terminal gap and the part after it,
  each letter tagged: `some (true, i)` on the opening created by step `R_i`, `some (false, j)`
  on the opening created by step `L_j`, `none` elsewhere.

**Formalization Note.** Forests are tuples `Fin u → BinaryTree Unit` (Mathlib's binary trees,
`numNodes` = node size) and the interleaving word is `σ : Fin (2 * u) → Bool` read left to right.
Atom indices `i, j` in tags are 1-based as in the paper. `spine` consumes the atom lists; when
a list runs out (never the case for the family `sigmaWords u`) it returns a junk empty result.
-/

namespace CellProbeTree.Matching

/-- The LR encoding of a binary tree. -/
def lrEnc : BinaryTree Unit → List DyckStep
  | .nil => []
  | .node _ l r => DyckStep.U :: lrEnc l ++ DyckStep.D :: lrEnc r

/-- Tag of a letter of a block word: `some (true, i)` = opening of spine step `R_i`,
`some (false, j)` = opening of spine step `L_j`, `none` = any other letter. -/
abbrev SpineTag := Option (Bool × ℕ)

/-- An untagged word. -/
def untagged (x : List DyckStep) : List (DyckStep × SpineTag) := x.map fun c => (c, none)

/-- `spine σ As Bs i j = (pre, post)`: the tagged block word is `pre ++ D ++ post` with the
terminal `D = ε` in the gap between them. `i`, `j` count the `R`- and `L`-steps already used. -/
def spine : List Bool → List (BinaryTree Unit) → List (BinaryTree Unit) → ℕ → ℕ →
    List (DyckStep × SpineTag) × List (DyckStep × SpineTag)
  | [], _, _, _, _ => ([], [])
  | true :: σ, A :: As, Bs, i, j =>
      let r := spine σ As Bs (i + 1) j
      ((DyckStep.U, some (true, i + 1)) :: untagged (lrEnc A) ++ (DyckStep.D, none) :: r.1, r.2)
  | false :: σ, As, B :: Bs, i, j =>
      let r := spine σ As Bs i (j + 1)
      ((DyckStep.U, some (false, j + 1)) :: r.1, r.2 ++ (DyckStep.D, none) :: untagged (lrEnc B))
  | true :: _, [], _, _, _ => ([], [])
  | false :: _, _, [], _, _ => ([], [])

/-- The tagged part of the block word before the terminal gap. -/
def blockPre (u : ℕ) (A B : Fin u → BinaryTree Unit) (σ : Fin (2 * u) → Bool) :
    List (DyckStep × SpineTag) :=
  (spine (List.ofFn σ) (List.ofFn A) (List.ofFn B) 0 0).1

/-- The tagged block word. -/
def blockTagged (u : ℕ) (A B : Fin u → BinaryTree Unit) (σ : Fin (2 * u) → Bool) :
    List (DyckStep × SpineTag) :=
  let r := spine (List.ofFn σ) (List.ofFn A) (List.ofFn B) 0 0
  r.1 ++ r.2

/-- The block word over `(`/`)`. -/
def blockWord (u : ℕ) (A B : Fin u → BinaryTree Unit) (σ : Fin (2 * u) → Bool) :
    List DyckStep :=
  (blockTagged u A B σ).map Prod.fst

/-- Total node size of a forest. -/
def forestSize {u : ℕ} (A : Fin u → BinaryTree Unit) : ℕ := ∑ i, (A i).numNodes

/-- `α_i = Σ_{v ≤ i} |A_v|` (1-based `v`), `α_0 = 0`. -/
def prefixSize {u : ℕ} (A : Fin u → BinaryTree Unit) (i : ℕ) : ℕ :=
  ∑ v : Fin u, if v.1 < i then (A v).numNodes else 0

/-- For the `i`-th occurrence (1-based) of the letter `b` in `σ`, the number of letters different
from `b` that precede it. With `b = true` this is `k_L(i)`, with `b = false` it is `k_R(j)`. -/
def precCount : List Bool → Bool → ℕ → ℕ
  | [], _, _ => 0
  | x :: σ, b, i => if x = b then (if i ≤ 1 then 0 else precCount σ b (i - 1))
      else precCount σ b i + 1

/-- Interleaving words with `u` letters `R` (`true`) and `u` letters `L` (`false`). -/
def sigmaWords (u : ℕ) : Finset (Fin (2 * u) → Bool) :=
  Finset.univ.filter fun σ => (Finset.univ.filter fun k => σ k = true).card = u

/-- The ordered `u`-tuples of binary trees of total node size `b`. -/
def forestsOfSize (u b : ℕ) : Finset (Fin u → BinaryTree Unit) :=
  (Finset.Nat.antidiagonalTuple u b).biUnion fun c =>
    Fintype.piFinset fun i => BinaryTree.treesOfNumNodesEq (c i)

/-- `F_u(b)` of (67): the number of ordered `u`-tuples of binary trees of total node size `b`. -/
def forestCount (u b : ℕ) : ℕ := (forestsOfSize u b).card

/-- The inputs of one block with parameters `u, a, b`: two forests of total sizes `a` and `b` and
an interleaving word. -/
def blockInputs (u a b : ℕ) :
    Finset ((Fin u → BinaryTree Unit) × (Fin u → BinaryTree Unit) × (Fin (2 * u) → Bool)) :=
  forestsOfSize u a ×ˢ forestsOfSize u b ×ˢ sigmaWords u

/-- `F_block`: the family of block words with parameters `u, a, b`. -/
def blockFamily (u a b : ℕ) : Finset (List DyckStep) :=
  (blockInputs u a b).image fun x => blockWord u x.1 x.2.1 x.2.2

end CellProbeTree.Matching


