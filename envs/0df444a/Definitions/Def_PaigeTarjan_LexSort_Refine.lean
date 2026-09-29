-- Prove2me | Definitions.Def_PaigeTarjan_LexSort_Refine
-- name    : PaigeTarjan_LexSort_Refine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:41:13.462197+00:00
-- url     : https://prove2.me/theorems/8d71d2ca-ff34-4303-bd0c-1c250a4d2ef1
-- title:
--   split($B_\alpha$, P) and the Refine step of the distinguishing-prefix algorithm
-- statement:
--   This file defines the refinement algorithm of §2 of Paige and Tarjan, which finds all distinguishing prefixes of a multiset $U = \{x_1,\dots,x_n\} \subseteq \Sigma^*0$ of strings.
--
--   A state of the algorithm is a set $P$ of labeled blocks $B_\alpha$ partitioning $U$, recorded by the set of labels $\alpha$. For a block $B_\alpha \in P$,
--   $$\mathrm{split}(B_\alpha, P) = \bigl(P \setminus \{B_\alpha\}\bigr) \cup \{\, B_{\alpha u} \mid u \in \Sigma \cup \{0\} \text{ such that } \exists x \in B_\alpha \text{ with } x(|\alpha|+1) = u \,\}.$$
--   The algorithm starts from $P = \{B_\lambda\}$ and repeats the step
--
--   **Refine.** Find an unfinished block $B_\alpha \in P$; replace $P$ by $\mathrm{split}(B_\alpha, P)$.
--
--   A **run** with $K$ steps is a sequence of states $P_0, P_1, \dots, P_K$ with $P_0 = \{B_\lambda\}$ in which each $P_{j+1}$ is obtained from $P_j$ by one Refine step. Any unfinished block may be chosen at each step, so runs cover every order of refinement.
--
--   **Formalization Note.** Positions in the paper are 1-based and Lean list indices are 0-based, so the paper's symbol $x(|\alpha|+1)$ is `(x i)[α.length]?` in Lean. Only children realised by some string of $B_\alpha$ are added, and $\alpha$ itself is removed. A run is `Ps : Fin (K + 1) → Finset (List (Fin (k + 1)))` with `Ps 0 = {[]}`.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 975, §2 (definition of split(B_α, P), initial partition P = {B_λ}, step Refine)

import Mathlib
import Definitions.Def_PaigeTarjan_LexSort_Basic

namespace PaigeTarjan.LexSort

open Classical in
/-- The labels of the blocks that replace `B_α` in `split(B_α, P)` (p. 975):
`{α u | u ∈ Σ ∪ {0} such that ∃ x ∈ B_α for which x(|α| + 1) = u}`.
Positions in the paper are 1-based; Lean list indices are 0-based, so the paper's position
`|α| + 1` is the Lean index `α.length`. -/
noncomputable def children {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (α : List (Fin (k + 1))) : Finset (List (Fin (k + 1))) :=
  (Finset.univ.filter (fun u : Fin (k + 1) =>
      ∃ i ∈ blk x α, (x i)[α.length]? = some u)).image (fun u => α ++ [u])

open Classical in
/-- `split(B_α, P)` (p. 975): replace the block labeled `α` in `P` by the blocks labeled
`α u`, `u ∈ Σ ∪ {0}`, that are realized by some string of `B_α`. A state `P` of the algorithm
is the finite set of labels of its blocks. -/
noncomputable def split {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (α : List (Fin (k + 1))) (P : Finset (List (Fin (k + 1)))) :
    Finset (List (Fin (k + 1))) :=
  P.erase α ∪ children x α

/-- One Refine step (p. 975): find an unfinished block `B_α ∈ P` and replace `P` by
`split(B_α, P)`. -/
def RefineStep {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (P P' : Finset (List (Fin (k + 1)))) : Prop :=
  ∃ α ∈ P, ¬ IsFinished x α ∧ P' = split x α P

/-- A run of the refinement algorithm with `K` Refine steps: states `P₀, …, P_K` with
`P₀ = {B_λ}` (the single label `λ = []`) and `P_{j+1}` obtained from `P_j` by one Refine step. -/
def IsRun {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (K : ℕ)
    (Ps : Fin (K + 1) → Finset (List (Fin (k + 1)))) : Prop :=
  Ps 0 = {[]} ∧ ∀ j : Fin K, RefineStep x (Ps j.castSucc) (Ps j.succ)

end PaigeTarjan.LexSort


