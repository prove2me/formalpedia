-- Prove2me | Definitions.Def_FlowLatRound_LabeledTree
-- name    : FlowLatRound_LabeledTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:41.421997+00:00
-- url     : https://prove2.me/theorems/037cdc37-257e-4b0a-a0f3-5c97d5c4f612
-- title:
--   §3.4 and App. C.3 — labeled trees and spanning forests on $[n]$, components, degrees, and Prüfer decoding
-- statement:
--   Simple graphs on the vertex set $[n]=\{0,\dots,n-1\}$ are finite sets of unordered pairs.
--
--   1. The component of $i$ is the least vertex set containing $i$ and closed under the edges; $\mathrm{comps}(E)$ is the set of components and $\deg_E(i)$ the number of edges at $i$.
--   2. A **labeled tree** is a loopless edge set with $n-1$ edges connecting $[n]$; a **spanning forest** is a loopless edge set with $\#\text{edges}+\#\text{components}=n$.
--   3. **Prüfer decoding** of a code $(x_1,\dots,x_{n-2})$: start with degrees $1+\#\{k:x_k=i\}$; for each $x_k$ join the least vertex of current degree $1$ to $x_k$ and lower both degrees; finally join the two vertices of degree $1$. It is written as a charged program because the sampler of Lemma C.6 runs it.
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), §3.4, p.8 (PDF 10); Appendix C.3, p.24 (PDF 26); Lemma C.6, p.26 (PDF 28)

import Mathlib
import Definitions.Def_FlowLatRound_CostModel

namespace FlowLatRound

/-! # Labeled trees and forests on `[n]`, and Prüfer decoding

Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027
submission, sha256 35bd3e4b…aeac), §3.4, p.8 (PDF 10: labeled trees on `[n]`, `deg_T`);
Appendix C.3, p.24 (PDF 26: spanning forests, components, Lemma C.4); Lemma C.6, p.26 (PDF 28:
Prüfer decoding).

**Formalization Note.** Vertices are `Fin n` (the paper's `[n]`, shifted to start at `0`). A
simple graph on `[n]` is a finite set of unordered pairs `Sym2 (Fin n)`; a labeled tree is a
loopless edge set with `n − 1` edges that connects `[n]`, and a (spanning) forest is a loopless
edge set with `#edges + #components = n`. The component of `i` is the least vertex set that
contains `i` and is closed under the edges. Prüfer decoding is the standard algorithm (repeatedly
join the least current leaf to the next code entry, then join the last two vertices of degree
`1`), written as a charged program so that the sampler of Lemma C.6 can run it; its output edge
set is `pruferTree`. -/

variable {n : ℕ}

/-- `j` lies in the connected component of `i` in the graph with edge set `E`: every vertex
set that contains `i` and is closed under the edges contains `j`. -/
def InComp (E : Finset (Sym2 (Fin n))) (i j : Fin n) : Prop :=
  ∀ S : Finset (Fin n), i ∈ S → (∀ a b : Fin n, s(a, b) ∈ E → a ∈ S → b ∈ S) → j ∈ S

instance (E : Finset (Sym2 (Fin n))) (i j : Fin n) : Decidable (InComp E i j) := by
  unfold InComp; infer_instance

/-- The vertex set of the connected component of `i` in the graph with edge set `E`. -/
def compOf (E : Finset (Sym2 (Fin n))) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (InComp E i)

/-- The components `V₁, …, V_c` of the graph with edge set `E`. -/
def comps (E : Finset (Sym2 (Fin n))) : Finset (Finset (Fin n)) :=
  Finset.univ.image (compOf E)

/-- The degree of `i` in the (loopless) graph with edge set `E`. -/
def degE (E : Finset (Sym2 (Fin n))) (i : Fin n) : ℕ :=
  (E.filter (fun e => i ∈ e)).card

/-- `E` is a labeled tree on `[n]`: loopless, `n − 1` edges, connected. -/
def IsLTree (E : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ E, ¬ e.IsDiag) ∧ E.card + 1 = n ∧ ∀ i, compOf E i = Finset.univ

instance (E : Finset (Sym2 (Fin n))) : Decidable (IsLTree E) := by
  unfold IsLTree; infer_instance

/-- `E` is a spanning forest of `[n]`: loopless and acyclic, i.e. `#edges + #components = n`. -/
def IsForest (E : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ E, ¬ e.IsDiag) ∧ E.card + (comps E).card = n

instance (E : Finset (Sym2 (Fin n))) : Decidable (IsForest E) := by
  unfold IsForest; infer_instance

/-- Labeled trees on `[n]`. -/
abbrev LTree (n : ℕ) := {E : Finset (Sym2 (Fin n)) // IsLTree E}

/-- Prüfer decoding of a code (a list of `n − 2` vertices) as a charged program returning the
edges as ordered pairs: at each code entry `x`, join the least vertex of current degree `1` to
`x`, where the degree of a vertex starts at `1 +` its number of occurrences in the code; finally
join the two vertices of degree `1`. -/
def pruferEdgesC (n : ℕ) (code : List (Fin n)) : Counted (List (Fin n × Fin n)) := do
  -- initial degrees: `n · (|code| + 1)` index comparisons
  charge (n * (code.length + 1) * opCost n n)
  let deg0 : Fin n → ℕ := fun i => 1 + code.count i
  let st ← code.foldlM
    (fun (st : (Fin n → ℕ) × List (Fin n × Fin n)) x => do
      -- the least leaf: at most `n` comparisons; two updates and one list step
      charge (n * opCost n n + 2 * opCost n 1 + 1)
      match (List.finRange n).find? (fun j => st.1 j = 1) with
      | some j => pure (Function.update (Function.update st.1 j 0) x (st.1 x - 1), (j, x) :: st.2)
      | none => pure st)
    (deg0, [])
  -- the last two leaves: `n` comparisons
  charge (n * opCost n n + 1)
  match (List.finRange n).filter (fun j => st.1 j = 1) with
  | [u, v] => pure ((u, v) :: st.2)
  | _ => pure st.2

/-- The edge set of the tree with Prüfer code `code`. -/
def pruferTree (n : ℕ) (code : List (Fin n)) : Finset (Sym2 (Fin n)) :=
  (((pruferEdgesC n code).run' 0).map (fun p => s(p.1, p.2))).toFinset

end FlowLatRound


