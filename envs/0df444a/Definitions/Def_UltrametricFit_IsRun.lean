-- Prove2me | Definitions.Def_UltrametricFit_IsRun
-- name    : UltrametricFit_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:47.775935+00:00
-- url     : https://prove2.me/theorems/da21f2ba-8df6-42f5-ab7c-ac19383af748
-- title:
--   Runs of Algorithm 1, Merge($\delta$), and their output
-- statement:
--   Algorithm 1 starts from singletons and goes through the layers $\ell=1,\dots,L$. On layer $\ell$, while there are two clusters $A,B$ of the current clustering with $x_\ell(A,B)\le\delta$, it merges them; when there are none, it records the clustering as $C_\ell$. The output is $U(i,j)=D_{\ell^*(i,j)}$, where $\ell^*(i,j)$ is the least layer whose clustering has $i,j$ in one cluster.
--
--   The module defines a **run** as the clusterings together with the merge lists of each layer, the **merge events** $(\ell^*,A,B)$, which are the nodes $(A\cup B,\ell^*)$ of the final forest, the relation "**$U$ is an output**", and the **covering** of a pair $i,j$ by an event, meaning $ij\in A\times B$.
--
--   This module is what makes the mission's main theorem a statement about the paper's algorithm and not about an arbitrary good ultrametric.
--
--   **Formalization Note** The paper fixes no merge order, so runs are a relation and each order is a run. The merged clusters are distinct. Eligibility is the non-strict $\le\delta$, and a layer ends only when no distinct pair is eligible. The output constrains only pairs $i\ne j$. Entries of the run beyond layer $L$ are not read.
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Algorithm 1, §3, p.8; §4.3, p.11; proof of Theorem 1, p.15

import Mathlib
import Definitions.Def_UltrametricFit_avgDist
import Definitions.Def_UltrametricFit_layerValue

namespace UltrametricFit

/-- **The inner while-loop of Algorithm 1** on one layer, Charikar, Gao, STOC 2027 submission
(manuscript sha256 87af12a2…), Algorithm 1 step 1, p.8: "While there exists a pair of clusters
A, B ∈ C such that x_ℓ(A, B) ≤ δ, merge them into a single cluster A ∪ B and update
C ← (C \ {A, B}) ∪ {A ∪ B}."

`LayerRun d δ C ms C'` says the loop started from `C` can perform exactly the merges `ms`, in that
order, and stop at `C'`.

**Formalization Note.** This is a relation: the paper fixes no merge order, and each order is a
run. The two clusters of a merge are distinct, because "a pair of clusters" that were equal would
never let a layer stop (`d(A, A) ≤ δ` by Claim 8). Eligibility is the non-strict `≤ δ`. The loop may
stop only when no distinct pair is eligible. -/
inductive LayerRun {n : ℕ} (d : Fin n → Fin n → ℝ) (δ : ℝ) :
    Finset (Finset (Fin n)) → List (Finset (Fin n) × Finset (Fin n)) →
      Finset (Finset (Fin n)) → Prop
  | stop (C : Finset (Finset (Fin n))) :
      (∀ A ∈ C, ∀ B ∈ C, A ≠ B → δ < avgDist d A B) → LayerRun d δ C [] C
  | step (C C' : Finset (Finset (Fin n))) (A B : Finset (Fin n))
      (ms : List (Finset (Fin n) × Finset (Fin n))) :
      A ∈ C → B ∈ C → A ≠ B → avgDist d A B ≤ δ →
      LayerRun d δ (insert (A ∪ B) ((C.erase A).erase B)) ms C' →
      LayerRun d δ C ((A, B) :: ms) C'

/-- **A run of Merge(δ)**, Charikar, Gao, STOC 2027 submission (manuscript sha256 87af12a2…),
Algorithm 1, p.8, on the solution `x` of the LP for `X`: the clusterings `C ℓ` (`C_ℓ` for
`ℓ ∈ [L]`, and `C 0` the initial clustering into singletons) and the merge lists `M ℓ` of each
layer `ℓ ∈ [L]`.

**Formalization Note.** Values of `C` and `M` beyond layer `L`, and `M 0`, are not read. -/
structure IsRun {n : ℕ} (X : Fin n → Fin n → ℝ) (x : ℕ → Fin n → Fin n → ℝ) (δ : ℝ)
    (C : ℕ → Finset (Finset (Fin n))) (M : ℕ → List (Finset (Fin n) × Finset (Fin n))) : Prop where
  init : C 0 = Finset.univ.image fun i => ({i} : Finset (Fin n))
  layer : ∀ ℓ ∈ Finset.Icc 1 (numLayers X), LayerRun (x ℓ) δ (C (ℓ - 1)) (M ℓ) (C ℓ)

/-- The nodes `(A ∪ B, ℓ*)` of the final forest `T_L`, Charikar, Gao, STOC 2027 submission
(manuscript sha256 87af12a2…), §4.3, p.11, as the list of merge events `(ℓ*, A, B)` of a run, in
execution order. -/
noncomputable def mergeEvents {n : ℕ} (X : Fin n → Fin n → ℝ)
    (M : ℕ → List (Finset (Fin n) × Finset (Fin n))) :
    List (ℕ × Finset (Fin n) × Finset (Fin n)) :=
  (List.range' 1 (numLayers X)).flatMap fun ℓ => (M ℓ).map fun e => (ℓ, e.1, e.2)

/-- `i, j` "are in the same cluster" of the clustering `C`, Algorithm 1, p.8. -/
def SameCluster {n : ℕ} (C : Finset (Finset (Fin n))) (i j : Fin n) : Prop :=
  ∃ A ∈ C, i ∈ A ∧ j ∈ A

/-- **The output of a run**, Charikar, Gao, STOC 2027 submission (manuscript sha256 87af12a2…),
Algorithm 1, p.8: "let ℓ*(i, j) be the minimum index ℓ ∈ [L] such that i, j are in the same cluster
in C_ℓ and U(i, j) = D_{ℓ*(i,j)}."

**Formalization Note.** This is relational and constrains only pairs `i ≠ j`, so the diagonal of
`U` stays free. Existence and uniqueness on pairs are a milestone, not an assumption. -/
def IsOutput {n : ℕ} (X : Fin n → Fin n → ℝ) (C : ℕ → Finset (Finset (Fin n)))
    (U : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ ℓ ∈ Finset.Icc 1 (numLayers X),
    SameCluster (C ℓ) i j ∧ (∀ ℓ' ∈ Finset.Icc 1 (numLayers X), ℓ' < ℓ → ¬ SameCluster (C ℓ') i j) ∧
      U i j = layerValue X ℓ

/-- The pair `i, j` "is covered by" the node `A ∪ B` of a merge event, Charikar, Gao, STOC 2027
submission (manuscript sha256 87af12a2…), proof of Theorem 1, p.15: `ij ∈ A × B`, for the unordered
pair. -/
def covers {n : ℕ} (i j : Fin n) (e : ℕ × Finset (Fin n) × Finset (Fin n)) : Bool :=
  decide ((i ∈ e.2.1 ∧ j ∈ e.2.2) ∨ (i ∈ e.2.2 ∧ j ∈ e.2.1))

end UltrametricFit


