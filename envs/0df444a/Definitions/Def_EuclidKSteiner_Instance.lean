-- Prove2me | Definitions.Def_EuclidKSteiner_Instance
-- name    : EuclidKSteiner_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:53.246689+00:00
-- url     : https://prove2.me/theorems/5239e62d-9293-4826-b631-4050fc7601f0
-- title:
--   Discrete Euclidean $k$-Steiner Tree: instances, the Euclidean MST weight, machine input and output
-- statement:
--   An **instance** of Discrete Euclidean $k$-Steiner Tree consists of a budget $k\ge0$, terminals $P_0,\dots,P_{n_P-1}$ and candidates $Q_0,\dots,Q_{n_Q-1}$ in $\mathbb R^d$ (Euclidean space with the distance $\|u-v\|_2$).
--
--   1. For a finite point set $X\subseteq\mathbb R^d$, $w(\mathrm{MST}(X))$ is the minimum total Euclidean length of a spanning tree of the complete graph on $X$ ($0$ when $|X|\le1$); a **Euclidean minimum spanning tree** of $X$ is a spanning tree attaining it.
--   2. For a set $S$ of candidate indices, the **selection** is the point set $P\cup S=\{P_i\}\cup\{Q_j: j\in S\}$.
--   3. The task is to find $S$ with $|S|\le k$ minimizing $w(\mathrm{MST}(P\cup S))$.
--   4. The **machine input** is the list of reals $k,n_P,n_Q$, followed by the $d$ coordinates of $P_0,P_1,\dots$, then those of $Q_0,Q_1,\dots$. The **output** of a selection, read from the cell after the input, is its size $m$ followed by the $m$ candidate indices (0-based).
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. Points are indexed sequences, so repeated input points are allowed; the point set of a selection is the image, and the paper's sets are the injective case.
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), §1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_EuclidKSteiner_SpanningTree

namespace EuclidKSteiner

open Classical

/-!
# Discrete Euclidean k-Steiner Tree: instances, the Euclidean MST weight, machine input and output

Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean k-Steiner Tree*,
STOC 2027 submission (manuscript sha256 75361687…), §1, p.1 (PDF p.3):
"Discrete Euclidean k-Steiner Tree. Input: A terminal set P ⊆ ℝ^d, a candidate set Q ⊆ ℝ^d, and an
integer k ≥ 0; n = |P| + |Q|. Parameter: The Steiner-point budget k. Task: Find a set S ⊆ Q with
|S| ≤ k minimizing w(MST(P ∪ S))."

**Formalization Note**
* `ℝ^d` is `EuclideanSpace ℝ (Fin d)`, whose `dist` is the Euclidean norm `∥u − v∥₂`.
* `P` and `Q` are indexed sequences `Fin nP → E d`, `Fin nQ → E d`; the point set of a selection is
  the image `{P i} ∪ {Q j : j ∈ S}` as a `Finset`, so repeated input points collapse. Sets in the
  paper are the injective case.
* The machine input is the list of reals `k, nP, nQ`, then the `d` coordinates of `P 0, P 1, …`,
  then those of `Q 0, Q 1, …`. The output, read from the cell right after the input, is the number
  `m` of chosen candidates followed by their indices (0-based, as reals).
-/

/-- Euclidean space `ℝ^d` with the Euclidean distance. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Euclidean length `∥u − v∥₂` of an unordered pair, a function on `Sym2 (E d)`. -/
noncomputable def edist2 {d : ℕ} : Sym2 (E d) → ℝ :=
  Sym2.lift ⟨fun u v => dist u v, fun u v => dist_comm u v⟩

/-- `T` is a **Euclidean minimum spanning tree** of the finite point set `X`: a minimum spanning
tree of the complete graph on `X` with Euclidean edge lengths.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §1, p.1 (PDF p.3). -/
def IsEuclMST {d : ℕ} (X : Finset (E d)) (T : Finset (Sym2 (E d))) : Prop :=
  IsMST X id (completeEdges X) edist2 T

/-- **`w(MST(X))`**: the total Euclidean length of a minimum spanning tree of the finite point set
`X`, the minimum over all spanning trees of the complete graph on `X`; `0` when `|X| ≤ 1`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §1, p.1 (PDF p.3). -/
noncomputable def mstWeight {d : ℕ} (X : Finset (E d)) : ℝ :=
  mstWeightOn X id (completeEdges X) edist2

/-- The point set `P ∪ S` of the selection `S ⊆ Q` (given by candidate indices). -/
noncomputable def selection {d nP nQ : ℕ} (P : Fin nP → E d) (Q : Fin nQ → E d)
    (S : Finset (Fin nQ)) : Finset (E d) :=
  Finset.univ.image P ∪ S.image Q

/-- The coordinates of an indexed point sequence, point by point, `d` cells per point. -/
noncomputable def coords {d m : ℕ} (P : Fin m → E d) : List ℝ :=
  (List.finRange m).flatMap fun i => (List.finRange d).map fun j => P i j

/-- **Machine input** of an instance: `k, nP, nQ`, then the coordinates of `P`, then those of `Q`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §1, p.1 (PDF p.3); real-RAM model, p.3 (PDF p.5). -/
noncomputable def layout {d nP nQ : ℕ} (k : ℕ) (P : Fin nP → E d) (Q : Fin nQ → E d) : List ℝ :=
  (k : ℝ) :: (nP : ℝ) :: (nQ : ℝ) :: (coords P ++ coords Q)

/-- After `t` steps the cells right after the input hold the list `out`: cell
`input.length + j` holds `out[j]`. -/
def OutputIs (A : MatMulTimeLP.Program) (input : List ℝ) (ω : MatMulTimeLP.Tape) (t : ℕ)
    (out : List ℝ) : Prop :=
  ∀ j : Fin out.length, MatMulTimeLP.outputAt A input ω t out.length j = out.get j

/-- The output encoding of a list of candidate indices: its length, then the indices as reals. -/
noncomputable def encodeIndices {m : ℕ} (L : List (Fin m)) : List ℝ :=
  (L.length : ℝ) :: L.map fun i => ((i : ℕ) : ℝ)

end EuclidKSteiner


