-- Prove2me | Definitions.Def_GraphTensorCP_wt
-- name    : GraphTensorCP_wt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:11.225655+00:00
-- url     : https://prove2.me/theorems/8af82209-a37b-414e-a5ce-24e153239fea
-- title:
--   Weighted graph tensor $\mathsf{WT}(Q)$, edge tensors $E^{(q)}_{i,j}$ and graph tensors $\mathsf{GT}_q(G)$
-- statement:
--   Let $Q$ be a dimension matrix of order $n$. The **weighted graph tensor** $\mathsf{WT}(Q)$ over a field $\mathbb F$ is the $n$-th order tensor that places, on every pair $i<j$ of legs, an identity matrix of size $Q_{i,j}$, and takes the Kronecker product of these edge tensors. In coordinates: let $\Lambda(Q)=\prod_{1\le i<j\le n}[Q_{i,j}]_0$ be the set of edge labelings, extended symmetrically by $\lambda_{j,i}=\lambda_{i,j}$ and $\lambda_{i,i}=0$. Leg $v$ has dimension $D_v=\prod_{j=1}^n Q_{v,j}$, with basis vectors indexed by the tuples $(\lambda_{v,j})_{j}$, and
--
--   $$\mathsf{WT}(Q)=\sum_{\lambda\in\Lambda(Q)}\ \bigotimes_{v=1}^{n} e_{(\lambda_{v,j})_j}.$$
--
--   Two special cases are named.
--
--   1. The **edge tensor** $E^{(q)}_{i,j}=E^{(q)}_{j,i}$ ($i\ne j$, $q\ge1$) is $\mathsf{WT}$ of the matrix equal to $q$ at $(i,j)$ and $(j,i)$ and $1$ elsewhere: legs $i,j$ have dimension $q$, the others dimension $1$, and $E^{(q)}_{i,j}=\sum_{a=0}^{q-1}\bigotimes_d v_{d,a}$ with $v_{d,a}=e^{(q)}_a$ for $d\in\{i,j\}$ and $e^{(1)}_0$ otherwise.
--   2. For a finite simple graph $G$ on $\{1,\dots,n\}$, the **graph tensor** $\mathsf{GT}_q(G)=\mathsf{WT}(Q)$ with $Q_{i,j}=q$ on the edges of $G$ and $1$ elsewhere.
--
--   $\mathsf{GT}_2(K_3)$ is the $2\times2$ matrix multiplication tensor, and the weighted graph tensors interpolate between matrix multiplication and its higher-order analogues; their asymptotic rank is the subject of the mission.
--
--   **Formalization Note** The paper indexes leg $v$ by the mixed-radix number $I^Q_v(\lambda)=\sum_j\lambda_{v,j}\prod_{h>j}Q_{v,h}$; Lean indexes it by the tuple $(\lambda_{v,j})_j$ itself, a bijective relabeling of the coordinates within each leg (the identification of Definition 2.5), so this is the same tensor. The sum runs over the labelings with $\lambda_{i,j}=\lambda_{j,i}$; for a dimension matrix the diagonal labels are forced to be $0$. Tensors are the published `MME.TensorObj`.
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 2.21, pp.22–23

import Mathlib
import Definitions.Def_mme_tensor

universe u

namespace GraphTensorCP

open PiTensorProduct

/-- A **symmetric edge labeling** for a matrix `Q`: a choice of a label `lab i j ∈ [Q_{i,j}]₀`
for every ordered pair, with `lab i j = lab j i` (Zhou, arXiv:2610.34273 (version of
2026-11-03), Definition 2.21, p.22: "Extend each labeling λ ∈ Λ(Q) symmetrically by
λ_{j,i} = λ_{i,j} and λ_{i,i} = 0"). For a dimension matrix, `Q_{i,i} = 1` forces
`lab i i = 0`, so these are exactly the labelings `λ ∈ Λ(Q) = ∏_{i<j} [Q_{i,j}]₀`. -/
def IsSymmLabel {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℕ}
    (lab : (i : Fin n) → (j : Fin n) → Fin (Q i j)) : Prop :=
  ∀ i j, (lab i j : ℕ) = lab j i

/-- The labelings `(i j : Fin n) → Fin (Q i j)` form a finite type (instance search does not
see through `Matrix` here, so the product instance is given explicitly). -/
instance labelFintype {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℕ) :
    Fintype ((i : Fin n) → (j : Fin n) → Fin (Q i j)) :=
  @Pi.instFintype _ _ _ _ (fun i => (inferInstance : Fintype ((j : Fin n) → Fin (Q i j))))

open scoped Classical in
/-- **Weighted graph tensor** `WT(Q)` (Zhou, *Asymptotic Rank of Weighted Graph Tensors via
Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), Definition 2.21, p.22),
in the paper's coordinate description
`WT(Q) = Σ_{λ ∈ Λ(Q)} ⊗_{v=1}^{n} e^{(D_v)}_{I^Q_v(λ)}`, `D_v = ∏_j Q_{v,j}`.

**Formalization Note.** Leg `v` is the space `F^{∏_j [Q_{v,j}]₀}` of functions on tuples
`(λ_{v,j})_j`, i.e. the paper's leg of dimension `D_v` with its basis indexed by the tuple
instead of by the mixed-radix number `I^Q_v(λ) = Σ_j λ_{v,j} ∏_{h>j} Q_{v,h}`. Mixed radix is
a bijection `∏_j [Q_{v,j}]₀ → [D_v]₀`, so this is the paper's tensor up to a permutation of
coordinates within each leg (≡perm, Definition 2.5), the same element of the tensor semiring.
The sum runs over symmetric labelings (`IsSymmLabel`). The definition typechecks for every
`Q`; it is the paper's `WT(Q)` when `Q` is a dimension matrix (`IsDimMatrix`). -/
noncomputable def wt (K : Type u) [Field K] {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℕ) :
    MME.TensorObj K n where
  V v := ((j : Fin n) → Fin (Q v j)) → K
  fin _ := Module.Finite.pi
  t := ∑ lab ∈ (Finset.univ.filter
      (fun lab : (i : Fin n) → (j : Fin n) → Fin (Q i j) => IsSymmLabel lab)),
    tprod K (fun v => (Pi.single (lab v) (1 : K) : ((j : Fin n) → Fin (Q v j)) → K))

/-- The dimension matrix of a single edge `{i, j}` of dimension `q`: `q` at `(i, j)` and
`(j, i)`, and `1` elsewhere (Zhou, arXiv:2610.34273 (version of 2026-11-03), Definition 2.21,
p.22). It is a dimension matrix when `i ≠ j` and `q ≥ 1`. -/
def edgeDim {n : ℕ} (i j : Fin n) (q : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun a b => if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then q else 1

/-- **Edge tensor** `E^{(q)}_{i,j}` (Zhou, arXiv:2610.34273 (version of 2026-11-03),
Definition 2.21, p.22): "E^{(q)}_{i,j} = Σ_{a=0}^{q−1} ⊗_{d=1}^{n} v_{d,a}, v_{d,a} = e^{(q)}_a for
d ∈ {i, j}, e^{(1)}_0 for d ∉ {i, j}", with "E^{(q)}_{j,i} = E^{(q)}_{i,j}".

**Formalization Note.** Defined as `WT` of the single-edge dimension matrix `edgeDim i j q`; its
legs `i, j` have dimension `q` and the others dimension `1`, so it is the paper's edge tensor
up to coordinates. It is symmetric in `i, j` by construction. The paper uses it for `i ≠ j`. -/
noncomputable def edgeTensor (K : Type u) [Field K] {n : ℕ} (i j : Fin n) (q : ℕ) :
    MME.TensorObj K n :=
  wt K (edgeDim i j q)

/-- The dimension matrix `Q` of the **graph tensor** `GT_q(G)` (Zhou, arXiv:2610.34273
(version of 2026-11-03), Definition 2.21, pp.22–23): `Q_{i,j} = q` on the edges of `G` and `1`
otherwise, so `GT_q(G) = WT(Q) = wt K (graphDim G q)`. The diagonal is `1` because a simple
graph has no loops. -/
def graphDim {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ) :
    Matrix (Fin n) (Fin n) ℕ :=
  fun a b => if G.Adj a b then q else 1

end GraphTensorCP


