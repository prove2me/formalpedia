-- Prove2me | Definitions.Def_FlowLatRound_FlowGraph
-- name    : FlowLatRound_FlowGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:50.21057+00:00
-- url     : https://prove2.me/theorems/901f1fbb-6236-4337-9bcd-fda8f7fa9724
-- title:
--   §3.1, p.6 — multigraphs, flow space $H_G$, flow lattice $\Lambda_G$, spanning trees, $\tau(G)$, $|C(T,e)|$, $U(G)$, $\ell(F)$, the Voronoi cell and the zonotope
-- statement:
--   An oriented multigraph $G$ has vertices $0,\dots,n-1$ and labeled edges $0,\dots,m-1$; edge $e$ runs from $\mathrm{src}(e)$ to $\mathrm{dst}(e)$, and loops and parallel edges are allowed. The degree counts a loop twice.
--
--   1. The incidence map is $(Ax)_v=\sum_{\mathrm{dst}(e)=v}x_e-\sum_{\mathrm{src}(e)=v}x_e$ (a loop gives a zero column); the **flow space** is $H_G=\ker A\subseteq\mathbb R^m$ and the **flow lattice** is $\Lambda_G=H_G\cap\mathbb Z^m$.
--   2. An edge set $F$ connects $G$ if every nonempty proper vertex set is crossed by an edge of $F$; a **spanning tree** is a connecting edge set with $n-1$ edges, and $\tau(G)$ is their number (parallel edges counted as distinct). The cycle rank is $d=m-n+1$.
--   3. For a spanning tree $T$ and $e\notin T$, $|C(T,e)|$ is the number of edges $f$ of $T+e$ whose removal leaves a spanning tree (the length of the fundamental cycle; a loop gives $1$).
--   4. $U(G)$ is the set of connected spanning subgraphs with exactly $n$ edges, and $\ell(F)$ the number of edges of $F$ whose removal leaves a spanning tree (the length of its unique cycle).
--   5. $K_G=\mathrm{Vor}(\Lambda_G)=\{x\in H_G:\|x\|\le\|x-z\|\ \forall z\in\Lambda_G\}$, and the zonotope $P_G[-\tfrac12,\tfrac12]^m$ is the orthogonal projection of the cube onto $H_G$.
--   6. An integer matrix $B\in\mathbb Z^{m\times k}$ is a basis of a lattice $\Lambda$ if its columns are linearly independent and generate $\Lambda$; $\mathrm{gram}(B)=B^{\top}B$.
--
--   **Formalization Note** $H_G$ is the kernel of the full incidence matrix, which equals the kernel of the paper's $A_G$ with one row deleted. Connectivity is the cut condition, so all these predicates are decidable.
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), §3.1, p.6 (PDF 8); Lemma 3.2 and Proposition 3.3, p.6; Appendix C opening, p.22 (PDF 24)

import Mathlib
import Definitions.Def_FlowLatRound_Geometry

namespace FlowLatRound

/-! # Multigraphs, flow spaces, flow lattices, spanning trees and the flow cell

Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027
submission, sha256 35bd3e4b…aeac), §3.1, p.6 (PDF 8); Lemma 3.2, p.6; Proposition 3.3, p.6;
Appendix C opening, p.22 (PDF 24).

**Formalization Note.** A multigraph with `n` vertices and `m` labeled edges is given with an
orientation: edge `e : Fin m` runs from `src e` to `dst e`; loops (`src e = dst e`) and parallel
edges are allowed. The flow space `H_G` is the kernel of the **full** `n × m` incidence map
`(A x)_v = Σ_{dst e = v} x_e − Σ_{src e = v} x_e` (a loop gives a zero column); it equals the
kernel of the paper's `A_G`, which deletes one row, because the rows sum to zero. Connectivity
of an edge set `F` is the cut condition: every nonempty proper vertex set is crossed by an edge
of `F`. A spanning tree is a connected edge set with `n − 1` edges (written `card + 1 = n`). -/

/-- An oriented multigraph with vertices `Fin n` and labeled edges `Fin m`; edge `e` runs from
`src e` to `dst e`. Loops and parallel edges are allowed (§3.1, p.6). -/
structure MGraph (n m : ℕ) where
  src : Fin m → Fin n
  dst : Fin m → Fin n

/-- The vector of `ℝ^m` (Euclidean) with coordinates `x`. -/
def toE {m : ℕ} (x : Fin m → ℝ) : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 x

/-- The integer vector `z ∈ ℤ^m` as a point of `ℝ^m`. -/
def intVec {m : ℕ} (z : Fin m → ℤ) : EuclideanSpace ℝ (Fin m) := toE (fun e => (z e : ℝ))

/-- The rational vector `y ∈ ℚ^m` as a point of `ℝ^m`. -/
def ratVec {m : ℕ} (y : Fin m → ℚ) : EuclideanSpace ℝ (Fin m) := toE (fun e => (y e : ℝ))

namespace MGraph

variable {n m : ℕ} (G : MGraph n m)

/-- The degree of `v`; a loop at `v` counts twice. -/
def deg (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun e => G.src e = v)).card +
    (Finset.univ.filter (fun e => G.dst e = v)).card

/-- The full incidence matrix: column `e` is `+1` at `dst e` and `−1` at `src e`, and zero for a
loop. -/
def incMat : Matrix (Fin n) (Fin m) ℝ :=
  fun v e => (if G.dst e = v then 1 else 0) - (if G.src e = v then 1 else 0)

/-- The incidence map `x ↦ A x` on `ℝ^m`. -/
noncomputable def incidence : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] (Fin n → ℝ) :=
  (Matrix.toLin' G.incMat).comp (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap

/-- The flow space `H_G = ker A_G ⊆ ℝ^m` (§3.1, p.6). -/
noncomputable def flowSpace : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  LinearMap.ker G.incidence

/-- The flow lattice `Λ_G = H_G ∩ ℤ^m`, the integral flows (§3.1, p.6). -/
noncomputable def flowLattice : AddSubgroup (EuclideanSpace ℝ (Fin m)) where
  carrier := {x | x ∈ G.flowSpace ∧ ∀ e, ∃ k : ℤ, x e = k}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨G.flowSpace.add_mem hx hy, fun e => ?_⟩
    obtain ⟨a, ha⟩ := hx' e
    obtain ⟨b, hb⟩ := hy' e
    exact ⟨a + b, by simp [ha, hb]⟩
  zero_mem' := ⟨G.flowSpace.zero_mem, fun _ => ⟨0, by simp⟩⟩
  neg_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨G.flowSpace.neg_mem hx, fun e => ?_⟩
    obtain ⟨a, ha⟩ := hx' e
    exact ⟨-a, by simp [ha]⟩

/-- `F` connects all vertices: every nonempty proper set of vertices is crossed by an edge of
`F` (one endpoint inside, the other outside). -/
def ConnectedBy (F : Finset (Fin m)) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    ∃ e ∈ F, (G.src e ∈ S ↔ G.dst e ∉ S)

instance (F : Finset (Fin m)) : Decidable (G.ConnectedBy F) := by
  unfold ConnectedBy; infer_instance

/-- `T` is (the edge set of) a spanning tree: it connects all vertices and has `n − 1` edges.
Parallel edges are distinct edges, so spanning trees are counted with multiplicity. -/
def IsSpanningTree (T : Finset (Fin m)) : Prop :=
  T.card + 1 = n ∧ G.ConnectedBy T

instance (T : Finset (Fin m)) : Decidable (G.IsSpanningTree T) := by
  unfold IsSpanningTree; infer_instance

/-- The spanning trees of `G`. -/
def spanningTrees : Finset (Finset (Fin m)) := Finset.univ.filter G.IsSpanningTree

/-- `τ(G)`, the number of spanning trees (parallel edges counted as distinct). `G` is connected
iff `0 < τ(G)`. -/
def tau : ℕ := G.spanningTrees.card

/-- The cycle rank `d = m − n + 1`. -/
def cycleRank : ℕ := m + 1 - n

/-- `|C(T, e)|`, the number of edges of the fundamental cycle of the non-tree edge `e` with
respect to the spanning tree `T`: an edge `f` of `T + e` lies on that cycle iff deleting it from
`T + e` leaves a spanning tree. A loop gives `1`. -/
def cycLen (T : Finset (Fin m)) (e : Fin m) : ℕ :=
  ((insert e T).filter (fun f => G.IsSpanningTree ((insert e T).erase f))).card

/-- `U(G)`: the connected spanning subgraphs of `G` with exactly `n` edges (Proposition 3.3). -/
def unicyclic : Finset (Finset (Fin m)) :=
  Finset.univ.filter (fun F => F.card = n ∧ G.ConnectedBy F)

/-- `ℓ(F)` for `F ∈ U(G)`: the length of its unique cycle, i.e. the number of edges `f` of `F`
whose deletion leaves a spanning tree (`= τ(F)`, proof of Proposition 3.3, p.22). -/
def ellF (F : Finset (Fin m)) : ℕ :=
  (F.filter (fun f => G.IsSpanningTree (F.erase f))).card

/-- The Voronoi cell `K = Vor(Λ_G) = {x ∈ H_G : ‖x‖ ≤ ‖x − z‖ for all z ∈ Λ_G}` (§2 Notation,
p.4), as a subset of the flow space. -/
noncomputable def voronoiG : Set G.flowSpace :=
  {x | ∀ z ∈ G.flowLattice,
    ‖(x : EuclideanSpace ℝ (Fin m))‖ ≤ ‖(x : EuclideanSpace ℝ (Fin m)) - z‖}

/-- The zonotope `P_G[−½, ½]^m`, the orthogonal projection of the cube onto `H_G` (Lemma 3.2). -/
noncomputable def zonotope : Set G.flowSpace :=
  G.flowSpace.orthogonalProjectionOnto '' {u | ∀ e, |u e| ≤ 1 / 2}

end MGraph

/-- `B ∈ ℤ^{m×k}` is a basis of the lattice `Λ ⊆ ℝ^m`: its columns, as real vectors, are
linearly independent and generate `Λ` as an additive group. -/
def IsZBasis {m k : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin m))) (B : Fin m → Fin k → ℤ) :
    Prop :=
  LinearIndependent ℝ (fun j => intVec (fun e => B e j)) ∧
    AddSubgroup.closure (Set.range (fun j => intVec (fun e => B e j))) = Λ

/-- The Gram matrix `BᵀB` of an integer matrix, over `ℝ`; `det Λ = √det(BᵀB)` for a basis `B`
of `Λ`. -/
def gram {m k : ℕ} (B : Fin m → Fin k → ℤ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ∑ e, (B e i : ℝ) * (B e j : ℝ)

end FlowLatRound


