-- Prove2me | Definitions.Def_PercCubeCycles_Joining
-- name    : PercCubeCycles_Joining
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:32.533341+00:00
-- url     : https://prove2.me/theorems/84faa83d-3bd9-41f3-8f64-1743647dbc8c
-- title:
--   Objects of Lemma 5.1 and Proposition 3.1 (joining marked trees through expanders)
-- statement:
--   **Lemma 5.1.** For pairwise disjoint sets $S_1,\dots,S_{2r}$ and a perfect matching $M$ on $[2r]$, the set $\mathcal M^+$ consists of the matchings $M^+$ on $[2r]$, edge disjoint from $M$, such that $([2r],M\cup M^+)$ is a Hamilton cycle or acyclic, together with vertex-disjoint paths $P_{xy}$ ($xy\in M^+$). Each $P_{xy}$ is an $S_x$-$S_y$ path of length at most $L=20d^2\log n-1$, and the paths avoid $S_z$ for every $z$ not matched by $M^+$.
--
--   **Proposition 3.1.** The data are pairwise vertex-disjoint subgraphs $G_0,\dots,G_k$, pairwise disjoint sets $S^*_{i,j}\subseteq V(G_j)$ of size $s$, pairwise vertex-disjoint trees $T_i\subseteq G_0$ with $(T_i,S^+_{i,0},S^-_{i,0})$ marked trees, perfect matchings of $G$ between $S^*_{i,j}$ and $S^*_{i,j+1}$, and the expansion condition (c) on $G_1,\dots,G_k$.
--
--   **Formalization Note** The sign $*$ is a `Bool`. The matching $M^*_{i,j}$ is a map of which only the values on $S^*_{i,j}$ matter. The input to the program lists $n,k,r,d,s$, then $G$, then $G_1,\dots,G_k$, the trees, the sets and the matchings. $G_0$ enters only through the trees.
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Proposition 3.1, p.9; Lemma 5.1, p.14

import Mathlib
import Definitions.Def_PercCubeCycles_Trees
import Definitions.Def_PercCubeCycles_MachineIO

set_option autoImplicit false

namespace PercCubeCycles

/-!
# The objects of Lemma 5.1 and Proposition 3.1

Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…): Proposition 3.1, p.9; Lemma 5.1, p.14.

**Formalization Note.**
* In Lemma 5.1 matchings on `[2r]` are graphs on `Fin (2 * r)`; `M ∪ M⁺` is `M ⊔ Mp`. A path `P_xy` is
  indexed by `x < y`.
* In Proposition 3.1 the sign `∗ ∈ {+, −}` is a `Bool` (`true` for `+`), `[r]` is `Fin r`, the indices
  `j ∈ {0, …, k}` are `Fin (k + 1)`. The matching `M^∗_{i,j}` is a map, of which only its values on
  `S^∗_{i,j}` matter. The unused integer `ℓ` of the page's list is dropped.
-/

variable {V : Type*}

/-- Lemma 5.1: `M` is a perfect matching on the vertex set. -/
def IsPerfectMatchingGraph {U : Type*} (M : SimpleGraph U) : Prop :=
  ∀ x, ∃! y, M.Adj x y

/-- Lemma 5.1 (I): `M` is a matching on the vertex set. -/
def IsMatchingGraph {U : Type*} (M : SimpleGraph U) : Prop :=
  ∀ x y z, M.Adj x y → M.Adj x z → y = z

/-- Lemma 5.1: the graph `Γ` is a Hamilton cycle: connected and `2`-regular. -/
def IsHamiltonCycleGraph {U : Type*} [Fintype U] (Γ : SimpleGraph U) : Prop :=
  Γ.Connected ∧ ∀ x, deg Γ x = 2

/-- Lemma 5.1: `Mp ∈ 𝓜⁺`: conditions (I) and (II) for the sets `S`, the matching `M` and
`L = 20d² log n − 1`. -/
def IsJoiningMatching [Fintype V] {r : ℕ} (G : SimpleGraph V) (S : Fin (2 * r) → Finset V) (d : ℕ)
    (M Mp : SimpleGraph (Fin (2 * r))) : Prop :=
  (IsMatchingGraph Mp ∧ Disjoint M Mp ∧ (IsHamiltonCycleGraph (M ⊔ Mp) ∨ (M ⊔ Mp).IsAcyclic)) ∧
  ∃ (u v : Fin (2 * r) → Fin (2 * r) → V) (P : ∀ x y, G.Walk (u x y) (v x y)),
    (∀ x y, x < y → Mp.Adj x y →
      (P x y).IsPath ∧ u x y ∈ S x ∧ v x y ∈ S y ∧
        ((P x y).length : ℝ) ≤ 20 * (d : ℝ) ^ 2 * Real.log (Fintype.card V) - 1) ∧
    (∀ x y x' y', x < y → Mp.Adj x y → x' < y' → Mp.Adj x' y' → (x, y) ≠ (x', y') →
      (P x y).support.Disjoint (P x' y').support) ∧
    (∀ z, (∀ y, ¬ Mp.Adj z y) → ∀ x y, x < y → Mp.Adj x y → ∀ a ∈ (P x y).support, a ∉ S z)

/-- The data of Proposition 3.1 in a graph `G`: the subgraphs `G₀, …, G_k`, the sets `S^∗_{i,j}`, the
trees `T₁, …, T_r`, and the matchings `M^∗_{i,j}`. -/
structure JoinData (G : SimpleGraph V) (k r : ℕ) where
  /-- `G₀, …, G_k`. -/
  Gs : Fin (k + 1) → G.Subgraph
  /-- `S^∗_{i,j}`, with `∗ = +` for `true`. -/
  S : Bool → Fin r → Fin (k + 1) → Finset V
  /-- `T₁, …, T_r`. -/
  T : Fin r → G.Subgraph
  /-- `M^∗_{i,j}` from `S^∗_{i,j}` to `S^∗_{i,j+1}`, `j < k`. -/
  Mt : Bool → Fin r → Fin k → V → V

/-- The hypotheses of Proposition 3.1, other than the integer bounds and `β^k < 1/r`. -/
def JoinData.Holds [Fintype V] {G : SimpleGraph V} {k r : ℕ} (D : JoinData G k r) (d s : ℕ) : Prop :=
  Pairwise (fun i j => Disjoint (D.Gs i).verts (D.Gs j).verts) ∧
  (∀ a i j, (D.S a i j : Set V) ⊆ (D.Gs j).verts ∧ (D.S a i j).card = s) ∧
  Pairwise (fun x y : Bool × Fin r × Fin (k + 1) =>
    Disjoint (D.S x.1 x.2.1 x.2.2) (D.S y.1 y.2.1 y.2.2)) ∧
  -- (a)
  ((∀ i, D.T i ≤ D.Gs 0) ∧ Pairwise (fun i j => Disjoint (D.T i).verts (D.T j).verts) ∧
    ∀ i, IsMarkedTree (D.T i) (D.S true i 0) (D.S false i 0)) ∧
  -- (b)
  (∀ a i (j : Fin k), Set.BijOn (D.Mt a i j) (D.S a i j.castSucc) (D.S a i j.succ) ∧
    ∀ x ∈ D.S a i j.castSucc, G.Adj x (D.Mt a i j x)) ∧
  -- (c)
  (∀ (j : Fin k) (A : Finset V), (A : Set V) ⊆ (D.Gs j.succ).verts →
    3 * A.card ≤ 2 * (D.Gs j.succ).verts.ncard →
    A.card ≤ d ^ 2 * (nbhd (D.Gs j.succ).spanningCoe A).card)

/-- `∑_{i ∈ [r]} d(Bᵢ)`, for `Bᵢ = (Tᵢ, S^+_{i,0}, S^−_{i,0})`. -/
noncomputable def JoinData.totalLength {G : SimpleGraph V} {k r : ℕ} (D : JoinData G k r) : ℕ :=
  ∑ i, markedLength (D.T i) (D.S true i 0) (D.S false i 0)

open scoped Classical in
/-- The input for the time clause of Proposition 3.1: `n, k, r, d, s`; the edge list of `G`; for each
`j ∈ [k]` the vertices and the edges of `G_j`; the edges of the trees; the sets `S^∗_{i,j}`; and each
matching `M^∗_{i,j}` as the pairs `x, M(x)`. `G₀` enters only through the trees. -/
noncomputable def JoinData.words {n : ℕ} {G : SimpleGraph (Fin n)} {k r : ℕ} (D : JoinData G k r)
    (d s : ℕ) : List ℤ :=
  [(n : ℤ), (k : ℤ), (r : ℤ), (d : ℤ), (s : ℤ)] ++ edgeWords G ++
    (List.finRange k).flatMap (fun j =>
      setWords (D.Gs j.succ).verts ++ edgeWords (D.Gs j.succ).spanningCoe) ++
    (List.finRange r).flatMap (fun i => edgeWords (D.T i).spanningCoe) ++
    [true, false].flatMap (fun a => (List.finRange r).flatMap fun i =>
      (List.finRange (k + 1)).flatMap fun j => setWords (D.S a i j : Set (Fin n))) ++
    [true, false].flatMap (fun a => (List.finRange r).flatMap fun i =>
      (List.finRange k).flatMap fun j =>
        ((List.finRange n).filter fun x => x ∈ D.S a i j.castSucc).flatMap fun (x : Fin n) =>
          [((x : ℕ) : ℤ), ((D.Mt a i j x : ℕ) : ℤ)])

end PercCubeCycles


