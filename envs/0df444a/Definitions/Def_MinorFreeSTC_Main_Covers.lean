-- Prove2me | Definitions.Def_MinorFreeSTC_Main_Covers
-- name    : MinorFreeSTC_Main_Covers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:17:27.721864+00:00
-- url     : https://prove2.me/theorems/ce291429-d076-43a9-bd00-10419ad9d67b
-- title:
--   Spanning tree covers (Def. 1), strong sparse partitions (Def. 2), separated neighborhood covers (Def. 3), centered hierarchies and hierarchy covers (Defs. 4–7), tiled centered families
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph.
--
--   **Spanning tree cover (Definition 1).** A family $T_0,\dots,T_{k-1}$ of spanning trees of $G$ (subgraphs of $G$ on all of $V$ that are trees, with the weights of $G$) is an **$\alpha$-distortion spanning tree cover** of size $k$ if for all $u,v\in V$: every tree dominates, $d_G(u,v)\le d_{T_i}(u,v)$, and some tree covers the pair,
--   $$\exists i:\ d_{T_i}(u,v)\le\alpha\cdot d_G(u,v).$$
--
--   **Strong sparse partition (Definition 2).** A $\Delta$-diameter partition $\mathcal P$ is a **strong $(\alpha,\tau)$-sparse partition** if every ball $B_G(v,\Delta/\alpha)$ meets at most $\tau$ clusters.
--
--   **Strong neighborhood cover (Definition 3).** Partial partitions $\mathcal C_0,\dots,\mathcal C_{k-1}$, $k\le\tau$, all of strong diameter at most $\Delta$, form a cover of **size $\tau$, padding $\alpha$, diameter $\Delta$** if for every $v$ some cluster contains $B_G(v,\Delta/\alpha)$; it is **$s$-separated** if distinct clusters $C_0,C_1$ of the same $\mathcal C_i$ satisfy $d_G(C_0,C_1)>s\Delta$.
--
--   **Hierarchies (Definitions 4–5).** $H=(\mathcal C_0,\dots,\mathcal C_\kappa)$ is a **hierarchical partition** if every $\mathcal C_i$ is a partition, $\mathcal C_0$ is the singleton partition, $\mathcal C_\kappa=\{V\}$ and $\mathcal C_i$ coarsens $\mathcal C_{i-1}$. For $\gamma>1$, $\lambda>0$ it is **$\gamma$-growing with offset $\lambda$** if $\operatorname{diam}(C)\le\lambda\gamma^i$ for $i\in[\kappa]$, $C\in\mathcal C_i$; it is **centered** with designated centers $\mathrm{cent}_i(C)\in C$.
--
--   **Centered distance (Definition 6).** For $u\ne v$, let $H(u,v)$ be the pairs $(i,C)$ with $i\in[\kappa]$, $C\in\mathcal C_i$, $u,v\in C$ and $\lambda\gamma^i\le 6d_G(u,v)$;
--   $$d^{\mathrm{cent}}_H(u,v)=\min_{(i,C)\in H(u,v)}\big(d_C(u,\mathrm{cent}_i(C))+d_C(v,\mathrm{cent}_i(C))\big),$$
--   $\infty$ if $H(u,v)=\emptyset$, and $d^{\mathrm{cent}}_H(u,u)=0$.
--
--   **Centered hierarchy cover (Definition 7).** Centered $\gamma$-growing hierarchical partitions $H_0,\dots,H_{m-1}$ (offsets may differ) with $\min_j d^{\mathrm{cent}}_{H_j}(u,v)\le\alpha\, d_G(u,v)$ for all $u,v$.
--
--   **Tiled centered family (conclusion of Lemma 12).** Partitions $\mathcal C_0,\dots,\mathcal C_{m-1}$ with centers such that every cluster is a union of clusters of a given partition $\mathcal P$, $\operatorname{rad}(C,\mathrm{cent}_i(C))\le 3\Delta$, and every pair with $\Delta\le d_G(u,v)\le2\Delta$ lies in a cluster $C$ with $d_C(u,\mathrm{cent}_i(C))+d_C(v,\mathrm{cent}_i(C))\le(1+\epsilon)d_G(u,v)$.
--
--   **Formalization Note.** Families are indexed by `Fin k`; a hierarchy stores its levels as `ℕ → Finset (Finset V)` (levels above $\kappa$ are ignored), its offset and its centers. Spanning trees are the published `RamseyLST.Main.SpanningTree`.
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 1 (Definition 1), p. 4 (Definition 2), pp. 14–15 (Definitions 3–7), pp. 29–30 (Lemma 12)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_RamseyLST_Main_RamseySpanningTree
import Definitions.Def_MinorFreeSTC_Main_Graphs

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-!
# Spanning tree covers, strong sparse partitions, neighborhood covers, centered hierarchies

Filtser, Fletcher, Hershkowitz, Milenković, *(1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free
Graphs with Size O(log log n)*, STOC 2027 submission (manuscript sha256 f475e254…): Definition 1
(p. 1, PDF 3), Definition 2 (p. 4, PDF 6), Definitions 3–7 (pp. 14–15, PDF 16–17).

* A spanning tree is the published `RamseyLST.Main.SpanningTree G` (a tree `T ≤ G` on all of `V`,
  with the weights of `G`); `T.dist` is `d_T`. A family of `k` trees is indexed by `Fin k`
  (repetitions allowed); its size is `k`.
* Clusters are `Finset V`; a (partial) partition is a `Finset (Finset V)`.
* A family of `k` partial partitions is `Fin k → Finset (Finset V)`.
* A hierarchy `(C_0, …, C_κ)` stores its levels as `C : ℕ → Finset (Finset V)` (levels above `κ`
  are ignored), its offset `λ` and its centers `cent i C`.
-/

variable {V : Type}

/-- Definition 1 (p. 1), spanning version: the family `T : Fin k → SpanningTree G` is an
`α`-distortion spanning tree cover of `G`: every tree dominates (`d_G(u, v) ≤ d_T(u, v)`) and every
pair `u, v` is covered by some tree (`d_T(u, v) ≤ α · d_G(u, v)`). Its size is `k`. -/
def IsSpanningTreeCover (G : WGraph V) (k : ℕ) (T : Fin k → RamseyLST.Main.SpanningTree G)
    (α : ℝ) : Prop :=
  (∀ i : Fin k, ∀ u v : V, G.dist u v ≤ (T i).dist u v) ∧
    ∀ u v : V, ∃ i : Fin k, (T i).dist u v ≤ ENNReal.ofReal α * G.dist u v

open Classical in
/-- Definition 2 (p. 4): `P` is a `∆`-strong-diameter partition of `V` which is a strong
`(α, τ)`-sparse partition: every ball `B_G(v, ∆/α)` meets at most `τ` clusters. -/
def IsStrongSparsePartition [Fintype V] (G : WGraph V) (P : Finset (Finset V))
    (Δ α τ : ℝ) : Prop :=
  IsPartition P ∧ DiamLe G P Δ ∧
    ∀ v : V, ((P.filter fun C => ∃ u ∈ C, u ∈ ball G v (Δ / α)).card : ℝ) ≤ τ

/-- Definition 3 (p. 14): `𝒞 = (𝒞_0, …, 𝒞_{k−1})` is a strong neighborhood cover of size at most
`τ`, padding `α` and diameter `∆`: `k ≤ τ` partial partitions, every cluster of strong diameter at
most `∆`, and every ball `B_G(v, ∆/α)` inside some cluster. -/
def IsNeighborhoodCover (G : WGraph V) (k : ℕ) (𝒞 : Fin k → Finset (Finset V))
    (τ α Δ : ℝ) : Prop :=
  (k : ℝ) ≤ τ ∧ (∀ i, IsPartialPartition (𝒞 i)) ∧ (∀ i, DiamLe G (𝒞 i) Δ) ∧
    ∀ v : V, ∃ i, ∃ C ∈ 𝒞 i, ball G v (Δ / α) ⊆ (C : Set V)

/-- Definition 3 (p. 15), separation: for every `i` and distinct `C₀, C₁ ∈ 𝒞_i`,
`d_G(C₀, C₁) > s∆`. -/
def IsSeparated (G : WGraph V) (k : ℕ) (𝒞 : Fin k → Finset (Finset V)) (s Δ : ℝ) : Prop :=
  ∀ i, ∀ C₀ ∈ 𝒞 i, ∀ C₁ ∈ 𝒞 i, C₀ ≠ C₁ →
    ENNReal.ofReal (s * Δ) < setDist G (C₀ : Set V) (C₁ : Set V)

/-- A `τ`-size, `α`-padded, `∆`-diameter, `s`-separated (strong) neighborhood cover. -/
def IsSepCover (G : WGraph V) (k : ℕ) (𝒞 : Fin k → Finset (Finset V)) (τ α Δ s : ℝ) : Prop :=
  IsNeighborhoodCover G k 𝒞 τ α Δ ∧ IsSeparated G k 𝒞 s Δ

/-- A (centered) hierarchy `H = (C_0, …, C_κ)` with offset `λ` and centers `cent_i(C)`. -/
structure Hierarchy (V : Type) where
  /-- The top level `κ`. -/
  κ : ℕ
  /-- The offset `λ`. -/
  offset : ℝ
  /-- The partition at level `i` (`i ≤ κ`). -/
  C : ℕ → Finset (Finset V)
  /-- The designated center `cent_i(C)` of the cluster `C` at level `i`. -/
  cent : ℕ → Finset V → V

/-- Definition 4 (p. 15): `H` is a hierarchical partition: `C_0` is the singleton partition,
`C_κ = {V}`, every `C_i` is a partition and `C_i` coarsens `C_{i−1}` for `i ∈ [κ]`. -/
def IsHierarchical [Fintype V] [DecidableEq V] (H : Hierarchy V) : Prop :=
  (∀ i ≤ H.κ, IsPartition (H.C i)) ∧ H.C 0 = Finset.univ.image (fun v : V => {v}) ∧
    H.C H.κ = {Finset.univ} ∧ ∀ i, 1 ≤ i → i ≤ H.κ → Coarsens (H.C i) (H.C (i - 1))

/-- Definition 4 (p. 15): for `γ > 1` and `λ > 0`, `H` is `γ`-growing with offset `λ`:
`diam(C) ≤ λγ^i` for every `i ∈ [κ]` and `C ∈ C_i`. -/
def IsGrowing (G : WGraph V) (H : Hierarchy V) (γ : ℝ) : Prop :=
  1 < γ ∧ 0 < H.offset ∧ ∀ i, 1 ≤ i → i ≤ H.κ → DiamLe G (H.C i) (H.offset * γ ^ i)

/-- Definition 5 (p. 15): the centers are designated: `cent_i(C) ∈ C` for `i ∈ {0, …, κ}`,
`C ∈ C_i`. -/
def IsCentered (H : Hierarchy V) : Prop := ∀ i ≤ H.κ, ∀ C ∈ H.C i, H.cent i C ∈ C

/-- A centered `γ`-growing hierarchical partition of `G` (Definitions 4–5), offset `H.offset`. -/
def IsCenteredGrowingHierarchy [Fintype V] [DecidableEq V] (G : WGraph V) (H : Hierarchy V)
    (γ : ℝ) : Prop :=
  IsHierarchical H ∧ IsGrowing G H γ ∧ IsCentered H

open Classical in
/-- Definition 6 (p. 15): the centered distance `d^cent_H(u, v)`: `0` if `u = v`; otherwise the
minimum of `d_C(u, cent_i(C)) + d_C(v, cent_i(C))` over `(i, C)` with `i ∈ [κ]`, `C ∈ C_i`,
`u, v ∈ C` and `λγ^i ≤ 6 d_G(u, v)`, and `∞` if there is no such pair. -/
noncomputable def centDist (G : WGraph V) (H : Hierarchy V) (γ : ℝ) (u v : V) : ℝ≥0∞ :=
  if u = v then 0 else
    ⨅ i ∈ Finset.Icc 1 H.κ, ⨅ C ∈ H.C i,
      ⨅ (_ : u ∈ C ∧ v ∈ C ∧ ENNReal.ofReal (H.offset * γ ^ i) ≤ 6 * G.dist u v),
        G.distIn (C : Set V) u (H.cent i C) + G.distIn (C : Set V) v (H.cent i C)

/-- Definition 7 (p. 15): `F = (H_0, …, H_{m−1})` is an `α`-distortion `γ`-growing centered
hierarchy cover of size `m`: centered `γ`-growing hierarchical partitions (offsets may differ)
with `min_j d^cent_{H_j}(u, v) ≤ α · d_G(u, v)` for all `u, v`. -/
def IsCenteredHierarchyCover [Fintype V] [DecidableEq V] (G : WGraph V) (m : ℕ)
    (F : Fin m → Hierarchy V) (α γ : ℝ) : Prop :=
  (∀ j, IsCenteredGrowingHierarchy G (F j) γ) ∧
    ∀ u v : V, (⨅ j : Fin m, centDist G (F j) γ u v) ≤ ENNReal.ofReal α * G.dist u v

/-- Lemma 12's conclusion for one family (p. 29–30): `C_0, …, C_{m−1}` are partitions of `V` with
designated centers `cent_i(C) ∈ C` such that **Tiling**: every cluster is a union of clusters of
`P`; **Bounded Strong Radius**: `rad(C, cent_i(C)) ≤ 3∆`; **Centered Distance Preservation**:
for all `u, v` with `∆ ≤ d_G(u, v) ≤ 2∆` some `C ∈ C_i` contains `u, v` and
`d_C(u, cent_i(C)) + d_C(v, cent_i(C)) ≤ (1 + ϵ) · d_G(u, v)`. -/
def IsTiledCenteredFamily [DecidableEq V] (G : WGraph V) (P : Finset (Finset V)) (Δ ϵ : ℝ) (m : ℕ)
    (C : Fin m → Finset (Finset V)) (cent : Fin m → Finset V → V) : Prop :=
  (∀ i, IsPartition (C i)) ∧ (∀ i, ∀ X ∈ C i, cent i X ∈ X) ∧
    (∀ i, ∀ X ∈ C i, ∃ Q ⊆ P, X = Q.biUnion id) ∧
    (∀ i, ∀ X ∈ C i, srad G (X : Set V) (cent i X) ≤ ENNReal.ofReal (3 * Δ)) ∧
    ∀ u v : V, ENNReal.ofReal Δ ≤ G.dist u v → G.dist u v ≤ ENNReal.ofReal (2 * Δ) →
      ∃ i, ∃ X ∈ C i, u ∈ X ∧ v ∈ X ∧
        G.distIn (X : Set V) u (cent i X) + G.distIn (X : Set V) v (cent i X) ≤
          ENNReal.ofReal (1 + ϵ) * G.dist u v

end MinorFreeSTC.Main


