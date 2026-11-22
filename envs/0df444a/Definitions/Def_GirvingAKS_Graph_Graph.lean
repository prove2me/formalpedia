-- Prove2me | Definitions.Def_GirvingAKS_Graph_Graph
-- name    : GirvingAKS_Graph_Graph
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:42.342867+00:00
-- url     : https://prove2.me/theorems/de8a94b5-8ef3-4ffe-b3e5-b4e559392e1a
-- title:
--   AKS sorting networks (Seiferas port) — General Graphs (Half-Edge Representation)
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Graph/Graph.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** A general graph on `n` vertices, allowing irregular degree, multi-edges, and self-loops. Represented via half-edges with a rotation (pairing) involution, generalizing the `RegularGraph` rotation map.
--
--   The key operation is `HalfEdgeGraph.contract`: given a surjection `s : Fin n → Fin m`, relabel vertices while keeping half-edges and pairing unchanged. This produces an irregular multigraph whose spectral gap is at most that of the original.
--
--   Used to reduce arbitrary-size expanders from the zig-zag family (which only produces graphs at sizes `D^(4(k+1))`) to any target size `m`.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Graph/Graph.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Graph_Regular

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Graph/Graph.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # General Graphs (Half-Edge Representation)

  A general graph on `n` vertices, allowing irregular degree, multi-edges,
  and self-loops. Represented via half-edges with a rotation (pairing)
  involution, generalizing the `RegularGraph` rotation map.

  The key operation is `HalfEdgeGraph.contract`: given a surjection `s : Fin n → Fin m`,
  relabel vertices while keeping half-edges and pairing unchanged. This produces
  an irregular multigraph whose spectral gap is at most that of the original.

  Used to reduce arbitrary-size expanders from the zig-zag family (which only
  produces graphs at sizes `D^(4(k+1))`) to any target size `m`.
-/


section


open Finset BigOperators


/-! **General HalfEdgeGraph** -/

/-- A graph on `n` vertices, represented by half-edges with a pairing involution.

    Each half-edge `e ∈ Fin halfs` has a source vertex `src e`.
    The rotation map `rot` pairs half-edges: if `rot e = e'`, then
    `{src e, src e'}` is an edge. The involution ensures each edge is
    seen from both sides.

    Compared to `RegularGraph n d` (which has exactly `n * d` half-edges,
    `d` per vertex), `HalfEdgeGraph n` allows irregular degree. -/
structure HalfEdgeGraph (n : ℕ) where
  /-- The total number of half-edges (= sum of degrees = 2 * number of edges). -/
  halfs : ℕ
  /-- The source vertex of each half-edge. -/
  src : Fin halfs → Fin n
  /-- The half-edge pairing: `rot e` is the other half of the edge containing `e`. -/
  rot : Fin halfs → Fin halfs
  /-- Pairing is an involution. -/
  rot_involution : ∀ e, rot (rot e) = e

/-- The target vertex of a half-edge: the vertex at the other end. -/
def HalfEdgeGraph.target {n : ℕ} (G : HalfEdgeGraph n) (e : Fin G.halfs) : Fin n :=
  G.src (G.rot e)

/-- The degree of a vertex: the number of half-edges sourced at it. -/
def HalfEdgeGraph.deg {n : ℕ} (G : HalfEdgeGraph n) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun e => G.src e = v)).card

/-- The rotation map as an equivalence (since it's an involution). -/
def HalfEdgeGraph.rotEquiv {n : ℕ} (G : HalfEdgeGraph n) :
    Fin G.halfs ≃ Fin G.halfs where
  toFun := G.rot
  invFun := G.rot
  left_inv := G.rot_involution
  right_inv := G.rot_involution


/-! **Contraction** -/

/-- Contract a graph by relabeling vertices via `s : Fin n → Fin m`.

    Half-edges and their pairing are unchanged; only vertex labels change.
    Self-loops arise when `s(src e) = s(target e)`. Multi-edges arise when
    multiple half-edge pairs map to the same vertex pair.

    This is the key construction for building expanders at arbitrary sizes:
    take an oversized zig-zag family member and contract to the target size. -/
def HalfEdgeGraph.contract {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ} (s : Fin n → Fin m) : HalfEdgeGraph m where
  halfs := G.halfs
  src e := s (G.src e)
  rot := G.rot
  rot_involution := G.rot_involution

@[simp]
theorem HalfEdgeGraph.contract_halfs {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ} (s : Fin n → Fin m) :
    (G.contract s).halfs = G.halfs :=
  rfl

@[simp]
theorem HalfEdgeGraph.contract_src {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ} (s : Fin n → Fin m)
    (e : Fin (G.contract s).halfs) :
    (G.contract s).src e = s (G.src e) :=
  rfl

@[simp]
theorem HalfEdgeGraph.contract_rot {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ} (s : Fin n → Fin m)
    (e : Fin (G.contract s).halfs) :
    (G.contract s).rot e = G.rot e :=
  rfl

@[simp]
theorem HalfEdgeGraph.contract_target {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ} (s : Fin n → Fin m)
    (e : Fin (G.contract s).halfs) :
    (G.contract s).target e = s (G.target e) :=
  rfl


/-! **Embedding Regular Graphs** -/

/-- Encode a `RegularGraph` rotation result as a half-edge index. -/
def rgEncode {n d : ℕ} (r : Fin n × Fin d) : Fin (n * d) :=
  ⟨r.1.val * d + r.2.val, Fin.pair_lt r.1 r.2⟩

/-- Decode a half-edge index into vertex and port. -/
def rgVertex {n d : ℕ} (hd : 0 < d) (e : Fin (n * d)) : Fin n :=
  ⟨e.val / d, (Nat.div_lt_iff_lt_mul hd).mpr e.isLt⟩

def rgPort {n d : ℕ} (hd : 0 < d) (e : Fin (n * d)) : Fin d :=
  ⟨e.val % d, Nat.mod_lt _ hd⟩

theorem rgEncode_val {n d : ℕ} (r : Fin n × Fin d) :
    (rgEncode r).val = r.1.val * d + r.2.val := rfl

theorem rgDecode_encode {n d : ℕ} (hd : 0 < d) (e : Fin (n * d)) :
    rgEncode (rgVertex hd e, rgPort hd e) = e := by
  apply Fin.ext; simp only [rgEncode, rgVertex, rgPort]
  have := Nat.div_add_mod e.val d
  rw [Nat.mul_comm] at this; omega

theorem rgVertex_encode {n d : ℕ} (hd : 0 < d) (r : Fin n × Fin d) :
    rgVertex hd (rgEncode r) = r.1 := by
  apply Fin.ext; simp only [rgVertex, rgEncode]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt r.2.isLt]; omega

theorem rgPort_encode {n d : ℕ} (hd : 0 < d) (r : Fin n × Fin d) :
    rgPort hd (rgEncode r) = r.2 := by
  apply Fin.ext; simp only [rgPort, rgEncode]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.2.isLt]

/-- The rotation map for `RegularGraph.toGraph`. -/
def rgRot {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    (e : Fin (n * d)) : Fin (n * d) :=
  rgEncode (G.rot (rgVertex hd e, rgPort hd e))

theorem rgRot_involution {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    (e : Fin (n * d)) : rgRot G hd (rgRot G hd e) = e := by
  simp only [rgRot, rgVertex_encode, rgPort_encode, Prod.mk.eta, G.rot_involution,
    rgDecode_encode]

/-- Convert a `RegularGraph n d` to a `HalfEdgeGraph n`.

    The `n * d` half-edges are indexed by `Fin (n * d)`, encoding
    the pair `(v, p) : Fin n × Fin d` as `v.val * d + p.val`.
    The source of half-edge `e` is `e / d` (the vertex index). -/
def RegularGraph.toGraph {n d : ℕ} (G : RegularGraph n d) : HalfEdgeGraph n where
  halfs := n * d
  src e := ⟨e.val / d, by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact absurd e.isLt (by simp)
    · exact (Nat.div_lt_iff_lt_mul hd).mpr e.isLt⟩
  rot e :=
    if hd : 0 < d then rgRot G hd e
    else absurd e.isLt (by simp [Nat.eq_zero_of_not_pos hd])
  rot_involution e := by
    show (if hd : 0 < d then _ else _) = e
    split
    · next hd => exact rgRot_involution G hd e
    · next hd => exact absurd e.isLt (by simp [Nat.eq_zero_of_not_pos hd])

@[simp]
theorem RegularGraph.toGraph_halfs {n d : ℕ} (G : RegularGraph n d) :
    G.toGraph.halfs = n * d :=
  rfl


/-! **Regular HalfEdgeGraph Embedding Properties** -/

/-- Target vertex in `toGraph` expressed via the rotation map. -/
theorem RegularGraph.toGraph_target_eq {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    (e : Fin (n * d)) :
    G.toGraph.target e = G.neighbor (rgVertex hd e) (rgPort hd e) := by
  show G.toGraph.src (G.toGraph.rot e) = (G.rot (rgVertex hd e, rgPort hd e)).1
  have hrot : G.toGraph.rot e = rgRot G hd e := by
    show (if hd' : 0 < d then rgRot G hd' e else _) = rgRot G hd e
    rw [dif_pos hd]
  rw [hrot]; simp only [rgRot]
  -- G.toGraph.src (rgEncode result) = result.1
  -- Both .val are result.1.val * d + result.2.val) / d = result.1.val
  apply Fin.ext
  show ((G.rot (rgVertex hd e, rgPort hd e)).1.val * d +
    (G.rot (rgVertex hd e, rgPort hd e)).2.val) / d = _
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt (G.rot _).2.isLt]
  omega

/-- Round-trip: rgEncode(v, rgPort(e)) = e when src(e) = v. -/
theorem rgEncode_rgPort {n d : ℕ} (hd : 0 < d) (v : Fin n) (e : Fin (n * d))
    (hv : e.val / d = v.val) : rgEncode (v, rgPort hd e) = e := by
  apply Fin.ext; simp only [rgEncode, rgPort]
  show v.val * d + e.val % d = e.val
  have := Nat.div_add_mod e.val d; rw [hv] at this
  have := Nat.mul_comm d v.val; omega

/-- Each vertex of a regular graph has degree `d` in `toGraph`. -/
theorem RegularGraph.toGraph_deg {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    (v : Fin n) : G.toGraph.deg v = d := by
  show (univ.filter (fun e => G.toGraph.src e = v)).card = d
  have heq : (univ.filter (fun e => G.toGraph.src e = v)).card = (univ (α := Fin d)).card :=
    Finset.card_nbij' (fun e ↦ rgPort hd e) (fun i ↦ rgEncode (v, i))
      -- Forward: filter → univ (trivial)
      (fun _ _ ↦ mem_coe.mpr (mem_univ _))
      -- Backward: univ → filter
      (fun i _ ↦ mem_coe.mpr (mem_filter.mpr ⟨mem_univ _,
        Fin.ext (congr_arg Fin.val (rgVertex_encode hd (v, i)))⟩))
      -- Left inverse: encode(v, port(e)) = e
      (fun e he ↦ rgEncode_rgPort hd v e
        (congr_arg Fin.val ((mem_filter.mp (mem_coe.mp he)).2)))
      -- Right inverse: port(encode(v, i)) = i
      (fun i _ ↦ rgPort_encode hd (v, i))
  rw [heq, card_univ, Fintype.card_fin]

/-- Summing over half-edges at vertex `v` in `toGraph` equals summing over ports. -/
theorem RegularGraph.toGraph_sum_target {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d)
    (v : Fin n) (f : Fin n → ℝ) :
    ∑ e ∈ univ.filter (G.toGraph.src · = v), f (G.toGraph.target e) =
      ∑ i : Fin d, f (G.neighbor v i) := by
  refine Finset.sum_nbij' (fun e ↦ rgPort hd e) (fun i ↦ rgEncode (v, i)) ?_ ?_ ?_ ?_ ?_
  -- Forward: filter → univ (trivial)
  · intro _ _; exact mem_univ _
  -- Backward: univ → filter
  · intro i _
    exact mem_filter.mpr ⟨mem_univ _, Fin.ext (congr_arg Fin.val (rgVertex_encode hd (v, i)))⟩
  -- Left inverse: encode(v, port(e)) = e
  · intro e he
    exact rgEncode_rgPort hd v e (congr_arg Fin.val (mem_filter.mp he).2)
  -- Right inverse: port(encode(v, i)) = i
  · intro i _; exact rgPort_encode hd (v, i)
  -- Function agrees: target(e) = neighbor(v, port(e))
  · intro e he
    have hv : e.val / d = v.val := congr_arg Fin.val (mem_filter.mp he).2
    have h2 : rgVertex hd e = v := Fin.ext hv
    exact (congrArg f (G.toGraph_target_eq hd e)).trans
      (congrArg (fun w => f (G.neighbor w (rgPort hd e))) h2)


/-! **Double Counting** -/

/-- Double-counting via the rotation bijection: summing `g(target e)` over
    all half-edges equals summing `g(src e)` over all half-edges. -/
theorem HalfEdgeGraph.sum_target_eq_sum_src {n : ℕ} (G : HalfEdgeGraph n) (g : Fin n → ℝ) :
    ∑ e, g (G.target e) = ∑ e, g (G.src e) := by
  show ∑ e, g (G.src (G.rot e)) = ∑ e, g (G.src e)
  exact G.rotEquiv.sum_comp (fun e ↦ g (G.src e))

/-- The sum of degrees equals the number of half-edges. -/
theorem HalfEdgeGraph.sum_deg {n : ℕ} (G : HalfEdgeGraph n) :
    ∑ v, G.deg v = G.halfs := by
  simp only [HalfEdgeGraph.deg]
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ (α := Fin G.halfs))
    (t := Finset.univ (α := Fin n)) (f := G.src)
    (fun e _ ↦ Finset.mem_univ (G.src e))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  linarith

/-- The degree of a contracted vertex equals the sum of degrees in the fiber. -/
theorem HalfEdgeGraph.contract_deg_eq_sum_fiber {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ}
    (s : Fin n → Fin m) (u : Fin m) :
    (G.contract s).deg u = ∑ v ∈ univ.filter (s · = u), G.deg v := by
  unfold HalfEdgeGraph.deg; simp only [HalfEdgeGraph.contract_src]
  set S := univ.filter (fun v : Fin n ↦ s v = u)
  set fiber := fun v ↦ univ.filter (fun e : Fin G.halfs ↦ G.src e = v)
  have partition : (univ.filter (fun e : Fin G.halfs ↦ s (G.src e) = u)) =
      S.biUnion fiber := by
    ext e; simp only [S, fiber, mem_filter, mem_univ, true_and, mem_biUnion]
    exact ⟨fun h ↦ ⟨G.src e, h, rfl⟩, fun ⟨_, hv, he⟩ ↦ he ▸ hv⟩
  have hdisj : (S : Set (Fin n)).PairwiseDisjoint fiber := by
    intro v₁ _ v₂ _ hne
    simp only [fiber, Finset.disjoint_filter]
    intro e _ h₁ h₂; exact hne (h₁.symm.trans h₂)
  show (univ.filter (fun e : Fin G.halfs ↦ s (G.src e) = u)).card = _
  rw [partition, Finset.card_biUnion hdisj]

end


