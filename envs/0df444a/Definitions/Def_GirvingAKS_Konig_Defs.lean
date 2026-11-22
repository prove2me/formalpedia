-- Prove2me | Definitions.Def_GirvingAKS_Konig_Defs
-- name    : GirvingAKS_Konig_Defs
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:16.180039+00:00
-- url     : https://prove2.me/theorems/cd9d6d50-40d7-4e35-a464-e3cfacf4a9ad
-- title:
--   AKS sorting networks (Seiferas port) — König's Edge Coloring — Definitions
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Konig/Defs.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Bipartite multigraph structures for König's edge coloring theorem. Used to prove depth bounds for expander-based halver networks.
--
--   Main definitions:
--
--   - `RegBipartite m d` — d-regular bipartite multigraph (m top, m bottom vertices)
--   - `PerfectMatching`  — port selection giving injective bottom assignment
--   - `RegBipartite.ofRegularGraph` — convert a `RegularGraph` to `RegBipartite`
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Konig/Defs.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Graph_Regular
import Definitions.Def_GirvingAKS_Graph_Graph

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Konig/Defs.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # König's Edge Coloring — Definitions

  Bipartite multigraph structures for König's edge coloring theorem.
  Used to prove depth bounds for expander-based halver networks.

  Main definitions:
  • `RegBipartite m d` — d-regular bipartite multigraph (m top, m bottom vertices)
  • `PerfectMatching`  — port selection giving injective bottom assignment
  • `RegBipartite.ofRegularGraph` — convert a `RegularGraph` to `RegBipartite`
-/


section


open Finset BigOperators


/-! **Regular Bipartite Multigraph** -/

/-- A d-regular bipartite multigraph: m top vertices, m bottom vertices,
    d ports per top vertex, and each bottom vertex has exactly d incoming edges.

    The `edges` function maps each (top vertex, port) pair to a bottom vertex.
    Top-regularity (degree d) is structural. Bottom-regularity is an axiom. -/
structure RegBipartite (m d : ℕ) where
  edges : Fin m → Fin d → Fin m
  bot_regular : ∀ u : Fin m,
    ((univ ×ˢ univ).filter (fun vp : Fin m × Fin d ↦ edges vp.1 vp.2 = u)).card = d


/-! **Perfect Matching** -/

/-- A perfect matching in a `RegBipartite`: a port selection for each top vertex
    such that the induced bottom assignment is injective (no two top vertices
    share a bottom vertex). -/
structure PerfectMatching {m d : ℕ} (B : RegBipartite m d) where
  portOf : Fin m → Fin d
  injective : Function.Injective (fun v ↦ B.edges v (portOf v))


/-! **Conversion from RegularGraph** -/

/-- The rotation map involution implies: for every bottom vertex u, the set
    of (v, p) with `G.neighbor v p = u` has exactly d elements. -/
theorem RegularGraph.neighbor_fiber_card {m d : ℕ} (G : RegularGraph m d) (u : Fin m) :
    ((univ ×ˢ univ).filter (fun vp : Fin m × Fin d ↦ G.neighbor vp.1 vp.2 = u)).card = d := by
  -- Bijection: q ↦ G.rot (u, q) maps {q : Fin d} → fiber {(v,p) | neighbor v p = u}
  -- with inverse (v, p) ↦ G.reversePort v p
  have key : ((univ ×ˢ univ).filter
      (fun vp : Fin m × Fin d ↦ G.neighbor vp.1 vp.2 = u)).card =
      (univ : Finset (Fin d)).card :=
    Finset.card_nbij' (fun vp ↦ G.reversePort vp.1 vp.2)
      (fun q ↦ G.rot (u, q))
      -- Forward: fiber → Fin d (reversePort lands in univ)
      (fun _ h ↦ Finset.mem_coe.mpr (mem_univ _))
      -- Backward: Fin d → fiber (rot lands in the fiber)
      (by
        intro q hq
        refine Finset.mem_coe.mpr (mem_filter.mpr ⟨Finset.mem_product.mpr ⟨mem_univ _, mem_univ _⟩, ?_⟩)
        show G.neighbor (G.rot (u, q)).1 (G.rot (u, q)).2 = u
        unfold RegularGraph.neighbor
        rw [Prod.mk.eta, G.rot_involution])
      -- Left inverse: rot ∘ (u, reversePort) recovers the pair
      (by
        intro ⟨v, p⟩ hvp
        have hvp' := (mem_filter.mp (Finset.mem_coe.mp hvp)).2
        -- hvp' : G.neighbor (v, p).1 (v, p).2 = u, i.e. (G.rot (v, p)).1 = u
        show G.rot (u, G.reversePort (v, p).1 (v, p).2) = (v, p)
        simp only [RegularGraph.reversePort]
        -- Goal: G.rot (u, (G.rot (v, p)).2) = (v, p)
        have hfst : (G.rot (v, p)).1 = u := by
          exact hvp'
        conv_lhs => rw [show (u, (G.rot (v, p)).2) = G.rot (v, p) from
          Prod.ext hfst.symm rfl]
        exact G.rot_involution (v, p))
      -- Right inverse: reversePort ∘ rot = projection
      (by
        intro q _
        show G.reversePort (G.rot (u, q)).1 (G.rot (u, q)).2 = q
        simp only [RegularGraph.reversePort, Prod.mk.eta]
        exact congr_arg Prod.snd (G.rot_involution (u, q)))
  rw [key, card_univ, Fintype.card_fin]

/-- Convert a `RegularGraph` to a `RegBipartite`. The edges function is
    `G.neighbor` and bottom-regularity follows from the rotation involution. -/
def RegBipartite.ofRegularGraph {m d : ℕ} (G : RegularGraph m d) : RegBipartite m d where
  edges v p := G.neighbor v p
  bot_regular := G.neighbor_fiber_card


/-! **Irregular HalfEdgeGraph → Regular Bipartite** -/

/-- Enumerate the half-edges sourced at vertex `v`, in increasing order by index. -/
noncomputable def HalfEdgeGraph.nthEdge {n : ℕ} (G : HalfEdgeGraph n) (v : Fin n)
    (p : Fin (G.deg v)) : Fin G.halfs :=
  ((univ.filter (G.src · = v)).orderIsoOfFin rfl p).val

theorem HalfEdgeGraph.nthEdge_src {n : ℕ} (G : HalfEdgeGraph n) (v : Fin n) (p : Fin (G.deg v)) :
    G.src (G.nthEdge v p) = v :=
  (mem_filter.mp ((univ.filter (G.src · = v)).orderIsoOfFin rfl p).prop).2

theorem HalfEdgeGraph.nthEdge_injective {n : ℕ} (G : HalfEdgeGraph n) (v : Fin n) :
    Function.Injective (G.nthEdge v) :=
  fun _ _ h ↦ ((univ.filter (G.src · = v)).orderIsoOfFin rfl).toEquiv.injective
    (Subtype.val_injective h)

theorem HalfEdgeGraph.nthEdge_surj {n : ℕ} (G : HalfEdgeGraph n) (v : Fin n) (e : Fin G.halfs)
    (he : G.src e = v) : ∃ p : Fin (G.deg v), G.nthEdge v p = e := by
  have he' : e ∈ univ.filter (G.src · = v) := mem_filter.mpr ⟨mem_univ e, he⟩
  obtain ⟨p, hp⟩ := ((univ.filter (G.src · = v)).orderIsoOfFin rfl).toEquiv.surjective ⟨e, he'⟩
  exact ⟨p, congr_arg Subtype.val hp⟩

/-- The port index of half-edge `e` at its source vertex (inverse of `nthEdge`). -/
noncomputable def HalfEdgeGraph.edgePort {n : ℕ} (G : HalfEdgeGraph n) (v : Fin n) (e : Fin G.halfs)
    (he : G.src e = v) : Fin (G.deg v) :=
  ((univ.filter (G.src · = v)).orderIsoOfFin rfl).toEquiv.symm
    ⟨e, mem_filter.mpr ⟨mem_univ e, he⟩⟩

theorem HalfEdgeGraph.nthEdge_edgePort {n : ℕ} (G : HalfEdgeGraph n) (v : Fin n) (e : Fin G.halfs)
    (he : G.src e = v) : G.nthEdge v (G.edgePort v e he) = e := by
  set s := univ.filter (G.src · = v)
  set iso := s.orderIsoOfFin rfl
  show (iso (iso.toEquiv.symm ⟨e, mem_filter.mpr ⟨mem_univ e, he⟩⟩)).val = e
  have h := iso.toEquiv.apply_symm_apply ⟨e, mem_filter.mpr ⟨mem_univ e, he⟩⟩
  exact congr_arg Subtype.val (by exact_mod_cast h)

theorem HalfEdgeGraph.edgePort_nthEdge {n : ℕ} (G : HalfEdgeGraph n) (v : Fin n) (p : Fin (G.deg v)) :
    G.edgePort v (G.nthEdge v p) (G.nthEdge_src v p) = p := by
  simp only [edgePort, nthEdge]
  exact (Finset.orderIsoOfFin _ rfl).symm_apply_apply p

/-- The number of half-edges targeting `u` equals `G.deg u` (rotation bijection). -/
theorem HalfEdgeGraph.card_target_filter {n : ℕ} (G : HalfEdgeGraph n) (u : Fin n) :
    (univ.filter (fun e ↦ G.target e = u)).card = G.deg u := by
  simp only [HalfEdgeGraph.deg]
  apply Finset.card_nbij' G.rot G.rot
  · intro e he
    simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at he ⊢
    exact he
  · intro e he
    simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at he ⊢
    show G.src (G.rot (G.rot e)) = u
    rw [G.rot_involution]; exact he
  · intro e _; exact G.rot_involution e
  · intro e _; exact G.rot_involution e

/-- The edges function for `ofGraph`: real half-edges for ports below `deg v`,
    self-loops for ports at or above `deg v`. -/
noncomputable def HalfEdgeGraph.padEdges {m : ℕ} (G : HalfEdgeGraph m) (Δ : ℕ)
    (v : Fin m) (p : Fin Δ) : Fin m :=
  if h : p.val < G.deg v then G.target (G.nthEdge v ⟨p.val, h⟩) else v

/-- Forward bijection map: fiber(u) → Fin Δ.
    Real (v, p): find the port of `rot(nthEdge v p)` at vertex u.
    Dummy (v, p): return p. -/
private noncomputable def HalfEdgeGraph.ofGraphFwd {m : ℕ} (G : HalfEdgeGraph m) (Δ : ℕ)
    (h_ub : ∀ v, G.deg v ≤ Δ) (u : Fin m) (v : Fin m) (p : Fin Δ) : Fin Δ :=
  if hp : p.val < G.deg v then
    if ht : G.target (G.nthEdge v ⟨p.val, hp⟩) = u then
      ⟨(G.edgePort u (G.rot (G.nthEdge v ⟨p.val, hp⟩)) ht).val,
       Nat.lt_of_lt_of_le (G.edgePort u _ ht).isLt (h_ub u)⟩
    else p
  else p

/-- Backward bijection map: Fin Δ → fiber(u).
    q < deg(u): target(nthEdge u q) paired with its port.
    q ≥ deg(u): (u, q) as dummy self-loop. -/
private noncomputable def HalfEdgeGraph.ofGraphBwd {m : ℕ} (G : HalfEdgeGraph m) (Δ : ℕ)
    (h_ub : ∀ v, G.deg v ≤ Δ) (u : Fin m) (q : Fin Δ) : Fin m × Fin Δ :=
  if hq : q.val < G.deg u then
    let e := G.nthEdge u ⟨q.val, hq⟩
    let p := G.edgePort (G.target e) (G.rot e) rfl
    (G.target e, ⟨p.val, Nat.lt_of_lt_of_le p.isLt (h_ub _)⟩)
  else (u, q)

private theorem HalfEdgeGraph.ofGraphBwd_mem {m : ℕ} (G : HalfEdgeGraph m) (Δ : ℕ)
    (h_ub : ∀ v, G.deg v ≤ Δ) (u : Fin m) (q : Fin Δ) :
    G.padEdges Δ (G.ofGraphBwd Δ h_ub u q).1 (G.ofGraphBwd Δ h_ub u q).2 = u := by
  simp only [ofGraphBwd]
  split
  · -- q < deg u
    rename_i hq
    set e := G.nthEdge u ⟨q.val, hq⟩
    simp only [padEdges]
    set p := G.edgePort (G.target e) (G.rot e) rfl
    rw [dif_pos p.isLt]
    show G.target (G.nthEdge (G.target e) ⟨p.val, p.isLt⟩) = u
    conv_lhs => rw [show (⟨p.val, p.isLt⟩ : Fin (G.deg (G.target e))) = p from rfl,
      G.nthEdge_edgePort (G.target e) (G.rot e) rfl]
    show G.src (G.rot (G.rot e)) = u
    rw [G.rot_involution]; exact G.nthEdge_src u ⟨q.val, hq⟩
  · -- q ≥ deg u
    rename_i hq
    simp only [padEdges]
    rw [dif_neg hq]

/-- Key lemma: `edgePort` respects equality of half-edges. -/
private theorem HalfEdgeGraph.edgePort_congr {n : ℕ} (G : HalfEdgeGraph n) (v : Fin n)
    (e₁ e₂ : Fin G.halfs) (h₁ : G.src e₁ = v) (h₂ : G.src e₂ = v) (heq : e₁ = e₂) :
    G.edgePort v e₁ h₁ = G.edgePort v e₂ h₂ := by
  subst heq; rfl

/-- Composing edgePort with nthEdge via an intermediate equality. -/
private theorem HalfEdgeGraph.edgePort_eq_of_nthEdge_eq {n : ℕ} (G : HalfEdgeGraph n) (v : Fin n)
    (e : Fin G.halfs) (he : G.src e = v) (q : Fin (G.deg v)) (hq : e = G.nthEdge v q) :
    G.edgePort v e he = q := by
  have : G.edgePort v e he = G.edgePort v (G.nthEdge v q) (G.nthEdge_src v q) :=
    G.edgePort_congr v e (G.nthEdge v q) he (G.nthEdge_src v q) hq
  rw [this, G.edgePort_nthEdge]

/-- Val-level version bridging across a vertex equality. -/
private theorem HalfEdgeGraph.edgePort_val_eq {n : ℕ} (G : HalfEdgeGraph n) (v w : Fin n)
    (e : Fin G.halfs) (he : G.src e = v) (hvw : v = w) (q : Fin (G.deg w))
    (hq : e = G.nthEdge w q) :
    (G.edgePort v e he).val = q.val := by
  subst hvw
  exact congr_arg Fin.val (G.edgePort_eq_of_nthEdge_eq v e he q hq)

private theorem HalfEdgeGraph.ofGraph_left_inv {m : ℕ} (G : HalfEdgeGraph m) (Δ : ℕ)
    (h_ub : ∀ v, G.deg v ≤ Δ) (u : Fin m) (q : Fin Δ) :
    G.ofGraphFwd Δ h_ub u (G.ofGraphBwd Δ h_ub u q).1 (G.ofGraphBwd Δ h_ub u q).2 = q := by
  unfold ofGraphBwd
  split
  · -- q < deg u: real edge
    rename_i hq
    simp only [ofGraphFwd]
    set e := G.nthEdge u ⟨q.val, hq⟩
    set p := G.edgePort (G.target e) (G.rot e) rfl
    rw [dif_pos p.isLt]
    have ht : G.target (G.nthEdge (G.target e) ⟨p.val, p.isLt⟩) = u := by
      conv_lhs => rw [show (⟨p.val, p.isLt⟩ : Fin _) = p from rfl,
        G.nthEdge_edgePort (G.target e) (G.rot e) rfl]
      show G.src (G.rot (G.rot e)) = u
      rw [G.rot_involution]; exact G.nthEdge_src u _
    rw [dif_pos ht]
    apply Fin.ext
    show (G.edgePort u (G.rot (G.nthEdge (G.target e) ⟨p.val, p.isLt⟩)) ht).val = q.val
    have key : G.rot (G.nthEdge (G.target e) ⟨p.val, p.isLt⟩) = G.nthEdge u ⟨q.val, hq⟩ := by
      conv_lhs => rw [show (⟨p.val, p.isLt⟩ : Fin _) = p from rfl,
        G.nthEdge_edgePort (G.target e) (G.rot e) rfl]
      exact G.rot_involution e
    exact congr_arg Fin.val (G.edgePort_eq_of_nthEdge_eq u _ ht ⟨q.val, hq⟩ key)
  · -- q ≥ deg u: dummy
    rename_i hq
    simp only [ofGraphFwd]
    rw [dif_neg hq]

private theorem HalfEdgeGraph.ofGraph_right_inv {m : ℕ} (G : HalfEdgeGraph m) (Δ : ℕ)
    (h_ub : ∀ v, G.deg v ≤ Δ) (u v : Fin m) (p : Fin Δ)
    (hvp : G.padEdges Δ v p = u) :
    G.ofGraphBwd Δ h_ub u (G.ofGraphFwd Δ h_ub u v p) = (v, p) := by
  simp only [padEdges] at hvp
  unfold ofGraphFwd
  split
  · -- p < deg v: real edge
    rename_i hp
    rw [dif_pos hp] at hvp
    rw [dif_pos hvp]
    set e := G.nthEdge v ⟨p.val, hp⟩
    set q := G.edgePort u (G.rot e) hvp
    -- Show the result of ofGraphBwd applied to q
    show G.ofGraphBwd Δ h_ub u ⟨q.val, Nat.lt_of_lt_of_le q.isLt (h_ub u)⟩ = (v, p)
    simp only [ofGraphBwd, dif_pos q.isLt]
    -- nthEdge u q = rot(e)
    have hq_eq : G.nthEdge u ⟨q.val, q.isLt⟩ = G.rot e := by
      have : (⟨q.val, q.isLt⟩ : Fin (G.deg u)) = q := rfl
      rw [this]; exact G.nthEdge_edgePort u (G.rot e) hvp
    -- target(nthEdge u q) = target(rot e) = src(rot(rot e)) = src e = v
    have htgt : G.target (G.nthEdge u ⟨q.val, q.isLt⟩) = v := by
      rw [hq_eq]; show G.src (G.rot (G.rot e)) = v
      rw [G.rot_involution]; exact G.nthEdge_src v _
    -- rot(nthEdge u q) = rot(rot e) = e = nthEdge v ⟨p.val, hp⟩
    have hrot_eq : G.rot (G.nthEdge u ⟨q.val, q.isLt⟩) = G.nthEdge v ⟨p.val, hp⟩ := by
      rw [hq_eq, G.rot_involution]
    -- edgePort.val at target = p.val
    have hport_val := G.edgePort_val_eq
      (G.target (G.nthEdge u ⟨q.val, q.isLt⟩)) v
      (G.rot (G.nthEdge u ⟨q.val, q.isLt⟩)) rfl htgt ⟨p.val, hp⟩ hrot_eq
    -- Combine: (target e', ⟨port.val, ...⟩) = (v, p)
    refine Prod.ext htgt ?_
    exact Fin.ext hport_val
  · -- p ≥ deg v: dummy
    rename_i hp
    rw [dif_neg hp] at hvp
    subst hvp
    unfold ofGraphBwd
    rw [dif_neg hp]

/-- Build a Δ-regular bipartite multigraph from a general graph with max degree ≤ Δ.
    Real edges use `nthEdge`; dummy edges are self-loops (vertex `v` maps to itself). -/
noncomputable def RegBipartite.ofGraph {m : ℕ} (G : HalfEdgeGraph m) (Δ : ℕ)
    (h_ub : ∀ v, G.deg v ≤ Δ) : RegBipartite m Δ where
  edges := G.padEdges Δ
  bot_regular u := by
    conv_rhs => rw [show Δ = (univ : Finset (Fin Δ)).card from
      by rw [card_univ, Fintype.card_fin]]
    exact Finset.card_nbij' (fun ⟨v, p⟩ ↦ G.ofGraphFwd Δ h_ub u v p)
      (G.ofGraphBwd Δ h_ub u)
      (fun _ _ ↦ mem_coe.mpr (mem_univ _))
      (fun q _ ↦ by
        simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_product, mem_univ, true_and]
        exact G.ofGraphBwd_mem Δ h_ub u q)
      (fun ⟨v, p⟩ hvp ↦ by
        have hvp' := (mem_filter.mp (mem_coe.mp hvp)).2
        exact G.ofGraph_right_inv Δ h_ub u v p hvp')
      (fun q _ ↦ G.ofGraph_left_inv Δ h_ub u q)

/-- For real ports (p < deg v), `ofGraph` returns the target of the corresponding edge. -/
theorem RegBipartite.ofGraph_real {m : ℕ} (G : HalfEdgeGraph m) (Δ : ℕ)
    (h_ub : ∀ v, G.deg v ≤ Δ) (v : Fin m) (p : Fin Δ) (hp : p.val < G.deg v) :
    (RegBipartite.ofGraph G Δ h_ub).edges v p = G.target (G.nthEdge v ⟨p.val, hp⟩) := by
  show G.padEdges Δ v p = _; simp only [HalfEdgeGraph.padEdges, dif_pos hp]

/-- For dummy ports (p ≥ deg v), `ofGraph` returns `v` itself. -/
theorem RegBipartite.ofGraph_dummy {m : ℕ} (G : HalfEdgeGraph m) (Δ : ℕ)
    (h_ub : ∀ v, G.deg v ≤ Δ) (v : Fin m) (p : Fin Δ) (hp : ¬(p.val < G.deg v)) :
    (RegBipartite.ofGraph G Δ h_ub).edges v p = v := by
  show G.padEdges Δ v p = _; simp only [HalfEdgeGraph.padEdges, dif_neg hp]

/-- Every real half-edge of `G` appears in `ofGraph` at some port. -/
theorem RegBipartite.ofGraph_covers {m : ℕ} (G : HalfEdgeGraph m) (Δ : ℕ)
    (h_ub : ∀ v, G.deg v ≤ Δ) (e : Fin G.halfs) :
    ∃ p : Fin Δ, (RegBipartite.ofGraph G Δ h_ub).edges (G.src e) p = G.target e := by
  obtain ⟨q, hq⟩ := G.nthEdge_surj (G.src e) e rfl
  have hqΔ : q.val < Δ := Nat.lt_of_lt_of_le q.isLt (h_ub (G.src e))
  refine ⟨⟨q.val, hqΔ⟩, ?_⟩
  show G.padEdges Δ (G.src e) ⟨q.val, hqΔ⟩ = G.target e
  simp only [HalfEdgeGraph.padEdges, dif_pos q.isLt, hq]

end


