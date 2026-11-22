-- Prove2me | Definitions.Def_GirvingAKS_Konig_ContractedBipartite
-- name    : GirvingAKS_Konig_ContractedBipartite
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:32:27.131134+00:00
-- url     : https://prove2.me/theorems/4d9b51f5-d35a-410b-904d-28557927fc14
-- title:
--   AKS sorting networks (Seiferas port) — Computable RegBipartite from Contracted Regular HalfEdgeGraph
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Konig/ContractedBipartite.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** For a `d`-regular graph `G` on `N` vertices contracted via `s : Fin N → Fin m`, builds a computable `RegBipartite m Δ` where `Δ ≥ fiberSize(v) * d` for all `v`. Edges at vertex `v` are enumerated by iterating the fiber `{u : Fin N | s(u) = v}` (sorted by `Fin.val`) and all `d` ports per fiber element. Padding ports map to self-loops.
--
--   This avoids the noncomputable `HalfEdgeGraph.nthEdge`/`orderIsoOfFin` path used by `RegBipartite.ofGraph`.
--
--   Key results:
--
--   - `contractedBipartite`: computable `RegBipartite m Δ`
--   - `contractedBipartite_covers`: every original edge appears at some port
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Konig/ContractedBipartite.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Konig_Defs
import Definitions.Def_GirvingAKS_Graph_Contract

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Konig/ContractedBipartite.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Computable RegBipartite from Contracted Regular HalfEdgeGraph

  For a `d`-regular graph `G` on `N` vertices contracted via `s : Fin N → Fin m`,
  builds a computable `RegBipartite m Δ` where `Δ ≥ fiberSize(v) * d` for all `v`.
  Edges at vertex `v` are enumerated by iterating the fiber `{u : Fin N | s(u) = v}`
  (sorted by `Fin.val`) and all `d` ports per fiber element. Padding ports
  map to self-loops.

  This avoids the noncomputable `HalfEdgeGraph.nthEdge`/`orderIsoOfFin` path used
  by `RegBipartite.ofGraph`.

  Key results:
  - `contractedBipartite`: computable `RegBipartite m Δ`
  - `contractedBipartite_covers`: every original edge appears at some port
-/


section


open Finset BigOperators


/-! **Fiber Enumeration** -/

/-- The sorted fiber of `v` under the contraction map `s`. -/
def fiberSorted {N m : ℕ} (s : Fin N → Fin m) (v : Fin m) : List (Fin N) :=
  (univ.filter (fun u : Fin N ↦ s u = v)).sort (· ≤ ·)

theorem fiberSorted_nodup {N m : ℕ} (s : Fin N → Fin m) (v : Fin m) :
    (fiberSorted s v).Nodup :=
  Finset.sort_nodup _ _

theorem fiberSorted_length {N m : ℕ} (s : Fin N → Fin m) (v : Fin m) :
    (fiberSorted s v).length = (univ.filter (fun u : Fin N ↦ s u = v)).card :=
  Finset.length_sort _

theorem fiberSorted_mem {N m : ℕ} (s : Fin N → Fin m) (v : Fin m)
    (u : Fin N) : u ∈ fiberSorted s v ↔ s u = v := by
  simp [fiberSorted, Finset.mem_sort, Finset.mem_filter]

/-- Index of `u` in the sorted fiber of `s u`. Uses `findIdx` with `BEq`. -/
def fiberIndex {N m : ℕ} (s : Fin N → Fin m) (u : Fin N) : ℕ :=
  (fiberSorted s (s u)).findIdx (· == u)

theorem fiberIndex_lt {N m : ℕ} (s : Fin N → Fin m) (u : Fin N) :
    fiberIndex s u < (fiberSorted s (s u)).length := by
  apply List.findIdx_lt_length_of_exists
  exact ⟨u, (fiberSorted_mem s (s u) u).mpr rfl, by simp⟩

/-- The element at `fiberIndex` position in the sorted fiber equals `u`. -/
theorem fiberSorted_get_fiberIndex {N m : ℕ} (s : Fin N → Fin m) (u : Fin N) :
    (fiberSorted s (s u))[(fiberIndex s u)]'(fiberIndex_lt s u) = u := by
  have h := (List.findIdx_eq (fiberIndex_lt s u)).mp rfl
  simp at h; exact h.1

/-- The fiber index of the `i`-th element in the sorted fiber is `i`. -/
theorem fiberIndex_of_get {N m : ℕ} (s : Fin N → Fin m) (v : Fin m)
    (i : ℕ) (hi : i < (fiberSorted s v).length) :
    fiberIndex s ((fiberSorted s v)[i]'hi) = i := by
  have h_sv : s ((fiberSorted s v)[i]'hi) = v :=
    (fiberSorted_mem s v _).mp (List.getElem_mem hi)
  unfold fiberIndex
  rw [show fiberSorted s (s ((fiberSorted s v)[i]'hi)) = fiberSorted s v from by rw [h_sv]]
  apply (List.findIdx_eq hi).mpr
  refine ⟨by simp [BEq.beq], fun j hji => ?_⟩
  simp only [BEq.beq]
  rw [decide_eq_false_iff_not]
  exact fun heq => absurd ((fiberSorted_nodup s v).getElem_inj_iff.mp heq) (by omega)

/-- The `s`-image of a fiber element equals `v`. -/
theorem fiberSorted_s_eq {N m : ℕ} (s : Fin N → Fin m) (v : Fin m)
    (i : ℕ) (hi : i < (fiberSorted s v).length) :
    s ((fiberSorted s v)[i]'hi) = v :=
  (fiberSorted_mem s v _).mp (List.getElem_mem hi)


/-! **Contracted Bipartite Construction** -/

/-- The edges function for the contracted bipartite graph.
    Port `p` decomposes as `(p / d, p % d)` = `(fiber_index, graph_port)`.
    If the fiber index is within the fiber of `v`, we follow the edge in `G`
    and apply the contraction map. Otherwise, self-loop. -/
def contractedEdges {N d m : ℕ} (G : RegularGraph N d)
    (s : Fin N → Fin m) (Δ : ℕ) (v : Fin m) (p : Fin Δ) : Fin m :=
  let fiber := fiberSorted s v
  let fiberIdx := p.val / d
  let port := p.val % d
  if hf : fiberIdx < fiber.length then
    if hd : port < d then
      s (G.neighbor (fiber.get ⟨fiberIdx, hf⟩) ⟨port, hd⟩)
    else v
  else v


/-! **Bot-regular bijection maps** -/

/-- Any `fiberIndex * d + j` is within `Δ` when `j < d`. -/
theorem fiberIndex_fin_bound {N d m : ℕ}
    (s : Fin N → Fin m) (Δ : ℕ)
    (h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ)
    (u' : Fin N) (j : Fin d) :
    fiberIndex s u' * d + j.val < Δ := by
  have := fiberIndex_lt s u'
  calc fiberIndex s u' * d + j.val
      < fiberIndex s u' * d + d := by omega
    _ = (fiberIndex s u' + 1) * d := by ring
    _ ≤ (fiberSorted s (s u')).length * d := Nat.mul_le_mul_right d this
    _ ≤ Δ := h_ub (s u')

/-- Forward map for `bot_regular`: given `(v, p)` in the filter, compute the
    corresponding port in `Fin Δ` via the rotation involution. -/
def botRegFwd {N d m : ℕ} (G : RegularGraph N d)
    (s : Fin N → Fin m) (Δ : ℕ)
    (h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ)
    (hd_pos : 0 < d) (vp : Fin m × Fin Δ) : Fin Δ :=
  let v := vp.1; let p := vp.2
  if hp : p.val / d < (fiberSorted s v).length then
    let v' := (fiberSorted s v)[p.val / d]'hp
    let port : Fin d := ⟨p.val % d, Nat.mod_lt _ hd_pos⟩
    let u' := G.neighbor v' port
    ⟨fiberIndex s u' * d + (G.reversePort v' port).val,
     fiberIndex_fin_bound s Δ h_ub u' (G.reversePort v' port)⟩
  else p

/-- Backward map for `bot_regular`: given a port `q : Fin Δ`, compute the
    source edge `(v, p)` via fiber lookup and rotation. -/
def botRegBwd {N d m : ℕ} (G : RegularGraph N d)
    (s : Fin N → Fin m) (Δ : ℕ)
    (h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ)
    (hd_pos : 0 < d) (u : Fin m) (q : Fin Δ) : Fin m × Fin Δ :=
  if hq : q.val < (fiberSorted s u).length * d then
    let fIdx := q.val / d
    let port := q.val % d
    have hfIdx : fIdx < (fiberSorted s u).length := by
      rw [Nat.div_lt_iff_lt_mul hd_pos]; exact hq
    let u' := (fiberSorted s u)[fIdx]'hfIdx
    let vp := G.rot (u', ⟨port, Nat.mod_lt _ hd_pos⟩)
    (s vp.1, ⟨fiberIndex s vp.1 * d + vp.2.val,
      fiberIndex_fin_bound s Δ h_ub vp.1 vp.2⟩)
  else (u, q)

theorem botRegFwd_pos {N d m : ℕ} {G : RegularGraph N d}
    {s : Fin N → Fin m} {Δ : ℕ}
    {h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ}
    {hd_pos : 0 < d} {v : Fin m} {p : Fin Δ}
    (hp : p.val / d < (fiberSorted s v).length) :
    botRegFwd G s Δ h_ub hd_pos (v, p) =
      ⟨fiberIndex s (G.neighbor ((fiberSorted s v)[p.val / d]'hp) ⟨p.val % d, Nat.mod_lt _ hd_pos⟩) * d +
        (G.reversePort ((fiberSorted s v)[p.val / d]'hp) ⟨p.val % d, Nat.mod_lt _ hd_pos⟩).val,
       fiberIndex_fin_bound s Δ h_ub _ _⟩ := by
  simp only [botRegFwd, dif_pos hp]

theorem botRegFwd_neg {N d m : ℕ} {G : RegularGraph N d}
    {s : Fin N → Fin m} {Δ : ℕ}
    {h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ}
    {hd_pos : 0 < d} {v : Fin m} {p : Fin Δ}
    (hp : ¬(p.val / d < (fiberSorted s v).length)) :
    botRegFwd G s Δ h_ub hd_pos (v, p) = p := by
  simp only [botRegFwd, dif_neg hp]

theorem botRegBwd_pos {N d m : ℕ} {G : RegularGraph N d}
    {s : Fin N → Fin m} {Δ : ℕ}
    {h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ}
    {hd_pos : 0 < d} {u : Fin m} {q : Fin Δ}
    (hq : q.val < (fiberSorted s u).length * d) :
    botRegBwd G s Δ h_ub hd_pos u q =
      let hfIdx : q.val / d < (fiberSorted s u).length :=
        (Nat.div_lt_iff_lt_mul hd_pos).mpr hq
      let u' := (fiberSorted s u)[q.val / d]'hfIdx
      let vp := G.rot (u', ⟨q.val % d, Nat.mod_lt _ hd_pos⟩)
      (s vp.1, ⟨fiberIndex s vp.1 * d + vp.2.val,
        fiberIndex_fin_bound s Δ h_ub _ _⟩) := by
  simp only [botRegBwd, dif_pos hq]

theorem botRegBwd_neg {N d m : ℕ} {G : RegularGraph N d}
    {s : Fin N → Fin m} {Δ : ℕ}
    {h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ}
    {hd_pos : 0 < d} {u : Fin m} {q : Fin Δ}
    (hq : ¬(q.val < (fiberSorted s u).length * d)) :
    botRegBwd G s Δ h_ub hd_pos u q = (u, q) := by
  simp only [botRegBwd, dif_neg hq]


/-- Roundtrip: `botRegFwd (botRegBwd u q) = q` in the real case. -/
private theorem botRegFwd_botRegBwd_real {N d m : ℕ} (G : RegularGraph N d)
    (s : Fin N → Fin m) (Δ : ℕ)
    (h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ)
    (hd_pos : 0 < d) (u : Fin m) (q : Fin Δ)
    (hq : q.val < (fiberSorted s u).length * d) :
    botRegFwd G s Δ h_ub hd_pos (botRegBwd G s Δ h_ub hd_pos u q) = q := by
  simp only [botRegBwd, dif_pos hq, botRegFwd]
  -- After unfolding both, goal has a dif from botRegFwd
  split
  · -- Real case: the botRegFwd condition holds
    rename_i hcond
    apply Fin.ext
    -- Strip Fin.val wrapper to get pure Nat goal
    dsimp only []
    -- The goal involves nested div/mod, fiber lookups, and rot
    -- Step 1: Simplify the fiber access index via div/mod
    have hfIdx : q.val / d < (fiberSorted s u).length :=
      (Nat.div_lt_iff_lt_mul hd_pos).mpr hq
    set u' := (fiberSorted s u)[q.val / d]'hfIdx
    set port_q : Fin d := ⟨q.val % d, Nat.mod_lt _ hd_pos⟩
    set vp := G.rot (u', port_q)
    have hdiv : (fiberIndex s vp.1 * d + vp.2.val) / d = fiberIndex s vp.1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd_pos,
        Nat.div_eq_of_lt vp.2.isLt]; omega
    have hmod : (fiberIndex s vp.1 * d + vp.2.val) % d = vp.2.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt vp.2.isLt]
    -- Step 2: The fiber access at the div index gives vp.1
    have h_get : ∀ (j : Nat) (hj : j < (fiberSorted s (s vp.1)).length),
        j = fiberIndex s vp.1 → (fiberSorted s (s vp.1))[j]'hj = vp.1 :=
      fun j hj heq => by subst heq; exact fiberSorted_get_fiberIndex s vp.1
    -- Step 3: The mod gives the port
    have h_port : ∀ (k : Nat) (hk : k < d),
        k = vp.2.val → (⟨k, hk⟩ : Fin d) = vp.2 :=
      fun k hk heq => Fin.ext heq
    -- Step 4: Rewrite fiber access and port in the goal
    rw [h_get _ _ hdiv, h_port _ _ hmod]
    -- Goal: fiberIndex s (G.neighbor vp.1 vp.2) * d + (G.reversePort vp.1 vp.2).val = q.val
    -- Step 5: Rot involution: G.rot vp = (u', port_q)
    have h_rot_inv : G.rot vp = (u', port_q) := G.rot_involution _
    show fiberIndex s (G.rot vp).1 * d + (G.rot vp).2.val = q.val
    rw [h_rot_inv]
    -- Goal: fiberIndex s u' * d + port_q.val = q.val
    have h_fidx : fiberIndex s u' = q.val / d := fiberIndex_of_get s u (q.val / d) hfIdx
    rw [h_fidx, show port_q.val = q.val % d from rfl, Nat.mul_comm]
    exact Nat.div_add_mod q.val d
  · -- Contradiction: the botRegFwd condition must hold
    rename_i hcond; exfalso; apply hcond
    have hfIdx : q.val / d < (fiberSorted s u).length :=
      (Nat.div_lt_iff_lt_mul hd_pos).mpr hq
    set u' := (fiberSorted s u)[q.val / d]'hfIdx
    set port_q : Fin d := ⟨q.val % d, Nat.mod_lt _ hd_pos⟩
    set vp := G.rot (u', port_q)
    have hdiv : (fiberIndex s vp.1 * d + vp.2.val) / d = fiberIndex s vp.1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd_pos,
        Nat.div_eq_of_lt vp.2.isLt]; omega
    rw [hdiv]; exact fiberIndex_lt s vp.1


/-! **Contracted Bipartite HalfEdgeGraph** -/

/-- Build a computable `RegBipartite` from a contracted regular graph.
    Requires `Δ` to be at least `fiberSize(v) * d` for every `v`. -/
def contractedBipartite {N d m : ℕ} (G : RegularGraph N d)
    (s : Fin N → Fin m) (Δ : ℕ)
    (h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ) :
    RegBipartite m Δ where
  edges := contractedEdges G s Δ
  bot_regular u := by
    -- Bijection between Fin Δ and {(v,p) | contractedEdges v p = u}
    conv_rhs => rw [show Δ = (univ : Finset (Fin Δ)).card from
      by rw [card_univ, Fintype.card_fin]]
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · -- d = 0: all edges are self-loops, trivial bijection
      exact Finset.card_nbij' (fun vp ↦ vp.2) (fun q ↦ (u, q))
        (fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _))
        (fun q _ ↦ by
          simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_univ, true_and, contractedEdges, Nat.div_zero, Nat.mod_zero]
          split_ifs <;> [omega; rfl; rfl])
        (fun ⟨v, p⟩ hvp ↦ by
          simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_univ, true_and, contractedEdges, Nat.div_zero, Nat.mod_zero] at hvp
          have : v = u := by split_ifs at hvp <;> [omega; exact hvp; exact hvp]
          subst this; rfl)
        (fun _ _ ↦ rfl)
    · -- d > 0: rotation involution argument
      refine Finset.card_nbij'
        (botRegFwd G s Δ h_ub hd_pos)
        (botRegBwd G s Δ h_ub hd_pos u)
        ?_ ?_ ?_ ?_
      · -- Obligation 1: i maps filter into univ (trivial)
        intro _ _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
      · -- Obligation 2: j maps univ into filter
        intro q _
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product]
        by_cases hq : q.val < (fiberSorted s u).length * d
        · -- Real case
          rw [botRegBwd_pos hq]
          have hfIdx : q.val / d < (fiberSorted s u).length :=
            (Nat.div_lt_iff_lt_mul hd_pos).mpr hq
          set u' := (fiberSorted s u)[q.val / d]'hfIdx
          set vp := G.rot (u', ⟨q.val % d, Nat.mod_lt _ hd_pos⟩)
          show contractedEdges G s Δ (s vp.1) _ = u
          simp only [contractedEdges]
          set idx := fiberIndex s vp.1
          have hidx_lt := fiberIndex_lt s vp.1
          have hdiv : (idx * d + vp.2.val) / d = idx := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd_pos,
              Nat.div_eq_of_lt vp.2.isLt]; omega
          have hmod : (idx * d + vp.2.val) % d = vp.2.val := by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt vp.2.isLt]
          rw [hdiv, hmod, dif_pos hidx_lt, dif_pos vp.2.isLt]
          have h_get := fiberSorted_get_fiberIndex s vp.1
          conv_lhs => rw [show (List.get (fiberSorted s (s vp.1)) ⟨idx, hidx_lt⟩) =
            (fiberSorted s (s vp.1))[idx]'hidx_lt from List.get_eq_getElem ..]
          rw [h_get]
          have : G.neighbor vp.1 vp.2 = u' := by
            show (G.rot vp).1 = u'
            have := G.rot_involution (u', ⟨q.val % d, Nat.mod_lt _ hd_pos⟩)
            simp only [vp] at this ⊢; rw [this]
          rw [this]
          exact fiberSorted_s_eq s u (q.val / d) hfIdx
        · -- Padding case
          rw [botRegBwd_neg hq]
          show contractedEdges G s Δ u q = u
          simp only [contractedEdges]
          rw [dif_neg (by intro h; exact hq ((Nat.div_lt_iff_lt_mul hd_pos).mp h))]
      · -- Obligation 3: LeftInvOn j i on filter (j(i(vp)) = vp)
        intro ⟨v, p⟩ hvp
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product] at hvp
        by_cases hp : p.val / d < (fiberSorted s v).length
        · -- Real edge case
          rw [botRegFwd_pos hp]
          set v' := (fiberSorted s v)[p.val / d]'hp
          set port : Fin d := ⟨p.val % d, Nat.mod_lt _ hd_pos⟩
          set u' := G.neighbor v' port
          have hu' : s u' = u := by
            show s (G.neighbor v' port) = u
            have : contractedEdges G s Δ v p = u := hvp
            simp only [contractedEdges] at this
            rw [dif_pos hp, dif_pos port.isLt] at this
            exact this
          have h_real : fiberIndex s u' * d + (G.reversePort v' port).val <
              (fiberSorted s u).length * d := by
            have := fiberIndex_lt s u'
            rw [hu'] at this
            calc fiberIndex s u' * d + (G.reversePort v' port).val
                < fiberIndex s u' * d + d := by omega
              _ = (fiberIndex s u' + 1) * d := by ring
              _ ≤ (fiberSorted s u).length * d := Nat.mul_le_mul_right d this
          rw [botRegBwd_pos h_real]
          have hdiv' : (fiberIndex s u' * d + (G.reversePort v' port).val) / d =
              fiberIndex s u' := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd_pos,
              Nat.div_eq_of_lt (G.reversePort v' port).isLt]; omega
          have hmod' : (fiberIndex s u' * d + (G.reversePort v' port).val) % d =
              (G.reversePort v' port).val := by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right,
              Nat.mod_eq_of_lt (G.reversePort v' port).isLt]
          have hidx_in_u : fiberIndex s u' < (fiberSorted s u).length := by
            have := fiberIndex_lt s u'; simp only [hu'] at this; exact this
          have h_get_u' : (fiberSorted s u)[fiberIndex s u']'hidx_in_u = u' := by
            have h := fiberSorted_get_fiberIndex s u'
            simp only [hu'] at h; exact h
          have h_rot : G.rot (u', G.reversePort v' port) = (v', port) := by
            show G.rot (G.rot (v', port)) = (v', port)
            exact G.rot_involution (v', port)
          -- After botRegBwd_pos, the goal decomposes via div/mod
          have hv' : s v' = v := fiberSorted_s_eq s v (p.val / d) hp
          have hv'_idx : fiberIndex s v' = p.val / d := by
            show fiberIndex s ((fiberSorted s v)[p.val / d]'hp) = p.val / d
            exact fiberIndex_of_get s v (p.val / d) hp
          refine Prod.ext ?_ ?_
          · -- s(rot(u', reversePort).1) = v
            apply Fin.ext; simp only [hdiv', hmod']
            conv_lhs => rw [h_get_u']
            rw [h_rot]; exact congr_arg Fin.val hv'
          · -- fiberIndex(rot(u', reversePort).1) * d + rot(u', reversePort).2.val = p.val
            apply Fin.ext; simp only [hdiv', hmod']
            conv_lhs => rw [h_get_u']
            rw [h_rot]; rw [show (v', port).2 = port from rfl]
            show fiberIndex s v' * d + port.val = p.val
            rw [hv'_idx, show port.val = p.val % d from rfl, Nat.mul_comm]
            exact Nat.div_add_mod p.val d
        · -- Padding case: contractedEdges gives v, so v = u
          rw [botRegFwd_neg hp]
          have hv_eq : v = u := by
            have : contractedEdges G s Δ v p = u := hvp
            simp only [contractedEdges] at this
            rw [dif_neg (by exact hp)] at this
            exact this
          subst hv_eq
          -- j(p) takes else branch since p not in real range
          rw [botRegBwd_neg (fun h ↦ hp ((Nat.div_lt_iff_lt_mul hd_pos).mpr h))]
      · -- Obligation 4: RightInvOn j i on univ (i(j(q)) = q)
        intro q _
        by_cases hq : q.val < (fiberSorted s u).length * d
        · exact botRegFwd_botRegBwd_real G s Δ h_ub hd_pos u q hq
        · rw [botRegBwd_neg hq, botRegFwd_neg (fun h ↦ hq ((Nat.div_lt_iff_lt_mul hd_pos).mp h))]

/-- Every edge of the original graph appears at some port in the contracted bipartite.
    Specifically, for any `u₀ : Fin N` and port `p₀ : Fin d`, there exists a port
    `q : Fin Δ` such that `contractedEdges G s Δ (s u₀) q = s (G.neighbor u₀ p₀)`. -/
theorem contractedBipartite_covers {N d m : ℕ} (G : RegularGraph N d)
    (s : Fin N → Fin m) (Δ : ℕ)
    (h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ)
    (u₀ : Fin N) (p₀ : Fin d) :
    ∃ q : Fin Δ, (contractedBipartite G s Δ h_ub).edges (s u₀) q =
      s (G.neighbor u₀ p₀) := by
  -- The port q = fiberIndex(u₀) * d + p₀.val
  set idx := fiberIndex s u₀
  have hidx_lt := fiberIndex_lt s u₀
  have hq_lt : idx * d + p₀.val < Δ := by
    calc idx * d + p₀.val
        < idx * d + d := by omega
      _ = (idx + 1) * d := by ring
      _ ≤ (fiberSorted s (s u₀)).length * d := Nat.mul_le_mul_right d hidx_lt
      _ ≤ Δ := h_ub (s u₀)
  refine ⟨⟨idx * d + p₀.val, hq_lt⟩, ?_⟩
  show contractedEdges G s Δ (s u₀) ⟨idx * d + p₀.val, hq_lt⟩ =
    s (G.neighbor u₀ p₀)
  simp only [contractedEdges]
  have hd_pos : 0 < d := Fin.pos p₀
  have hdiv : (idx * d + p₀.val) / d = idx := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd_pos, Nat.div_eq_of_lt p₀.isLt]; omega
  have hmod : (idx * d + p₀.val) % d = p₀.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p₀.isLt]
  rw [hdiv, hmod]
  have hf : idx < (fiberSorted s (s u₀)).length := hidx_lt
  rw [dif_pos hf, dif_pos p₀.isLt]
  -- Need: fiber.get ⟨idx, hf⟩ = u₀
  have h_get : (fiberSorted s (s u₀)).get ⟨idx, hf⟩ = u₀ := by
    exact fiberSorted_get_fiberIndex s u₀
  simp only [h_get]

end


