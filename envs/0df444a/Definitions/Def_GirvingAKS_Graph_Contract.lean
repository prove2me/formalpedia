-- Prove2me | Definitions.Def_GirvingAKS_Graph_Contract
-- name    : GirvingAKS_Graph_Contract
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:32:01.150385+00:00
-- url     : https://prove2.me/theorems/ecb15235-1a78-4c4c-93c3-7ea455f5e83b
-- title:
--   AKS sorting networks (Seiferas port) — Contraction Degree Bounds and Equal-Fiber Contraction
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Graph/Contract.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** For a `d`-regular graph on `N` vertices contracted via `v ↦ v % n`:
--
--   - **General case:** degree lies in `[d · ⌊N/n⌋, d · (⌊N/n⌋ + 1)]`,
--
--   giving degree ratio ≤ 2 (HalfEdgeGraph Tanner → Halver pipeline).
--
--   - **Divisible case** (`n ∣ N`): all fibers have exactly `N/n` elements,
--
--   so the contracted graph is `(d * (N/n))`-regular. The rotation map encodes ports as `(fiber_position, original_port)` pairs.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Graph/Contract.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Graph_Graph
import Definitions.Def_GirvingAKS_Graph_Walk

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Graph/Contract.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Contraction Degree Bounds and Equal-Fiber Contraction

  For a `d`-regular graph on `N` vertices contracted via `v ↦ v % n`:
  - **General case:** degree lies in `[d · ⌊N/n⌋, d · (⌊N/n⌋ + 1)]`,
    giving degree ratio ≤ 2 (HalfEdgeGraph Tanner → Halver pipeline).
  - **Divisible case** (`n ∣ N`): all fibers have exactly `N/n` elements,
    so the contracted graph is `(d * (N/n))`-regular. The rotation map
    encodes ports as `(fiber_position, original_port)` pairs.
-/


section


open Finset BigOperators


/-! **Mod-n Fiber Size Bounds** -/

/-- Lower bound on mod-`n` fiber size: at least `⌊N/n⌋` values in `Fin N`
    are congruent to `u` mod `n`. -/
theorem mod_fiber_card_lb {N n : ℕ} (hn : 0 < n) (_hNn : n ≤ N) (u : Fin n) :
    N / n ≤ (univ.filter (fun v : Fin N ↦ v.val % n = u.val)).card := by
  set fiber := univ.filter (fun v : Fin N ↦ v.val % n = u.val)
  -- Inject Fin (N/n) into fiber via k ↦ u.val + k * n
  have h_lt : ∀ k : Fin (N / n), u.val + k.val * n < N := by
    intro k
    have hkn : k.val * n + n ≤ N := by
      calc k.val * n + n = (k.val + 1) * n := by ring
        _ ≤ (N / n) * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt k.isLt)
        _ ≤ N := Nat.div_mul_le_self N n
    linarith [u.isLt]
  let f : Fin (N / n) → Fin N := fun k ↦ ⟨u.val + k.val * n, h_lt k⟩
  have hf_inj : Function.Injective f := by
    intro k₁ k₂ h
    simp only [f, Fin.mk.injEq] at h
    ext
    have h_eq : k₁.val * n = k₂.val * n := by omega
    calc k₁.val = k₁.val * n / n := (Nat.mul_div_cancel _ hn).symm
      _ = k₂.val * n / n := by rw [h_eq]
      _ = k₂.val := Nat.mul_div_cancel _ hn
  have hf_mem : ∀ k, f k ∈ fiber := by
    intro k; simp only [f, fiber, mem_filter, mem_univ, true_and]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt u.isLt]
  calc N / n
      = (univ.image f).card := by
        rw [card_image_of_injective _ hf_inj, card_univ, Fintype.card_fin]
    _ ≤ fiber.card :=
        card_le_card (fun v hv ↦ by
          obtain ⟨k, _, rfl⟩ := mem_image.mp hv; exact hf_mem k)

/-- Upper bound on mod-`n` fiber size: at most `⌊N/n⌋ + 1` values in `Fin N`
    are congruent to `u` mod `n`. -/
theorem mod_fiber_card_ub {N n : ℕ} (_hn : 0 < n) (u : Fin n) :
    (univ.filter (fun v : Fin N ↦ v.val % n = u.val)).card ≤ N / n + 1 := by
  set fiber := univ.filter (fun v : Fin N ↦ v.val % n = u.val)
  -- Inject fiber into Fin (N/n + 1) via v ↦ v.val / n
  let g : Fin N → Fin (N / n + 1) := fun v ↦ ⟨v.val / n, by
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (le_of_lt v.isLt))⟩
  have hg_inj : Set.InjOn g fiber := by
    intro v₁ hv₁ v₂ hv₂ h
    simp only [g, Fin.mk.injEq] at h
    have hmod₁ : v₁.val % n = u.val := by simpa [fiber] using hv₁
    have hmod₂ : v₂.val % n = u.val := by simpa [fiber] using hv₂
    ext
    calc v₁.val
        = n * (v₁.val / n) + v₁.val % n := (Nat.div_add_mod v₁.val n).symm
      _ = n * (v₂.val / n) + v₂.val % n := by rw [h, hmod₁, hmod₂]
      _ = v₂.val := Nat.div_add_mod v₂.val n
  calc fiber.card
      ≤ (fiber.image g).card := le_of_eq (card_image_of_injOn hg_inj).symm
    _ ≤ (univ : Finset (Fin (N / n + 1))).card := card_le_card (subset_univ _)
    _ = N / n + 1 := by rw [card_univ, Fintype.card_fin]


/-- When `n ∣ N`, the mod-`n` fiber has exactly `N/n` elements. -/
theorem mod_fiber_card_exact {N n : ℕ} (hn : 0 < n) (hdvd : n ∣ N) (u : Fin n) :
    (univ.filter (fun v : Fin N ↦ v.val % n = u.val)).card = N / n := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- N = 0: Fin 0 is empty, fiber is empty, 0/n = 0
    simp
  · -- N > 0: n ∣ N and N > 0 implies n ≤ N
    have hNn : n ≤ N := Nat.le_of_dvd hN hdvd
    apply le_antisymm
    · -- Upper bound: inject fiber into Fin (N/n) via v ↦ v / n
      set fiber := univ.filter (fun v : Fin N ↦ v.val % n = u.val)
      have hq : 0 < N / n := Nat.div_pos hNn hn
      let g : Fin N → Fin (N / n) := fun v ↦ ⟨v.val / n, by
        apply Nat.div_lt_of_lt_mul
        rw [Nat.mul_comm, Nat.div_mul_cancel hdvd]; exact v.isLt⟩
      have hg_inj : Set.InjOn g fiber := by
        intro v₁ hv₁ v₂ hv₂ h
        simp only [g, Fin.mk.injEq] at h
        have hmod₁ : v₁.val % n = u.val := by simpa [fiber] using hv₁
        have hmod₂ : v₂.val % n = u.val := by simpa [fiber] using hv₂
        ext
        calc v₁.val
            = n * (v₁.val / n) + v₁.val % n := (Nat.div_add_mod v₁.val n).symm
          _ = n * (v₂.val / n) + v₂.val % n := by rw [h, hmod₁, hmod₂]
          _ = v₂.val := Nat.div_add_mod v₂.val n
      calc fiber.card
          ≤ (fiber.image g).card := le_of_eq (card_image_of_injOn hg_inj).symm
        _ ≤ (univ : Finset (Fin (N / n))).card := card_le_card (subset_univ _)
        _ = N / n := by rw [card_univ, Fintype.card_fin]
    · exact mod_fiber_card_lb hn hNn u


/-! **Regular HalfEdgeGraph Contraction Degree** -/

/-- The contracted degree of a `d`-regular graph via mod-`n` contraction
    equals `d` times the fiber size. -/
theorem RegularGraph.contract_mod_deg {N d n : ℕ} (G : RegularGraph N d) (hd : 0 < d)
    (hn : 0 < n) (u : Fin n) :
    (G.toGraph.contract (fun v : Fin N ↦ ⟨v.val % n, Nat.mod_lt _ hn⟩)).deg u =
    d * (univ.filter (fun v : Fin N ↦ v.val % n = u.val)).card := by
  rw [HalfEdgeGraph.contract_deg_eq_sum_fiber]
  have filter_eq : univ.filter
      (fun v : Fin N ↦ (⟨v.val % n, Nat.mod_lt v.val hn⟩ : Fin n) = u) =
      univ.filter (fun v : Fin N ↦ v.val % n = u.val) := by
    ext v; simp [Fin.ext_iff]
  rw [filter_eq]
  simp_rw [G.toGraph_deg hd]
  rw [sum_const, nsmul_eq_mul, mul_comm]; push_cast; ring

/-- Degree lower bound: `d · ⌊N/n⌋ ≤ contracted degree`. -/
theorem RegularGraph.contract_mod_deg_lb {N d n : ℕ} (G : RegularGraph N d) (hd : 0 < d)
    (hn : 0 < n) (hNn : n ≤ N) (u : Fin n) :
    d * (N / n) ≤
    (G.toGraph.contract (fun v : Fin N ↦ ⟨v.val % n, Nat.mod_lt _ hn⟩)).deg u := by
  rw [G.contract_mod_deg hd hn]
  exact Nat.mul_le_mul_left d (mod_fiber_card_lb hn hNn u)

/-- Degree upper bound: `contracted degree ≤ d · (⌊N/n⌋ + 1)`. -/
theorem RegularGraph.contract_mod_deg_ub {N d n : ℕ} (G : RegularGraph N d) (hd : 0 < d)
    (hn : 0 < n) (u : Fin n) :
    (G.toGraph.contract (fun v : Fin N ↦ ⟨v.val % n, Nat.mod_lt _ hn⟩)).deg u ≤
    d * (N / n + 1) := by
  rw [G.contract_mod_deg hd hn]
  exact Nat.mul_le_mul_left d (mod_fiber_card_ub hn u)

/-- Degree ratio bound: any vertex's degree is at most twice any other's.
    Since `⌊N/n⌋ ≥ 1` (from `n ≤ N`), we have `⌊N/n⌋ + 1 ≤ 2 · ⌊N/n⌋`. -/
theorem RegularGraph.contract_mod_deg_ratio {N d n : ℕ} (G : RegularGraph N d) (hd : 0 < d)
    (hn : 0 < n) (hNn : n ≤ N) (u₁ u₂ : Fin n) :
    (G.toGraph.contract (fun v : Fin N ↦ ⟨v.val % n, Nat.mod_lt _ hn⟩)).deg u₁ ≤
    2 * (G.toGraph.contract (fun v : Fin N ↦ ⟨v.val % n, Nat.mod_lt _ hn⟩)).deg u₂ := by
  have h1 := G.contract_mod_deg_ub hd hn (u := u₁)
  have h2 := G.contract_mod_deg_lb hd hn hNn (u := u₂)
  have hq : 1 ≤ N / n := Nat.div_pos hNn hn
  calc (G.toGraph.contract _).deg u₁
      ≤ d * (N / n + 1) := h1
    _ ≤ d * (2 * (N / n)) := by apply Nat.mul_le_mul_left; omega
    _ = 2 * (d * (N / n)) := by ring
    _ ≤ 2 * (G.toGraph.contract _).deg u₂ := Nat.mul_le_mul_left 2 h2


/-! **Equal-Fiber Contraction (Divisible Case)** -/

/-- Fiber vertex: the k-th vertex in fiber u is `u + k * m`. -/
def fiberVertex {N m : ℕ} (_hm : 0 < m) (hdvd : m ∣ N) (u : Fin m)
    (k : Fin (N / m)) : Fin N :=
  ⟨u.val + k.val * m, by
    calc u.val + k.val * m
        < m + k.val * m := by omega
      _ = (k.val + 1) * m := by ring
      _ ≤ (N / m) * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt k.isLt)
      _ = N := Nat.div_mul_cancel hdvd⟩

@[simp]
theorem fiberVertex_mod {N m : ℕ} (hm : 0 < m) (hdvd : m ∣ N) (u : Fin m)
    (k : Fin (N / m)) : (fiberVertex hm hdvd u k).val % m = u.val := by
  simp only [fiberVertex]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt u.isLt]

@[simp]
theorem fiberVertex_div {N m : ℕ} (hm : 0 < m) (hdvd : m ∣ N) (u : Fin m)
    (k : Fin (N / m)) : (fiberVertex hm hdvd u k).val / m = k.val := by
  simp only [fiberVertex]
  rw [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt u.isLt]; omega

/-- The rotation map for the equal-fiber contracted graph.

    Port encoding: port `jp` in `Fin ((N / m) * d)` encodes `(k, p)`
    where `k = jp / d` (fiber position) and `p = jp % d` (original port).

    The rotation follows edge `(u + k*m, p)` in the original graph,
    then contracts and re-encodes the result. -/
def contractDivisible_rot {N d m : ℕ} (G : RegularGraph N d) (hm : 0 < m)
    (hdvd : m ∣ N)
    (x : Fin m × Fin ((N / m) * d)) : Fin m × Fin ((N / m) * d) :=
  if hd : d = 0 then
    absurd x.2.isLt (by simp [hd])
  else
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    let k : Fin (N / m) := ⟨x.2.val / d,
      (Nat.div_lt_iff_lt_mul hd_pos).mpr x.2.isLt⟩
    let p : Fin d := ⟨x.2.val % d, Nat.mod_lt _ hd_pos⟩
    let v := fiberVertex hm hdvd x.1 k
    let r := G.rot (v, p)
    let w := r.1
    let q := r.2
    let u' : Fin m := ⟨w.val % m, Nat.mod_lt _ hm⟩
    let k' : Fin (N / m) := ⟨w.val / m,
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_div_cancel' hdvd]; exact w.isLt)⟩
    (u', ⟨k'.val * d + q.val, Fin.pair_lt k' q⟩)

/-- Fiber vertex reconstruction: the fiber vertex for `w % m` at position `w / m`
    is `w` itself (when `m ∣ N`). -/
theorem fiberVertex_reconstruct {N m : ℕ} (hm : 0 < m) (hdvd : m ∣ N) (w : Fin N) :
    fiberVertex hm hdvd ⟨w.val % m, Nat.mod_lt _ hm⟩
      ⟨w.val / m, Nat.div_lt_of_lt_mul (by rw [Nat.mul_div_cancel' hdvd]; exact w.isLt)⟩ = w := by
  ext; simp only [fiberVertex]
  have := Nat.mod_add_div w.val m
  linarith [Nat.mul_comm m (w.val / m)]

/-- `contractDivisible_rot` sends `(⟨w%m⟩, ⟨(w/m)*d + q⟩)` to `(⟨v%m⟩, ⟨(v/m)*d + p⟩)`
    whenever `G.rot (w, q) = (v, p)`. This factored formulation avoids
    dependent type issues in the involution proof. -/
theorem contractDivisible_rot_of_rot {N d m : ℕ} (G : RegularGraph N d) (hm : 0 < m)
    (hdvd : m ∣ N) (hd : d ≠ 0) (w v : Fin N) (q p : Fin d)
    (hrot : G.rot (w, q) = (v, p)) :
    contractDivisible_rot G hm hdvd
      (⟨w.val % m, Nat.mod_lt _ hm⟩,
       ⟨w.val / m * d + q.val, Fin.pair_lt
          ⟨w.val / m, Nat.div_lt_of_lt_mul
            (by rw [Nat.mul_div_cancel' hdvd]; exact w.isLt)⟩ q⟩) =
      (⟨v.val % m, Nat.mod_lt _ hm⟩,
       ⟨v.val / m * d + p.val, Fin.pair_lt
          ⟨v.val / m, Nat.div_lt_of_lt_mul
            (by rw [Nat.mul_div_cancel' hdvd]; exact v.isLt)⟩ p⟩) := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- Port decode identities
  have hk : (w.val / m * d + q.val) / d = w.val / m := by
    rw [show w.val / m * d + q.val = q.val + w.val / m * d from by omega]
    rw [Nat.add_mul_div_right _ _ hd_pos, Nat.div_eq_of_lt q.isLt]; omega
  have hp : (w.val / m * d + q.val) % d = q.val := by
    rw [show w.val / m * d + q.val = q.val + w.val / m * d from by omega]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt q.isLt]
  -- Fiber vertex reconstruction: fiberVertex(w%m, w/m) = w
  have hfv : (fiberVertex hm hdvd ⟨w.val % m, Nat.mod_lt _ hm⟩
    ⟨(w.val / m * d + q.val) / d,
      (Nat.div_lt_iff_lt_mul hd_pos).mpr
        (Fin.pair_lt (⟨w.val / m, Nat.div_lt_of_lt_mul
          (by rw [Nat.mul_div_cancel' hdvd]; exact w.isLt)⟩ : Fin (N / m)) q)⟩ : Fin N) = w := by
    ext; simp only [fiberVertex, hk]
    have := Nat.mod_add_div w.val m; linarith [Nat.mul_comm m (w.val / m)]
  -- Port Fin equality
  have hpf : (⟨(w.val / m * d + q.val) % d, Nat.mod_lt _ hd_pos⟩ : Fin d) = q := by
    ext; exact hp
  -- Unfold, eliminate dite. simp reduces let-bindings and applies rewrites.
  unfold contractDivisible_rot
  simp only [dif_neg hd, hfv, hpf, hrot]

theorem contractDivisible_rot_involution {N d m : ℕ} (G : RegularGraph N d)
    (hm : 0 < m) (hdvd : m ∣ N)
    (x : Fin m × Fin ((N / m) * d)) :
    contractDivisible_rot G hm hdvd (contractDivisible_rot G hm hdvd x) = x := by
  rcases x with ⟨u, jp⟩
  by_cases hd : d = 0
  · exact absurd jp.isLt (by simp [hd])
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- First application: unfold to get the result in terms of G.rot
  have h_first : contractDivisible_rot G hm hdvd (u, jp) =
      let v := fiberVertex hm hdvd u ⟨jp.val / d, (Nat.div_lt_iff_lt_mul hd_pos).mpr jp.isLt⟩
      let r := G.rot (v, ⟨jp.val % d, Nat.mod_lt _ hd_pos⟩)
      (⟨r.1.val % m, Nat.mod_lt _ hm⟩,
       ⟨r.1.val / m * d + r.2.val, Fin.pair_lt
          ⟨r.1.val / m, Nat.div_lt_of_lt_mul
            (by rw [Nat.mul_div_cancel' hdvd]; exact r.1.isLt)⟩ r.2⟩) := by
    unfold contractDivisible_rot; rw [dif_neg hd]
  rw [h_first]
  -- Name intermediate values
  set v := fiberVertex hm hdvd u ⟨jp.val / d, _⟩
  set w := (G.rot (v, ⟨jp.val % d, Nat.mod_lt _ hd_pos⟩)).1
  set q := (G.rot (v, ⟨jp.val % d, Nat.mod_lt _ hd_pos⟩)).2
  -- Second application: use contractDivisible_rot_of_rot
  have hrot : G.rot (w, q) = (v, ⟨jp.val % d, Nat.mod_lt _ hd_pos⟩) := by
    show G.rot ((G.rot (v, _)).1, (G.rot (v, _)).2) = _
    rw [Prod.mk.eta]; exact G.rot_involution _
  rw [contractDivisible_rot_of_rot G hm hdvd hd w v q ⟨jp.val % d, _⟩ hrot]
  -- Now need: (v%m, v/m*d + jp%d) = (u, jp)
  ext
  · show v.val % m = u.val
    exact fiberVertex_mod hm hdvd u _
  · show v.val / m * d + jp.val % d = jp.val
    rw [fiberVertex_div hm hdvd u _]
    linarith [Nat.mod_add_div jp.val d, Nat.mul_comm d (jp.val / d)]

/-- Equal-fiber contraction of a `d`-regular graph on `N` vertices to `m`
    vertices (when `m ∣ N`). The result is `((N / m) * d)`-regular.

    Port encoding: each contracted vertex `u` has `N/m` fiber elements
    and `d` original ports per element, giving `(N / m) * d` total ports.
    Port `jp` encodes `(k, p) = (jp / d, jp % d)` where `k` is the fiber
    position and `p` is the original graph port. -/
def RegularGraph.contractDivisible {N d : ℕ} (G : RegularGraph N d)
    (m : ℕ) (hm : 0 < m) (hdvd : m ∣ N) :
    RegularGraph m ((N / m) * d) where
  rot := contractDivisible_rot G hm hdvd
  rot_involution := contractDivisible_rot_involution G hm hdvd

/-- The neighbor function of `contractDivisible` at port `⟨k*d+p, _⟩` is
    `G.neighbor (fiberVertex u k) p` projected to `Fin m`. -/
theorem contractDivisible_neighbor_eq {N d m : ℕ} (G : RegularGraph N d)
    (hm : 0 < m) (hdvd : m ∣ N) (hd : 0 < d) (u : Fin m) (k : Fin (N / m)) (p : Fin d) :
    ((G.contractDivisible m hm hdvd).neighbor u ⟨k.val * d + p.val, Fin.pair_lt k p⟩).val =
    (G.neighbor (fiberVertex hm hdvd u k) p).val % m := by
  -- Both sides compute: follow edge (fiberVertex(u,k), p) in G, take .1 % m.
  -- The LHS decodes port k*d+p into fiber position k and original port p.
  -- Unfold neighbor to expose .rot, then simp contractDivisible to reach contractDivisible_rot
  simp only [RegularGraph.neighbor, RegularGraph.contractDivisible, contractDivisible_rot]
  rw [dif_neg (by omega : ¬d = 0)]
  -- After dif_neg, the definition has let-bindings that decode the port.
  -- The key facts: (k*d+p)/d = k and (k*d+p)%d = p
  -- After beta-reduction, fiberVertex(u, k) feeds into G.rot, giving the same result.
  -- Use simp to reduce let-bindings and Fin arithmetic
  simp only [show (k.val * d + p.val) / d = k.val from by
    rw [show k.val * d + p.val = p.val + k.val * d from by omega]
    rw [Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt p.isLt]; omega,
    show (k.val * d + p.val) % d = p.val from by
    rw [show k.val * d + p.val = p.val + k.val * d from by omega]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.isLt]]

/-- Fiber bijection: `(u, k) ↦ fiberVertex(u, k) = u + k*m` bijects
    `Fin m × Fin (N/m)` with `Fin N` when `m ∣ N`. -/
def fiberEquiv {N m : ℕ} (hm : 0 < m) (hdvd : m ∣ N) :
    Fin m × Fin (N / m) ≃ Fin N where
  toFun := fun ⟨u, k⟩ ↦ fiberVertex hm hdvd u k
  invFun := fun v ↦ (⟨v.val % m, Nat.mod_lt _ hm⟩,
    ⟨v.val / m, Nat.div_lt_of_lt_mul (by rw [Nat.mul_div_cancel' hdvd]; exact v.isLt)⟩)
  left_inv := fun ⟨u, k⟩ ↦
    Prod.ext (Fin.ext (fiberVertex_mod hm hdvd u k)) (Fin.ext (fiberVertex_div hm hdvd u k))
  right_inv := fun v ↦ fiberVertex_reconstruct hm hdvd v

/-- Port decomposition: `(k, p) ↦ k*d + p` bijects `Fin Q × Fin d` with `Fin (Q*d)`. -/
def portEquiv {Q d : ℕ} (hd : 0 < d) : Fin Q × Fin d ≃ Fin (Q * d) where
  toFun := fun ⟨k, p⟩ ↦ ⟨k.val * d + p.val, Fin.pair_lt k p⟩
  invFun := fun jp ↦ (⟨jp.val / d, (Nat.div_lt_iff_lt_mul hd).mpr jp.isLt⟩,
                       ⟨jp.val % d, Nat.mod_lt _ hd⟩)
  left_inv := fun ⟨k, p⟩ ↦ by
    ext
    · show (k.val * d + p.val) / d = k.val
      rw [show k.val * d + p.val = p.val + k.val * d from by omega]
      rw [Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt p.isLt]; omega
    · show (k.val * d + p.val) % d = p.val
      rw [show k.val * d + p.val = p.val + k.val * d from by omega]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.isLt]
  right_inv := fun jp ↦ by
    ext; show (jp.val / d) * d + jp.val % d = jp.val
    rw [Nat.mul_comm]; exact Nat.div_add_mod jp.val d

/-- The spectral gap of an equal-fiber contracted graph is at most that of the
    original.

    Proof: define lift `g(v) = f(v % m)`. The contracted walk operator is a
    fiber average of the original: `(W_C f)(u) = (1/(N/m)) · ∑_k (W_G g)(u+k·m)`.
    By Jensen, `|(W_C-M)f(u)|² ≤ (1/(N/m))·∑_k|(W_G-M)g(u+k·m)|²`. Summing
    over u and using `‖g‖² = (N/m)·‖f‖²` gives `‖(W_C-M)f‖ ≤ spectralGap(G)·‖f‖`.
    The neighbor decomposition `contractDivisible_neighbor_eq` provides the key
    algebraic identity relating the contracted and original walk operators. -/
theorem spectralGap_contractDivisible {N d : ℕ} (G : RegularGraph N d)
    (m : ℕ) (hm : 0 < m) (hdvd : m ∣ N) (hd : 0 < d) (hq : 0 < N / m) :
    spectralGap (G.contractDivisible m hm hdvd) ≤ spectralGap G := by
  set Q := N / m with hQ_def
  set C := G.contractDivisible m hm hdvd
  have hQ_pos : (0 : ℝ) < ↑Q := Nat.cast_pos.mpr hq
  have hQ_ne : (↑Q : ℝ) ≠ 0 := ne_of_gt hQ_pos
  have hd_ne : (↑d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold spectralGap
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  -- Define lift: g(v) = f(v % m)
  set g : EuclideanSpace ℝ (Fin N) :=
    WithLp.toLp 2 (fun v : Fin N ↦ f ⟨v.val % m, Nat.mod_lt _ hm⟩) with hg_def
  -- Reduce to squared norms
  rw [← Real.sqrt_sq (norm_nonneg ((C.walkCLM - meanCLM m) f)),
      ← Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  apply Real.sqrt_le_sqrt
  rw [mul_pow, EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs]
  -- Goal: ∑ u, (((C.walkCLM - meanCLM m) f) u) ^ 2 ≤ ‖C.walkCLM - meanCLM m‖ ^ 2 * ‖f‖ ^ 2
  -- Per-vertex walk identity: C.walkCLM f u = Q⁻¹ * ∑_k G.walkCLM g (fv u k)
  have walk_eq : ∀ u : Fin m,
      C.walkCLM f u =
      (↑Q)⁻¹ * ∑ k : Fin Q, G.walkCLM g (fiberVertex hm hdvd u k) := by
    intro u
    simp only [RegularGraph.walkCLM_apply]
    -- Reindex sum over Fin(Q*d) as double sum over Fin Q × Fin d
    rw [show (∑ i : Fin (Q * d), f (C.neighbor u i)) =
      ∑ k : Fin Q, ∑ p : Fin d, f (C.neighbor u ⟨k.val * d + p.val, Fin.pair_lt k p⟩) from by
      rw [← Fintype.sum_prod_type']
      exact ((portEquiv hd).sum_comp (fun jp ↦ f (C.neighbor u jp))).symm]
    -- Replace C.neighbor with G.neighbor via contractDivisible_neighbor_eq
    have nbr_eq : ∀ (k : Fin Q) (p : Fin d),
        f (C.neighbor u ⟨k.val * d + p.val, Fin.pair_lt k p⟩) =
        g (G.neighbor (fiberVertex hm hdvd u k) p) := by
      intro k p
      show f (C.neighbor u ⟨k.val * d + p.val, Fin.pair_lt k p⟩) =
        f ⟨(G.neighbor (fiberVertex hm hdvd u k) p).val % m, Nat.mod_lt _ hm⟩
      exact congr_arg f.ofLp (Fin.ext (contractDivisible_neighbor_eq G hm hdvd hd u k p))
    simp_rw [nbr_eq]
    -- Now: (∑_k ∑_p g(G.nbr(fv u k, p))) / (Q*d) = Q⁻¹ * ∑_k (∑_p g(G.nbr(fv u k, p))) / d
    have hcast : (↑(N / m * d) : ℝ) = ↑Q * ↑d := by push_cast; rfl
    rw [Finset.sum_div]; simp_rw [hcast]
    simp_rw [show ∀ (a : ℝ), a / (↑Q * ↑d) = (↑Q)⁻¹ * (a / ↑d) from
      fun a ↦ by field_simp]
    rw [← Finset.mul_sum]
  -- Fiber reindexing helper (used in mean_eq and norm_sq)
  have fiber_simp : ∀ x : Fin m × Fin Q,
      g ((fiberEquiv hm hdvd) x) = f x.1 := by
    intro ⟨u, k⟩
    show f ⟨(fiberVertex hm hdvd u k).val % m, _⟩ = f u
    simp only [fiberVertex_mod, Fin.eta]
  -- Mean identity: meanCLM m f u = meanCLM N g v (both equal (∑ f) / m)
  have mean_eq : ∀ (u : Fin m) (k : Fin Q),
      meanCLM m f u = meanCLM N g (fiberVertex hm hdvd u k) := by
    intro u k
    simp only [meanCLM_apply]
    have sum_g : ∑ v : Fin N, g v = ↑Q * ∑ w : Fin m, f w := by
      rw [← (fiberEquiv hm hdvd).sum_comp]; simp_rw [fiber_simp]
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
    rw [sum_g]
    have hNQm : (↑N : ℝ) = ↑Q * ↑m := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
    rw [hNQm, mul_div_mul_left _ _ hQ_ne]
  -- Combined per-vertex identity (LHS in CLM form to match goal)
  have per_vertex : ∀ u : Fin m,
      ((C.walkCLM - meanCLM m) f) u =
      (↑Q)⁻¹ * ∑ k : Fin Q,
        ((G.walkCLM - meanCLM N) g) (fiberVertex hm hdvd u k) := by
    intro u
    -- Convert to component form (definitional equality)
    show C.walkCLM f u - meanCLM m f u =
      (↑Q)⁻¹ * ∑ k : Fin Q,
        (G.walkCLM g (fiberVertex hm hdvd u k) -
         meanCLM N g (fiberVertex hm hdvd u k))
    rw [walk_eq u]
    conv_lhs => rw [show meanCLM m f u =
      (↑Q)⁻¹ * (↑Q * meanCLM m f u) from by rw [inv_mul_cancel_left₀ hQ_ne]]
    rw [← mul_sub]
    congr 1
    rw [show ↑Q * meanCLM m f u =
      ∑ k : Fin Q, meanCLM N g (fiberVertex hm hdvd u k) from by
      rw [show ↑Q * meanCLM m f u = ∑ _k : Fin Q, (meanCLM m f u : ℝ) from by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
      exact Finset.sum_congr rfl (fun k _ ↦ mean_eq u k)]
    simp only [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp_rw [per_vertex]
  -- Jensen per vertex: (Q⁻¹ * ∑ a)² ≤ Q⁻¹ * ∑ a²
  set h := fun u k ↦ ((G.walkCLM - meanCLM N) g) (fiberVertex hm hdvd u k)
  have jensen : ∀ u : Fin m,
      ((↑Q : ℝ)⁻¹ * ∑ k : Fin Q, h u k) ^ 2 ≤
      (↑Q : ℝ)⁻¹ * ∑ k : Fin Q, (h u k) ^ 2 := by
    intro u
    have cs := @sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _ Finset.univ (fun k ↦ h u k)
    simp only [Finset.card_univ, Fintype.card_fin] at cs
    -- cs : (∑ k, h u k) ^ 2 ≤ ↑Q * ∑ k, (h u k) ^ 2
    rw [mul_pow]
    calc (↑Q : ℝ)⁻¹ ^ 2 * (∑ k, h u k) ^ 2
        ≤ (↑Q : ℝ)⁻¹ ^ 2 * (↑Q * ∑ k, (h u k) ^ 2) :=
          mul_le_mul_of_nonneg_left cs (sq_nonneg _)
      _ = (↑Q : ℝ)⁻¹ * ∑ k, (h u k) ^ 2 := by
          rw [sq (↑Q : ℝ)⁻¹, mul_assoc, inv_mul_cancel_left₀ hQ_ne]
  calc ∑ u, ((↑Q : ℝ)⁻¹ * ∑ k, h u k) ^ 2
      ≤ ∑ u, (↑Q : ℝ)⁻¹ * ∑ k, (h u k) ^ 2 :=
        Finset.sum_le_sum (fun u _ ↦ jensen u)
    _ = (↑Q : ℝ)⁻¹ * ∑ u, ∑ k, (h u k) ^ 2 := by rw [← Finset.mul_sum]
    _ = (↑Q : ℝ)⁻¹ * ∑ v, (((G.walkCLM - meanCLM N) g) v) ^ 2 := by
        congr 1
        rw [show ∑ u : Fin m, ∑ k : Fin Q, (h u k) ^ 2 =
          ∑ p : Fin m × Fin Q, (h p.1 p.2) ^ 2 from
          (Fintype.sum_prod_type' (fun u k ↦ (h u k) ^ 2)).symm]
        simp only [h]
        exact (fiberEquiv hm hdvd).sum_comp
          (fun v ↦ (((G.walkCLM - meanCLM N) g) v) ^ 2)
    _ ≤ (↑Q : ℝ)⁻¹ * (‖G.walkCLM - meanCLM N‖ * ‖g‖) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        calc ∑ v, (((G.walkCLM - meanCLM N) g) v) ^ 2
            = ∑ v, ‖((G.walkCLM - meanCLM N) g) v‖ ^ 2 := by
              simp_rw [Real.norm_eq_abs, sq_abs]
          _ = ‖(G.walkCLM - meanCLM N) g‖ ^ 2 := by
              rw [← EuclideanSpace.norm_sq_eq]
          _ ≤ (‖G.walkCLM - meanCLM N‖ * ‖g‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) ((G.walkCLM - meanCLM N).le_opNorm g) 2
    _ = ‖G.walkCLM - meanCLM N‖ ^ 2 * ((↑Q : ℝ)⁻¹ * ‖g‖ ^ 2) := by
        rw [mul_pow]; ring
    _ = ‖G.walkCLM - meanCLM N‖ ^ 2 * ‖f‖ ^ 2 := by
        congr 1
        -- Q⁻¹ * ‖g‖² = ‖f‖²
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        simp_rw [Real.norm_eq_abs, sq_abs]
        -- ∑_v g(v)² = Q * ∑_u f(u)², so Q⁻¹ * that = ∑ f²
        have norm_sq : ∑ v : Fin N, (g v) ^ 2 = ↑Q * ∑ u : Fin m, (f u) ^ 2 := by
          rw [← (fiberEquiv hm hdvd).sum_comp]; simp_rw [fiber_simp]
          rw [Fintype.sum_prod_type]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.mul_sum]
        rw [norm_sq, inv_mul_cancel_left₀ hQ_ne]

end


