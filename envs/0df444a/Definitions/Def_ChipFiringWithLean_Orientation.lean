-- Prove2me | Definitions.Def_ChipFiringWithLean_Orientation
-- name    : ChipFiringWithLean_Orientation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:49:33.069241+00:00
-- url     : https://prove2.me/theorems/a326f925-3973-4ce2-bf33-e479216c86d1
-- title:
--   Orientation
-- statement:
--   Definitions and structural lemmas for Orientation, from DhyeyMavani2003/chip-firing-with-lean contributors (see pinned LICENSE and source headers)'s pinned Chip-firing on multigraphs and Riemann-Roch for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Theorems.Thm_burn_flow_reverse
public import Theorems.Thm_burnin_degree
public import Theorems.Thm_config_degree_mono
public import Theorems.Thm_config_eq_of_le_and_degree
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_num_edges_symmetric
public import Theorems.Thm_sum_card_filter_eq_mul
public import Theorems.Thm_superstable_burn_list
public import Theorems.Thm_superstable_iff_q_reduced
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
structure CFOrientation (G : CFGraph) where
  /-- The multiset of directed edges in the orientation. -/
  directed_edges : Multiset (G.V × G.V)
  /-- The total directed flow between two vertices preserves the graph's edge multiplicity. -/
  count_preserving : ∀ v w,
    num_edges G v w =
    Multiset.count (v, w) directed_edges + Multiset.count (w, v) directed_edges
abbrev flow {G: CFGraph} (O : CFOrientation G) (u v : G.V) : ℕ :=
  Multiset.count (u,v) O.directed_edges
lemma opp_flow {G : CFGraph} (O : CFOrientation G) (u v : G.V) :
  flow O u v + flow O v u= (num_edges G u v) := by
  rw[O.count_preserving u v]
lemma double_sum {T : Type*} [DecidableEq T] [Fintype T] (f : T × T → ℕ) :
    ∑ (u : T), ∑ (v : T), f ⟨u, v⟩ = ∑ (e : T × T), f e := by
  rw [← Finset.sum_product]
  simp only [univ_product_univ]
lemma card_directed_edges_eq_card_edges {G : CFGraph} (O : CFOrientation G) : Multiset.card  O.directed_edges = Multiset.card G.edges := by
  have hms (M : Multiset (G.V × G.V)): ∀ e ∈ M, e ∈ univ := by
      intro e _
      exact mem_univ e

  let f (u v : G.V) := flow O u v
  let g (u v : G.V) := Multiset.count ⟨u,v⟩ G.edges
  have h_uv (u v : G.V) : f u v + f v u = g u v + g v u := by
    have h := O.count_preserving u v
    dsimp only [flow, f, g]
    dsimp only [num_edges] at h
    rw [← h]
    rw [← Multiset.sum_count_eq_card (hms ((Multiset.filter (fun e ↦ e = (u, v) ∨ e = (v, u)) G.edges)))]
    -- Now simplify the count of a in the filtered multiset
    have h_msum (u v : G.V) : Multiset.filter (λ e => e = (u, v) ∨ e = (v, u)) G.edges = Multiset.filter (λ e => e = ⟨u,v⟩) G.edges + Multiset.filter (λ e => e = ⟨v,u⟩) G.edges := by
      apply Multiset.ext.mpr
      intro e
      simp only [count_add]
      repeat rw [Multiset.count_filter]
      by_cases h_e : e = ⟨u,v⟩
      · -- case: e = ⟨u,v⟩
        simp only [h_e, Prod.mk.injEq, true_or, ↓reduceIte, Nat.left_eq_add, ite_eq_right_iff,
            count_eq_zero, and_imp]
        intro h_eq _
        rw [h_eq]
        exact G.loopless v
      · -- case: e ≠ ⟨u,v⟩
        by_cases h_e' : e = ⟨v,u⟩
        · -- case: e = ⟨v,u⟩
          simp only [h_e', Prod.mk.injEq, or_true, ↓reduceIte, Nat.right_eq_add, ite_eq_right_iff,
              count_eq_zero, and_imp]
          intro h_eq _
          rw [h_eq]
          exact G.loopless u
        · -- case: e ≠ ⟨v,u⟩
          simp only [h_e, h_e', or_self, ↓reduceIte, add_zero]
    rw [h_msum]
    simp only [count_add]
    rw [sum_add_distrib]
    simp only [count_filter, sum_ite_eq', mem_univ, ↓reduceIte]
  have lhs : ∑ u: G.V, ∑ v : G.V, (f u v + f v u)= 2 * Multiset.card O.directed_edges := by
    simp only [sum_add_distrib]
    dsimp only [flow, f]
    nth_rewrite 2 [Finset.sum_comm]
    rw [← two_mul]
    have h_replace := double_sum (λ e : G.V × G.V => Multiset.count e O.directed_edges)
    simp only [h_replace]
    simp only [mem_univ, implies_true, sum_count_eq_card]
  have rhs : ∑ u : G.V, ∑ v : G.V, (g u v + g v u) = 2 * Multiset.card G.edges := by
    simp only [sum_add_distrib]
    dsimp only [g]
    nth_rewrite 2 [Finset.sum_comm]
    rw [← two_mul]
    have h_replace := double_sum (λ e : G.V × G.V => Multiset.count e G.edges)
    simp only [h_replace]
    simp only [mem_univ, implies_true, sum_count_eq_card]
  simp only [h_uv] at lhs
  rw [lhs] at rhs
  linarith
def indeg (G : CFGraph) (O : CFOrientation G) (v : G.V) : ℕ :=
  Multiset.card (O.directed_edges.filter (λ e => e.snd = v))
lemma indeg_eq_sum_flow {G : CFGraph} (O : CFOrientation G) (v : G.V) :
  indeg G O v = ∑ w : G.V, flow O w v := by
  dsimp only [indeg, flow]
  suffices h_eq : (∀ S : Multiset (G.V × G.V) , ∀ v : G.V,
    Multiset.card (S.filter (λ e => e.snd = v)) = ∑ u : G.V, Multiset.count (u, v) S) by
    exact h_eq O.directed_edges v
  -- Prove by induction on the set of directed edges, following the pattern of the proof of
  -- degree_eq_total_flow in Basic.lean. I suspect the two can be unified.
  intro S v
  induction S using Multiset.induction_on with
  | empty =>
    simp only [filter_zero, Multiset.card_zero]
    simp only [notMem_zero, not_false_eq_true, count_eq_zero_of_notMem, sum_const_zero]
  | cons e S ih =>
    simp only [Multiset.filter_cons, card_add, count_cons, sum_add_distrib]
    rw [ih]
    nth_rewrite 1 [add_comm]
    apply add_left_cancel_iff.mpr
    obtain ⟨eu,ev⟩ := e
    by_cases h_ev_eq_v : ev = v
    · -- Case ev = v
      rw [h_ev_eq_v]
      simp only [↓reduceIte, Multiset.card_singleton, Prod.mk.injEq, and_true, sum_ite_eq',
          mem_univ]
    · -- Case ev ≠ v
      rw [if_neg h_ev_eq_v, Multiset.card_zero]
      -- Flip the sides of the equation in the goal
      have : ∑ x : G.V, (if (x, v) = (eu, ev) then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp only [Prod.mk.injEq, ite_eq_right_iff, one_ne_zero, imp_false, not_and]
        intro _
        contrapose! h_ev_eq_v
        rw [h_ev_eq_v]
      -- refine Finset.sum_eq_zero ?_
      rw [this]
def outdeg (G : CFGraph) (O : CFOrientation G) (v : G.V) : ℕ :=
  Multiset.card (O.directed_edges.filter (λ e => e.fst = v))
def is_source (G : CFGraph) (O : CFOrientation G) (v : G.V) : Prop :=
  indeg G O v = 0
def directed_edge (G : CFGraph) (O : CFOrientation G) (u v : G.V) : Prop :=
  (u, v) ∈ O.directed_edges
structure DirectedPath {G : CFGraph} (O : CFOrientation G) where
  /-- The sequence of vertices in the path. -/
  vertices : List G.V
  /-- The path is nonempty. -/
  non_empty : vertices.length > 0
  /-- Every consecutive pair forms a directed edge. -/
  valid_edges : List.IsChain (directed_edge G O) vertices
def non_repeating {G: CFGraph} {O : CFOrientation G} (p : DirectedPath O) : Prop :=
  p.vertices.Nodup
lemma path_length_bound {G : CFGraph} {O : CFOrientation G} (p : DirectedPath O) :
  non_repeating p → p.vertices.length ≤ Fintype.card G.V := by
  intro h_distinct
  exact List.Nodup.length_le_card h_distinct
def is_acyclic (G : CFGraph) (O : CFOrientation G) : Prop :=
  ∀ (p : DirectedPath O), non_repeating p
lemma indeg_ge_one_of_not_source (G : CFGraph) (O : CFOrientation G) (v : G.V) :
    ¬ is_source G O v → indeg G O v ≥ 1 := by
  intro h_not_source -- h_not_source : is_source G O v = false
  unfold is_source at h_not_source -- h_not_source : (decide (indeg G O v = 0)) = false
  apply Nat.one_le_iff_ne_zero.mpr -- Goal is indeg G O v ≠ 0
  intro h_eq_zero -- Assume indeg G O v = 0
  exact h_not_source h_eq_zero
lemma indeg_minus_one_nonneg_of_not_source (G : CFGraph) (O : CFOrientation G) (v : G.V) :
    ¬ is_source G O v → 0 ≤ (indeg G O v : ℤ) - 1 := by
  intro h_not_source
  have h_indeg_ge_1 : indeg G O v ≥ 1 := indeg_ge_one_of_not_source G O v h_not_source
  apply Int.sub_nonneg_of_le
  exact Nat.cast_le.mpr h_indeg_ge_1
lemma subset_source (G : CFGraph) (O : CFOrientation G) (S : Finset G.V):
  S.Nonempty → is_acyclic G O → ∃ v ∈ S, ∀ w ∈ S, flow O w v = 0 := by
  intro S_nonempty h_acyclic
  by_contra! no_sourceless

  let S_path (p : DirectedPath O) : Prop :=
    ∀ v ∈ p.vertices, v ∈ S

  have arb_path (n : ℕ) : ∃ (p : DirectedPath O), S_path p ∧ p.vertices.length = n + 1:= by
    induction n with
    | zero =>
    · -- Base case: n = 0
      -- Create a list consisting of v only
      rcases S_nonempty with ⟨v, h_v_in_S⟩
      use {
        vertices := [v],
        non_empty := by
          simp only [List.length_cons, List.length_nil, zero_add, gt_iff_lt, Order.lt_one_iff],
        valid_edges := List.isChain_singleton v
      }
      simp only [List.length_cons, List.length_nil, zero_add, and_true]
      intro u h_u_in_path
      rw [List.mem_singleton] at h_u_in_path
      rw [h_u_in_path]
      exact h_v_in_S
    | succ n ih =>
    · -- Inductive step: assume true for n, prove for n + 1
      rcases ih with ⟨p, h_len⟩
      cases hp: p.vertices with
      | nil =>
        -- This case should not happen since p.vertices has length n + 1 ≥ 1
        exfalso
        rw [hp] at h_len
        simp only [List.length_nil, Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero,
            and_false] at h_len
      | cons v p' =>
        specialize no_sourceless v
        have v_S : v ∈ S := h_len.1 v (by simp only [hp, List.mem_cons, true_or])
        rcases (no_sourceless v_S) with h_no_parent
        rcases h_no_parent with ⟨u, h_u⟩
        let new_path : List G.V := u :: p.vertices
        use {
          vertices := new_path,
          non_empty := by
            rw [List.length_cons]
            exact Nat.succ_pos _,
          valid_edges := by
            dsimp only [new_path]
            cases h_case : p.vertices with
            | nil =>
              -- Path was just [v], so new path is [u, v]
              simp only [List.IsChain.singleton]
            | cons v' vs =>
              have eq_vv': v = v' := by
                rw [h_case] at hp
                simp only [List.cons.injEq] at hp
                obtain ⟨h,_⟩ := hp
                rw [h]
              rw [← eq_vv']
              constructor
              -- Show the new first link is a directed edge
              have := h_u.2
              dsimp only [flow, ne_eq] at this
              contrapose! this with h_no_edge
              simp only [count_eq_zero]
              exact h_no_edge
              -- Now show the rest of the path is valid
              have h_rec := p.valid_edges
              rw [h_case] at h_rec
              rw [← eq_vv'] at h_rec
              exact h_rec
        }
        -- Show that the path lies in S
        constructor
        intro v h_v_in_path
        simp only at h_v_in_path
        dsimp only [new_path] at h_v_in_path
        cases h_v_in_path with
        | head h_eq_v =>
          exact h_u.1
        | tail _ h_v_in_tail =>
          exact h_len.1 v h_v_in_tail
        -- Show the length is n + 2
        rw [List.length_cons]
        rw [h_len.2]
  specialize arb_path (Fintype.card G.V)
  rcases arb_path with ⟨p, h_len⟩
  have ineq := path_length_bound p (h_acyclic p)
  linarith
lemma acyclic_has_source (G : CFGraph) (O : CFOrientation G) :
  is_acyclic G O → ∃ v : G.V, is_source G O v := by
  intro h_acyclic
  have h := subset_source G O Finset.univ Finset.univ_nonempty h_acyclic
  rcases h with ⟨v, _, h_source⟩
  use v
  dsimp only [is_source]
  rw [indeg_eq_sum_flow]
  apply Finset.sum_eq_zero
  exact h_source
lemma is_source_of_unique_source {G : CFGraph} (O : CFOrientation G) {q : G.V} (h_acyclic : is_acyclic G O)
    (h_unique_source : ∀ w, is_source G O w → w = q) :
  is_source G O q := by
  rcases acyclic_has_source G O h_acyclic with ⟨q', h_q'⟩
  specialize h_unique_source q'
  have := h_unique_source h_q'
  rw [this] at h_q'
  exact h_q'
def acyclic_with_unique_source (G : CFGraph) (O : CFOrientation G) (q : G.V) : Prop :=
  is_acyclic G O ∧ ∀ w, is_source G O w → w = q
lemma source_of_acyclic_with_unique_source {G : CFGraph} {O : CFOrientation G} {q : G.V}
    (hO : acyclic_with_unique_source G O q) : is_source G O q :=
  is_source_of_unique_source O hO.1 hO.2
def config_of_source {G : CFGraph} {O : CFOrientation G} {q : G.V}
    (hO : acyclic_with_unique_source G O q) : Config G q :=
  { chips := λ v => if v = q then 0 else (indeg G O v : ℤ) - 1,
    q_zero := by simp only [↓reduceIte]
    non_negative := by
      intro v
      simp only [ge_iff_le]
      split_ifs with h_eq
      · linarith
      · have h_not_source : ¬ is_source G O v := by
          intro hs_v
          exact h_eq (hO.2 v hs_v)
        exact indeg_minus_one_nonneg_of_not_source G O v h_not_source
  }
def ordiv (G : CFGraph) (O : CFOrientation G) : CFDiv G :=
  λ v => indeg G O v - 1
def orqed {G : CFGraph} (O : CFOrientation G) {q : G.V}
    (hO : acyclic_with_unique_source G O q) : q_eff_div G q := {
      D := ordiv G O,
      h_eff := by
        intro v v_ne_q
        dsimp only [ordiv]
        contrapose! v_ne_q with v_q
        have h_indeg : indeg G O v = 0 := by
          linarith
        rw [indeg_eq_sum_flow] at h_indeg
        -- Sum of non-negative terms is zero, so each term is zero
        apply hO.2
        contrapose! h_indeg with h_not_source
        dsimp only [is_source] at h_not_source
        rw [indeg_eq_sum_flow] at h_not_source
        intro h_bad
        rw [h_bad] at h_not_source
        simp only [not_true_eq_false] at h_not_source
    }
def orientation_to_config (G : CFGraph) (O : CFOrientation G) (q : G.V)
    (hO : acyclic_with_unique_source G O q) : Config G q :=
  config_of_source hO
lemma config_and_divisor_from_O {G : CFGraph} (O : CFOrientation G) {q : G.V}
    (hO : acyclic_with_unique_source G O q) :
  orientation_to_config G O q hO = toConfig (orqed O hO) := by
  let c := orientation_to_config G O q hO
  let D := orqed O hO
  rw [eq_config_iff_eq_chips]
  funext v
  by_cases h_v: v = q
  · -- Case v = q
    rw [h_v]
    have (c d : Config G q) : c.chips q = d.chips q := by
      rw [c.q_zero, d.q_zero]
    rw [this]
  · -- Case v ≠ q
    dsimp only [orientation_to_config, config_of_source, orqed, toConfig, ordiv, Pi.sub_apply,
        Pi.smul_apply, Int.zsmul_eq_mul]
    simp only [h_v, ↓reduceIte, ne_eq, not_false_eq_true, one_chip_apply_other', mul_zero, sub_zero]
lemma degree_ordiv {G : CFGraph} (O : CFOrientation G) :
  deg (ordiv G O) = (genus G) - 1 := by
  have flow_sum : deg (ordiv G O) = (∑ v : G.V, ∑ w : G.V, ↑(flow O w v)) - (Fintype.card G.V) := by
    calc
      deg (ordiv G O)
        = ∑ v : G.V, ordiv G O v := by rfl
      _ = ∑ v : G.V, (∑ w : G.V, ↑(flow O w v) - 1) := by
        apply Finset.sum_congr rfl
        intro x _
        dsimp only [ordiv]
        rw [indeg_eq_sum_flow O x]
        simp only [Nat.cast_sum]
      _ = (∑ v : G.V, ∑ w : G.V, ↑(flow O w v)) - (Fintype.card G.V) := by
        rw [Finset.sum_sub_distrib]
        simp only [sum_const, card_univ, Int.nsmul_eq_mul, mul_one]
  dsimp only [genus]
  rw [flow_sum]
  suffices h : (∑ v : G.V, ∑ w : G.V, ↑(flow O w v)) = ↑(Multiset.card G.edges) by linarith [h]
  calc
    ∑ v : G.V, ∑ w : G.V, ↑(flow O w v)
      = ∑ v : G.V, (indeg G O v) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [indeg_eq_sum_flow]
    _ = ∑ v : G.V, Multiset.card (O.directed_edges.filter (λ e => e.snd = v)) := by
      dsimp only [indeg]
    _ = ↑(Multiset.card O.directed_edges) := by
      -- Each directed edge points into exactly one vertex
      rw [sum_card_filter_eq_mul G O.directed_edges (λ v e => e.snd = v) 1 ?_, one_mul]
      intro e _
      refine Finset.card_eq_one.mpr ⟨e.2, ?_⟩
      ext x
      simp only [eq_comm, Finset.mem_filter, mem_univ, true_and, Finset.mem_singleton]
    _ = ↑(Multiset.card G.edges) := by
      exact card_directed_edges_eq_card_edges O
    _ = Multiset.card G.edges := by
      rfl
lemma config_degree_from_O {G : CFGraph} (O : CFOrientation G) {q : G.V}
    (hO : acyclic_with_unique_source G O q) :
  config_degree (orientation_to_config G O q hO) = genus G := by
  rw [config_and_divisor_from_O O hO]
  -- Use config_degree_div_degree to relate config_degree to deg of the underlying divisor.
  have h_q_source : indeg G O q = 0 := source_of_acyclic_with_unique_source hO
  have h1 := config_degree_div_degree (orqed O hO)
  -- (orqed O ...).D = ordiv G O definitionally, so:
  have h2 : (orqed O hO).D q = (indeg G O q : ℤ) - 1 := rfl
  have h3 : deg (orqed O hO).D = (genus G : ℤ) - 1 := degree_ordiv O
  have h4 : (indeg G O q : ℤ) = 0 := by exact_mod_cast h_q_source
  linarith
lemma ordiv_q_reduced {G : CFGraph} (O : CFOrientation G) {q : G.V}
    (hO : acyclic_with_unique_source G O q) : q_reduced G q (ordiv G O) := by
  constructor
  · -- Show ordiv is effective away from q
    intro v h_v_ne_q
    simp only [ne_eq] at h_v_ne_q -- Now just ¬ v = q
    dsimp only [ordiv]
    suffices indeg G O v > 0  by
      linarith
    contrapose! h_v_ne_q with indeg_zero
    apply hO.2
    apply Nat.eq_zero_of_le_zero at indeg_zero
    dsimp only [is_source]
    simp only [indeg_zero]
  · -- Show no valid firing move exists for subsets not containing q
    intro S h_q_S S_nonempty hlegal
    have h_source := subset_source G O S S_nonempty hO.1
    rcases h_source with ⟨v, h_v_S, h_flow⟩
    apply (not_lt_of_ge (hlegal v h_v_S))
    dsimp only [ordiv]
    -- Cancel -1 from both sides
    apply Int.lt_of_le_sub_one
    apply sub_le_sub_right
    -- Expand indeg and compare terms
    rw [indeg_eq_sum_flow O v, Nat.cast_sum]
    -- Split the LHS sum into the x ∈ S part and the x ∉ S part
    have flow_bound (w : G.V) : flow O w v ≤ if w ∈ S then 0 else num_edges G w v := by
      by_cases h_w_in_S : w ∈ S
      · -- Case: w ∈ S
        simp only [h_w_in_S, ↓reduceIte, nonpos_iff_eq_zero, count_eq_zero]
        specialize h_flow w
        apply h_flow at h_w_in_S
        dsimp only [flow] at h_w_in_S
        -- Now deduce (w,v) ∉ O.directed_edges from count = 0.
        exact  Multiset.count_eq_zero.mp h_w_in_S
      · -- Case: w ∉ S
        simp only [h_w_in_S, ↓reduceIte]
        rw [← opp_flow O w v]
        linarith
    have sum_flow_bound : ∑ w : G.V, ↑(flow O w v) ≤ ∑ w : G.V, if w ∈ S then 0 else ↑(num_edges G w v) := by
      apply Finset.sum_le_sum
      intro u _
      specialize flow_bound u
      exact flow_bound
    rw [Finset.sum_ite, sum_const,smul_zero, zero_add] at sum_flow_bound
    -- Do some annoying casting business to remove ↑.
    rw [outdeg_S_eq_sum_filter]
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    apply Nat.cast_le.mpr
    apply le_trans sum_flow_bound
    -- Final step: we have num_edges G _ v on LHS and G v _ on the right. Use symmetry.
    simp only [num_edges_symmetric, Std.le_refl]
lemma orientation_config_superstable (G : CFGraph) (O : CFOrientation G) (q : G.V)
    (hO : acyclic_with_unique_source G O q) :
    superstable G q (orientation_to_config G O q hO) := by
    let c := orientation_to_config G O q hO
    apply (superstable_iff_q_reduced G q (genus G -1) c).mpr

    have h_c := config_and_divisor_from_O O hO
    dsimp only [c]
    rw [h_c]
    have : genus G - 1 = deg ((orqed O hO).D) := by
      simpa only [orqed] using (degree_ordiv O).symm
    rw [this]
    rw [div_of_config_of_div (orqed O hO)]
    exact ordiv_q_reduced O hO
def canonical_divisor (G : CFGraph) : CFDiv G :=
  λ v => (vertex_degree G v) - 2
lemma count_map_swap {G : CFGraph} (M : Multiset (G.V × G.V)) (v w : G.V) :
  Multiset.count (v, w) (M.map Prod.swap) = Multiset.count (w, v) M :=
  Multiset.count_map_eq_count' Prod.swap M Prod.swap_injective (w, v)
def CFOrientation.reverse (G : CFGraph) (O : CFOrientation G) : CFOrientation G where
  directed_edges := O.directed_edges.map Prod.swap
  count_preserving v w := by
    rw [count_map_swap, count_map_swap, add_comm]
    exact O.count_preserving v w
def multiset_of_count {T : Type*} [DecidableEq T] [Fintype T] (f : T → ℕ) : Multiset T :=
  DFinsupp.toMultiset (DFinsupp.equivFunOnFintype.symm f)
@[simp] lemma count_of_multiset_of_count {T : Type*} [DecidableEq T] [Fintype T]
    (f : T → ℕ) : ∀ e : T, Multiset.count e (multiset_of_count f) = f e := by
  intro e
  rw [← Multiset.toDFinsupp_apply]
  calc
    (Multiset.toDFinsupp (multiset_of_count f)) e = (DFinsupp.equivFunOnFintype.symm f) e := by
      simp only [multiset_of_count, DFinsupp.toMultiset_toDFinsupp]
    _ = f e := by
      simpa only [DFinsupp.equivFunOnFintype_apply]
          using congrFun (Equiv.apply_symm_apply DFinsupp.equivFunOnFintype f) e
def orientation_from_flow {G : CFGraph} (f : G.V × G.V → ℕ) (h_count_preserving : ∀ v w : G.V, f (v,w) + f (w,v) = num_edges G v w) : CFOrientation G :=
  {
    directed_edges := multiset_of_count f,
    count_preserving := by
      intro v w
      simpa only [count_of_multiset_of_count] using (h_count_preserving v w).symm
  }
def burn_orientation {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (h_full : ∀ (v :G.V), v ∈ L.list): CFOrientation G := orientation_from_flow (burn_flow L) (burn_flow_reverse L h_full)
lemma dp_dec {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (h_full : ∀ (v :G.V), v ∈ L.list) (p : DirectedPath (burn_orientation L h_full)) :
  List.IsChain (· > ·) (p.vertices.map (λ v => List.idxOf v L.list)) := by
  refine List.isChain_map_of_isChain (f := fun v => List.idxOf v L.list) ?_ p.valid_edges
  intro v v' h_edge
  dsimp only [directed_edge] at h_edge
  simp only [burn_orientation] at h_edge
  dsimp only [orientation_from_flow] at h_edge
  have h_count : Multiset.count ⟨v,v'⟩ (multiset_of_count (burn_flow L)) > 0 := by
    contrapose! h_edge with h_zero
    apply Nat.eq_zero_of_le_zero at h_zero
    exact Multiset.count_eq_zero.mp h_zero
  simp only [count_of_multiset_of_count, gt_iff_lt] at h_count
  dsimp only [burn_flow] at h_count
  by_contra! h_not_gt
  have : ¬ (v ∈ L.list ∧ List.idxOf v' L.list < List.idxOf v L.list) := by
    intro ⟨_, h_lt⟩
    omega
  simp only [this, ↓reduceIte, lt_self_iff_false] at h_count
lemma burn_nodup {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (h_full : ∀ (v :G.V), v ∈ L.list) (p : DirectedPath (burn_orientation L h_full)) : p.vertices.Nodup := by
  let q : List ℕ := p.vertices.map (λ v => List.idxOf v L.list)
  have h_sorted : q.SortedGT := (List.sortedGT_iff_isChain).2 (dp_dec L h_full p)
  exact List.Nodup.of_map (λ v => List.idxOf v L.list) h_sorted.nodup
lemma burn_acyclic {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (h_full : ∀ (v :G.V), v ∈ L.list) :
  is_acyclic G (burn_orientation L h_full) := by
  dsimp only [is_acyclic]
  intro p
  dsimp only [non_repeating]
  exact burn_nodup L h_full p
lemma burn_unique_source {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (h_full : ∀ (v :G.V), v ∈ L.list) :
  ∀ w, is_source G (burn_orientation L h_full) w → w = q := by
  intro w h_source
  dsimp only [is_source] at h_source
  rw [indeg_eq_sum_flow (burn_orientation L h_full) w] at h_source
  dsimp only [burn_orientation, orientation_from_flow, flow] at h_source
  simp only [count_of_multiset_of_count] at h_source
  -- Remove the decide and true parts
  contrapose! h_source with h_ne
  have ineq := burnin_degree L w (h_full w) h_ne
  -- rw [Nat.cast_sum] at ineq
  have : c.chips w ≥ 0 := by
    apply c.non_negative w
  let ineq := lt_of_le_of_lt this ineq
  apply ne_of_lt at ineq
  contrapose! ineq
  rw [Nat.cast_sum]
  simp only [Finset.sum_eq_zero_iff, mem_univ, forall_const] at ineq
  simp only [ineq, CharP.cast_eq_zero, sum_const_zero]
lemma burn_acyclic_with_unique_source {G : CFGraph} {q : G.V} {c : Config G q}
    (L : burn_list G c) (h_full : ∀ (v : G.V), v ∈ L.list) :
    acyclic_with_unique_source G (burn_orientation L h_full) q :=
  ⟨burn_acyclic L h_full, burn_unique_source L h_full⟩
theorem superstable_dhar {G : CFGraph} {q : G.V} {c : Config G q} (h_ss : superstable G q c) :
    ∃ (O : CFOrientation G) (hO : acyclic_with_unique_source G O q),
      c ≤ orientation_to_config G O q hO := by
  rcases superstable_burn_list G c h_ss with ⟨L, h_full⟩
  let O := burn_orientation L h_full
  have hO : acyclic_with_unique_source G O q := burn_acyclic_with_unique_source L h_full
  use O, hO
  intro v
  dsimp only [orientation_to_config, config_of_source]
  by_cases h_vq : v = q
  · -- Case: v = q
    rw [h_vq]
    simp only [↓reduceIte]
    linarith [c.q_zero]
  · -- Case: v ≠ q
    simp only [h_vq, ↓reduceIte]
    rw [indeg_eq_sum_flow O v]
    dsimp only [flow]
    dsimp only [burn_orientation, orientation_from_flow, O]
    simp only [count_of_multiset_of_count]
    have ineq := burnin_degree L v (h_full v) h_vq
    linarith
theorem orientation_config_maximal (G : CFGraph) (O : CFOrientation G) (q : G.V)
    (hO : acyclic_with_unique_source G O q) :
    maximal_superstable G (orientation_to_config G O q hO) := by
  dsimp only [maximal_superstable]
  let cO := orientation_to_config G O q hO
  have h_ssO : superstable G q cO := orientation_config_superstable G O q hO
  refine ⟨h_ssO, ?_⟩
  -- Goal is now just maximality of cO.
  -- Suppose another divisor is bigger. There's an orientation divisor yet above that one.
  intro c h_ss h_ge
  rcases superstable_dhar h_ss with ⟨O', hO', h_ge'⟩
  let c' := orientation_to_config G O' q hO'
  -- Sandwich c between cO and c', which have the same degree
  have h_deg_le : config_degree cO ≤ config_degree c := config_degree_mono h_ge
  have h_deg_le' : config_degree c ≤ config_degree c' := config_degree_mono h_ge'
  rw [config_degree_from_O O hO] at h_deg_le
  rw [config_degree_from_O O' hO'] at h_deg_le'
  have h_deg : config_degree c = genus G := by
    linarith
  have h_deg : config_degree c = config_degree cO := by
    rw [config_degree_from_O O hO]
    exact h_deg
  -- Now apply config equality from degree and ge
  exact config_eq_of_le_and_degree h_ge h_deg


