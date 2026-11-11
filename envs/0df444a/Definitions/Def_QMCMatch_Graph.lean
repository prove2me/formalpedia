-- Prove2me | Definitions.Def_QMCMatch_Graph
-- name    : QMCMatch_Graph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T15:23:26.554801+00:00
-- url     : https://prove2.me/theorems/94e18d8f-c1e8-4ca2-93e8-f7fcf1705ef5
-- title:
--   Exchanging two matchings on a component of their union
-- statement:
--   Lemmas on two matchings $M,N$. If a vertex set $C$ is closed under $M$ and under $N$ (no edge leaves it), then `swp M N C` is a matching that covers the vertices of $C$ as $N$ does and the others as $M$ does, and for every edge function $f$, $f(\mathrm{swp}\,M\,N\,C)+f(\mathrm{swp}\,N\,M\,C)=f(M)+f(N)$ (`swp_isM`, `swp_cov_in`, `swp_cov_out`, `swp_sum`, `swp_card`). A matching closed on $C$ covers exactly $2\,|M[C]|$ vertices of $C$ (`two_mul_card_inside`). The main lemma `comp_deficient_le_two`: in a connected component of $M\cup N$, at most two vertices are missed by $M$ or by $N$, because the component is a path or a cycle. It is proved by counting: a connected graph on $c$ vertices has at least $c-1$ edges, and every vertex has degree at most two.
-- source:
--   Supporting library for QuantumMaxCutEnergy.matching_polytope_integral_rounding (Prove2me Quantum Max-Cut campaign). Edmonds, Maximum matching and a polyhedron with 0,1-vertices, J. Res. Nat. Bur. Standards 69B, 1965; proof after Schrijver, Short proofs on the matching polyhedron, J. Combin. Theory Ser. B 34, 1983, and Combinatorial Optimization, Section 25.4 (Cunningham-Marsh formula).

import Definitions.Def_QMCMatch_Defs

/-!
Exchange of two matchings on a vertex set closed under both, and the structure of a
connected component of the union of two matchings.
-/

noncomputable section
open scoped BigOperators
open Classical
open QuantumMaxCutEnergy

namespace QMCMatch

variable {n : ℕ}

theorem isM_empty : IsM (∅ : Finset (Edge n)) := by
  intro e he
  exact absurd he (Finset.notMem_empty e)

theorem isM_subset {M N : Finset (Edge n)} (hM : IsM M) (h : N ⊆ M) : IsM N := by
  intro e he e' he' hne
  exact hM e (h he) e' (h he') hne

theorem isM_insert {M : Finset (Edge n)} (hM : IsM M) (e : Edge n)
    (h1 : ¬ cov M e.val.1) (h2 : ¬ cov M e.val.2) : IsM (insert e M) := by
  intro e1 h1' e2 h2' hne
  rw [Finset.mem_insert] at h1' h2'
  rcases h1' with h1' | h1' <;> rcases h2' with h2' | h2'
  · exact absurd (h1'.trans h2'.symm) hne
  · subst h1'
    exact ⟨fun h => h1 ⟨_, h2', Or.inl h⟩, fun h => h1 ⟨_, h2', Or.inr h⟩,
      fun h => h2 ⟨_, h2', Or.inl h⟩, fun h => h2 ⟨_, h2', Or.inr h⟩⟩
  · subst h2'
    exact ⟨fun h => h1 ⟨_, h1', Or.inl h.symm⟩, fun h => h2 ⟨_, h1', Or.inl h.symm⟩,
      fun h => h1 ⟨_, h1', Or.inr h.symm⟩, fun h => h2 ⟨_, h1', Or.inr h.symm⟩⟩
  · exact hM _ h1' _ h2' hne

theorem cov_mono {F F' : Finset (Edge n)} (h : F ⊆ F') {v : Fin n} (hv : cov F v) :
    cov F' v := by
  obtain ⟨e, he, h'⟩ := hv
  exact ⟨e, h he, h'⟩

/-- In a matching every vertex lies on at most one edge. -/
theorem isM_unique {M : Finset (Edge n)} (hM : IsM M) {e e' : Edge n} (he : e ∈ M)
    (he' : e' ∈ M) {v : Fin n} (hv : v = e.val.1 ∨ v = e.val.2)
    (hv' : v = e'.val.1 ∨ v = e'.val.2) : e = e' := by
  by_contra hne
  obtain ⟨a, b, c, d⟩ := hM e he e' he' hne
  rcases hv with hv | hv <;> rcases hv' with hv' | hv'
  · exact a (hv.symm.trans hv')
  · exact b (hv.symm.trans hv')
  · exact c (hv.symm.trans hv')
  · exact d (hv.symm.trans hv')

theorem mem_outside_iff (F : Finset (Edge n)) (C : Finset (Fin n)) (e : Edge n) :
    e ∈ outside F C ↔ e ∈ F ∧ e.val.1 ∉ C ∧ e.val.2 ∉ C := by
  unfold outside
  exact Finset.mem_filter

theorem mem_inside_iff (F : Finset (Edge n)) (C : Finset (Fin n)) (e : Edge n) :
    e ∈ inside F C ↔ e ∈ F ∧ e.val.1 ∈ C ∧ e.val.2 ∈ C := by
  unfold inside
  exact Finset.mem_filter

theorem mem_swp_iff (M N : Finset (Edge n)) (C : Finset (Fin n)) (e : Edge n) :
    e ∈ swp M N C ↔
      (e ∈ M ∧ e.val.1 ∉ C ∧ e.val.2 ∉ C) ∨ (e ∈ N ∧ e.val.1 ∈ C ∧ e.val.2 ∈ C) := by
  unfold swp
  rw [Finset.mem_union, mem_outside_iff, mem_inside_iff]

theorem mem_comp_iff (F : Finset (Edge n)) (t v : Fin n) :
    v ∈ comp F t ↔ Relation.ReflTransGen (adj F) t v := by
  unfold comp
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem swp_subset (M N S : Finset (Edge n)) (C : Finset (Fin n)) (hM : M ⊆ S)
    (hN : N ⊆ S) : swp M N C ⊆ S := by
  intro e he
  rw [mem_swp_iff] at he
  rcases he with h | h
  · exact hM h.1
  · exact hN h.1

theorem swp_isM (M N : Finset (Edge n)) (C : Finset (Fin n)) (hM : IsM M) (hN : IsM N) :
    IsM (swp M N C) := by
  intro e he e' he' hne
  rw [mem_swp_iff] at he he'
  rcases he with h | h <;> rcases he' with h' | h'
  · exact hM _ h.1 _ h'.1 hne
  · exact ⟨fun k => h.2.1 (by rw [k]; exact h'.2.1), fun k => h.2.1 (by rw [k]; exact h'.2.2),
      fun k => h.2.2 (by rw [k]; exact h'.2.1), fun k => h.2.2 (by rw [k]; exact h'.2.2)⟩
  · exact ⟨fun k => h'.2.1 (by rw [← k]; exact h.2.1), fun k => h'.2.2 (by rw [← k]; exact h.2.1),
      fun k => h'.2.1 (by rw [← k]; exact h.2.2), fun k => h'.2.2 (by rw [← k]; exact h.2.2)⟩
  · exact hN _ h.1 _ h'.1 hne

theorem swp_cov_in (M N : Finset (Edge n)) (C : Finset (Fin n))
    (hN : ∀ e ∈ N, (e.val.1 ∈ C ↔ e.val.2 ∈ C)) {v : Fin n} (hv : v ∈ C) :
    cov (swp M N C) v ↔ cov N v := by
  constructor
  · rintro ⟨e, he, h⟩
    rw [mem_swp_iff] at he
    rcases he with he | he
    · exfalso
      rcases h with h | h
      · exact he.2.1 (h ▸ hv)
      · exact he.2.2 (h ▸ hv)
    · exact ⟨e, he.1, h⟩
  · rintro ⟨e, he, h⟩
    refine ⟨e, ?_, h⟩
    rw [mem_swp_iff]
    right
    refine ⟨he, ?_⟩
    rcases h with h | h
    · have h1 : e.val.1 ∈ C := h ▸ hv
      exact ⟨h1, (hN e he).1 h1⟩
    · have h2 : e.val.2 ∈ C := h ▸ hv
      exact ⟨(hN e he).2 h2, h2⟩

theorem swp_cov_out (M N : Finset (Edge n)) (C : Finset (Fin n))
    (hM : ∀ e ∈ M, (e.val.1 ∈ C ↔ e.val.2 ∈ C)) {v : Fin n} (hv : v ∉ C) :
    cov (swp M N C) v ↔ cov M v := by
  constructor
  · rintro ⟨e, he, h⟩
    rw [mem_swp_iff] at he
    rcases he with he | he
    · exact ⟨e, he.1, h⟩
    · exfalso
      rcases h with h | h
      · exact hv (h ▸ he.2.1)
      · exact hv (h ▸ he.2.2)
  · rintro ⟨e, he, h⟩
    refine ⟨e, ?_, h⟩
    rw [mem_swp_iff]
    left
    refine ⟨he, ?_⟩
    rcases h with h | h
    · have h1 : e.val.1 ∉ C := h ▸ hv
      exact ⟨h1, fun h2 => h1 ((hM e he).2 h2)⟩
    · have h2 : e.val.2 ∉ C := h ▸ hv
      exact ⟨fun h1 => h2 ((hM e he).1 h1), h2⟩

theorem sum_swp_eq (M N : Finset (Edge n)) (C : Finset (Fin n)) (f : Edge n → ℕ) :
    ∑ e ∈ swp M N C, f e = ∑ e ∈ outside M C, f e + ∑ e ∈ inside N C, f e := by
  unfold swp
  apply Finset.sum_union
  rw [Finset.disjoint_left]
  intro e he he'
  rw [mem_outside_iff] at he
  rw [mem_inside_iff] at he'
  exact he.2.1 he'.2.1

theorem sum_split_eq (M : Finset (Edge n)) (C : Finset (Fin n))
    (hM : ∀ e ∈ M, (e.val.1 ∈ C ↔ e.val.2 ∈ C)) (f : Edge n → ℕ) :
    ∑ e ∈ M, f e = ∑ e ∈ outside M C, f e + ∑ e ∈ inside M C, f e := by
  have h : outside M C = M.filter (fun e => ¬ (e.val.1 ∈ C ∧ e.val.2 ∈ C)) := by
    unfold outside
    apply Finset.filter_congr
    intro e he
    have := hM e he
    tauto
  rw [h, add_comm]
  unfold inside
  exact (Finset.sum_filter_add_sum_filter_not M _ f).symm

theorem swp_sum (M N : Finset (Edge n)) (C : Finset (Fin n))
    (hM : ∀ e ∈ M, (e.val.1 ∈ C ↔ e.val.2 ∈ C))
    (hN : ∀ e ∈ N, (e.val.1 ∈ C ↔ e.val.2 ∈ C)) (f : Edge n → ℕ) :
    ∑ e ∈ swp M N C, f e + ∑ e ∈ swp N M C, f e = ∑ e ∈ M, f e + ∑ e ∈ N, f e := by
  rw [sum_swp_eq, sum_swp_eq, sum_split_eq M C hM f, sum_split_eq N C hN f]
  omega

theorem card_swp_eq (M N : Finset (Edge n)) (C : Finset (Fin n)) :
    (swp M N C).card = (outside M C).card + (inside N C).card := by
  have h := sum_swp_eq M N C (fun _ => 1)
  simpa using h

theorem card_split_eq (M : Finset (Edge n)) (C : Finset (Fin n))
    (hM : ∀ e ∈ M, (e.val.1 ∈ C ↔ e.val.2 ∈ C)) :
    M.card = (outside M C).card + (inside M C).card := by
  have h := sum_split_eq M C hM (fun _ => 1)
  simpa using h

theorem swp_card (M N : Finset (Edge n)) (C : Finset (Fin n))
    (hM : ∀ e ∈ M, (e.val.1 ∈ C ↔ e.val.2 ∈ C))
    (hN : ∀ e ∈ N, (e.val.1 ∈ C ↔ e.val.2 ∈ C)) :
    (swp M N C).card + (inside M C).card = M.card + (inside N C).card := by
  rw [card_swp_eq, card_split_eq M C hM]
  omega

theorem mem_comp_self (F : Finset (Edge n)) (t : Fin n) : t ∈ comp F t := by
  rw [mem_comp_iff]

theorem comp_closed (F : Finset (Edge n)) (t : Fin n) :
    ∀ e ∈ F, (e.val.1 ∈ comp F t ↔ e.val.2 ∈ comp F t) := by
  intro e he
  rw [mem_comp_iff, mem_comp_iff]
  constructor
  · intro h
    exact h.tail ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  · intro h
    exact h.tail ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩

theorem comp_cov (F : Finset (Edge n)) (t : Fin n) {v : Fin n} (hv : v ∈ comp F t)
    (hvt : v ≠ t) : cov F v := by
  rw [mem_comp_iff] at hv
  rcases hv.cases_tail with h | ⟨c, _, e, he, h | h⟩
  · exact absurd h hvt
  · exact ⟨e, he, Or.inr h.2⟩
  · exact ⟨e, he, Or.inl h.2⟩

/-- A matching closed on `C` covers an even number of vertices of `C`. -/
theorem two_mul_card_inside (M : Finset (Edge n)) (C : Finset (Fin n)) (hM : IsM M)
    (hC : ∀ e ∈ M, (e.val.1 ∈ C ↔ e.val.2 ∈ C)) :
    2 * (inside M C).card = (C.filter (fun v => cov M v)).card := by
  have h : C.filter (fun v => cov M v) =
      (inside M C).biUnion (fun e => ({e.val.1, e.val.2} : Finset (Fin n))) := by
    ext v
    rw [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hv, e, he, h⟩
      refine ⟨e, ?_, ?_⟩
      · rw [mem_inside_iff]
        refine ⟨he, ?_⟩
        rcases h with h | h
        · have h1 : e.val.1 ∈ C := h ▸ hv
          exact ⟨h1, (hC e he).1 h1⟩
        · have h2 : e.val.2 ∈ C := h ▸ hv
          exact ⟨(hC e he).2 h2, h2⟩
      · rw [Finset.mem_insert, Finset.mem_singleton]
        exact h
    · rintro ⟨e, he, h⟩
      rw [mem_inside_iff] at he
      rw [Finset.mem_insert, Finset.mem_singleton] at h
      refine ⟨?_, e, he.1, h⟩
      rcases h with h | h
      · rw [h]; exact he.2.1
      · rw [h]; exact he.2.2
  rw [h, Finset.card_biUnion]
  · rw [Finset.sum_const_nat (fun e _ => Finset.card_pair (ne_of_lt e.property)), mul_comm]
  · intro e he e' he' hne
    rw [Finset.mem_coe, mem_inside_iff] at he he'
    show Disjoint ({e.val.1, e.val.2} : Finset (Fin n)) {e'.val.1, e'.val.2}
    rw [Finset.disjoint_left]
    intro v hv hv'
    rw [Finset.mem_insert, Finset.mem_singleton] at hv hv'
    exact hne (isM_unique hM he.1 he'.1 hv hv')

theorem two_mul_card (M : Finset (Edge n)) (hM : IsM M) :
    2 * M.card = (Finset.univ.filter (fun v : Fin n => cov M v)).card := by
  have h := two_mul_card_inside M Finset.univ hM (fun e _ => by simp)
  have h' : inside M Finset.univ = M := by
    ext e
    rw [mem_inside_iff]
    simp
  rw [h'] at h
  exact h

theorem adj_ne (F : Finset (Edge n)) {a b : Fin n} (h : adj F a b) : a ≠ b := by
  obtain ⟨e, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rw [h1, h2]; exact ne_of_lt e.property
  · rw [h1, h2]; exact ne_of_gt e.property

theorem adj_symm (F : Finset (Edge n)) {a b : Fin n} (h : adj F a b) : adj F b a := by
  obtain ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · exact ⟨e, he, Or.inr ⟨h2, h1⟩⟩
  · exact ⟨e, he, Or.inl ⟨h2, h1⟩⟩

/-- A component has at least as many inside edges as vertices minus one. -/
theorem comp_card_le (F : Finset (Edge n)) (t : Fin n) :
    (comp F t).card ≤ (inside F (comp F t)).card + 1 := by
  let G : SimpleGraph {v // v ∈ comp F t} :=
    SimpleGraph.fromRel (fun a b => adj F a.1 b.1)
  have hreach : ∀ v, Relation.ReflTransGen (adj F) t v → ∀ hv : v ∈ comp F t,
      G.Reachable ⟨t, mem_comp_self F t⟩ ⟨v, hv⟩ := by
    intro v h
    induction h with
    | refl => intro hv; exact SimpleGraph.Reachable.refl _
    | @tail b c hab hbc ih =>
      intro hv
      have hb : b ∈ comp F t := (mem_comp_iff F t b).2 hab
      refine (ih hb).trans (SimpleGraph.Adj.reachable ?_)
      rw [SimpleGraph.fromRel_adj]
      exact ⟨fun h => adj_ne F hbc (congrArg Subtype.val h), Or.inl hbc⟩
  have hconn : G.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    exact ⟨⟨t, mem_comp_self F t⟩, fun w => hreach w.1 ((mem_comp_iff F t w.1).1 w.2) w.2⟩
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card] at h1
  have h2 : G.edgeFinset.card ≤ (inside F (comp F t)).card := by
    have hinj : Function.Injective (Sym2.map (Subtype.val : {v // v ∈ comp F t} → Fin n)) :=
      Sym2.map.injective Subtype.val_injective
    rw [← Finset.card_image_of_injective _ hinj]
    refine (Finset.card_le_card ?_).trans
      (Finset.card_image_le (s := inside F (comp F t)) (f := fun e => s(e.val.1, e.val.2)))
    intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    induction y using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at hy
      have hab : adj F a.1 b.1 := hy.2.elim id (adj_symm F)
      obtain ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hab
      · refine ⟨e, (mem_inside_iff _ _ _).2 ⟨he, h1 ▸ a.2, h2 ▸ b.2⟩, ?_⟩
        rw [Sym2.map_mk, h1, h2]
      · refine ⟨e, (mem_inside_iff _ _ _).2 ⟨he, h2 ▸ b.2, h1 ▸ a.2⟩, ?_⟩
        rw [Sym2.map_mk, h1, h2]
        exact Sym2.eq_swap
  omega

/-- A component of the union of two matchings is a path or a cycle: at most two of its
vertices are missed by one of the two matchings. -/
theorem comp_deficient_le_two (M N : Finset (Edge n)) (hM : IsM M) (hN : IsM N)
    (t : Fin n) :
    ((comp (M ∪ N) t).filter (fun v => ¬ cov M v ∨ ¬ cov N v)).card ≤ 2 := by
  have hcl := comp_closed (M ∪ N) t
  have hcM : ∀ e ∈ M, (e.val.1 ∈ comp (M ∪ N) t ↔ e.val.2 ∈ comp (M ∪ N) t) :=
    fun e he => hcl e (Finset.mem_union_left _ he)
  have hcN : ∀ e ∈ N, (e.val.1 ∈ comp (M ∪ N) t ↔ e.val.2 ∈ comp (M ∪ N) t) :=
    fun e he => hcl e (Finset.mem_union_right _ he)
  have h1 := comp_card_le (M ∪ N) t
  have h2 := two_mul_card_inside M _ hM hcM
  have h3 := two_mul_card_inside N _ hN hcN
  have h4 : (inside (M ∪ N) (comp (M ∪ N) t)).card ≤
      (inside M (comp (M ∪ N) t)).card + (inside N (comp (M ∪ N) t)).card := by
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro e he
    rw [mem_inside_iff, Finset.mem_union] at he
    rw [Finset.mem_union, mem_inside_iff, mem_inside_iff]
    rcases he.1 with h | h
    · exact Or.inl ⟨h, he.2⟩
    · exact Or.inr ⟨h, he.2⟩
  have h5 := Finset.card_filter_add_card_filter_not (s := comp (M ∪ N) t) (fun v => cov M v)
  have h6 := Finset.card_filter_add_card_filter_not (s := comp (M ∪ N) t) (fun v => cov N v)
  have h7 : ((comp (M ∪ N) t).filter (fun v => ¬ cov M v ∨ ¬ cov N v)).card ≤
      ((comp (M ∪ N) t).filter (fun v => ¬ cov M v)).card +
      ((comp (M ∪ N) t).filter (fun v => ¬ cov N v)).card := by
    rw [Finset.filter_or]
    exact Finset.card_union_le _ _
  omega

end QMCMatch


