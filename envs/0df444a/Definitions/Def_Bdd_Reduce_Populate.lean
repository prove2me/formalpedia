-- Prove2me | Definitions.Def_Bdd_Reduce_Populate
-- name    : Bdd_Reduce_Populate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:09:13.801685+00:00
-- url     : https://prove2.me/theorems/764ecea2-6d47-4747-8a5f-4cd04fdef649
-- title:
--   Populate
-- statement:
--   Definitions and structural lemmas for Populate, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Populate.lean

import Definitions.Def_Bdd_Reduce_State
import Theorems.Thm_Bdd_reduced_of_terminal
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_OBdd_reduced_of_terminal
import Theorems.Thm_RawBdd_RawPointer_cook_eq
import Theorems.Thm_Reduce_Invariant_ids_isSome
import Theorems.Thm_Reduce_set_id_ne
import Theorems.Thm_Reduce_set_id_self
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
open Pointer
open Bdd
open RawBdd
namespace Reduce
lemma get_id_bounded {n m : Nat} {O : OBdd n m} {ps : ProvedState n m} {i : Nat}
    (inv : Invariant O ps i) {p : Pointer m}
    (h : ∀ j, p = .node j → (ps.state.ids[j]).isSome) :
    (get_id ps p h).Bounded ps.state.size := by
  match p with
  | .terminal b => intro k hk; exact absurd hk (by simp [get_id])
  | .node k =>
    simp only [get_id]
    obtain ⟨ptr, hkptr⟩ := Option.isSome_iff_exists.mp (h k rfl)
    have heq : (ps.state.ids[k]).get (h k rfl) = ptr := by simp [hkptr]
    rw [heq]
    obtain ⟨_, hptr, _⟩ := inv.2 k ptr hkptr
    unfold RawPointer.Bounded
    intro i hi
    exact hptr hi
lemma get_id_semantic {n m : Nat} {O : OBdd n m} {ps : ProvedState n m} {i : Nat}
    (inv : Invariant O ps i) (p : Pointer m)
    (hp : Bdd.Ordered ⟨O.1.heap, p⟩)
    (hch : ∀ l, p = .node l → (ps.state.ids[l]).isSome) :
    ∃ (hptr : (get_id ps p hch).Bounded ps.state.size)
      (ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, (get_id ps p hch).cook hptr⟩),
      OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, (get_id ps p hch).cook hptr⟩, ho⟩ ∧
      ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, (get_id ps p hch).cook hptr⟩, ho⟩ I =
           OBdd.evaluate ⟨⟨O.1.heap, p⟩, hp⟩ I := by
  cases p with
  | terminal b =>
    refine ⟨fun h => absurd h (by simp [get_id]), Bdd.Ordered_of_terminal,
             Bdd.reduced_of_terminal, fun I => ?_⟩
    change OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, .terminal b⟩, _⟩ I =
           OBdd.evaluate ⟨⟨O.1.heap, .terminal b⟩, hp⟩ I
    exact (congrFun OBdd.evaluate_terminal I).trans (congrFun OBdd.evaluate_terminal I).symm
  | node l =>
    simp only [get_id]
    obtain ⟨_, hptr, ho, hred, heval⟩ := inv.2 l _ (Option.get_mem (hch l rfl))
    exact ⟨hptr, ho, hred, heval⟩
def populate_queue {n m : Nat} (O : OBdd n m)
    (i : Fin n)
    (acc : List ((RawPointer × RawPointer) × Fin m)) :
    (l : List (Fin m)) →
    (ps : ProvedState n m) →
    Invariant O ps i.1 →
    (∀ j ∈ l, O.1.heap[j].var.1 = i.1) →
    (∀ j ∈ l, Reachable O.1.heap O.1.root (.node j)) →
    (∀ entry ∈ acc, entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) →
    -- Non-redundancy of accumulator entries.
    (∀ entry ∈ acc, entry.1.1 ≠ entry.1.2) →
    -- Entry correctness for accumulator entries.
    (∀ entry ∈ acc, EntryCorrect O ps i.1 entry) →
    -- VarInvariant is preserved.
    VarInvariant O ps →
    { p : ProvedState n m × List ((RawPointer × RawPointer) × Fin m) //
        Invariant O p.1 i.1 ∧
        p.1.state.size = ps.state.size ∧
        -- AllAbove and HeapInjective are preserved (populate_queue only calls set_id).
        (AllAbove ps i.1 ∧ HeapInjective ps → AllAbove p.1 i.1 ∧ HeapInjective p.1) ∧
        -- Accumulator entries are preserved in the output list.
        (∀ entry ∈ acc, entry ∈ p.2) ∧
        -- ids only grow: once set, stays set.
        (∀ k : Fin m, (ps.state.ids[k]).isSome → (p.1.state.ids[k]).isSome) ∧
        (∀ j ∈ l, (∃ key, (key, j) ∈ p.2) ∨ (p.1.state.ids[j]).isSome) ∧
        -- All queue entries have key pointers bounded by the output state's heap size.
        (∀ entry ∈ p.2, entry.1.1.Bounded p.1.state.size ∧ entry.1.2.Bounded p.1.state.size) ∧
        -- All queue entries are non-redundant: key.1 ≠ key.2.
        (∀ entry ∈ p.2, entry.1.1 ≠ entry.1.2) ∧
        -- Entry correctness for all queue entries.
        (∀ entry ∈ p.2, EntryCorrect O p.1 i.1 entry) ∧
        -- VarInvariant is preserved.
        VarInvariant O p.1 }
  | [], ps, inv, _, _, hbounds_acc, hnonred_acc, hec_acc, hvarinv =>
      ⟨⟨ps, acc⟩, inv, rfl, id,
       fun _ he => he,
       fun _ hk => hk,
       fun _ hj => by simp at hj,
       hbounds_acc,
       hnonred_acc,
       hec_acc,
       hvarinv⟩
  | j :: tail, ps, inv, hvar, hreach, hbounds_acc, hnonred_acc, hec_acc, hvarinv => by
      have hvar_j   : O.1.heap[j].var.1 = i.1 := hvar   j (.head _)
      have hreach_j : Reachable O.1.heap O.1.root (.node j) := hreach j (.head _)
      -- For any child k of j (via some edge), ids[k] is already set.
      -- Proof: orderness gives var[j] < var[k]; completeness then gives isSome.
      have hchild : ∀ (p : Pointer m), Edge O.1.heap (.node j) p →
          ∀ k, p = .node k → (ps.state.ids[k]).isSome := by
        intro p hedgep k hk; subst hk
        have hreach_k : Reachable O.1.heap O.1.root (.node k) := .tail hreach_j hedgep
        apply inv.ids_isSome _ hreach_k
        have hmay := O.2
          (show O.1.RelevantEdge ⟨.node j, hreach_j⟩ ⟨.node k, hreach_k⟩ from hedgep)
        -- Unfold the ordered-edge condition to get a Nat inequality.
        simp only [Bdd.RelevantMayPrecede, Pointer.MayPrecede, Pointer.toVar,
                   Fin.mk_lt_mk] at hmay
        -- hmay : var[j].1 < var[k].1;  hvar_j : var[j].1 = i.1
        linarith [hvar_j]
      let lid := get_id ps O.1.heap[j].low  (hchild _ (Edge.low  rfl))
      let hid := get_id ps O.1.heap[j].high (hchild _ (Edge.high rfl))
      -- Helpers for reasoning about set_id without ps' aliasing issues.
      have ids_set_self : (set_id ps j lid).state.ids[j] = some lid := set_id_self ps j lid
      have ids_set_ne : ∀ k : Fin m, k ≠ j →
          (set_id ps j lid).state.ids[k] = ps.state.ids[k] :=
        fun k hkj => set_id_ne ps j k lid hkj
      by_cases heq : lid = hid
      · -- Redundant: set ids[j] := lid and recurse on tail.
        have hinv' : Invariant O (set_id ps j lid) i.1 := by
          constructor
          · -- Completeness: j has var = i.1, so i.1 < var[k] forces k ≠ j.
            intro k hk hreach_k
            have hkj : k ≠ j := fun h => by subst h; linarith [hvar_j]
            rw [ids_set_ne k hkj]; exact inv.1 k hk hreach_k
          · -- Correctness
            intro k ptr hkptr
            by_cases hkj : k = j
            · subst hkj
              rw [ids_set_self] at hkptr
              simp only [Option.some.injEq] at hkptr; subst hkptr
              -- lid correctly represents sub-BDD at k (redundant case: lid = hid)
              have hj : Bdd.Ordered ⟨O.1.heap, Pointer.node k⟩ :=
                Bdd.ordered_of_reachable hreach_j
              have hlow_ord : Bdd.Ordered ⟨O.1.heap, O.1.heap[k].low⟩ :=
                Bdd.ordered_of_reachable (Relation.ReflTransGen.tail hreach_j (Edge.low rfl))
              have hhigh_ord : Bdd.Ordered ⟨O.1.heap, O.1.heap[k].high⟩ :=
                Bdd.ordered_of_reachable (Relation.ReflTransGen.tail hreach_j (Edge.high rfl))
              obtain ⟨hptr, ho, hred, heval_low⟩ :=
                get_id_semantic inv _ hlow_ord (hchild _ (Edge.low rfl))
              obtain ⟨hptr_h, ho_h, _, heval_high⟩ :=
                get_id_semantic inv _ hhigh_ord (hchild _ (Edge.high rfl))
              refine ⟨hj, hptr, ho, hred, fun I => ?_⟩
              -- cook with equal raw pointers gives equal Pointer m (bounds are Props).
              have cook_eq_of_eq : ∀ (p q : RawPointer)
                  (hp : p.Bounded ps.state.size) (hq : q.Bounded ps.state.size),
                  p = q → p.cook hp = q.cook hq := fun p q hp hq hpq => by
                subst hpq; exact RawPointer.cook_eq
              have hcook_eq : hid.cook hptr_h = lid.cook hptr :=
                cook_eq_of_eq hid lid hptr_h hptr heq.symm
              -- evaluations at hid and lid in cook_heap coincide.
              have heval_hid_eq_lid :
                  OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, hid.cook hptr_h⟩, ho_h⟩ I =
                  OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, lid.cook hptr⟩, ho⟩ I :=
                congrArg (OBdd.evaluate · I)
                  (Subtype.ext (by simp [hcook_eq]))
              -- eval(high in old) = eval(low in old): both children reduce to lid = hid.
              have branches_eq :
                  OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[k].high⟩, hhigh_ord⟩ I =
                  OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[k].low⟩, hlow_ord⟩ I :=
                (heval_high I).symm.trans (heval_hid_eq_lid.trans (heval_low I))
              -- Proof of ordered-proof-irrelevance for evaluate.
              have eval_pi : ∀ (B : Bdd n m) (h1 h2 : B.Ordered) (I : Vector Bool n),
                  OBdd.evaluate ⟨B, h1⟩ I = OBdd.evaluate ⟨B, h2⟩ I :=
                fun B h1 h2 I => congrArg (OBdd.evaluate · I) (Subtype.ext rfl)
              calc OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, lid.cook hptr⟩, ho⟩ I
                  = OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[k].low⟩, hlow_ord⟩ I :=
                    heval_low I
                _ = if I[O.1.heap[k].var]
                      then OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[k].high⟩, hhigh_ord⟩ I
                      else OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[k].low⟩, hlow_ord⟩ I := by
                    rw [branches_eq]; simp
                _ = OBdd.evaluate ⟨⟨O.1.heap, Pointer.node k⟩, hj⟩ I := by
                    exact (OBdd.evaluate_node (v := O.1.heap) (j := k) (h := hj) (I := I)).symm
            · rw [ids_set_ne k hkj] at hkptr
              exact inv.2 k ptr hkptr
        -- EntryCorrect is preserved through set_id ps j lid for acc entries.
        have hec_acc' : ∀ entry ∈ acc, EntryCorrect O (set_id ps j lid) i.1 entry := by
          intro entry hmem
          obtain ⟨hr, hv, hlo, hhi, hlo_t, hhi_t⟩ := hec_acc entry hmem
          refine ⟨hr, hv, fun l hl => ?_, fun l hl => ?_, hlo_t, hhi_t⟩
          · -- l is a child of entry.2, so var[l] > i = var[j], hence l ≠ j
            have hord_j' : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩ := Bdd.ordered_of_reachable hr
            have hreach_l : Reachable O.1.heap O.1.root (.node l) :=
              .tail hr (Edge.low hl)
            have hmay := O.2 (show O.1.RelevantEdge ⟨.node entry.2, hr⟩ ⟨.node l, hreach_l⟩
              from Edge.low hl)
            simp only [Bdd.RelevantMayPrecede, Pointer.MayPrecede, Pointer.toVar, Fin.mk_lt_mk] at hmay
            have hlj : l ≠ j := fun h => by subst h; linarith [hv]
            rw [ids_set_ne l hlj]; exact hlo l hl
          · have hreach_l : Reachable O.1.heap O.1.root (.node l) :=
              .tail hr (Edge.high hl)
            have hmay := O.2 (show O.1.RelevantEdge ⟨.node entry.2, hr⟩ ⟨.node l, hreach_l⟩
              from Edge.high hl)
            simp only [Bdd.RelevantMayPrecede, Pointer.MayPrecede, Pointer.toVar, Fin.mk_lt_mk] at hmay
            have hlj : l ≠ j := fun h => by subst h; linarith [hv]
            rw [ids_set_ne l hlj]; exact hhi l hl
        -- VarInvariant is preserved through set_id ps j lid.
        have hvarinv' : VarInvariant O (set_id ps j lid) := by
          intro j₀ k₀ hids₀
          by_cases hjj₀ : j₀ = j
          · -- j₀ = j: ids[j] was just set to lid
            rw [hjj₀] at hids₀ ⊢
            rw [ids_set_self] at hids₀
            have hids₀ := Option.some.inj hids₀
            -- hids₀ : lid = .inr k₀.1
            -- lid = get_id ps O.1.heap[j].low h. Examine O.1.heap[j].low.
            -- lid = .inr k₀.1 (from hids₀). Need: O.heap[j].var ≤ ps.heap[k₀].va
            -- lid came from get_id on the low child.
            -- Use a helper lemma to extract the child node index.
            have ⟨l, hlow, hids_l⟩ : ∃ l, O.1.heap[j].low = .node l ∧
                ps.state.ids[l] = some (.inr k₀.1) := by
              -- lid = get_id ps O.1.heap[j].low _. Case-split on the low pointer.
              cases hlow_case : O.1.heap[j].low with
              | terminal b =>
                have hlid_bool : lid = .inl b := by
                  simp only [lid]; simp_rw [hlow_case]; rfl
                exact absurd (hlid_bool ▸ hids₀) (by simp)
              | node l =>
                use l, rfl
                have hlid_eq : lid = (ps.state.ids[l]).get
                    (hchild (.node l) (Edge.low hlow_case) l rfl) := by
                  simp only [lid]; simp_rw [hlow_case]; rfl
                rw [hlid_eq] at hids₀
                exact (Option.some_get _).symm.trans (congrArg some hids₀)
            have hvi := hvarinv l k₀ hids_l
            have hmay := O.2 (show O.1.RelevantEdge ⟨.node j, hreach_j⟩
              ⟨.node l, .tail hreach_j (Edge.low hlow)⟩ from Edge.low hlow)
            simp only [Bdd.RelevantMayPrecede, Pointer.MayPrecede, Pointer.toVar,
                       Fin.mk_lt_mk] at hmay
            exact Nat.le_trans (Nat.le_of_lt hmay) hvi
          · rw [ids_set_ne j₀ hjj₀] at hids₀
            exact hvarinv j₀ k₀ hids₀
        obtain ⟨⟨ps_f, list_f⟩, hinv_f, hsize_f, hpres_f, hacc_f, hmono_f, hpost_f, hbounds_f, hnonred_f, hec_f, hvarinv_f⟩ :=
          populate_queue O i acc tail (set_id ps j lid) hinv'
            (fun k hk => hvar   k (.tail _ hk))
            (fun k hk => hreach k (.tail _ hk))
            -- accumulator bounds unchanged (size of set_id = size of ps)
            hbounds_acc
            hnonred_acc
            hec_acc'
            hvarinv'
        exact ⟨⟨ps_f, list_f⟩, hinv_f, hsize_f, hpres_f, hacc_f,
               fun k hk => hmono_f k (by
                 by_cases hkj : k = j
                 · subst hkj; simp [ids_set_self]
                 · rw [ids_set_ne k hkj]; exact hk),
               fun k hk => by
                 cases hk with
                 | head =>
                   right; exact hmono_f j (by simp [ids_set_self])
                 | tail _ hk' => exact hpost_f k hk',
               hbounds_f,
               hnonred_f,
               hec_f,
               hvarinv_f⟩
      · -- Non-redundant: add ((lid, hid), j) to accumulator; recurse unchanged.
        have hlid_bound : lid.Bounded ps.state.size := get_id_bounded inv (hchild _ (Edge.low  rfl))
        have hhid_bound : hid.Bounded ps.state.size := get_id_bounded inv (hchild _ (Edge.high rfl))
        -- EntryCorrect for the new entry ((lid, hid), j)
        -- Helper: get_id on a node pointer yields (ids[l]).get
        have get_id_node : ∀ (l : Fin m) (h : ∀ k, Pointer.node l = .node k → (ps.state.ids[k]).isSome),
            get_id ps (.node l) h = (ps.state.ids[l]).get (h l rfl) := fun _ _ => rfl
        -- Helper: get_id on terminal yields .inl b
        have get_id_terminal : ∀ (b : Bool) (h : ∀ k, Pointer.terminal b = .node k → (ps.state.ids[k]).isSome),
            get_id ps (.terminal b) h = .inl b := fun _ _ => rfl
        have hec_new : EntryCorrect O ps i.1 ⟨⟨lid, hid⟩, j⟩ := by
          refine ⟨hreach_j, hvar_j, fun l hl => ?_, fun l hl => ?_, fun b hb => ?_, fun b hb => ?_⟩
          · -- lid = get_id ps (.node l) _, i.e., (ids[l]).get _
            have hlid : lid = (ps.state.ids[l]).get (hchild _ (Edge.low rfl) l hl) := by
              simp only [lid]
              simp_rw [hl]
              rfl
            rw [hlid]; exact (Option.some_get _).symm
          · have hhid : hid = (ps.state.ids[l]).get (hchild _ (Edge.high rfl) l hl) := by
              simp only [hid]
              simp_rw [hl]
              rfl
            rw [hhid]; exact (Option.some_get _).symm
          · have : lid = .inl b := by
              simp only [lid]
              simp_rw [hb]
              rfl
            exact this
          · have : hid = .inl b := by
              simp only [hid]
              simp_rw [hb]
              rfl
            exact this
        obtain ⟨⟨ps_f, list_f⟩, hinv_f, hsize_f, hpres_f, hacc_f, hmono_f, hpost_f, hbounds_f, hnonred_f, hec_f, hvarinv_f⟩ :=
          populate_queue O i (⟨⟨lid, hid⟩, j⟩ :: acc) tail ps inv
            (fun k hk => hvar   k (.tail _ hk))
            (fun k hk => hreach k (.tail _ hk))
            -- bounds for the new head entry + old acc entries
            (fun entry he => by
              cases he with
              | head => exact ⟨hlid_bound, hhid_bound⟩
              | tail _ he' => exact hbounds_acc entry he')
            -- non-redundancy: new entry has lid ≠ hid, old acc entries are non-redundant
            (fun entry he => by
              cases he with
              | head => exact heq
              | tail _ he' => exact hnonred_acc entry he')
            -- entry correctness for new entry + old acc entries
            (fun entry he => by
              cases he with
              | head => exact hec_new
              | tail _ he' => exact hec_acc entry he')
            hvarinv
        exact ⟨⟨ps_f, list_f⟩, hinv_f, hsize_f, hpres_f,
               fun e he => hacc_f e (.tail _ he),
               hmono_f,
               fun k hk => by
                 cases hk with
                 | head => left; exact ⟨⟨lid, hid⟩, hacc_f _ (.head _)⟩
                 | tail _ hk' => exact hpost_f k hk',
               hbounds_f,
               hnonred_f,
               hec_f,
               hvarinv_f⟩
end Reduce


