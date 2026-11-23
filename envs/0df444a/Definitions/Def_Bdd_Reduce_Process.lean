-- Prove2me | Definitions.Def_Bdd_Reduce_Process
-- name    : Bdd_Reduce_Process
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:12:10.869811+00:00
-- url     : https://prove2.me/theorems/4e41c4d2-96b3-4854-a483-3590a18d3216
-- title:
--   Process
-- statement:
--   Definitions and structural lemmas for Process, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Process.lean

import Definitions.Def_Bdd_Reduce_Populate
import Theorems.Thm_Bdd_high_root_eq_high
import Theorems.Thm_Bdd_low_root_eq_low
import Theorems.Thm_Bdd_ordered_of_low_high_ordered
import Theorems.Thm_Bdd_reduced_of_terminal
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_Node_equiv_symm
import Theorems.Thm_OBdd_high_root_eq_high
import Theorems.Thm_OBdd_low_root_eq_low
import Theorems.Thm_OBdd_reduced_of_terminal
import Theorems.Thm_OBdd_toTree_eq_toTree_of_ordered_heap_all_reachable_eq
import Theorems.Thm_P2M_OBdd_evaluate_terminal__321343d95937
import Theorems.Thm_P2M_OBdd_toTree_terminal__6f80b985dd51
import Theorems.Thm_Pointer_Reachable_iff
import Theorems.Thm_Pointer_equiv_symm
import Theorems.Thm_RawBdd_RawNode_cook_equiv
import Theorems.Thm_RawBdd_RawPointer_cook_equiv
import Theorems.Thm_RawBdd_cook_inj
import Theorems.Thm_RawBdd_push_evaluate
import Theorems.Thm_RawBdd_push_ordered
import Theorems.Thm_Reduce_keyLE_antisymm
import Theorems.Thm_Reduce_keyLE_refl
import Theorems.Thm_Reduce_keyLE_trans
import Theorems.Thm_Reduce_push_back_lt
import Theorems.Thm_Reduce_set_id_ne
import Theorems.Thm_Reduce_set_id_self
import Theorems.Thm_Reduce_structural_canonical_reduced
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered RawBdd.RawPointer RawBdd.RawPointer.Bounded Subrelation
open Pointer
open Bdd
open RawBdd
namespace Reduce
structure StepInv {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) (i : Nat) (s₀ : Nat)
    (curkey : RawPointer × RawPointer) (curptr : RawPointer)
    (Q : List ((RawPointer × RawPointer) × Fin m)) : Prop where
  hs0        : s₀ ≤ ps.state.size
  hbase      : ∀ k : Fin ps.state.size, k.1 < s₀ → i < ps.state.heap[k].va.1
  hsuffix    : ∀ k : Fin ps.state.size, s₀ ≤ k.1 → ps.state.heap[k].va.1 = i
  hheapinj   : HeapInjective ps
  hvarinv    : VarInvariant O ps
  hcurlvl    : ∀ k : Fin ps.state.size, curptr = .inr k.1 → ps.state.heap[k].va.1 = i
  hnonred    : ∀ e ∈ Q, e.1.1 ≠ e.1.2
  hbounds0   : ∀ e ∈ Q, e.1.1.Bounded s₀ ∧ e.1.2.Bounded s₀
  hsorted    : Q.Pairwise (fun a b => KeyLE a.1 b.1)
  hcur_le    : ∀ e ∈ Q, KeyLE curkey e.1
  hpushed_le : ∀ k : Fin ps.state.size, s₀ ≤ k.1 →
                 KeyLE (ps.state.heap[k].lo, ps.state.heap[k].hi) curkey
def StepInv.hbnd {n m : Nat} {O : OBdd n m} {ps : ProvedState n m} {i s₀ : Nat}
    {curkey : RawPointer × RawPointer} {curptr : RawPointer}
    {Q : List ((RawPointer × RawPointer) × Fin m)}
    (si : StepInv O ps i s₀ curkey curptr Q) {e : (RawPointer × RawPointer) × Fin m}
    (hmem : e ∈ Q) : e.1.1.Bounded ps.state.size ∧ e.1.2.Bounded ps.state.size :=
  ⟨RawPointer.bounded_of_le (si.hbounds0 e hmem).1 si.hs0,
   RawPointer.bounded_of_le (si.hbounds0 e hmem).2 si.hs0⟩
lemma push_reduced {n s : Nat} {v : Vector (RawNode n) s} {N : RawNode n}
    {hh  : ∀ k : Fin s,       v[k].Bounded k}
    {hh' : ∀ k : Fin (s + 1), (v.push N)[k].Bounded k}
    {p : RawPointer} {hp : p.Bounded s} {hp' : p.Bounded (s + 1)}
    {ho  : Bdd.Ordered ⟨cook_heap v hh,       p.cook hp ⟩}
    {ho' : Bdd.Ordered ⟨cook_heap (v.push N) hh', p.cook hp'⟩}
    (hred : OBdd.Reduced ⟨⟨cook_heap v hh, p.cook hp⟩, ho⟩) :
    OBdd.Reduced ⟨⟨cook_heap (v.push N) hh', p.cook hp'⟩, ho'⟩ := by
  have back := @push_back_lt n s v N hh hh' p hp hp'
  -- For any node j reachable from any reachable pointer q in new heap,
  -- j.1 < s and nodes are equiv.
  have sub_back : ∀ (q : Pointer (s + 1)),
      Pointer.Reachable (cook_heap (v.push N) hh') (p.cook hp') q →
      ∀ j : Fin (s + 1),
      Pointer.Reachable (cook_heap (v.push N) hh') q (.node j) →
      ∃ hj : j.1 < s,
        Node.equiv (cook_heap v hh)[(⟨j.1, hj⟩ : Fin s)] (cook_heap (v.push N) hh')[j] := by
    intro q hq_root j hj_q
    have hj_root := Relation.ReflTransGen.trans hq_root hj_q
    obtain ⟨hj_lt, _⟩ := back j hj_root
    exact ⟨hj_lt, by
      simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn,
        Vector.getElem_push_lt hj_lt]
      exact Node.equiv_symm RawNode.cook_equiv⟩
  -- Helper: Pointer.equiv for same type implies equality.
  have equiv_eq : ∀ {m : Nat} (a b : Pointer m), Pointer.equiv a b → a = b := by
    intro m a b hab
    cases a with
    | terminal ba =>
      have := hab.1 ba rfl
      exact this ▸ rfl
    | node ja =>
      obtain ⟨jb, hjb_eq, hjab⟩ := hab.2 ja rfl
      rw [hjb_eq]
      congr 1
      exact Fin.ext hjab
  -- Helper: Pointer.equiv is transitive.
  have equiv_trans : ∀ {m1 m2 m3 : Nat} {a : Pointer m1} {b : Pointer m2} {c : Pointer m3},
      Pointer.equiv a b → Pointer.equiv b c → Pointer.equiv a c := by
    intro m1 m2 m3 a b c hab hbc
    constructor
    · intro ba ha
      exact hbc.1 ba (hab.1 ba ha)
    · intro ja hja
      obtain ⟨jb, hjb, hjab⟩ := hab.2 ja hja
      obtain ⟨jc, hjc, hjbc⟩ := hbc.2 jb hjb
      exact ⟨jc, hjc, hjab.trans hjbc⟩
  -- Part 1: NoRedundancy
  constructor
  · intro ⟨q, hq_reach⟩ hred_q
    cases q with
    | terminal b => cases hred_q
    | node j =>
      obtain ⟨hj_lt, hj_reach_old⟩ := back j hq_reach
      cases hred_q with
      | red hlow_eq_high =>
        -- Node.equiv between old and new heaps at index j
        obtain ⟨_, hnode_equiv⟩ := sub_back (.node j) hq_reach j .refl
        obtain ⟨_, hequiv_low, hequiv_high⟩ := hnode_equiv
        -- hequiv_low : Pointer.equiv old_heap[j'].low new_heap[j].low
        -- hequiv_high : Pointer.equiv old_heap[j'].high new_heap[j].high
        -- hlow_eq_high : new_heap[j].low = new_heap[j].high
        -- Therefore old.low ≡ new.low = new.high ≡ old.high
        -- i.e., Pointer.equiv old.low old.high
        have hequiv_high' : Pointer.equiv
            (cook_heap v hh)[(⟨j.1, hj_lt⟩ : Fin s)].low
            (cook_heap v hh)[(⟨j.1, hj_lt⟩ : Fin s)].high :=
          equiv_trans hequiv_low (hlow_eq_high ▸ Pointer.equiv_symm hequiv_high)
        -- Since both are in Pointer s, equiv implies equality
        have hred_old : (cook_heap v hh)[(⟨j.1, hj_lt⟩ : Fin s)].low =
                        (cook_heap v hh)[(⟨j.1, hj_lt⟩ : Fin s)].high :=
          equiv_eq _ _ hequiv_high'
        exact hred.1 ⟨.node ⟨j.1, hj_lt⟩, hj_reach_old⟩ (Pointer.Redundant.red hred_old)
  · -- Part 2: SimilarRP injectivity
    -- Need: if SimilarRP O' rp rq, then rp.val = rq.val
    intro ⟨rp, hrp_reach⟩ ⟨rq, hrq_reach⟩ hsim
    -- hsim : SimilarRP O' ⟨rp, _⟩ ⟨rq, _⟩ (= toTree equality of sub-BDDs)
    -- Case split: both must be same kind (terminal/node) for SimilarRP.
    -- We need the toTree equality for case analysis.
    have htree_sim : OBdd.toTree ⟨⟨cook_heap (v.push N) hh', rp⟩,
          Bdd.ordered_of_reachable hrp_reach⟩ =
        OBdd.toTree ⟨⟨cook_heap (v.push N) hh', rq⟩,
          Bdd.ordered_of_reachable hrq_reach⟩ := hsim
    -- Case analysis on rp
    cases rp with
    | terminal bp =>
      cases rq with
      | terminal bq =>
        -- htree_sim was simplified by cases to: bp = bq (or leaf bp = leaf bq)
        -- Goal: ⟨terminal bp, _⟩ = ⟨terminal bq, _⟩
        simp [OBdd.toTree_terminal'] at htree_sim
        subst htree_sim
        rfl
      | node jq =>
        exact absurd htree_sim (by simp [OBdd.toTree_terminal', OBdd.toTree_node])
    | node jp =>
      cases rq with
      | terminal bq =>
        exact absurd htree_sim (by simp [OBdd.toTree_terminal', OBdd.toTree_node])
      | node jq =>
        -- Both nodes: use push_ordered_aux and toTree transfer
        obtain ⟨hjp_lt, hjp_reach_old⟩ := back jp hrp_reach
        obtain ⟨hjq_lt, hjq_reach_old⟩ := back jq hrq_reach
        -- toTree in new heap = toTree in old heap, for each sub-BDD
        -- Ordered sub-BDDs in old heap
        let jp' : Fin s := ⟨jp.1, hjp_lt⟩
        let jq' : Fin s := ⟨jq.1, hjq_lt⟩
        -- Ordered sub-BDDs in old and new heaps (inferred from reachability).
        have hop  : Bdd.Ordered ⟨cook_heap v hh,         .node jp'⟩ :=
          Bdd.ordered_of_reachable (O := ⟨⟨cook_heap v hh, p.cook hp⟩, ho⟩)         hjp_reach_old
        have hoq  : Bdd.Ordered ⟨cook_heap v hh,         .node jq'⟩ :=
          Bdd.ordered_of_reachable (O := ⟨⟨cook_heap v hh, p.cook hp⟩, ho⟩)         hjq_reach_old
        have hop' : Bdd.Ordered ⟨cook_heap (v.push N) hh', .node jp⟩ :=
          Bdd.ordered_of_reachable (O := ⟨⟨cook_heap (v.push N) hh', p.cook hp'⟩, ho'⟩) hrp_reach
        have hoq' : Bdd.Ordered ⟨cook_heap (v.push N) hh', .node jq⟩ :=
          Bdd.ordered_of_reachable (O := ⟨⟨cook_heap (v.push N) hh', p.cook hp'⟩, ho'⟩) hrq_reach
        have htree_p :
            OBdd.toTree ⟨⟨cook_heap v hh, Pointer.node jp'⟩, hop⟩ =
            OBdd.toTree ⟨⟨cook_heap (v.push N) hh', Pointer.node jp⟩, hop'⟩ := by
          apply OBdd.toTree_eq_toTree_of_ordered_heap_all_reachable_eq
          · exact sub_back (Pointer.node jp) hrp_reach
          · -- Pointer.equiv (.node jp : Pointer (s+1)) (.node jp' : Pointer s), jp.1 = jp'.1
            constructor
            · intro b hb; exact absurd hb (by simp)
            · intro j hj
              exact ⟨jp', rfl, by have h := Pointer.node.inj hj; subst h; rfl⟩
        have htree_q :
            OBdd.toTree ⟨⟨cook_heap v hh, Pointer.node jq'⟩, hoq⟩ =
            OBdd.toTree ⟨⟨cook_heap (v.push N) hh', Pointer.node jq⟩, hoq'⟩ := by
          apply OBdd.toTree_eq_toTree_of_ordered_heap_all_reachable_eq
          · exact sub_back (Pointer.node jq) hrq_reach
          · constructor
            · intro b hb; exact absurd hb (by simp)
            · intro j hj
              exact ⟨jq', rfl, by have h := Pointer.node.inj hj; subst h; rfl⟩
        -- SimilarRP in old BDD
        have hsim_old : OBdd.SimilarRP ⟨⟨cook_heap v hh, p.cook hp⟩, ho⟩
            ⟨Pointer.node jp', hjp_reach_old⟩
            ⟨Pointer.node jq', hjq_reach_old⟩ := by
          show OBdd.toTree _ = OBdd.toTree _
          rw [htree_p, htree_q]
          exact htree_sim
        have hval_eq := hred.2 hsim_old
        -- hval_eq : (InvImage Eq Subtype.val) ⟨.node jp', _⟩ ⟨.node jq', _⟩
        --         = (.node jp' = .node jq')
        simp only [InvImage, Pointer.node.injEq] at hval_eq
        -- hval_eq : jp' = jq' (as Fin s); since jp.1 = jp'.1 and jq.1 = jq'.1, jp = jq
        have hjpjq : jp.1 = jq.1 := by simpa using Fin.ext_iff.mp hval_eq
        exact congrArg Pointer.node (Fin.ext hjpjq)
lemma push_node_correct' {n m : Nat} {i : Nat}
    (O : OBdd n m)
    (ps : ProvedState n m)
    (inv : Invariant O ps i)
    (entry : (RawPointer × RawPointer) × Fin m)
    (hec : EntryCorrect O ps i entry)
    (hbound : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size)
    (hnonred : entry.1.1 ≠ entry.1.2)
    (s₀ : Nat) (_hs0 : s₀ ≤ ps.state.size)
    (hbound0 : entry.1.1.Bounded s₀ ∧ entry.1.2.Bounded s₀)
    (hprefix : ∀ k : Fin ps.state.size, k.1 < s₀ → i < ps.state.heap[k].va.1)
    (hheapinj : HeapInjective ps)
    (hfresh : ∀ k : Fin ps.state.size,
        ps.state.heap[k] ≠ ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩) :
    let hN  : (RawNode.mk O.1.heap[entry.2].var entry.1.1 entry.1.2).Bounded
                ps.state.size := ⟨hbound.1, hbound.2⟩
    let ps₁ := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).1
    let ptr := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).2
    let ps₂ := set_id ps₁ entry.2 ptr
    ∃ hj  : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
    ∃ hp  : ptr.Bounded ps₂.state.size,
    ∃ ho  : Bdd.Ordered ⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩,
      OBdd.Reduced ⟨⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩, ho⟩ ∧
      ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩, ho⟩ I =
           OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I := by
  set s := ps.state.size
  set N : RawNode n := ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩
  have hN : N.Bounded s := ⟨hbound.1, hbound.2⟩
  -- Let hh' be the pushed heap's bound proof
  have hh' : ∀ k : Fin (s + 1), (ps.state.heap.push N)[k].Bounded k := (push_node ps N hN).1.hh
  -- Definitional equalities
  have hsize : (push_node ps N hN).1.state.size = s + 1 := rfl
  have hheap : (push_node ps N hN).1.state.heap = ps.state.heap.push N := rfl
  -- Witness 1: hj
  have hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩ := Bdd.ordered_of_reachable hec.1
  -- Witness 2: hp (ptr = .inr s, bounded by s+1)
  have hp : (push_node ps N hN).2.Bounded
      (set_id (push_node ps N hN).1 entry.2 (push_node ps N hN).2).state.size := by
    have hsize2 : (set_id (push_node ps N hN).1 entry.2 (push_node ps N hN).2).state.size = s + 1 := rfl
    intro j hj
    have hjs : s = j := Sum.inr.inj hj
    omega
  have hlo_ord : Bdd.Ordered ⟨O.1.heap, O.1.heap[entry.2].low⟩ := OBdd.ordered_of_low_edge hj
  have hhi_ord : Bdd.Ordered ⟨O.1.heap, O.1.heap[entry.2].high⟩ := OBdd.ordered_of_high_edge hj
  -- Inline child semantics for low child
  obtain ⟨hptr_lo, ho_lo, hred_lo, heval_lo⟩ :
      ∃ (hptr_lo : entry.1.1.Bounded s),
      ∃ (ho_lo : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, entry.1.1.cook hptr_lo⟩),
        OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, entry.1.1.cook hptr_lo⟩, ho_lo⟩ ∧
        ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, entry.1.1.cook hptr_lo⟩, ho_lo⟩ I =
             OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[entry.2].low⟩, hlo_ord⟩ I := by
    revert hlo_ord
    cases hlow : O.1.heap[entry.2].low with
    | terminal b =>
      intro hlo_ord
      have he : entry.1.1 = .inl b := hec.2.2.2.2.1 b hlow
      rw [he]
      exact ⟨by intro j hj; simp at hj, Bdd.Ordered_of_terminal, Bdd.reduced_of_terminal,
             fun I => (congrFun OBdd.evaluate_terminal I).trans (congrFun OBdd.evaluate_terminal I).symm⟩
    | node l =>
      intro hlo_ord
      obtain ⟨_, hptr_lo, ho_lo, hred_lo, heval_lo⟩ := inv.2 l entry.1.1 (hec.2.2.1 l hlow)
      exact ⟨hptr_lo, ho_lo, hred_lo, fun I => (heval_lo I).trans
        (congrArg (OBdd.evaluate · I) (Subtype.ext (by simp)))⟩
  -- Inline child semantics for high child
  obtain ⟨hptr_hi, ho_hi, hred_hi, heval_hi⟩ :
      ∃ (hptr_hi : entry.1.2.Bounded s),
      ∃ (ho_hi : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, entry.1.2.cook hptr_hi⟩),
        OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, entry.1.2.cook hptr_hi⟩, ho_hi⟩ ∧
        ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, entry.1.2.cook hptr_hi⟩, ho_hi⟩ I =
             OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[entry.2].high⟩, hhi_ord⟩ I := by
    revert hhi_ord
    cases hhigh : O.1.heap[entry.2].high with
    | terminal b =>
      intro hhi_ord
      have he : entry.1.2 = .inl b := hec.2.2.2.2.2 b hhigh
      rw [he]
      exact ⟨by intro j hj; simp at hj, Bdd.Ordered_of_terminal, Bdd.reduced_of_terminal,
             fun I => (congrFun OBdd.evaluate_terminal I).trans (congrFun OBdd.evaluate_terminal I).symm⟩
    | node l =>
      intro hhi_ord
      obtain ⟨_, hptr_hi, ho_hi, hred_hi, heval_hi⟩ := inv.2 l entry.1.2 (hec.2.2.2.1 l hhigh)
      exact ⟨hptr_hi, ho_hi, hred_hi, fun I => (heval_hi I).trans
        (congrArg (OBdd.evaluate · I) (Subtype.ext (by simp)))⟩
  -- Lift child ordered BDDs to the new heap
  have hb1 : entry.1.1.Bounded (s + 1) := RawPointer.bounded_of_le hptr_lo (Nat.le_succ s)
  have hb2 : entry.1.2.Bounded (s + 1) := RawPointer.bounded_of_le hptr_hi (Nat.le_succ s)
  have ho_lo' : Bdd.Ordered ⟨cook_heap (ps.state.heap.push N) hh', entry.1.1.cook hb1⟩ :=
    push_ordered ho_lo
  have ho_hi' : Bdd.Ordered ⟨cook_heap (ps.state.heap.push N) hh', entry.1.2.cook hb2⟩ :=
    push_ordered ho_hi
  have hred_lo' := push_reduced (hp' := hb1) (ho' := ho_lo') hred_lo
  have hred_hi' := push_reduced (hp' := hb2) (ho' := ho_hi') hred_hi
  -- Compute the cooked node at index s
  have hMs_var : (cook_heap (ps.state.heap.push N) hh')[(⟨s, Nat.lt_succ_self s⟩ : Fin (s + 1))].var =
      O.1.heap[entry.2].var := by
    simp only [cook_heap, Vector.getElem_ofFn, Fin.getElem_fin,
               show s = ps.state.size from rfl, Vector.getElem_push_eq, RawNode.cook,
               show N.va = O.1.heap[entry.2].var from rfl]
  have hMs_low : (cook_heap (ps.state.heap.push N) hh')[(⟨s, Nat.lt_succ_self s⟩ : Fin (s + 1))].low =
      entry.1.1.cook hb1 := by
    simp only [cook_heap, Vector.getElem_ofFn, Fin.getElem_fin,
               show s = ps.state.size from rfl, Vector.getElem_push_eq, RawNode.cook,
               show N.lo = entry.1.1 from rfl]
  have hMs_high : (cook_heap (ps.state.heap.push N) hh')[(⟨s, Nat.lt_succ_self s⟩ : Fin (s + 1))].high =
      entry.1.2.cook hb2 := by
    simp only [cook_heap, Vector.getElem_ofFn, Fin.getElem_fin,
               show s = ps.state.size from rfl, Vector.getElem_push_eq, RawNode.cook,
               show N.hi = entry.1.2 from rfl]
  -- Helper: var of old node j < s in new heap = ps.state.heap[j].va
  have hMj_var : ∀ (j : Fin s),
      (cook_heap (ps.state.heap.push N) hh')[(⟨j.1, Nat.lt_trans j.isLt (Nat.lt_succ_self s)⟩ : Fin (s + 1))].var =
      ps.state.heap[j].va := by
    intro j
    simp only [cook_heap, Vector.getElem_ofFn, Fin.getElem_fin,
               Vector.getElem_push_lt (show j.1 < ps.state.size from j.isLt), RawNode.cook]
  -- Ordered: use ordered_of_low_high_ordered
  have hptr_cook : (push_node ps N hN).2.cook hp =
      .node (⟨s, Nat.lt_succ_self s⟩ : Fin (s + 1)) := by
    simp [push_node, RawPointer.cook]
    rfl
  have ho : Bdd.Ordered ⟨cook_heap (ps.state.heap.push N) hh',
      (.node (⟨s, Nat.lt_succ_self s⟩ : Fin (s + 1)))⟩ := by
    apply Bdd.ordered_of_low_high_ordered (h := rfl)
    · -- low ordered
      simp only [Bdd.low]
      rw [hMs_low]
      exact ho_lo'
    · -- B.var < B.low.var
      cases h11 : entry.1.1 with
      | inl b =>
        have hcook : entry.1.1.cook hb1 = .terminal b := by
          have key : ∀ (p : RawPointer) (h : p.Bounded (s+1)), p = .inl b → p.cook h = .terminal b :=
            fun p h hp => by subst hp; rfl
          exact key entry.1.1 hb1 h11
        simp only [Bdd.var, Bdd.low_root_eq_low, Bdd.low_heap_eq_heap]
        rw [hMs_low, hcook, Pointer.toVar_terminal_eq]
        simp only [Fin.lt_def, Pointer.toVar_node_eq]
        exact Fin.isLt _
      | inr j =>
        have hjlt0 : j < s₀ := hbound0.1 h11
        have hjlt : j < s := hbound.1 h11
        have hcook : entry.1.1.cook hb1 = .node ⟨j, hb1 h11⟩ := by
          have key : ∀ (p : RawPointer) (h : p.Bounded (s+1)), (hp : p = .inr j) → p.cook h = .node ⟨j, h hp⟩ :=
            fun p h hp => by subst hp; rfl
          exact key entry.1.1 hb1 h11
        simp only [Bdd.var, Bdd.low_root_eq_low, Bdd.low_heap_eq_heap]
        rw [hMs_low, hcook]
        simp only [Pointer.toVar_node_eq, Fin.lt_def]
        rw [show (⟨j, hb1 h11⟩ : Fin (s + 1)) =
              ⟨j, Nat.lt_trans hjlt (Nat.lt_succ_self s)⟩ from Fin.ext rfl]
        rw [hMs_var, hMj_var ⟨j, hjlt⟩]
        exact hec.2.1 ▸ hprefix ⟨j, hjlt⟩ hjlt0
    · -- high ordered
      simp only [Bdd.high]
      rw [hMs_high]
      exact ho_hi'
    · -- B.var < B.high.var
      cases h12 : entry.1.2 with
      | inl b =>
        have hcook : entry.1.2.cook hb2 = .terminal b := by
          have key : ∀ (p : RawPointer) (h : p.Bounded (s+1)), p = .inl b → p.cook h = .terminal b :=
            fun p h hp => by subst hp; rfl
          exact key entry.1.2 hb2 h12
        simp only [Bdd.var, Bdd.high_root_eq_high, Bdd.high_heap_eq_heap]
        rw [hMs_high, hcook, Pointer.toVar_terminal_eq]
        simp only [Fin.lt_def, Pointer.toVar_node_eq]
        exact Fin.isLt _
      | inr j =>
        have hjlt0 : j < s₀ := hbound0.2 h12
        have hjlt : j < s := hbound.2 h12
        have hcook : entry.1.2.cook hb2 = .node ⟨j, hb2 h12⟩ := by
          have key : ∀ (p : RawPointer) (h : p.Bounded (s+1)), (hp : p = .inr j) → p.cook h = .node ⟨j, h hp⟩ :=
            fun p h hp => by subst hp; rfl
          exact key entry.1.2 hb2 h12
        simp only [Bdd.var, Bdd.high_root_eq_high, Bdd.high_heap_eq_heap]
        rw [hMs_high, hcook]
        simp only [Pointer.toVar_node_eq, Fin.lt_def]
        rw [show (⟨j, hb2 h12⟩ : Fin (s + 1)) =
              ⟨j, Nat.lt_trans hjlt (Nat.lt_succ_self s)⟩ from Fin.ext rfl]
        rw [hMs_var, hMj_var ⟨j, hjlt⟩]
        exact hec.2.1 ▸ hprefix ⟨j, hjlt⟩ hjlt0
  -- NoRedundancy of the new BDD
  have hnored : Bdd.NoRedundancy ⟨cook_heap (ps.state.heap.push N) hh',
      .node (⟨s, Nat.lt_succ_self s⟩ : Fin (s + 1))⟩ := by
    intro ⟨ptr', hreach'⟩
    rcases Pointer.Reachable_iff.mp hreach' with h_root | ⟨j', h_node, h_child⟩
    · obtain rfl : ptr' = .node ⟨s, Nat.lt_succ_self s⟩ := h_root.symm
      intro hred; cases hred with
      | red heq =>
        rw [hMs_low, hMs_high] at heq
        exact hnonred (cook_inj heq)
    · have hj' : j' = ⟨s, Nat.lt_succ_self s⟩ := Pointer.node.inj h_node.symm
      subst hj'
      rcases h_child with h_lo | h_hi
      · rw [hMs_low] at h_lo; exact hred_lo'.1 ⟨ptr', h_lo⟩
      · rw [hMs_high] at h_hi; exact hred_hi'.1 ⟨ptr', h_hi⟩
  -- ho_final: ordered proof with ptr.cook hp
  have ho_final : Bdd.Ordered ⟨cook_heap (ps.state.heap.push N) hh',
      (push_node ps N hN).2.cook hp⟩ := by
    generalize h : (push_node ps N hN).2.cook hp = root_val
    rw [← h, hptr_cook] at *
    clear h
    exact ho
  -- OBdd equality: since ptr.cook hp = .node ⟨s,⋯⟩, the two OBdds are propositionally equal.
  have hO_eq : (⟨⟨cook_heap (ps.state.heap.push N) hh', (push_node ps N hN).2.cook hp⟩,
      ho_final⟩ : OBdd n (s + 1)) =
      ⟨⟨cook_heap (ps.state.heap.push N) hh', .node ⟨s, Nat.lt_succ_self s⟩⟩, ho⟩ :=
    Subtype.ext (congrArg
      (fun r => (⟨cook_heap (ps.state.heap.push N) hh', r⟩ : Bdd n (s + 1))) hptr_cook)
  -- hred_full: reduced
  have hred_full : OBdd.Reduced ⟨⟨cook_heap (ps.state.heap.push N) hh',
      (push_node ps N hN).2.cook hp⟩, ho_final⟩ := by
    rw [hO_eq]
    apply structural_canonical_reduced
    · -- hsc: heap injectivity
      intro k1 k2 heq_k
      simp only [Fin.getElem_fin] at heq_k
      by_cases hk1s : k1.1 = s
      · by_cases hk2s : k2.1 = s
        · exact Fin.ext (hk1s.trans hk2s.symm)
        · exfalso
          have hk2lt : k2.1 < s := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp k2.isLt) hk2s
          have hk1eq : k1 = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext hk1s
          subst hk1eq
          rw [Vector.getElem_push_eq, Vector.getElem_push_lt hk2lt] at heq_k
          -- heq_k : N = ps.state.heap[k2.1]; contradicts freshness of N.
          exact hfresh ⟨k2.1, hk2lt⟩ heq_k.symm
      · have hk1lt : k1.1 < s := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp k1.isLt) hk1s
        by_cases hk2s : k2.1 = s
        · exfalso
          have hk2eq : k2 = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext hk2s
          subst hk2eq
          rw [Vector.getElem_push_lt hk1lt, Vector.getElem_push_eq] at heq_k
          -- heq_k : ps.state.heap[k1.1] = N; contradicts freshness of N.
          exact hfresh ⟨k1.1, hk1lt⟩ heq_k
        · have hk2lt : k2.1 < s := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp k2.isLt) hk2s
          rw [Vector.getElem_push_lt hk1lt, Vector.getElem_push_lt hk2lt] at heq_k
          -- heq_k : ps.state.heap[k1.1]'hk1lt = ps.state.heap[k2.1]'hk2lt
          have heq := hheapinj (⟨k1.1, hk1lt⟩ : Fin s) (⟨k2.1, hk2lt⟩ : Fin s) heq_k
          have : k1.1 = k2.1 := by have := congr_arg Fin.val heq; exact this
          exact Fin.ext this
    · -- hnored: NoRedundancy
      exact hnored
  -- heval_full: evaluation
  have heval_full : ∀ I, OBdd.evaluate ⟨⟨cook_heap (ps.state.heap.push N) hh',
      (push_node ps N hN).2.cook hp⟩, ho_final⟩ I =
      OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I := by
    intro I
    rw [hO_eq]
    have eval_lo : OBdd.evaluate ⟨⟨cook_heap (ps.state.heap.push N) hh', entry.1.1.cook hb1⟩,
        ho_lo'⟩ I = OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[entry.2].low⟩, hlo_ord⟩ I := by
      rw [push_evaluate (hu := ho_lo)]; exact heval_lo I
    have eval_hi : OBdd.evaluate ⟨⟨cook_heap (ps.state.heap.push N) hh', entry.1.2.cook hb2⟩,
        ho_hi'⟩ I = OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[entry.2].high⟩, hhi_ord⟩ I := by
      rw [push_evaluate (hu := ho_hi)]; exact heval_hi I
    simp only [OBdd.evaluate_node]
    simp only [hMs_var]
    by_cases hI : I[O.1.heap[entry.2].var] = true
    · simp only [if_pos hI]
      exact (congr_arg (OBdd.evaluate · I)
          (Subtype.ext (congrArg (fun r => ({heap := cook_heap (ps.state.heap.push N) hh', root := r} : Bdd n (s+1)))
            hMs_high))).trans eval_hi
    · simp only [if_neg hI]
      exact (congr_arg (OBdd.evaluate · I)
          (Subtype.ext (congrArg (fun r => ({heap := cook_heap (ps.state.heap.push N) hh', root := r} : Bdd n (s+1)))
            hMs_low))).trans eval_lo
  exact ⟨hj, hp, ho_final, hred_full, heval_full⟩
def process_record {n m : Nat} {i : Nat} (O : OBdd n m)
    (curkey : RawPointer × RawPointer) (curptr : RawPointer)
    (entry  : (RawPointer × RawPointer) × Fin m)
    (ps : ProvedState n m)
    (inv : Invariant O ps i)
    (hbound : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size)
    -- When entry.1 = curkey, curptr correctly represents entry.2.
    (hcurptr_correct : entry.1 = curkey →
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : curptr.Bounded ps.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I)
    -- When entry.1 ≠ curkey, the freshly pushed node for entry.2 is correct.
    (hnewnode_correct : ¬(entry.1 = curkey) →
        let hN : (RawNode.mk O.1.heap[entry.2].var entry.1.1 entry.1.2).Bounded ps.state.size :=
              ⟨hbound.1, hbound.2⟩
        let ps₁' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).1
        let ptr' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).2
        let ps₂' := set_id ps₁' entry.2 ptr'
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : ptr'.Bounded ps₂'.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I) :
    { p : ProvedState n m × (RawPointer × RawPointer) × RawPointer //
        Invariant O p.1 i ∧
        (p.1.state.ids[entry.2]).isSome ∧
        (∀ k : Fin m, (ps.state.ids[k]).isSome → (p.1.state.ids[k]).isSome) ∧
        (∀ k : Fin m, k ≠ entry.2 → p.1.state.ids[k] = ps.state.ids[k]) ∧
        ps.state.size ≤ p.1.state.size } :=
  let ⟨key, j⟩ := entry
  -- Helpers for reasoning about ids after set_id.
  have ids_set_self : ∀ (ps0 : ProvedState n m) (ptr : RawPointer),
      (set_id ps0 j ptr).state.ids[j] = some ptr :=
    fun ps0 ptr => set_id_self ps0 j ptr
  have ids_set_ne : ∀ (ps0 : ProvedState n m) (ptr : RawPointer) (k : Fin m), k ≠ j →
      (set_id ps0 j ptr).state.ids[k] = ps0.state.ids[k] :=
    fun ps0 ptr k hkj => set_id_ne ps0 j k ptr hkj
  if heq : key = curkey then
    -- Isomorphic: assign j to the same output pointer as curptr.
    let ps' := set_id ps j curptr
    ⟨⟨ps', curkey, curptr⟩,
     -- Invariant:
     ⟨fun k hk hreach_k => by
        by_cases hkj : k = j
        · subst hkj
          simp only [Option.isSome_iff_exists]
          exact ⟨curptr, ids_set_self ps curptr⟩
        · rw [ids_set_ne ps curptr k hkj]; exact inv.1 k hk hreach_k,
      fun k ptr hkptr => by
        by_cases hkj : k = j
        · subst hkj
          rw [ids_set_self ps] at hkptr
          simp only [Option.some.injEq] at hkptr; subst hkptr
          exact hcurptr_correct heq
        · rw [ids_set_ne ps curptr k hkj] at hkptr
          exact inv.2 k ptr hkptr⟩,
     -- ids[j].isSome:
     by simp only [Option.isSome_iff_exists]; exact ⟨curptr, ids_set_self ps curptr⟩,
     -- isSome monotone:
     fun k hk => by
       by_cases hkj : k = j
       · subst hkj
         simp only [Option.isSome_iff_exists]
         exact ⟨curptr, ids_set_self ps curptr⟩
       · rw [ids_set_ne ps curptr k hkj]; exact hk,
     -- ids exact for k ≠ j:
     fun k hkj => ids_set_ne ps curptr k hkj,
     -- size unchanged:
     le_refl _⟩
  else
    -- New equivalence class: push a fresh output node, then assign j to it.
    have hN : (RawNode.mk O.1.heap[j].var key.1 key.2).Bounded ps.state.size :=
      ⟨hbound.1, hbound.2⟩
    -- Use non-destructuring let so ps₁ is a transparent let binding.
    let ps₁ : ProvedState n m := (push_node ps ⟨O.1.heap[j].var, key.1, key.2⟩ hN).1
    let ptr : RawPointer             := (push_node ps ⟨O.1.heap[j].var, key.1, key.2⟩ hN).2
    -- These hold by rfl since ps₁ is a transparent let.
    have hps₁_ids : ∀ k : Fin m, ps₁.state.ids[k] = ps.state.ids[k] := fun _ => rfl
    have hps₁_size : ps₁.state.size = ps.state.size + 1 := rfl
    let ps₂ := set_id ps₁ j ptr
    ⟨⟨ps₂, key, ptr⟩,
     -- Invariant:
     ⟨fun k hk hreach_k => by
        by_cases hkj : k = j
        · subst hkj
          simp only [Option.isSome_iff_exists]
          exact ⟨ptr, ids_set_self ps₁ ptr⟩
        · rw [ids_set_ne ps₁ ptr k hkj, hps₁_ids k]
          exact inv.1 k hk hreach_k,
      fun k ptr_k hkptr => by
        by_cases hkj : k = j
        · subst hkj
          rw [ids_set_self ps₁] at hkptr
          simp only [Option.some.injEq] at hkptr; subst hkptr
          exact hnewnode_correct heq
        · -- k ≠ j: ids[k] unchanged through push and set_id
          rw [ids_set_ne ps₁ ptr k hkj, hps₁_ids k] at hkptr
          obtain ⟨hj_k, hptr_k, ho_k, hred_k, heval_k⟩ := inv.2 k ptr_k hkptr
          -- Lift hptr_k to the new (larger) heap size.
          have hptr_k' : ptr_k.Bounded ps₂.state.size :=
            RawPointer.bounded_of_le hptr_k (hps₁_size ▸ Nat.le_succ _)
          -- Lift ordering through push_node (ps₂.state.heap = ps.state.heap.push N by rfl).
          have ho_k' : Bdd.Ordered ⟨cook_heap ps₂.state.heap ps₂.hh, ptr_k.cook hptr_k'⟩ :=
            push_ordered ho_k
          exact ⟨hj_k, hptr_k', ho_k',
                 push_reduced hred_k,
                 fun I => (congr_fun (push_evaluate (hu := ho_k)) I).trans (heval_k I)⟩⟩,
     -- ids[j].isSome:
     by simp only [Option.isSome_iff_exists]; exact ⟨ptr, ids_set_self ps₁ ptr⟩,
     -- isSome monotone: push_node doesn't change ids, set_id j ptr adds one entry
     fun k hk => by
       by_cases hkj : k = j
       · subst hkj
         simp only [Option.isSome_iff_exists]
         exact ⟨ptr, ids_set_self ps₁ ptr⟩
       · rw [ids_set_ne ps₁ ptr k hkj, hps₁_ids k]; exact hk,
     -- ids exact for k ≠ j:
     fun k hkj => by rw [ids_set_ne ps₁ ptr k hkj, hps₁_ids k],
     -- size grows by 1:
     hps₁_size ▸ Nat.le_succ _⟩
lemma node_fresh {n m : Nat} {ps : ProvedState n m} {i s₀ : Nat}
    {curkey K : RawPointer × RawPointer} {vi : Fin n}
    (hbase : ∀ k : Fin ps.state.size, k.1 < s₀ → i < ps.state.heap[k].va.1)
    (hpushed_le : ∀ k : Fin ps.state.size, s₀ ≤ k.1 →
        KeyLE (ps.state.heap[k].lo, ps.state.heap[k].hi) curkey)
    (hvi : vi.1 = i)
    (hKcur : KeyLE curkey K) (hKne : K ≠ curkey) :
    ∀ k : Fin ps.state.size, ps.state.heap[k] ≠ (⟨vi, K.1, K.2⟩ : RawNode n) := by
  intro k hk
  by_cases hks : k.1 < s₀
  · have hlt := hbase k hks
    rw [hk] at hlt
    have hva : (⟨vi, K.1, K.2⟩ : RawNode n).va.1 = i := hvi
    omega
  · have hle := hpushed_le k (Nat.le_of_not_lt hks)
    have hkey : (ps.state.heap[k].lo, ps.state.heap[k].hi) = K := by rw [hk]
    rw [hkey] at hle
    exact hKne (keyLE_antisymm hKcur hle).symm
def StepInv.nc {n m : Nat} {O : OBdd n m} {ps : ProvedState n m} {i s₀ : Nat}
    {curkey : RawPointer × RawPointer} {curptr : RawPointer}
    {Q : List ((RawPointer × RawPointer) × Fin m)}
    (si : StepInv O ps i s₀ curkey curptr Q) (inv : Invariant O ps i)
    {e : (RawPointer × RawPointer) × Fin m} (hec : EntryCorrect O ps i e) (hmem : e ∈ Q) :
    ¬(e.1 = curkey) → NodePushedCorrectly O ps e (si.hbnd hmem) :=
  fun hne => push_node_correct' O ps inv e hec (si.hbnd hmem) (si.hnonred e hmem)
    s₀ si.hs0 (si.hbounds0 e hmem) si.hbase si.hheapinj
    (node_fresh si.hbase si.hpushed_le hec.2.1 (si.hcur_le e hmem) hne)
lemma process_record_stepinv {n m : Nat} {i : Nat} (O : OBdd n m)
    (curkey : RawPointer × RawPointer) (curptr : RawPointer)
    (head : (RawPointer × RawPointer) × Fin m)
    (tail : List ((RawPointer × RawPointer) × Fin m))
    (ps : ProvedState n m)
    (inv : Invariant O ps i)
    (s₀ : Nat)
    (hbounds : ∀ entry ∈ head :: tail, entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size)
    (hcurptr_sem : ∀ entry ∈ head :: tail, entry.1 = curkey →
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : curptr.Bounded ps.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I)
    (hnewnode_sem : ∀ entry ∈ head :: tail,
        (hbound_entry : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) →
        ¬(entry.1 = curkey) →
        let hN : (RawNode.mk O.1.heap[entry.2].var entry.1.1 entry.1.2).Bounded ps.state.size :=
              ⟨hbound_entry.1, hbound_entry.2⟩
        let ps₁' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).1
        let ptr' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).2
        let ps₂' := set_id ps₁' entry.2 ptr'
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : ptr'.Bounded ps₂'.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I)
    (hec : ∀ entry ∈ head :: tail, EntryCorrect O ps i entry)
    (si : StepInv O ps i s₀ curkey curptr (head :: tail)) :
    let result := process_record O curkey curptr head ps inv (hbounds head (.head _))
          (hcurptr_sem head (.head _))
          (hnewnode_sem head (.head _) (hbounds head (.head _)))
    StepInv O result.1.1 i s₀ result.1.2.1 result.1.2.2 tail := by
  intro result
  by_cases heq_h : head.1 = curkey
  · -- result = (set_id ps head.2 curptr, curkey, curptr).
    have hps' : result.1.1 = set_id ps head.2 curptr := by
      show (process_record O curkey curptr head ps inv (hbounds head (.head _))
        (hcurptr_sem head (.head _))
        (hnewnode_sem head (.head _) (hbounds head (.head _)))).val.1 = set_id ps head.2 curptr
      simp only [process_record, dif_pos heq_h]
    have hck' : result.1.2.1 = curkey := by
      show (process_record O curkey curptr head ps inv (hbounds head (.head _))
        (hcurptr_sem head (.head _))
        (hnewnode_sem head (.head _) (hbounds head (.head _)))).val.2.1 = curkey
      simp only [process_record, dif_pos heq_h]
    have hcp' : result.1.2.2 = curptr := by
      show (process_record O curkey curptr head ps inv (hbounds head (.head _))
        (hcurptr_sem head (.head _))
        (hnewnode_sem head (.head _) (hbounds head (.head _)))).val.2.2 = curptr
      simp only [process_record, dif_pos heq_h]
    rw [hps', hck', hcp']
    -- set_id leaves size/heap/hh defeq; only ids change.
    refine ⟨si.hs0, si.hbase, si.hsuffix, si.hheapinj, ?_, ?_,
            fun e he => si.hnonred e (.tail _ he),
            fun e he => si.hbounds0 e (.tail _ he),
            (List.pairwise_cons.mp si.hsorted).2,
            fun e he => si.hcur_le e (.tail _ he), si.hpushed_le⟩
    · -- hvarinv for set_id ps head.2 curptr
      intro j k hjk
      show O.1.heap[j].var.1 ≤ ps.state.heap[k].va.1
      by_cases hjh : j = head.2
      · subst hjh
        rw [set_id_self ps head.2 curptr] at hjk
        have hcur : curptr = .inr k.1 := by injection hjk
        have hva : ps.state.heap[k].va.1 = i := si.hcurlvl k hcur
        have hvj : O.1.heap[head.2].var.1 = i := (hec head (.head _)).2.1
        omega
      · rw [set_id_ne ps head.2 j curptr hjh] at hjk
        exact si.hvarinv j k hjk
    · -- hcurlvl unchanged (curptr, heap defeq)
      exact si.hcurlvl
  · -- push a fresh node for head, then set_id.
    have hN : (RawNode.mk O.1.heap[head.2].var head.1.1 head.1.2).Bounded ps.state.size :=
      ⟨(hbounds head (.head _)).1, (hbounds head (.head _)).2⟩
    let Nh : RawNode n := ⟨O.1.heap[head.2].var, head.1.1, head.1.2⟩
    have hNh : Nh = ⟨O.1.heap[head.2].var, head.1.1, head.1.2⟩ := rfl
    have hvar_head : O.1.heap[head.2].var.1 = i := (hec head (.head _)).2.1
    have hcur_head : KeyLE curkey head.1 := si.hcur_le head (.head _)
    have hps' : result.1.1 = set_id (push_node ps Nh hN).1 head.2 (push_node ps Nh hN).2 := by
      show (process_record O curkey curptr head ps inv (hbounds head (.head _))
        (hcurptr_sem head (.head _))
        (hnewnode_sem head (.head _) (hbounds head (.head _)))).val.1 =
          set_id (push_node ps Nh hN).1 head.2 (push_node ps Nh hN).2
      simp only [process_record, dif_neg heq_h]
      rfl
    have hck' : result.1.2.1 = head.1 := by
      show (process_record O curkey curptr head ps inv (hbounds head (.head _))
        (hcurptr_sem head (.head _))
        (hnewnode_sem head (.head _) (hbounds head (.head _)))).val.2.1 = head.1
      simp only [process_record, dif_neg heq_h]
    have hcp' : result.1.2.2 = (push_node ps Nh hN).2 := by
      show (process_record O curkey curptr head ps inv (hbounds head (.head _))
        (hcurptr_sem head (.head _))
        (hnewnode_sem head (.head _) (hbounds head (.head _)))).val.2.2 = (push_node ps Nh hN).2
      simp only [process_record, dif_neg heq_h]
      rfl
    rw [hps', hck', hcp']
    -- (push_node ps Nh hN).2 = .inr ps.state.size
    have hptr_eq : (push_node ps Nh hN).2 = (.inr ps.state.size : RawPointer) := rfl
    -- Nh ∉ ps.state.heap (freshness).
    have hfresh : ∀ k : Fin ps.state.size, ps.state.heap[k] ≠ Nh :=
      node_fresh si.hbase si.hpushed_le hvar_head hcur_head heq_h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- hs0
      show s₀ ≤ ps.state.size + 1
      exact Nat.le_succ_of_le si.hs0
    · -- hbase
      show ∀ k : Fin (ps.state.size + 1), k.1 < s₀ →
          i < (ps.state.heap.push Nh)[k].va.1
      intro k hk
      have hks0 : k.1 < ps.state.size := Nat.lt_of_lt_of_le hk si.hs0
      simp only [Fin.getElem_fin, Vector.getElem_push_lt hks0]
      exact si.hbase ⟨k.1, hks0⟩ hk
    · -- hsuffix
      show ∀ k : Fin (ps.state.size + 1), s₀ ≤ k.1 →
          (ps.state.heap.push Nh)[k].va.1 = i
      intro k hk
      by_cases hks : k.1 < ps.state.size
      · simp only [Fin.getElem_fin, Vector.getElem_push_lt hks]
        exact si.hsuffix ⟨k.1, hks⟩ hk
      · have hkσ : k.1 = ps.state.size := by omega
        simp only [Fin.getElem_fin, show k.1 = ps.state.size from hkσ, Vector.getElem_push_eq]
        exact hvar_head
    · -- hheapinj
      show HeapInjective (set_id (push_node ps Nh hN).1 head.2 (push_node ps Nh hN).2)
      intro k1 k2 heq_k
      -- k1 k2 : Fin (ps.state.size + 1) (defeq); extract Nat bounds.
      have hk1b : k1.1 < ps.state.size + 1 := k1.isLt
      have hk2b : k2.1 < ps.state.size + 1 := k2.isLt
      simp only [Fin.getElem_fin] at heq_k
      change (ps.state.heap.push Nh)[k1.1]'hk1b = (ps.state.heap.push Nh)[k2.1]'hk2b at heq_k
      have hval : k1.1 = k2.1 := by
        by_cases hk1 : k1.1 < ps.state.size
        · by_cases hk2 : k2.1 < ps.state.size
          · rw [Vector.getElem_push_lt (i := k1.1) hk1,
                Vector.getElem_push_lt (i := k2.1) hk2] at heq_k
            have h := si.hheapinj ⟨k1.1, hk1⟩ ⟨k2.1, hk2⟩ heq_k
            exact (Fin.mk.injEq _ _ _ _).mp h
          · have hk2σ : k2.1 = ps.state.size := by omega
            exfalso
            rw [Vector.getElem_push_lt (i := k1.1) hk1] at heq_k
            rw [show ((ps.state.heap.push Nh)[k2.1]'hk2b) = Nh by
                  simp only [show k2.1 = ps.state.size from hk2σ, Vector.getElem_push_eq]] at heq_k
            exact hfresh ⟨k1.1, hk1⟩ heq_k
        · have hk1σ : k1.1 = ps.state.size := by omega
          by_cases hk2 : k2.1 < ps.state.size
          · exfalso
            rw [Vector.getElem_push_lt (i := k2.1) hk2] at heq_k
            rw [show ((ps.state.heap.push Nh)[k1.1]'hk1b) = Nh by
                  simp only [show k1.1 = ps.state.size from hk1σ, Vector.getElem_push_eq]] at heq_k
            exact hfresh ⟨k2.1, hk2⟩ heq_k.symm
          · have hk2σ : k2.1 = ps.state.size := by omega
            exact hk1σ.trans hk2σ.symm
      exact Fin.eq_of_val_eq hval
    · -- hvarinv
      show VarInvariant O (set_id (push_node ps Nh hN).1 head.2 (push_node ps Nh hN).2)
      intro j k hjk
      show O.1.heap[j].var.1 ≤ (ps.state.heap.push Nh)[k.1].va.1
      by_cases hjh : j = head.2
      · subst hjh
        rw [set_id_self (push_node ps Nh hN).1 head.2 (push_node ps Nh hN).2] at hjk
        have hcur : (push_node ps Nh hN).2 = .inr k.1 := by injection hjk
        rw [hptr_eq] at hcur
        have hkσ : k.1 = ps.state.size := (Sum.inr.inj hcur).symm
        simp only [Fin.getElem_fin, show k.1 = ps.state.size from hkσ, Vector.getElem_push_eq, hNh]
        exact Nat.le_refl _
      · rw [set_id_ne (push_node ps Nh hN).1 head.2 j (push_node ps Nh hN).2 hjh] at hjk
        change ps.state.ids[j] = some (.inr k.1) at hjk
        -- the target node index k must be < ps.state.size (it existed before the push)
        have hk_lt : k.1 < ps.state.size := by
          obtain ⟨_, hbnd, _, _, _⟩ := inv.2 j (.inr k.1) hjk
          exact hbnd rfl
        simp only [Fin.getElem_fin, Vector.getElem_push_lt hk_lt]
        exact si.hvarinv j ⟨k.1, hk_lt⟩ hjk
    · -- hcurlvl (relative to new curptr = .inr ps.state.size)
      show ∀ k : Fin (ps.state.size + 1), (push_node ps Nh hN).2 = .inr k.1 →
          (ps.state.heap.push Nh)[k].va.1 = i
      intro k hk
      rw [hptr_eq] at hk
      have hkσ : k.1 = ps.state.size := (Sum.inr.inj hk).symm
      simp only [Fin.getElem_fin, show k.1 = ps.state.size from hkσ, Vector.getElem_push_eq]
      exact hvar_head
    · -- hnonred for tail
      exact fun e he => si.hnonred e (.tail _ he)
    · -- hbounds0 for tail (s₀ unchanged)
      exact fun e he => si.hbounds0 e (.tail _ he)
    · -- hsorted for tail
      exact (List.pairwise_cons.mp si.hsorted).2
    · -- hcur_le (relative to head.1): every tail key ≥ head.1
      exact (List.pairwise_cons.mp si.hsorted).1
    · -- hpushed_le (relative to head.1)
      show ∀ k : Fin (ps.state.size + 1), s₀ ≤ k.1 →
          KeyLE ((ps.state.heap.push Nh)[k].lo, (ps.state.heap.push Nh)[k].hi) head.1
      intro k hk
      by_cases hks : k.1 < ps.state.size
      · simp only [Fin.getElem_fin, Vector.getElem_push_lt hks]
        exact keyLE_trans (si.hpushed_le ⟨k.1, hks⟩ hk) hcur_head
      · have hkσ : k.1 = ps.state.size := by omega
        simp only [Fin.getElem_fin, show k.1 = ps.state.size from hkσ, Vector.getElem_push_eq]
        show KeyLE (Nh.lo, Nh.hi) head.1
        rw [hNh]
        exact keyLE_refl head.1
lemma process_record_curptr_sem {n m : Nat} {i : Nat} (O : OBdd n m)
    (curkey : RawPointer × RawPointer) (curptr : RawPointer)
    (head : (RawPointer × RawPointer) × Fin m)
    (tail : List ((RawPointer × RawPointer) × Fin m))
    (ps : ProvedState n m)
    (inv : Invariant O ps i)
    (hbounds : ∀ entry ∈ head :: tail, entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size)
    (hcurptr_sem : ∀ entry ∈ head :: tail, entry.1 = curkey →
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : curptr.Bounded ps.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I)
    (hnewnode_sem : ∀ entry ∈ head :: tail,
        (hbound_entry : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) →
        ¬(entry.1 = curkey) →
        let hN : (RawNode.mk O.1.heap[entry.2].var entry.1.1 entry.1.2).Bounded ps.state.size :=
              ⟨hbound_entry.1, hbound_entry.2⟩
        let ps₁' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).1
        let ptr' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).2
        let ps₂' := set_id ps₁' entry.2 ptr'
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : ptr'.Bounded ps₂'.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I)
    (hec : ∀ entry ∈ head :: tail, EntryCorrect O ps i entry) :
    let result := process_record O curkey curptr head ps inv (hbounds head (.head _))
          (hcurptr_sem head (.head _))
          (hnewnode_sem head (.head _) (hbounds head (.head _)))
    let ps' := result.1.1
    let curkey' := result.1.2.1
    let curptr' := result.1.2.2
    ∀ entry ∈ tail, entry.1 = curkey' →
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : curptr'.Bounded ps'.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps'.state.heap ps'.hh, curptr'.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps'.state.heap ps'.hh, curptr'.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps'.state.heap ps'.hh, curptr'.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I := by
  by_cases heq_h : head.1 = curkey
  · -- process_record returns (set_id ps head.2 curptr, curkey, curptr)
    intro result ps' curkey' curptr' entry hmem heq_entry
    have hcurkey' : curkey' = curkey := by
      show (process_record O curkey curptr head ps inv (hbounds head (.head _))
        (hcurptr_sem head (.head _))
        (hnewnode_sem head (.head _) (hbounds head (.head _)))).val.2.1 = curkey
      simp only [process_record, dif_pos heq_h]
    have hcurptr' : curptr' = curptr := by
      show (process_record O curkey curptr head ps inv (hbounds head (.head _))
        (hcurptr_sem head (.head _))
        (hnewnode_sem head (.head _) (hbounds head (.head _)))).val.2.2 = curptr
      simp only [process_record, dif_pos heq_h]
    have hps' : ps' = set_id ps head.2 curptr := by
      show (process_record O curkey curptr head ps inv (hbounds head (.head _))
        (hcurptr_sem head (.head _))
        (hnewnode_sem head (.head _) (hbounds head (.head _)))).val.1 = set_id ps head.2 curptr
      simp only [process_record, dif_pos heq_h]
    rw [hcurkey'] at heq_entry
    rw [hps', hcurptr']
    exact hcurptr_sem entry (.tail _ hmem) heq_entry
  · -- New class branch: ¬(head.1 = curkey), so curkey' = head.1
    intro result ps' curkey' curptr' entry hmem heq_entry
    let hN : (RawNode.mk O.1.heap[head.2].var head.1.1 head.1.2).Bounded ps.state.size :=
      ⟨(hbounds head (.head _)).1, (hbounds head (.head _)).2⟩
    let ps₁' := (push_node ps ⟨O.1.heap[head.2].var, head.1.1, head.1.2⟩ hN).1
    let ptr' := (push_node ps ⟨O.1.heap[head.2].var, head.1.1, head.1.2⟩ hN).2
    let ps₂' := set_id ps₁' head.2 ptr'
    have hcurkey' : curkey' = head.1 := by
      show (process_record O curkey curptr head ps inv (hbounds head (.head _))
        (hcurptr_sem head (.head _))
        (hnewnode_sem head (.head _) (hbounds head (.head _)))).val.2.1 = head.1
      simp only [process_record, dif_neg heq_h]
    have hcurptr' : curptr' = ptr' := by
      show (process_record O curkey curptr head ps inv (hbounds head (.head _))
        (hcurptr_sem head (.head _))
        (hnewnode_sem head (.head _) (hbounds head (.head _)))).val.2.2 = ptr'
      simp only [process_record, dif_neg heq_h]
      rfl
    have hps' : ps' = ps₂' := by
      show (process_record O curkey curptr head ps inv (hbounds head (.head _))
        (hcurptr_sem head (.head _))
        (hnewnode_sem head (.head _) (hbounds head (.head _)))).val.1 = ps₂'
      simp only [process_record, dif_neg heq_h]
      rfl
    obtain ⟨hj_h, hp_h, ho_h, hred_h, heval_h⟩ :=
      hnewnode_sem head (.head _) (hbounds head (.head _)) heq_h
    -- entry.1 = head.1 from heq_entry
    have hentry_key : entry.1 = head.1 := hcurkey' ▸ heq_entry
    have hnotiso_entry : ¬(entry.1 = curkey) := hentry_key ▸ heq_h
    -- Ordering for entry.2
    have hj_entry : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩ :=
      Bdd.ordered_of_reachable (hec entry (.tail _ hmem)).1
    -- Both at the same variable index i
    have hvar_eq : O.1.heap[head.2].var = O.1.heap[entry.2].var :=
      Fin.ext ((hec head (.head _)).2.1.trans (hec entry (.tail _ hmem)).2.1.symm)
    have hkey_lo : entry.1.1 = head.1.1 := congrArg Prod.fst hentry_key
    have hkey_hi : entry.1.2 = head.1.2 := congrArg Prod.snd hentry_key
    -- Helper: two raw pointers both mapped to the same output raw-pointer evaluate equally in O
    have eval_child_eq : ∀ (lid : RawPointer) (p1 p2 : Pointer m)
        (hord1 : Bdd.Ordered ⟨O.1.heap, p1⟩) (hord2 : Bdd.Ordered ⟨O.1.heap, p2⟩)
        (h1n : ∀ l : Fin m, p1 = .node l → ps.state.ids[l] = some lid)
        (h1t : ∀ b : Bool, p1 = .terminal b → lid = .inl b)
        (h2n : ∀ l : Fin m, p2 = .node l → ps.state.ids[l] = some lid)
        (h2t : ∀ b : Bool, p2 = .terminal b → lid = .inl b)
        (I : Vector Bool n),
        OBdd.evaluate ⟨⟨O.1.heap, p1⟩, hord1⟩ I = OBdd.evaluate ⟨⟨O.1.heap, p2⟩, hord2⟩ I := by
      intro lid p1 p2 hord1 hord2 h1n h1t h2n h2t I
      cases p1 with
      | terminal b1 =>
        have hlid1 : lid = .inl b1 := h1t b1 rfl
        simp only [OBdd.evaluate_terminal]
        cases p2 with
        | terminal b2 =>
          have hlid2 : lid = .inl b2 := h2t b2 rfl
          simp only [OBdd.evaluate_terminal, Function.const_apply]
          exact Sum.inl.inj (hlid1.symm.trans hlid2)
        | node l2 =>
          have hids2 : ps.state.ids[l2] = some (.inl b1) := hlid1 ▸ h2n l2 rfl
          obtain ⟨_, hbnd2, ho2, _, heval2⟩ := inv.2 l2 (.inl b1) hids2
          have hb1 : OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, RawPointer.cook (.inl b1) hbnd2⟩, ho2⟩ =
                     Function.const _ b1 := OBdd.evaluate_terminal' rfl
          simp only [Function.const_apply]
          have h := heval2 I
          rw [hb1, Function.const_apply] at h
          exact h
      | node l1 =>
        have hids1 : ps.state.ids[l1] = some lid := h1n l1 rfl
        obtain ⟨_, hbnd1, ho1, _, heval1⟩ := inv.2 l1 lid hids1
        cases p2 with
        | terminal b2 =>
          have hlid2 : lid = .inl b2 := h2t b2 rfl
          subst hlid2
          have hb2 : OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, RawPointer.cook (.inl b2) hbnd1⟩, ho1⟩ =
                     Function.const _ b2 := OBdd.evaluate_terminal' rfl
          simp only [OBdd.evaluate_terminal, Function.const_apply]
          have h := heval1 I
          rw [hb2, Function.const_apply] at h
          exact h.symm
        | node l2 =>
          have hids2 : ps.state.ids[l2] = some lid := h2n l2 rfl
          obtain ⟨_, hbnd2, ho2, _, heval2⟩ := inv.2 l2 lid hids2
          have hOBdd_eq : (⟨⟨cook_heap ps.state.heap ps.hh, lid.cook hbnd1⟩, ho1⟩ : OBdd n _) =
                           ⟨⟨cook_heap ps.state.heap ps.hh, lid.cook hbnd2⟩, ho2⟩ := by
            apply Subtype.ext
            simp only []
          rw [hOBdd_eq] at heval1
          exact (heval1 I).symm.trans (heval2 I)
    -- head.2 and entry.2 evaluate equally in O
    have heval_eq : ∀ I, OBdd.evaluate ⟨⟨O.1.heap, .node head.2⟩, hj_h⟩ I =
                         OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj_entry⟩ I := fun I => by
      simp only [OBdd.evaluate_node]
      simp only [hvar_eq]
      split_ifs
      · exact eval_child_eq head.1.2
            (O.1.heap[head.2].high) (O.1.heap[entry.2].high)
            (OBdd.ordered_of_high_edge hj_h) (OBdd.ordered_of_high_edge hj_entry)
            (fun l h => (hec head (.head _)).2.2.2.1 l h)
            (fun b h => (hec head (.head _)).2.2.2.2.2 b h)
            (fun l h => hkey_hi ▸ (hec entry (.tail _ hmem)).2.2.2.1 l h)
            (fun b h => hkey_hi ▸ (hec entry (.tail _ hmem)).2.2.2.2.2 b h) I
      · exact eval_child_eq head.1.1
            (O.1.heap[head.2].low) (O.1.heap[entry.2].low)
            (OBdd.ordered_of_low_edge hj_h) (OBdd.ordered_of_low_edge hj_entry)
            (fun l h => (hec head (.head _)).2.2.1 l h)
            (fun b h => (hec head (.head _)).2.2.2.2.1 b h)
            (fun l h => hkey_lo ▸ (hec entry (.tail _ hmem)).2.2.1 l h)
            (fun b h => hkey_lo ▸ (hec entry (.tail _ hmem)).2.2.2.2.1 b h) I
    rw [hps', hcurptr']
    exact ⟨hj_entry, hp_h, ho_h, hred_h, fun I => (heval_h I).trans (heval_eq I)⟩
def process_queue {n m : Nat} {i : Nat} (O : OBdd n m)
    (curkey : RawPointer × RawPointer) (curptr : RawPointer) (s₀ : Nat) :
    (Q : List ((RawPointer × RawPointer) × Fin m)) →
    (ps : ProvedState n m) →
    Invariant O ps i →
    (∀ entry ∈ Q, entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) →
    -- Semantic correctness: when entry's key matches curkey, curptr represents entry.2.
    (hcurptr_sem : ∀ entry ∈ Q, entry.1 = curkey →
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : curptr.Bounded ps.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I) →
    -- (new-node correctness is no longer threaded: it is derived from `si` via `StepInv.nc`)
    (hec : ∀ entry ∈ Q, EntryCorrect O ps i entry) →
    (si : StepInv O ps i s₀ curkey curptr Q) →
    { ps' : ProvedState n m //
        Invariant O ps' i ∧
        (∀ k : Fin m, (ps.state.ids[k]).isSome → (ps'.state.ids[k]).isSome) ∧
        (∀ entry ∈ Q, (ps'.state.ids[entry.2]).isSome) ∧
        VarInvariant O ps' ∧
        HeapInjective ps' ∧
        ∀ k : Fin ps'.state.size, i ≤ ps'.state.heap[k].va.1 }
  | [], ps, inv, _, _, _, si =>
      ⟨ps, inv, fun _ hk => hk, fun _ h => by simp at h, si.hvarinv, si.hheapinj,
       fun k => by
         by_cases hk : k.1 < s₀
         · exact Nat.le_of_lt (si.hbase k hk)
         · exact Nat.le_of_eq (si.hsuffix k (Nat.le_of_not_lt hk)).symm⟩
  | head :: tail, ps, inv, hbounds, hcurptr_sem, hec, si =>
      -- New-node correctness for every entry, derived from `si` (replaces the threaded
      -- `hnewnode_sem` hypothesis and the deleted `process_record_newnode_sem` lemma).
      let hnewnode_sem : ∀ entry ∈ head :: tail,
          (hbound_entry : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) →
          ¬(entry.1 = curkey) →
          NodePushedCorrectly O ps entry ⟨hbound_entry.1, hbound_entry.2⟩ :=
        fun entry hmem _hbe hne => si.nc inv (hec entry hmem) hmem hne
      let result := process_record O curkey curptr head ps inv (hbounds head (.head _))
          (hcurptr_sem head (.head _))
          (hnewnode_sem head (.head _) (hbounds head (.head _)))
      let ps' := result.1.1
      let curkey' := result.1.2.1
      let curptr' := result.1.2.2
      let inv' := result.2.1
      let hhead := result.2.2.1
      let hmono_rec := result.2.2.2.1
      let hmono_exact := result.2.2.2.2.1
      let hsize_rec := result.2.2.2.2.2
      -- Lift the tail bounds to the (possibly larger) ps'.state.size.
      have hbounds' : ∀ entry ∈ tail,
          entry.1.1.Bounded ps'.state.size ∧ entry.1.2.Bounded ps'.state.size := by
        intro entry hmem
        have := hbounds entry (.tail _ hmem)
        exact ⟨RawPointer.bounded_of_le this.1 hsize_rec,
               RawPointer.bounded_of_le this.2 hsize_rec⟩
      -- Lift EntryCorrect to ps' for tail entries (children of tail nodes have var > i ≠ head.2's var).
      have hec_tail' : ∀ e ∈ tail, EntryCorrect O ps' i e := by
        intro e hmem_e
        obtain ⟨hr, hv, hlo, hhi, hlt, hht⟩ := hec e (.tail _ hmem_e)
        have hec_hd := hec head (.head _)
        -- For a child l of e.2, l ≠ head.2 (child has var > i = head.2's var)
        have child_ne : ∀ l : Fin m,
            (O.1.heap[e.2].low = .node l ∨ O.1.heap[e.2].high = .node l) → l ≠ head.2 := by
          intro l hedge h_eq
          have hedge' : O.1.RelevantEdge ⟨.node e.2, hr⟩
              ⟨.node l, .tail hr (hedge.elim (Edge.low ·) (Edge.high ·))⟩ :=
            hedge.elim (Edge.low ·) (Edge.high ·)
          have hmay : O.1.heap[e.2].var.1 < O.1.heap[l].var.1 := by
            have h := O.2 hedge'
            simp only [Bdd.RelevantMayPrecede, Pointer.MayPrecede, Pointer.toVar,
                       Fin.mk_lt_mk] at h
            exact h
          have h_var_l : O.1.heap[l].var.1 = i := h_eq ▸ hec_hd.2.1
          omega
        exact ⟨hr, hv,
          fun l hl => (hmono_exact l (child_ne l (.inl hl))).trans (hlo l hl),
          fun l hl => (hmono_exact l (child_ne l (.inr hl))).trans (hhi l hl),
          hlt, hht⟩
      let si' := process_record_stepinv O curkey curptr head tail ps inv s₀
            hbounds hcurptr_sem hnewnode_sem hec si
      let ⟨ps'', inv'', hmono_tail, htail, hvar'', hinj'', hlvl''⟩ :=
        process_queue O curkey' curptr' s₀ tail ps' inv' hbounds'
          (process_record_curptr_sem O curkey curptr head tail ps inv hbounds hcurptr_sem hnewnode_sem hec)
          hec_tail'
          si'
      ⟨ps'', inv'',
       -- isSome monotone: compose record's and tail's monotonicity.
       fun k hk => hmono_tail k (hmono_rec k hk),
       fun entry h => by
         cases h with
         | head =>
           -- head's id was set by process_record; tail preserves it.
           exact hmono_tail head.2 hhead
         | tail _ h => exact htail entry h,
       hvar'', hinj'', hlvl''⟩
end Reduce


