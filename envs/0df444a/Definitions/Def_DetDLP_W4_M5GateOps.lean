-- Prove2me | Definitions.Def_DetDLP_W4_M5GateOps
-- name    : DetDLP_W4_M5GateOps
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T02:21:53.456341+00:00
-- url     : https://prove2.me/theorems/e792108d-9b9b-42fa-87ad-507fb8c6e8ea
-- title:
--   Bounded arithmetic and wire reads for the gate evaluator
-- statement:
--   Unary-bounded sums, words, quantification, and Fermat root-power computations preserve polynomial time. Degree-checked wire lookup agrees with the finite graph for arbitrary input lists.

import Definitions.Def_DetDLP_W4_M5EdgeNat

set_option autoImplicit false
namespace DetDLP.w4_M5GateOps
open Groundwork Groundwork.PolyT w4_MulParams w4_M5GraphBounds w4_M5Evaluator w4_M5EdgeNat w4_M5PortEval
attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.div Groundwork.PolyT.mod Groundwork.PolyT.mul Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.prodMk Groundwork.PolyT.length P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219 J_poly n0_poly L1_poly L2_poly mu_poly
abbrev Pad := List Unit
def cap (q : Pad) (n : ℕ) := min n (1100*(q.length+1))
private theorem budget {α} [Enc α] {q : α → Pad} (hq : PolyT q) : Unary (fun x => 1100*((q x).length+1)) := by
  let l := fun x => (List.replicate 1100 ()).flatMap (fun _ => () :: q x)
  have h : PolyT l := Groundwork.PolyT.flatMap (f := fun x (_ : Unit) => () :: q x) (by apply P2M_Groundwork_PolyT_cons__3a60f43a3b86 (const ()); exact Groundwork.PolyT.comp hq (by fun_prop)) (const _)
  apply h.congr; intro x
  change l x = List.replicate (1100*((q x).length+1)) ()
  have len_aux (c : ℕ) : ((List.replicate c ()).flatMap (fun _ => () :: q x)).length = c*((q x).length+1) := by
    induction c with
    | zero => simp
    | succ c ih => simp only [List.replicate_succ,List.flatMap_cons,List.length_append,List.length_cons,ih,Nat.succ_mul]; omega
  have hl : (l x).length = 1100*((q x).length+1) := len_aux 1100
  rw [← hl]; exact List.eq_replicate_of_mem (by simp)

theorem cap_unary {α} [Enc α] {q : α → Pad} {n : α → ℕ} (hq : PolyT q) (hn : PolyT n) : Unary (fun x => cap (q x) (n x)) := by
  simpa only [cap,List.length_replicate] using unary_min_length hn (budget hq)

def pow2 (q : Pad) (n : ℕ) := 2 ^ cap q n
def sumN (q : Pad) (n : ℕ) (f : ℕ → ℕ) := ((List.range (cap q n)).map f).sum
def allN (q : Pad) (n : ℕ) (f : ℕ → Bool) := (List.range (cap q n)).all f
@[local fun_prop] theorem pow2_poly {α} [Enc α] {q : α → Pad} {n : α → ℕ} (hq : PolyT q) (hn : PolyT n) : PolyT (fun x => pow2 (q x) (n x)) := pow_unary (const _) (cap_unary hq hn)
@[local fun_prop] theorem sumN_poly {α} [Enc α] {q : α → Pad} {n : α → ℕ} {f : α → ℕ → ℕ} (hq : PolyT q) (hn : PolyT n) (hf : PolyT fun z : α × ℕ => f z.1 z.2) : PolyT (fun x => sumN (q x) (n x) (f x)) := Groundwork.PolyT.sum (Groundwork.PolyT.map hf (Groundwork.PolyT.range (cap_unary hq hn)))
@[local fun_prop] theorem allN_poly {α} [Enc α] {q : α → Pad} {n : α → ℕ} {f : α → ℕ → Bool} (hq : PolyT q) (hn : PolyT n) (hf : PolyT fun z : α × ℕ => f z.1 z.2) : PolyT (fun x => allN (q x) (n x) (f x)) := Groundwork.PolyT.all hf (Groundwork.PolyT.range (cap_unary hq hn))

def word (q : Pad) (n : ℕ) (f : ℕ → Bool) := sumN q n (fun i => (if f i then 1 else 0) * pow2 q i)
@[local fun_prop] theorem word_poly {α} [Enc α] {q : α → Pad} {n : α → ℕ} {f : α → ℕ → Bool} (hq : PolyT q) (hn : PolyT n) (hf : PolyT fun z : α × ℕ => f z.1 z.2) : PolyT (fun x => word (q x) (n x) (f x)) := by
  apply sumN_poly hq hn; apply Groundwork.PolyT.mul
  · exact Groundwork.PolyT.ite' (c := fun z : α × ℕ => f z.1 z.2 = true) (by simpa using hf) (const 1) (const 0)
  · exact pow2_poly (Groundwork.PolyT.comp hq (by fun_prop)) (by fun_prop)

def Q (q : Pad) := pow2 q (J q.length) + 1
def rootPow (q : Pad) (n : ℕ) := pow2 q ((rootStep q.length * n) % (2 * J q.length))
def invPow (q : Pad) (n : ℕ) := rootPow q ((L1 q.length * L2 q.length - 1) * n)
def invScale (q : Pad) := Q q - pow2 q (J q.length - μ q.length)
@[local fun_prop] theorem Q_poly {α} [Enc α] {q : α → Pad} (hq : PolyT q) : PolyT (fun x => Q (q x)) := by unfold Q; fun_prop
@[local fun_prop] theorem rootPow_poly {α} [Enc α] {q : α → Pad} {n : α → ℕ} (hq : PolyT q) (hn : PolyT n) : PolyT (fun x => rootPow (q x) (n x)) := by simp only [rootPow,rootStep,← L1_mul_L2]; fun_prop
@[local fun_prop] theorem invPow_poly {α} [Enc α] {q : α → Pad} {n : α → ℕ} (hq : PolyT q) (hn : PolyT n) : PolyT (fun x => invPow (q x) (n x)) := by unfold invPow; fun_prop
@[local fun_prop] theorem invScale_poly {α} [Enc α] {q : α → Pad} (hq : PolyT q) : PolyT (fun x => invScale (q x)) := by unfold invScale; fun_prop

def portList (q : Pad) (v : ℕ) := portsNat (cap q (edgeCount q.length (W q.length))) v (srcNat q.length) (dstNat q.length)
theorem portList_poly {α} [Enc α] {q : α → Pad} {v : α → ℕ} (hq : PolyT q) (hv : PolyT v) : PolyT (fun x => portList (q x) (v x)) := by
  apply portsNat_poly (cap_unary hq (by simp only [edgeCount,W]; fun_prop)) hv
  · apply srcNat_poly <;> fun_prop
  · apply dstNat_poly <;> fun_prop

def wire (q : Pad) (v : ℕ) (a : List Bool) (e : ℕ) :=
  let p := portList q v
  let i := p.idxOf e
  if i < p.length then a[i]?.getD false else false

attribute [local irreducible] portList
set_option maxHeartbeats 1000000 in
theorem wire_poly {α} [Enc α] {q : α → Pad} {v e : α → ℕ} {a : α → List Bool} (hq : PolyT q) (hv : PolyT v) (ha : PolyT a) (he : PolyT e) : PolyT (fun x => wire (q x) (v x) (a x) (e x)) := by
  have hp := portList_poly hq hv
  have hi := Groundwork.PolyT.idxOf he hp
  apply Groundwork.PolyT.ite' (c := fun x => (portList (q x) (v x)).idxOf (e x) < (portList (q x) (v x)).length)
  · exact Groundwork.PolyT.decide_lt hi (Groundwork.PolyT.length hp)
  · exact readNat_poly hp ha he
  · exact const _

theorem sumN_eq (q : Pad) {n : ℕ} (h : n ≤ 1100*(q.length+1)) (f : ℕ → ℕ) : sumN q n f = ∑ i : Fin n, f i.val := by
  rw [sumN,cap,min_eq_left h,Fin.sum_univ_eq_sum_range,← List.sum_toFinset f (List.nodup_range (n := n)),List.toFinset_range]
theorem word_eq (q : Pad) {n : ℕ} (h : n ≤ 1100*(q.length+1)) (f : ℕ → Bool) : word q n f = bitsToNat (fun i : Fin n => f i.val) := by
  rw [word,sumN_eq q h]; unfold bitsToNat; apply Finset.sum_congr rfl
  intro i _; simp only [pow2,cap,min_eq_left (le_trans (Nat.le_of_lt i.isLt) h)]
theorem allN_true (q : Pad) {n : ℕ} (h : n ≤ 1100*(q.length+1)) (f : ℕ → Bool) : allN q n f = true ↔ ∀ i : Fin n, f i.val = true := by
  simp only [allN,cap,min_eq_left h,List.all_eq_true,List.mem_range,Fin.forall_iff]

private theorem idx_map {n} (l : List (Fin n)) (b : Fin n) : (l.map Fin.val).idxOf b.val = l.idxOf b := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    by_cases h : j = b
    · subst j; simp
    · have hv : j.val ≠ b.val := fun hh => h (Fin.ext hh)
      simp [h,hv,ih]

theorem wire_eq (q : Pad) (hd : 1 ≤ q.length) (v : Fin (graph q.length hd).nV) (a : List Bool) (e : Edge q.length (W q.length)) :
    wire q v.val a (edgeIndex q.length (W q.length) e).val = w4_M5PortTensor.readWire hd v (fun i => a[i.val]?.getD false) e := by
  let G := graph q.length hd
  have hp : portList q v.val = (G.ports v).map Fin.val := by
    have hb : edgeCount q.length (W q.length) ≤ 1100*(q.length+1) := (graph_edge_bound hd).le
    unfold portList cap; rw [min_eq_left hb]
    exact portsNat_eq G v _ _ (fun i => congrArg Prod.fst (endpointsNat_eq hd i)) (fun i => congrArg Prod.snd (endpointsNat_eq hd i))
  let i := (G.ports v).idxOf (edgeIndex q.length (W q.length) e)
  have hi : ((G.ports v).map Fin.val).idxOf (edgeIndex q.length (W q.length) e).val = i := idx_map _ _
  simp only [wire,w4_M5PortTensor.readWire,hp,hi,List.length_map]
  change (if i < (G.ports v).length then _ else _) = (List.ofFn (fun j : Fin (G.deg v) => a[j.val]?.getD false))[i]?.getD false
  by_cases h : i < (G.ports v).length
  · simp [h,List.getElem?_eq_getElem,show i < G.deg v from h]
  · simp [h,List.getElem?_eq_none,show G.deg v ≤ i from Nat.le_of_not_gt h]

end DetDLP.w4_M5GateOps


