-- Prove2me | Definitions.Def_DetDLP_S6B_Port
-- name    : DetDLP_S6B_Port
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:56:16.271828+00:00
-- url     : https://prove2.me/theorems/5abef84c-e451-4c4a-89dd-df53ebc22b86
-- title:
--   Uniform polynomial-time evaluation of doubly pinned multiplier entries
-- statement:
--   The input consists of the product and trial-pin descriptor, a vertex number, and the local port bits in increasing edge order. A polynomial-time evaluator combines the original multiplication gate with checks on every incident external edge. Its one-coefficient output encodes precisely the doubly pinned tensor entry, so it meets the entry premise for the uniform counting machine.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proposition 2.6 (pp. 10–11)

import Definitions.Def_DetDLP_S6B_CountCall
import Definitions.Def_DetDLP_W4_M5Evaluator
import Definitions.Def_DetDLP_W5_M6Sort
set_option autoImplicit false
namespace DetDLP.S6BPort
open Groundwork Groundwork.PolyT w4_MulParams w4_M5GraphBounds w4_M5GateOps w4_M5EdgeNat w4_M5PortEval w4_M5PortTensor w4_M5Evaluator w5_M6PinnedCount w5_M6DivisorConstraints
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] Groundwork.PolyT.const Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.prodMk Groundwork.PolyT.mul Groundwork.PolyT.div Groundwork.PolyT.length P2M_Groundwork_PolyT_ite__226169acf219 P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f J_poly L1_poly L2_poly n0_poly w5_M6Sort.cw_poly w5_M6Sort.encode_poly
def widthOf (desc : List Bool) : ℕ := desc.length / 10

@[simp] theorem widthOf_pinnedDesc (d N : ℕ) (trial : Fin (4*d) → Option Bool) :
    widthOf (pinnedDesc d N trial) = d := by simp [widthOf]

def bitAt (desc : List Bool) (offset : ℕ) : Bool := desc[offset]?.getD false

/-- The first 2d descriptor bits constrain only the product coordinates. -/
def productPinAt (d : ℕ) (desc : List Bool) (i : ℕ) : Option Bool :=
  if 2*d ≤ i then some (bitAt desc (i - 2*d)) else none

/-- The presence and value blocks start at offsets 2d and 6d. -/
def trialPinAt (d : ℕ) (desc : List Bool) (i : ℕ) : Option Bool :=
  if bitAt desc (2*d + i) then some (bitAt desc (6*d + i)) else none

private theorem bitAt_left {n : ℕ} (f : Fin n → Bool) (tail : List Bool) (i : Fin n) :
    bitAt (List.ofFn f ++ tail) i.val = f i := by
  rw [bitAt, List.getElem?_append_left (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]

private theorem bitAt_skip (xs ys : List Bool) (i : ℕ) :
    bitAt (xs ++ ys) (xs.length + i) = bitAt ys i := by
  rw [bitAt, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, bitAt]

private theorem bitAt_after_field {n : ℕ} (f : Fin n → Bool) (tail : List Bool) (i : ℕ) :
    bitAt (List.ofFn f ++ tail) (n + i) = bitAt tail i := by
  simpa only [List.length_ofFn] using bitAt_skip (List.ofFn f) tail i

theorem productBit_pinnedDesc (d N : ℕ) (trial : Fin (4*d) → Option Bool) (j : Fin (2*d)) :
    bitAt (pinnedDesc d N trial) j.val = natWord (2*d) N j := by
  rw [pinnedDesc, List.append_assoc, bitAt_left]

theorem presenceBit_pinnedDesc (d N : ℕ) (trial : Fin (4*d) → Option Bool) (i : Fin (4*d)) :
    bitAt (pinnedDesc d N trial) (2*d + i.val) = (trial i).isSome := by
  rw [pinnedDesc, List.append_assoc, bitAt_after_field, bitAt_left]

theorem valueBit_pinnedDesc (d N : ℕ) (trial : Fin (4*d) → Option Bool) (i : Fin (4*d)) :
    bitAt (pinnedDesc d N trial) (6*d + i.val) = (trial i).getD false := by
  let front := List.ofFn (natWord (2*d) N) ++ List.ofFn (fun j => (trial j).isSome)
  have hf : front.length = 6*d := by simp only [front, List.length_append, List.length_ofFn]; omega
  change bitAt (front ++ List.ofFn (fun j => (trial j).getD false)) (6*d + i.val) = _
  rw [← hf, bitAt_skip]
  simp only [bitAt, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]

@[simp] theorem productPinAt_pinnedDesc (d N : ℕ) (trial : Fin (4*d) → Option Bool)
    (i : Fin (4*d)) : productPinAt d (pinnedDesc d N trial) i.val = outputPins d N i := by
  by_cases hi : 2*d ≤ i.val
  · let j : Fin (2*d) := ⟨i.val - 2*d, by have := i.isLt; omega⟩
    simp only [productPinAt, outputPins, if_pos hi, dif_pos hi]
    exact congrArg some (productBit_pinnedDesc d N trial j)
  · simp only [productPinAt, outputPins, if_neg hi, dif_neg hi]

@[simp] theorem trialPinAt_pinnedDesc (d N : ℕ) (trial : Fin (4*d) → Option Bool)
    (i : Fin (4*d)) : trialPinAt d (pinnedDesc d N trial) i.val = trial i := by
  rw [trialPinAt, presenceBit_pinnedDesc, valueBit_pinnedDesc]
  cases trial i <;> rfl

def interfaceNo (d i : ℕ) := if i < 2*d then i else edgeBase d 9 (i-2*d)

theorem interfaceNo_eq {d : ℕ} (hd : 1 ≤ d) (i : Fin (4*d)) : interfaceNo d i.val = (ext hd i).val := by
  unfold interfaceNo ext extEdge
  split <;> rename_i h
  · split <;> rename_i h0
    · change _ = i.val + d*0; omega
    · change _ = i.val-d + d*1; omega
  · rw [dif_neg (show ¬ i.val < d by omega)]; rfl

def ok (desc : List Bool) (i : ℕ) (actual : Bool) :=
  let d := widthOf desc
  (if 2*d ≤ i then actual == bitAt desc (i-2*d) else true) &&
  (if bitAt desc (2*d+i) then actual == bitAt desc (6*d+i) else true)

theorem ok_spec {d : ℕ} (N : ℕ) (p : Fin (4*d) → Option Bool) (i : Fin (4*d)) (b : Bool) :
    ok (pinnedDesc d N p) i.val b = true ↔ (∀ c, outputPins d N i = some c → b = c) ∧ (∀ c, p i = some c → b = c) := by
  have A := productPinAt_pinnedDesc d N p i
  have B := trialPinAt_pinnedDesc d N p i
  rw [← A,← B]
  simp only [ok,widthOf_pinnedDesc,productPinAt,trialPinAt,Bool.and_eq_true]
  split <;> split <;> simp

def checks (q : Pad) (desc : List Bool) (v : ℕ) (a : List Bool) := allN q (4*q.length) (fun i => allN q a.length (fun j =>
  if (portList q v)[j]?.getD 0 = interfaceNo q.length i then ok desc i (a[j]?.getD false) else true))

theorem checks_spec (q : Pad) (hd : 1 ≤ q.length) (N : ℕ) (p : Fin (4*q.length) → Option Bool)
    (v : Fin (graph q.length hd).nV) (a : Fin ((graph q.length hd).deg v) → Bool) :
    checks q (pinnedDesc q.length N p) v.val (List.ofFn a) = true ↔
    (∀ i b, outputPins q.length N i = some b → ∀ j, ((graph q.length hd).ports v).get j = ext hd i → a j = b) ∧
    (∀ i b, p i = some b → ∀ j, ((graph q.length hd).ports v).get j = ext hd i → a j = b) := by
  let G := graph q.length hd
  have he := (graph_edge_bound hd).le
  have hdeg : G.deg v ≤ G.nE := (List.length_filter_le ..).trans List.length_finRange.le
  have hp : portList q v.val = (G.ports v).map Fin.val := by
    change edgeCount q.length (W q.length) ≤ _ at he
    unfold portList cap; rw [min_eq_left he]; exact portsNat_eq G v _ _ (fun i => congrArg Prod.fst (endpointsNat_eq hd i)) (fun i => congrArg Prod.snd (endpointsNat_eq hd i))
  have bound : (graph q.length hd).deg v ≤ 1100*(q.length+1) := hdeg.trans he
  have readPort (j : Fin ((graph q.length hd).deg v)) : (portList q v.val)[j.val]?.getD 0 = ((G.ports v).get j).val := by
    rw [hp,List.getElem?_map,List.getElem?_eq_getElem j.isLt]; rfl
  have readBit (j : Fin ((graph q.length hd).deg v)) : (List.ofFn a)[j.val]?.getD false = a j := by simp [List.getElem?_ofFn,j.isLt]
  simp only [checks,List.length_ofFn,allN_true q (show 4*q.length ≤ 1100*(q.length+1) by omega),allN_true q bound,readPort,readBit,interfaceNo_eq hd]
  constructor
  · intro h
    have t (i : Fin (4*q.length)) (j : Fin (G.deg v)) (hj : (G.ports v).get j = ext hd i) :=
      (ok_spec N p i (a j)).mp (by simpa [hj] using h i j)
    exact ⟨fun i b hb j hj => (t i j hj).1 b hb, fun i b hb j hj => (t i j hj).2 b hb⟩
  · rintro ⟨l,r⟩ i j
    by_cases h : (G.ports v).get j = ext hd i
    · have t := (ok_spec N p i (a j)).mpr ⟨fun b hb => l i b hb j h,fun b hb => r i b hb j h⟩
      simpa [h] using t
    · have hn : ((G.ports v).get j).val ≠ (ext hd i).val := fun he => h (Fin.ext he)
      simp [hn]
attribute [local fun_prop] Groundwork.PolyT.comp portList_poly allN_poly Groundwork.PolyT.optionElim
@[local fun_prop] private theorem no_poly {α} [Enc α] {d i : α → ℕ} (hd : PolyT d) (hi : PolyT i) : PolyT (fun x => interfaceNo (d x) (i x)) := by simp only [interfaceNo,edgeBase,W]; fun_prop
@[local fun_prop] private theorem ok_poly {α} [Enc α] {s : α → List Bool} {i : α → ℕ} {a : α → Bool} (hs : PolyT s) (hi : PolyT i) (ha : PolyT a) : PolyT (fun x => ok (s x) (i x) (a x)) := by simp only [ok,widthOf,bitAt]; fun_prop
attribute [local irreducible] portList ok interfaceNo
set_option maxHeartbeats 1000000 in
@[local fun_prop] theorem checks_poly {α} [Enc α] {q : α → Pad} {s a : α → List Bool} {v : α → ℕ} (hq : PolyT q) (hs : PolyT s) (hv : PolyT v) (ha : PolyT a) : PolyT fun x => checks (q x) (s x) (v x) (a x) := by
  unfold checks
  apply allN_poly (q := q) (n := fun x => 4*(q x).length) (f := fun x i => allN (q x) (a x).length (fun j => if (portList (q x) (v x))[j]?.getD 0 = interfaceNo (q x).length i then ok (s x) i ((a x)[j]?.getD false) else true)) hq (Groundwork.PolyT.mul (const 4) (Groundwork.PolyT.length hq))
  have q' : PolyT (fun z : α × ℕ => q z.1) := Groundwork.PolyT.comp hq (Groundwork.PolyT.fst (f:=fun p : α × ℕ => p) Groundwork.PolyT.id')
  have a' : PolyT (fun z : α × ℕ => a z.1) := Groundwork.PolyT.comp ha (Groundwork.PolyT.fst (f:=fun p : α × ℕ => p) Groundwork.PolyT.id')
  apply allN_poly (q := fun z : α × ℕ => q z.1) (n := fun z => (a z.1).length) (f := fun z j => if (portList (q z.1) (v z.1))[j]?.getD 0 = interfaceNo (q z.1).length z.2 then ok (s z.1) z.2 ((a z.1)[j]?.getD false) else true) q' (Groundwork.PolyT.length a')
  let pr := fun z : (α × ℕ) × ℕ => z.1.1
  have hpr : PolyT pr := Groundwork.PolyT.fst (Groundwork.PolyT.fst (f:=fun p : (α × ℕ) × ℕ => p) Groundwork.PolyT.id')
  have hq'' := Groundwork.PolyT.comp hq hpr
  have ha'' := Groundwork.PolyT.comp ha hpr
  have hs'' := Groundwork.PolyT.comp hs hpr
  have hv'' := Groundwork.PolyT.comp hv hpr
  dsimp only [pr] at hq'' ha'' hs'' hv''
  have hi : PolyT (fun z : (α × ℕ) × ℕ => z.1.2) := Groundwork.PolyT.snd (Groundwork.PolyT.fst (f:=fun p : (α × ℕ) × ℕ => p) Groundwork.PolyT.id')
  have hj : PolyT (fun z : (α × ℕ) × ℕ => z.2) := Groundwork.PolyT.snd (f:=fun p : (α × ℕ) × ℕ => p) Groundwork.PolyT.id'
  have he := portList_poly hq'' hv''
  have hf := no_poly (Groundwork.PolyT.length hq'') hi
  fun_prop

def padOf (desc : List Bool) : Pad := (desc.take (widthOf desc)).map (fun _ => ())
@[simp] theorem padOf_len (desc : List Bool) : (padOf desc).length = widthOf desc := by simp [padOf,widthOf,Nat.div_le_self]

private def canon (d v : ℕ) (a : List Bool) := encodePortQuery (countWord d) v a
private theorem frame_flat (w : List Bool) : Encoding.frame w = w.flatMap (fun b => [true,b]) ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [Encoding.frame, List.flatMap] using congrArg (fun u => true::b::u) ih

private def field (desc : List Bool) (v : ℕ) (a : List Bool) :=
  (w4_M5Evaluator.f (canon (widthOf desc) v a)).headD false && checks (padOf desc) desc v a

def eval (xs : List Bool) :=
  let t := firstThree xs
  if field t.1 (decodeNat t.2.1) t.2.2 then encodeNatListBin [1] else encodeNatListBin [0]

attribute [local fun_prop] Groundwork.PolyT.map Groundwork.PolyT.flatMap
private theorem canon_poly {α} [Enc α] {d v : α → ℕ} {a : α → List Bool} (hd : PolyT d) (hv : PolyT v) (ha : PolyT a) : PolyT (fun x => canon (d x) (v x) (a x)) := by simp only [canon,encodePortQuery,Encoding.encodeList,id_eq,frame_flat]; fun_prop

attribute [local irreducible] checks firstThree w4_M5Evaluator.f canon
set_option maxHeartbeats 1000000 in
theorem eval_poly : PolyT eval := by
  have hs := Groundwork.PolyT.fst firstThree_poly
  have hv := Groundwork.PolyT.fst (Groundwork.PolyT.snd query_components)
  have ha := Groundwork.PolyT.snd (Groundwork.PolyT.snd firstThree_poly)
  have hd : PolyT (fun x => widthOf (firstThree x).1) := by unfold widthOf; fun_prop
  have hq : PolyT (fun x => padOf (firstThree x).1) := by unfold padOf; fun_prop
  have hb := Groundwork.PolyT.comp f_poly (canon_poly hd hv ha)
  have hc := checks_poly hq hs hv ha
  unfold eval field
  dsimp only
  apply P2M_Groundwork_PolyT_ite__226169acf219
  · simpa using Groundwork.PolyT.and' (Groundwork.PolyT.headD hb (const false)) hc
  · exact const _
  · exact const _

theorem eval_spec : S6BCountCall.entrySpec eval := by
  intro d hd N pin v a
  let desc := pinnedDesc d N pin
  have hw : widthOf desc = d := widthOf_pinnedDesc ..
  have hq : (padOf desc).length = d := (padOf_len desc).trans hw
  have hgate := f_spec d hd v a
  have hchk : checks (padOf desc) desc v.val (List.ofFn a) = true ↔
    (∀ i b, outputPins d N i = some b → ∀ j, ((graph d hd).ports v).get j = ext hd i → a j = b) ∧
    (∀ i b, pin i = some b → ∀ j, ((graph d hd).ports v).get j = ext hd i → a j = b) := by
    have gen (q : Pad) (d : ℕ) (eq : q.length = d) (hd : 1 ≤ d) (p : Fin (4*d) → Option Bool) (v : Fin (graph d hd).nV) (a : Fin ((graph d hd).deg v) → Bool) : checks q (pinnedDesc d N p) v.val (List.ofFn a) = true ↔
        (∀ i b, outputPins d N i = some b → ∀ j, ((graph d hd).ports v).get j = ext hd i → a j = b) ∧
        (∀ i b, p i = some b → ∀ j, ((graph d hd).ports v).get j = ext hd i → a j = b) := by
      subst d
      exact checks_spec q hd N p v a
    exact gen _ _ hq hd pin v a
  have hb : field desc v.val (List.ofFn a) = pinTensor (graph d hd) (pinTensor (graph d hd) (tensor hd) (ext hd) (outputPins d N)) (ext hd) pin v a := by
    apply Bool.eq_iff_iff.mpr
    simp only [field,hw,canon,hgate,List.headD_cons,Bool.and_eq_true,hchk,pinTensor_eq_true,and_assoc]
    rfl
  have hp : firstThree (encodePortQuery desc v.val (List.ofFn a)) = (desc,countWord v.val,List.ofFn a) := by simp [firstThree,encodePortQuery,Encoding.encodeList,splitFrame_frame_append]
  change EncodesTruncPoly _ 1 (eval (encodePortQuery desc v.val (List.ofFn a))) _
  unfold eval
  simp only [hp,countWord_value,hb,productEntry]
  apply (encodesTruncPoly_one_iff _ _ _).2
  split <;> first | exact ⟨1,Nat.one_lt_two_pow (by omega),rfl,by simp⟩ | exact ⟨0,by positivity,rfl,by simp⟩
end DetDLP.S6BPort


