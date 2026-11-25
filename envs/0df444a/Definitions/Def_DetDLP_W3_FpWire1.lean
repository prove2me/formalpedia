-- Prove2me | Definitions.Def_DetDLP_W3_FpWire1
-- name    : DetDLP_W3_FpWire1
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:29:31.34675+00:00
-- url     : https://prove2.me/theorems/57ec4774-04d2-4a1e-b7f5-29ffe81e9fe2
-- title:
--   Binary parameter budgets in native prime-field wire queries
-- statement:
--   For the canonical prime-field query, each of the bit width, block count, and address width is at most the length of its binary input packet. The packet contains the prime, the threshold and the seed list. Framing the input again as the description of a local port query preserves these bounds.

import Definitions.Def_DetDLP_W3_Separator

set_option autoImplicit false
namespace DetDLP
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem w3_frameLength (w : List Bool) : (Encoding.frame w).length = 2*w.length+1 := by
  induction w with
  | nil => rfl
  | cons b w ih => change (Encoding.frame w).length+1+1 = 2*(w.length+1)+1; omega

theorem w3_encodedMemberLength {α : Type*} {enc : α → List Bool} {a : α} {xs : List α}
    (ha : a ∈ xs) : (enc a).length + 1 ≤ (Encoding.encodeList enc xs).length := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [Encoding.encodeList,List.length_cons,List.length_append,w3_frameLength]
    rcases List.mem_cons.mp ha with rfl | h
    · omega
    · have := ih h; omega

theorem w3_encodedCount {α : Type*} (enc : α → List Bool) (xs : List α) :
    xs.length ≤ (Encoding.encodeList enc xs).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [Encoding.encodeList,List.length_cons,List.length_append]; omega

theorem w3_clogWord (n : ℕ) : Nat.clog 2 n ≤ (countWord n).length := by
  by_cases h : n = 0
  · simp [h,countWord]
  simp only [countWord,if_neg h,Nat.size_eq_bits_len]
  exact (Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.lt_size_self n).le

theorem w3_fpNativeInputBounds (q : w3_Query) (hq : w3_fpQueries q) :
    q.b ≤ q.input.length ∧ q.m ≤ q.input.length ∧ q.k ≤ q.input.length := by
  obtain ⟨p,hp,h67,hnz,h64,hM,seed,F,hF,P,y,pre,rfl⟩ := hq
  let m := blockCount (bitLen p)
  let T := hashThreshold p (p-1) m (p-1)
  let ns := [p,(P : ZMod p).val,p-1,T]
  let ss := (List.finRange m).flatMap fun i => [(seed i).1.val+1,(seed i).2.val]
  let ws := [encodeNatListBin ns,encodeNatListBin ss,encodeFpFactorBlocks F,
    encodeNatListBin (List.ofFn fun j => (y j).val),pre]
  change bitLen p ≤ (Encoding.encodeList id ws).length ∧
    m ≤ (Encoding.encodeList id ws).length ∧ Nat.clog 2 (2*T) ≤ (Encoding.encodeList id ws).length
  have h1 := w3_encodedMemberLength (enc := id) (show encodeNatListBin ns ∈ ws by simp [ws])
  have h2 := w3_encodedMemberLength (enc := id) (show encodeNatListBin ss ∈ ws by simp [ws])
  have h3 := w3_encodedMemberLength (enc := countWord) (show p ∈ ns by simp [ns])
  have h4 := w3_encodedMemberLength (enc := countWord) (show T ∈ ns by simp [ns])
  change (encodeNatListBin ns).length + 1 ≤ _ at h1
  change (encodeNatListBin ss).length + 1 ≤ _ at h2
  change _ ≤ (encodeNatListBin ns).length at h3 h4
  have hs : ss.length = 2*m := by simp [ss,List.length_flatMap,Nat.mul_comm]
  have hc : ss.length ≤ (encodeNatListBin ss).length := w3_encodedCount _ _
  have hk : Nat.clog 2 (2*T) ≤ (countWord T).length + 1 := by
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    rw [pow_succ, Nat.mul_comm 2 T]
    exact Nat.mul_le_mul_right 2 ((Nat.clog_le_iff_le_pow (by decide)).mp (w3_clogWord T))
  have hb : bitLen p ≤ (countWord p).length := w3_clogWord p
  omega

theorem w3_portDescBound (w a : List Bool) (v : ℕ) : w.length ≤ (encodePortQuery w v a).length := by
  simp [encodePortQuery,Encoding.encodeList,w3_frameLength]; omega

end DetDLP


