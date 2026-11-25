-- Prove2me | Definitions.Def_DetDLP_S8M_SubPortFits
-- name    : DetDLP_S8M_SubPortFits
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T05:48:18.454804+00:00
-- url     : https://prove2.me/theorems/f9911f27-0050-4329-bfd6-a425ec9aa8d1
-- title:
--   Tag 6 sub-bank and prefix port fits
-- statement:
--   Proves fit for tabulated gate rows and prefix rows, and identifies the anchor count for the Tag 6 bank.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_AddFoldPortFits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
namespace DetDLP.S8M.PortEval
open S8H0 S8H.PortCombinators S8J S8J.CircuitRealizes NamedBlocks RegisterMap GateRoutes LocalGateEq PortPoly
variable {s : Shape}
theorem tabMany {k n c : ℕ} (hc : 0<c) (f : ℕ → GC) (a : Fin (n+1) → B k) (sz : ∀ j, (f j).1=c) (h : ∀ i : Fin (n+1), FitsG (f i) (a i).core) : FitsG (tab (n+1) f) (RangeRows.many n a).core := by
  induction n generalizing f with
  | zero =>
    rw [RangeRows.many]; have H : FitsG (f 0) (a 0).core := h 0
    refine ⟨by simpa [tab] using H.1,fun i w => ?_⟩; have hi : i.val < c := by rw [←sz 0,H.1]; exact i.isLt
    simpa only [tab,sz,Nat.div_eq_of_lt hi,Nat.mod_eq_of_lt hi] using H.2 i w
  | succ n ih =>
    have H := catB (h 0) (ih (fun j => f (j+1)) (fun i => a i.succ) (fun j => sz _) (fun i => h i.succ))
    rw [RangeRows.many]; refine ⟨?_,fun i w => ?_⟩
    · simp only [tab,sz,Nat.succ_mul]; have h' := H.1; simp only [catG,tab,sz,Nat.succ_mul] at h'; omega
    rw [←H.2]; simp only [tab,catG,Fin.val_zero,sz]; split_ifs with hi
    · simp [Nat.div_eq_of_lt hi,Nat.mod_eq_of_lt hi]
    · obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi); rw [hj]; simp [Nat.add_div_left _ hc]
theorem tabAll {n c : ℕ} (hc : 0<c) (f : ℕ → GC) (a : Fin n → B (s.size+1)) (sz : ∀ j, (f j).1=c) (h : ∀ i : Fin n, FitsG (f i) (a i).core) : FitsG (tab n f) (S8G.SeedAndAtomBank.allRows n a).core := by
  cases n with
  | zero => exact ⟨Nat.zero_mul _,fun i => i.elim0⟩
  | succ n => exact tabMany hc f a sz h

theorem anchor_eq (m d e : ℕ) : anchorCount m d e = (Routes.bank m d e).size+1 := by
  simp only [anchorCount,Routes.bank,ECAtomSlot.slotShape,S8H4.Routes.bank,GateRoutes.S,RegisterMap.bank,ECMapRows.mapShape,S8N.ECAddRoutes.addShape,ECMapRows.slot,RegisterMap.run,RegisterMap.triple,RegisterMap.mul,GateRoutes.auxShape,Shape.size]; ring
private theorem digit_read {m b d e : ℕ} (hd : b ≤ d) (i : Fin (2*m)) {r : Ref (Routes.bank m d e)} (hr : r ∈ Routes.digits b i) (z : Bool) : r.read z = z := by
  simp only [Routes.digits,List.mem_cons,List.mem_append,List.mem_ofFn,Set.mem_range] at hr
  rcases hr with rfl | ⟨k,rfl⟩ | ⟨k,rfl⟩
  · rfl
  all_goals have hk := k.rev.isLt.trans_le hd; simp only [GateRoutes.word,HashRows.padded,dif_pos hk,Ref.read]
theorem prefixFits (m b d e : ℕ) (hd : b ≤ d) (η : W) : FitsG (prefixG (2*m*(2*b+1)) η) (Routes.prefixRows (m:=m) (d:=d) (e:=e) b η).core := by
  let r := Routes.refs (m:=m) (d:=d) (e:=e) b
  have len : r.length = 2*m*(2*b+1) := by simp [r,Routes.refs,Routes.digits,List.length_flatMap]; ring
  have read {a} (ha : a ∈ r) (z) : a.read z = z := by
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp ha; rcases List.mem_append.mp hi with h|h <;> exact digit_read hd _ h z
  refine ⟨rfl,fun i w => ?_⟩; unfold Routes.prefixRows; dsimp only; rw [rows_local]; have hi : i.val < η.length := i.isLt
  change decide (i.val < _ ∧ _ = η.getD i.val false) = decide (i.val < r.length ∧ (r[i.val]?.getD _).read _ = η[i.val])
  rw [←len]; by_cases h : i.val < r.length
  · simp [h,List.getElem?_eq_getElem h,read (List.getElem_mem ..),List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,bit]
  · simp [h]
end DetDLP.S8M.PortEval


