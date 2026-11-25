-- Prove2me | Definitions.Def_DetDLP_S8C_AddSound
-- name    : DetDLP_S8C_AddSound
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:49:29.738545+00:00
-- url     : https://prove2.me/theorems/b70b765a-a07f-4c37-8fd1-1b64e57a62aa
-- title:
--   Verification of the ripple-adder column tests
-- statement:
--   At every positive width the local tests of the five-port addition layout agree with the recursive carry predicate. Thus the previously proved arithmetic soundness and uniqueness of carry bits apply to the concrete layout.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8C_AddLayout
import Definitions.Def_DetDLP_W3_FpCarryPins
set_option autoImplicit false
namespace DetDLP.S8C.AddLayout

private theorem low (x : ℕ) : (x.testBit 0).toNat = x%2 := by
  rw [Nat.testBit_zero]; by_cases h : x%2=1 <;> simp [h] <;> omega

def scanIn {d : ℕ} (cin : Bool) (c : Fin d → Bool) (j : ℕ) : Bool :=
  if j=0 then cin else if h : j-1 < d then c ⟨j-1,h⟩ else false

private theorem scan_succ {d : ℕ} (cin : Bool) (c : Fin (d+1) → Bool) (j : ℕ) (hj : j ≤ d) :
    scanIn cin c (j+1) = scanIn (c 0) (fun i : Fin d => c i.succ) j := by
  cases j with
  | zero => simp [scanIn]
  | succ j => simp [scanIn,show j<d by omega,show j+1<d+1 by omega]

def entries {d : ℕ} (a b z : ℕ) (cin : Bool) (c : Fin d → Bool) : Prop :=
  (∀ i : Fin d, (a.testBit i.val).toNat+(b.testBit i.val).toNat+(scanIn cin c i.val).toNat =
    (z.testBit i.val).toNat+2*(c i).toNat) ∧ scanIn cin c d = false

theorem entries_iff {d : ℕ} (a b z : ℕ) (cin : Bool) (c : Fin d → Bool) :
    entries a b z cin c ↔ w3_addColumns d a b z cin c := by
  induction d generalizing a b z cin with
  | zero => simp [entries,scanIn,w3_addColumns]
  | succ d ih =>
    rw [w3_addColumns,← ih]
    let tail := fun i : Fin d => c i.succ
    have hs (i : Fin d) : scanIn cin c (i.val+1) = scanIn (c 0) tail i.val := scan_succ _ _ _ i.isLt.le
    have hend : scanIn cin c (d+1) = scanIn (c 0) tail d := scan_succ _ _ _ le_rfl
    constructor
    · rintro ⟨hf,hb⟩
      refine ⟨?_,fun i => ?_,hend ▸ hb⟩
      · simpa only [Fin.val_zero,low,scanIn,if_pos rfl,if_true] using hf 0
      · simpa only [hs,Fin.val_succ,Nat.testBit_succ,tail] using hf i.succ
    · rintro ⟨h0,ht,hend'⟩
      refine ⟨?_,hend.trans hend'⟩
      intro i; cases i using Fin.cases with
      | zero => simpa only [Fin.val_zero,low,scanIn,if_pos rfl,if_true] using h0
      | succ i => simpa only [hs,Fin.val_succ,Nat.testBit_succ,tail] using ht i

theorem columns_iff {d : ℕ} (hd : 0 < d) (a b z : ℕ) (cin : Bool) (c : Fin d → Bool) :
    Columns cin (fun i => a.testBit i.val) (fun i => b.testBit i.val) (fun i => z.testBit i.val) c ↔
    w3_addColumns d a b z cin c := by
  rw [← entries_iff]
  have hi (i : Fin d) : scanIn cin c i.val = (if i.val=0 then cin else c (prev i)) := by
    by_cases h : i.val=0 <;> simp [h,scanIn,prev,show i.val-1 < d by omega]
  let last : Fin d := ⟨d-1,by omega⟩
  have hl : scanIn cin c d = c last := by simp [scanIn,hd.ne',last,show d-1<d by omega]
  constructor
  · intro h
    exact ⟨fun i => (hi i).symm ▸ (h i).1,hl.trans ((h last).2 (by dsimp [last]; omega))⟩
  · rintro ⟨h,hf⟩ i
    refine ⟨hi i ▸ h i,fun hidx => ?_⟩
    have eq : i = last := Fin.ext (by dsimp [last]; omega)
    exact eq.symm ▸ (hl.symm.trans hf)

end DetDLP.S8C.AddLayout


