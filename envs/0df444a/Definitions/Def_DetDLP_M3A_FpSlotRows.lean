-- Prove2me | Definitions.Def_DetDLP_M3A_FpSlotRows
-- name    : DetDLP_M3A_FpSlotRows
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T11:39:28.780595+00:00
-- url     : https://prove2.me/theorems/16bd2a38-a125-4e19-b6dd-092744f3e715
-- title:
--   Finite-field slot physical row semantics
-- statement:
--   Derives the checked integer equations and propagated reduction flag from the eight physical slot rows.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3A_FpSlotTile

set_option autoImplicit false
namespace DetDLP.M3A.FpSlotRows
open S8G.FpPhysicalAtom S8L.FpPair.Stage S8C S8J

abbrev Rows (d : ℕ) := Vec ((8*(d+1))*4)
def get {d : ℕ} (w : Rows d) (j : Fin 8) (l : Fin 4) (i : Fin (d+1)) := w (AddLayout.reg (col j i) l)
def number {d : ℕ} (w : Rows d) (j : Fin 8) (l : Fin 4) := (readWord (get w j l)).val

def wordsOK {d : ℕ} (p T : ℕ) (w : Rows d) :=
  (∀ j : Fin 7, number w j.castSucc 0 + number w j.castSucc 1 + (decide (j.val<5)).toNat = number w j.castSucc 2) ∧
  number w 0 1 = 0 ∧ number w 1 1 = 0 ∧ get w 0 2 (Fin.last d) = false ∧ get w 1 2 (Fin.last d) = false ∧
  get w 0 0 (Fin.last d) = false ∧ number w 2 2 = p ∧ number w 4 2 = p ∧ number w 3 2 = T ∧
  get w 5 0 (Fin.last d) = false ∧ get w 5 1 (Fin.last d) = false ∧
  (∀ i, get w 7 0 i = get w 7 0 0 ∧ get w 7 2 i = false ∧ get w 7 3 i = get w 7 0 0 ∧
    get w 7 1 i = (get w 7 0 0 && p.testBit i.val))

private def Row {d : ℕ} (p T : ℕ) (w : Rows d) (j : Fin 8) (i : Fin (d+1)) :=
  let a := get w j 0 i; let b := get w j 1 i; let z := get w j 2 i; let c := get w j 3 i
  let prev := get w j 3 (AddLayout.prev i)
  if j.val=7 then a=c ∧ z=false ∧ (i.val≠0 → a=prev) ∧ b=(a && p.testBit i.val)
  else a.toNat+b.toNat+(if i.val=0 then decide (j.val<5) else prev).toNat=z.toNat+2*c.toNat ∧ (i.val=d → c=false) ∧
    (j.val<2 → b=false ∧ (i.val=d → z=false)) ∧ (j.val=0 ∧ i.val=d → a=false) ∧
    (j.val=2 ∨ j.val=4 → z=p.testBit i.val) ∧ (j.val=3 → z=T.testBit i.val) ∧
    (j.val=5 ∧ i.val=d → a=false ∧ b=false)

private theorem pred {d : ℕ} (j : Fin 8) (i : Fin (d+1)) (h : i.val ≠ 0) : AddLayout.prev (col j i) = col j (AddLayout.prev i) := by
  apply Fin.ext; simp only [AddLayout.prev,col,finProdFinEquiv_apply_val,if_neg h]
  rw [if_neg (by omega)]; omega

private theorem row_iff {d : ℕ} (p T : ℕ) (w : Rows d) : Accept _ (rowTest d p T) w ↔ ∀ j i, Row p T w j i := by
  have atcol (j : Fin 8) (i : Fin (d+1)) : rowTest d p T (col j i) (fun e => w ((AddLayout.layout _).bit e.val)) = true ↔ Row p T w j i := by
    simp only [rowTest,col,Equiv.symm_apply_apply,AddLayout.layout,AddLayout.bit_pos,Row,get]
    have pr (hi : i.val ≠ 0) : AddLayout.prev (finProdFinEquiv (j,i)) = finProdFinEquiv (j,AddLayout.prev i) := pred j i hi
    by_cases hj : j.val=7 <;> simp only [hj,if_true,if_false,decide_eq_true_eq] <;>
      by_cases hi : i.val=0 <;> simp (config := {decide := true}) only [hi,if_true,if_false,not_true_eq_false,false_implies,not_false_eq_true,dif_pos,dif_neg] <;> first | rfl | (rw [pr hi]; rfl)
  constructor
  · exact fun h j i => (atcol j i).mp (h _)
  · intro h g; obtain ⟨⟨j,i⟩,rfl⟩ := finProdFinEquiv.surjective g; exact (atcol j i).mpr (h j i)

private theorem get_bits {d : ℕ} (w : Rows d) (j : Fin 8) (l : Fin 4) (i : Fin (d+1)) : (number w j l).testBit i.val = get w j l i := read_bit _ i

private theorem eq_number {d : ℕ} (w : Rows d) (j : Fin 8) (l : Fin 4) {n : ℕ} (hn : n < 2^(d+1))
    (h : ∀ i, get w j l i = n.testBit i.val) : number w j l = n := by
  exact congrArg Fin.val ((congrArg readWord (funext h)).trans (read_word (⟨n,hn⟩ : Fin (2^(d+1)))))

private theorem columns {d : ℕ} (w : Rows d) (j : Fin 8) (c : Bool) :
    AddLayout.Columns c (get w j 0) (get w j 1) (get w j 2) (get w j 3) ↔
    w3_addColumns (d+1) (number w j 0) (number w j 1) (number w j 2) c (get w j 3) := by
  simpa only [get_bits] using AddLayout.columns_iff (by omega : 0 < d+1) (number w j 0) (number w j 1) (number w j 2) c (get w j 3)

private theorem flag {d p T : ℕ} {w : Rows d} (h : ∀ j i, Row p T w j i) : ∀ i, get w 7 0 i = get w 7 0 0 := by
  have H (i : Fin (d+1)) : get w 7 0 i = get w 7 3 i ∧ get w 7 2 i = false ∧ (i.val ≠ 0 → get w 7 0 i = get w 7 3 (AddLayout.prev i)) ∧ get w 7 1 i = (get w 7 0 i && p.testBit i.val) := by
    simpa only [Row,show (7:Fin 8).val=7 by rfl,if_true] using h 7 i
  rintro ⟨i,hi⟩; induction i with
  | zero => rfl
  | succ i ih =>
    let a : Fin (d+1) := ⟨i+1,hi⟩
    let b : Fin (d+1) := ⟨i,by omega⟩
    have hb : AddLayout.prev a = b := Fin.ext (by simp [a,b,AddLayout.prev])
    exact ((H a).2.2.1 (Nat.succ_ne_zero _)).trans ((congrArg (get w 7 3) hb).trans ((H b).1.symm.trans (ih b.isLt)))

/-- Seven complete integer equations and the unique propagated reduction flag follow from the physical row checks. -/
theorem sound {d p T : ℕ} {w : Rows d} (hp : p < 2^(d+1)) (hT : T < 2^(d+1)) (hw : Accept _ (rowTest d p T) w) : wordsOK p T w := by
  have H := (row_iff p T w).mp hw
  have F := flag H
  have generic (j : Fin 8) (hj : j.val ≠ 7) (i : Fin (d+1)) := (if_neg hj).mp (H j i)
  have Eq (j : Fin 7) : AddLayout.Columns (decide (j.val<5)) (get w j.castSucc 0) (get w j.castSucc 1) (get w j.castSucc 2) (get w j.castSucc 3) := by
    intro i; have h := generic j.castSucc (by change j.val ≠ 7; omega) i
    exact ⟨h.1,fun hi => h.2.1 (by omega)⟩
  refine ⟨fun j => w3_addColumns_sound (readWord _).isLt (readWord _).isLt (readWord _).isLt ((columns ..).mp (Eq j)),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply eq_number _ _ _ (Nat.two_pow_pos _); intro i; rw [Nat.zero_testBit]; exact ((generic 0 (by decide) i).2.2.1 (by decide)).1
  · apply eq_number _ _ _ (Nat.two_pow_pos _); intro i; rw [Nat.zero_testBit]; exact ((generic 1 (by decide) i).2.2.1 (by decide)).1
  · exact ((generic 0 (by decide) (Fin.last d)).2.2.1 (by decide)).2 rfl
  · exact ((generic 1 (by decide) (Fin.last d)).2.2.1 (by decide)).2 rfl
  · exact (generic 0 (by decide) (Fin.last d)).2.2.2.1 ⟨rfl,rfl⟩
  · exact eq_number _ _ _ hp (fun i => (generic 2 (by decide) i).2.2.2.2.1 (Or.inl rfl))
  · exact eq_number _ _ _ hp (fun i => (generic 4 (by decide) i).2.2.2.2.1 (Or.inr rfl))
  · exact eq_number _ _ _ hT (fun i => (generic 3 (by decide) i).2.2.2.2.2.1 rfl)
  · exact ((generic 5 (by decide) (Fin.last d)).2.2.2.2.2.2 ⟨rfl,rfl⟩).1
  · exact ((generic 5 (by decide) (Fin.last d)).2.2.2.2.2.2 ⟨rfl,rfl⟩).2
  · intro i; have h := H 7 i; simp only [Row,show (7:Fin 8).val=7 by rfl,if_true] at h
    exact ⟨F i,h.2.1,h.1.symm.trans (F i),h.2.2.2.trans (congrArg (· && p.testBit i.val) (F i))⟩

end DetDLP.M3A.FpSlotRows
abbrev DetDLP_M3A_FpSlotRows := @DetDLP.M3A.FpSlotRows.wordsOK


