-- Prove2me | Definitions.Def_DetDLP_S8C_AddLayout
-- name    : DetDLP_S8C_AddLayout
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:42:55.290575+00:00
-- url     : https://prove2.me/theorems/f586b139-171f-4e81-9125-1352cbecdd88
-- title:
--   Five-port binary addition layout
-- statement:
--   A W3 factor layout for a little-endian ripple adder with public initial carry and zero final carry. At positive width each satisfying bit assignment obeys the column equations. There are five incidences per column, gate degree at most five, and copy degree at most two.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_W3_FpIncidence
set_option autoImplicit false
namespace DetDLP.S8C.AddLayout

/-- Columns are in little-endian order. The fifth incidence reads the preceding carry;
    column zero ignores that port and uses the public carry instead. -/
def col {d : ℕ} (e : Fin (d*5)) : Fin d := ⟨e.val/5,by have := e.isLt; omega⟩
def pos {d : ℕ} (i : Fin d) (l : Fin 5) : Fin (d*5) := ⟨5*i.val+l.val,by omega⟩
def reg {d : ℕ} (i : Fin d) (l : Fin 4) : Fin (d*4) := ⟨4*i.val+l.val,by omega⟩
def prev {d : ℕ} (i : Fin d) : Fin d := ⟨if i.val=0 then d-1 else i.val-1,by have := i.isLt; split <;> omega⟩
def bit {d : ℕ} (e : Fin (d*5)) : Fin (d*4) :=
  if h : e.val%5 < 4 then reg (col e) ⟨e.val%5,h⟩ else reg (prev (col e)) 3

def layout (d : ℕ) : w3_FactorLayout where
  ng := d
  nb := d*4
  ne := d*5
  gate := col
  bit := bit
  rep b := pos (⟨b.val/4,by have := b.isLt; omega⟩ : Fin d) ⟨b.val%4,by omega⟩
  rep_bit b := by
    unfold bit
    rw [dif_pos (by change (5*(b.val/4)+b.val%4)%5 < 4; omega)]
    apply Fin.ext; change 4*((5*(b.val/4)+b.val%4)/5) + (5*(b.val/4)+b.val%4)%5 = b.val
    omega

@[simp] theorem col_pos {d : ℕ} (i : Fin d) (l : Fin 5) : col (pos i l) = i := by
  apply Fin.ext; simp only [col,pos]; omega

def test {d : ℕ} (cin : Bool) : w3_factorTest (layout d) := fun i f =>
  let get (l : Fin 5) := f ⟨pos i l,col_pos i l⟩
  let carry := if i.val=0 then cin else get 4
  decide ((get 0).toNat + (get 1).toNat + carry.toNat = (get 2).toNat + 2*(get 3).toNat ∧
    (i.val+1 = d → get 3 = false))

def Columns {d : ℕ} (cin : Bool) (a b z c : Fin d → Bool) := ∀ i : Fin d,
  (a i).toNat+(b i).toNat+(if i.val=0 then cin else c (prev i)).toNat = (z i).toNat+2*(c i).toNat ∧
  (i.val+1 = d → c i = false)

theorem bit_pos {d : ℕ} (i : Fin d) (l : Fin 5) : bit (pos i l) =
    if h : l.val < 4 then reg i ⟨l.val,h⟩ else reg (prev i) 3 := by
  have h : (pos i l).val % 5 = l.val := by change (5*i.val+l.val)%5=l.val; omega
  simp only [bit,h,col_pos]

theorem test_iff {d : ℕ} (cin : Bool) (x : Fin (d*4) → Bool) :
    (∀ g, test cin g (fun e => x ((layout d).bit e.1)) = true) ↔
    Columns cin (fun i => x (reg i 0)) (fun i => x (reg i 1)) (fun i => x (reg i 2)) (fun i => x (reg i 3)) := by
  unfold test Columns; simp only [layout,bit_pos,decide_eq_true_eq]; rfl

/-- Exact edge count, independent of the values of the three operands. -/
@[simp] theorem edges (d : ℕ) : (w3_factorGraph (layout d)).nE = d*5 := rfl

private theorem gateBound {d : ℕ} (i : Fin d) :
    (((List.finRange (d*5)).filter fun e => decide (col e = i))).length ≤ 5 := by
  let F := (List.finRange (d*5)).filter fun e => decide (col e = i)
  have nd : F.Nodup := (List.nodup_finRange _).filter _
  let f : ↥F.toFinset → Fin 5 := fun e => ⟨e.1.val%5,by omega⟩
  have inj : Function.Injective f := by
    intro e t h; have he : col e.1 = i := by simpa [F] using e.2
    have ht : col t.1 = i := by simpa [F] using t.2
    have heq := congrArg Fin.val (he.trans ht.symm); have hmod := congrArg Fin.val h
    apply Subtype.ext; apply Fin.ext; change e.1.val/5=t.1.val/5 at heq
    change e.1.val%5=t.1.val%5 at hmod; omega
  have h := Fintype.card_le_of_injective f inj
  rw [Fintype.card_coe, List.toFinset_card_of_nodup nd, Fintype.card_fin] at h
  exact h

theorem gateDegree {d : ℕ} (i : Fin d) : (w3_factorGraph (layout d)).deg (Fin.castAdd (d*4) i) ≤ 5 :=
  (w3_gateDegree (layout d) i).le.trans (gateBound i)

private theorem prev_inj {d : ℕ} : Function.Injective (@prev d) := by
  intro i j h; have he := congrArg Fin.val h; simp only [prev] at he
  apply Fin.ext; split_ifs at he <;> omega

private theorem samePort {d : ℕ} (e t : Fin (d*5)) (h : bit e = bit t)
    (hl : (e.val%5 < 4) ↔ (t.val%5 < 4)) : e = t := by
  by_cases he : e.val%5 < 4
  · have ht := hl.mp he
    simp only [bit,dif_pos he,dif_pos ht] at h
    have eq := congrArg Fin.val h; change 4*(e.val/5)+e.val%5 = 4*(t.val/5)+t.val%5 at eq
    apply Fin.ext; omega
  · have ht : ¬t.val%5 < 4 := fun v => he (hl.mpr v)
    simp only [bit,dif_neg he,dif_neg ht] at h
    have eq := congrArg Fin.val h
    change 4*(prev (col e)).val+3 = 4*(prev (col t)).val+3 at eq
    have hc : prev (col e) = prev (col t) := Fin.ext (by omega)
    have hc' := congrArg Fin.val (prev_inj hc); change e.val/5=t.val/5 at hc'
    apply Fin.ext; omega

theorem bitDegree {d : ℕ} (b : Fin (d*4)) : (w3_factorGraph (layout d)).deg (Fin.natAdd d b) ≤ 2 := by
  apply (w3_bitDegree (layout d) b).le.trans
  let F := (List.finRange (d*5)).filter fun e => decide (bit e = b)
  have nd : F.Nodup := (List.nodup_finRange _).filter _
  let f : ↥F.toFinset → Bool := fun e => decide (e.1.val%5 < 4)
  have inj : Function.Injective f := by
    intro e t h; have he : bit e.1 = b := by simpa [F] using e.2
    have ht : bit t.1 = b := by simpa [F] using t.2
    apply Subtype.ext; apply samePort _ _ (he.trans ht.symm)
    by_cases he' : e.1.val%5 < 4 <;> by_cases ht' : t.1.val%5 < 4 <;> simp_all [f] <;> omega
  have h := Fintype.card_le_of_injective f inj
  rw [Fintype.card_coe,List.toFinset_card_of_nodup nd,Fintype.card_bool] at h; exact h

theorem degree {d : ℕ} (v : Fin (d + d*4)) : (w3_factorGraph (layout d)).deg v ≤ 5 :=
  Fin.addCases gateDegree (fun b => (bitDegree b).trans (by decide)) v

end DetDLP.S8C.AddLayout


