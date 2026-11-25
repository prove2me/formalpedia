-- Prove2me | Definitions.Def_DetDLP_M3A_FpSlotSound
-- name    : DetDLP_M3A_FpSlotSound
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T12:49:50.810743+00:00
-- url     : https://prove2.me/theorems/37785931-01ac-459e-8b63-bf77e887a851
-- title:
--   Native Fp slot readout soundness
-- statement:
--   Decodes the residue and padded hash bus of any accepting tile, proves the multiplier receives raw pin plus one, and rules out incrementing the slope twice.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3A_FpSlotRows
import Definitions.Def_DetDLP_S8L_FpPairPhysicalHash

set_option autoImplicit false
namespace DetDLP.M3A.FpSlotSound
open S8J S8G.FpPhysicalAtom S8L.FpPair.Stage.Links FpSlotTile

variable {d k p T a b : ℕ} (hd : 1 ≤ d)

/-- The bus has a unique extension to the pinned physical atom. -/
noncomputable abbrev forget : {x : Fin (slotLayout d k hd).nb → Bool //
    Accept _ (slotTest hd p T a b) x} ≃ {x : Fin (S8G.FpPhysicalAtom.layout d hd).nb → Bool //
    Accept _ (seedTest hd p T a b) x} := forgetBus hd p T a b

/-- A pinned physical atom is exactly its multiplier checks, eight column strips, and all physical ties. -/
theorem physical_iff (x : Fin (S8G.FpPhysicalAtom.layout d hd).nb → Bool) :
    Accept _ (seedTest hd p T a b) x ↔
      (Accept _ (S8G.FpPhysicalAtom.stageTest hd p) (x ∘ Fin.castAdd _) ∧
        Accept _ (S8G.FpPhysicalAtom.rowTest d p (min T p)) (x ∘ Fin.natAdd _)) ∧
      (∀ i, x (ties hd i).1 = x (ties hd i).2) ∧
      (∀ i, (x (aWire hd i) = a.testBit i.val ∧ x (bWire hd i) = b.testBit i.val)) := by
  classical
  rw [seedTest,atPins_iff,atPins_iff]
  rw [S8G.FpPhysicalAtom.accept_iff]
  constructor
  · rintro ⟨⟨⟨h,u⟩,v⟩,w⟩; exact ⟨h,u,fun i => ⟨v i,w i⟩⟩
  · rintro ⟨h,u,v⟩; exact ⟨⟨⟨h,u⟩,fun i => (v i).1⟩,fun i => (v i).2⟩

open FpSlotRows S8L.FpPair.Stage w4_M5PortTensor

abbrev rowPart (x : Fin (slotLayout d k hd).nb → Bool) : Rows d :=
  (x ∘ Fin.castAdd k) ∘ Fin.natAdd _

/-- The public residue is the result on the positive-input strip. -/
theorem residue_read (x : Fin (slotLayout d k hd).nb → Bool) (i : Fin d) :
    x (xBits hd i) = (number (rowPart hd x) 1 2).testBit i.val :=
  (read_bit (get (rowPart hd x) 1 2) i.castSucc).symm

/-- The exported hash word is the linked third strip, followed by forced zero padding. -/
theorem hash_read {x : Fin (slotLayout d k hd).nb → Bool}
    (hx : Accept _ (slotTest hd p T a b) x) (i : Fin k) (hi : i.val < d+1) :
    x (zBits hd i) = x (tap hd ⟨i.val,lt_min i.isLt hi⟩) := by
  exact read_low hd hx ⟨i.val,lt_min i.isLt hi⟩

theorem hash_pad {x : Fin (slotLayout d k hd).nb → Bool}
    (hx : Accept _ (slotTest hd p T a b) x) (i : Fin k) (hi : d+1 ≤ i.val) :
    x (zBits hd i) = false := read_high hd hx i hi

private theorem num_of_bits {w : Rows d} {j : Fin 8} {l : Fin 4} {n : ℕ}
    (hn : n < 2^(d+1)) (h : ∀ i, get w j l i = n.testBit i.val) : number w j l = n :=
  congrArg Fin.val ((congrArg readWord (funext h)).trans (read_word (⟨n,hn⟩ : Fin (2^(d+1)))))

private theorem padded {w : Rows d} {j : Fin 8} {l : Fin 4} {n : ℕ} (hn : n < 2^d)
    (h : ∀ i : Fin d, get w j l i.castSucc = n.testBit i.val)
    (ht : get w j l (Fin.last d) = false) : number w j l = n := by
  apply num_of_bits (hn.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  intro i; induction i using Fin.lastCases with
  | last => exact ht.trans (Nat.testBit_lt_two_pow hn).symm
  | cast i => exact h i

private theorem roweq {w : Rows d} {j j' : Fin 8} {l l' : Fin 4}
    (h : ∀ i, get w j l i = get w j' l' i) : number w j l = number w j' l' :=
  congrArg (fun v => (readWord v).val) (funext h)

/-- A pinned slot adds one to its first parameter before passing it to M5. -/
theorem multiplier_input {x : Fin (slotLayout d k hd).nb → Bool}
    (ha : a < 2^d) (hp : p < 2^d) (hx : Accept _ (slotTest hd p T a b) x) (i : Fin d) :
    x (Fin.castAdd k (st hd (mul1 hd (inPos false i)))) = (a+1).testBit i.val := by
  let v := x ∘ Fin.castAdd k
  let w := rowPart hd x
  have H := (physical_iff hd v).mp ((forget hd ⟨x,hx⟩).2)
  have hpb : p < 2^(d+1) := hp.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have W := FpSlotRows.sound hpb ((min_le_right T p).trans_lt hpb) H.1.2
  have hn : number w 0 0 = a := padded ha (fun t => (H.2.2 t).1) W.2.2.2.2.2.1
  have E := W.1 (0 : Fin 7)
  change number w 0 0 + number w 0 1 + 1 = number w 0 2 at E
  rw [hn,show number w 0 1 = 0 from W.2.1,Nat.add_zero] at E
  have tie := H.2.1 (Fin.castAdd (5*(d+1)) (finProdFinEquiv ((0 : Fin 3),i)))
  simp only [ties,Fin.addCases_left,Equiv.symm_apply_apply] at tie
  exact tie.symm.trans ((read_bit (get w 0 2) i.castSucc).symm.trans (congrArg (fun n : ℕ => n.testBit i.val) E.symm))

private theorem premainder {n : ℕ} (hn : n < 2^d) (i : Fin (2*d)) (h : d ≤ i.val) : n.testBit i.val = false :=
  Nat.testBit_lt_two_pow (hn.trans_le (Nat.pow_le_pow_right (by decide) h))

/-- Read the numeric hash straight from the threshold comparison row. -/
theorem hash_bits {x : Fin (slotLayout d k hd).nb → Bool} (hx : Accept _ (slotTest hd p T a b) x)
    (i : Fin k) : x (zBits hd i) = (number (rowPart hd x) 3 0).testBit i.val := by
  by_cases hi : i.val < d+1
  · exact (hash_read hd hx i hi).trans (read_bit (get (rowPart hd x) 3 0) ⟨i.val,hi⟩).symm
  · exact (hash_pad hd hx i (by omega)).trans (Nat.testBit_lt_two_pow ((readWord _).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)))).symm

/-- For raw pin a the actual multiplier is a+1. Both exposed words are the ones used by that hash. -/
theorem hash_value (mul : w3_modMulInterface) (hp : 2 ≤ p) (hf : p < 2^d)
    (ha : a+1 < p) (hb : b < p) {x : Fin (slotLayout d k hd).nb → Bool}
    (hx : Accept _ (slotTest hd p T a b) x) :
    let w := rowPart hd x
    number w 3 0 = ((a+1)*number w 1 2+b)%p := by
  let v := x ∘ Fin.castAdd k
  let w := rowPart hd x
  let s : StageBits hd := v ∘ Fin.castAdd _
  have H := (physical_iff hd v).mp ((forget hd ⟨x,hx⟩).2)
  have hpb : p < 2^(d+1) := hf.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have W : wordsOK p (min T p) w := FpSlotRows.sound hpb ((min_le_right T p).trans_lt hpb) H.1.2
  obtain ⟨eqs,_,_,_,_,_,zp,zp',zt,_,topb,flag⟩ := W
  have ts := H.2.1
  have short (j : Fin 3) (i : Fin d) := ts (Fin.castAdd (5*(d+1)) (finProdFinEquiv (j,i)))
  have long (j : Fin 5) (i : Fin (d+1)) := ts (Fin.natAdd (3*d) (finProdFinEquiv (j,i)))
  simp only [ties,Fin.addCases_left,Fin.addCases_right,Equiv.symm_apply_apply] at short long
  have e12 : number w 1 2 = number w 2 0 := roweq (long 0)
  have e36 : number w 3 0 = number w 6 0 := roweq (long 1)
  have e45 : number w 4 0 = number w 5 0 := roweq (long 2)
  have e56 : number w 5 2 = number w 6 2 := roweq (long 3)
  have e76 : number w 7 1 = number w 6 1 := roweq (long 4)
  have eqj (j : Fin 7) := eqs j
  have e2 := eqj 2; have e3 := eqj 3; have e4 := eqj 4; have e5 := eqj 5; have e6 := eqj 6
  change number w 2 0 + number w 2 1 + 1 = number w 2 2 at e2
  change number w 3 0 + number w 3 1 + 1 = number w 3 2 at e3
  change number w 4 0 + number w 4 1 + 1 = number w 4 2 at e4
  change number w 5 0 + number w 5 1 + 0 = number w 5 2 at e5
  change number w 6 0 + number w 6 1 + 0 = number w 6 2 at e6
  have hu : number w 5 0 < p := by omega
  have hxlt : number w 1 2 < p := by omega
  have hz : number w 3 0 < p := by omega
  have hn : number w 5 1 = b := padded (hb.trans hf) (fun i => (H.2.2 i).2) topb
  have hs := H.1.1
  change Accept _ (S8G.FpPhysicalAtom.stageTest hd p) s at hs
  unfold S8G.FpPhysicalAtom.stageTest at hs
  erw [atPins_iff,atPins_iff] at hs
  have bound : Boundary hd p (a+1) (number w 1 2) (number w 5 0) s := by
    refine ⟨multiplier_input hd (by omega) hf hx,fun i => ?_,hs.1.2,fun i => ?_⟩
    · exact (short 1 i).symm.trans (read_bit (get w 1 2) i.castSucc).symm
    · by_cases hi : i.val < d
      · let t : Fin d := ⟨i.val,hi⟩
        exact (short 2 t).symm.trans (read_bit (get w 5 0) t.castSucc).symm
      · let t : Fin d := ⟨i.val-d,by have := i.isLt; omega⟩
        have et : (⟨d+t.val,by omega⟩ : Fin (2*d)) = i := Fin.ext (by dsimp [t]; omega)
        rw [premainder (hu.trans hf) i (by omega),←et]; exact hs.2 t
  have HH := (linked_iff ..).mp (And.intro hs.1.1 bound)
  have c := decode hd ((hu.trans hf).trans_le (Nat.pow_le_pow_right (by decide) (show d ≤ 2*d by omega))) s HH.1 HH.2
  have rem := ((mul d hd p (a+1) (number w 1 2) (number w 5 0) hp hf.le ha hxlt hu).2 hf).2 _ c
  let f := get w 7 0 0
  have fl : number w 7 1 = (if f then p else 0) := by
    cases he : f
    · apply num_of_bits (Nat.two_pow_pos _); intro i; simpa [←show f = get w 7 0 0 from rfl,he] using (flag i).2.2.2
    · apply num_of_bits hpb; intro i; simpa [←show f = get w 7 0 0 from rfl,he] using (flag i).2.2.2
  change number w 3 0 = _
  rw [←Nat.mod_add_mod,←rem]
  have final : number w 5 0+b = number w 3 0+(if f then p else 0) := by omega
  rw [final]; cases f <;> simp [Nat.mod_eq_of_lt hz]

/-- A second increment cannot realize the entry for unit 1 at seed (0,0):
    its expected address is 1, but the low bit on the physical bus is false. -/
theorem double_increment_counterexample (mul : w3_modMulInterface) (hp : 2 < p) (hf : p < 2^d)
    (hk : 0 < k) {x : Fin (slotLayout d k hd).nb → Bool}
    (hx : Accept _ (slotTest hd p T 1 0) x)
    (hres : ∀ i : Fin d, x (xBits hd i) = (1 : ℕ).testBit i.val) :
    x (zBits hd ⟨0,hk⟩) ≠ (1 : ℕ).testBit 0 := by
  let w := rowPart hd x
  have H := (physical_iff hd _).mp ((forget hd ⟨x,hx⟩).2)
  have hpb : p < 2^(d+1) := hf.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have W := FpSlotRows.sound hpb ((min_le_right T p).trans_lt hpb) H.1.2
  have h1 : number w 1 2 = 1 := padded (by omega) hres W.2.2.2.2.1
  have h2 := hash_value hd mul hp.le hf (by omega) (by omega) hx
  change number w 3 0 = ((1+1)*number w 1 2+0)%p at h2
  rw [h1] at h2
  change number w 3 0 = 2%p at h2
  rw [Nat.mod_eq_of_lt hp] at h2
  rw [hash_bits hd hx]
  change (number w 3 0).testBit 0 ≠ (1 : ℕ).testBit 0
  rw [h2]; decide

end DetDLP.M3A.FpSlotSound
noncomputable abbrev DetDLP_M3A_FpSlotSound := @DetDLP.M3A.FpSlotSound.hash_value


