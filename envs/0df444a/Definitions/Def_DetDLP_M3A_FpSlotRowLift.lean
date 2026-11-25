-- Prove2me | Definitions.Def_DetDLP_M3A_FpSlotRowLift
-- name    : DetDLP_M3A_FpSlotRowLift
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T14:23:14.456262+00:00
-- url     : https://prove2.me/theorems/8b2ed8ff-5a98-4bc8-95bd-7114e7299dcc
-- title:
--   Fp slot row witness lift
-- statement:
--   Public slot index readout and unique 8-row addition-strip witness lift for pinned Fp hash-slot tiles.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4.2 (pp. 14-15)

import Definitions.Def_DetDLP_M3A_FpSlotLift

set_option autoImplicit false
namespace DetDLP.M3A.FpSlotRowLift

export FpSlotLift (Accepted toResidue forget physical_iff rowPart residue_read hash_read hash_pad multiplier_input hash_bits hash_value)

open FpSlotRows FpSlotTile S8J S8G.FpPhysicalAtom

variable {d k m p T : ℕ} (hd : 1 ≤ d) (mul : w3_modMulInterface) (hp : 2 ≤ p) (hf : p < 2^d)
variable (seed : FpSeed p m) (i : Fin m)
variable [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ)
variable (hF : (F i).Nodup ∧ (F i).toFinset = fpFactorBlock T seed i)

/-- Forward direction of the slot equivalence with the original raw seed pin. -/
noncomputable def index (x : Accepted hd seed i T k) : Fin ((w3_fpFB F).blocks i).length :=
  (w3_fpBlockResidueEquiv seed F i T hF).symm (toResidue hd mul hp hf seed i x)

theorem residue_eq (x : Accepted hd seed i T k) :
    let r := index hd mul hp hf seed i F hF x
    (w3_fpResidue (((w3_fpFB F).blocks i).get r).toMul).val = number (rowPart hd x.1) 1 2 :=
  congrArg (fun z : w3_fpBlockResidues seed i T => z.val.val)
    ((w3_fpBlockResidueEquiv seed F i T hF).apply_symm_apply (toResidue hd mul hp hf seed i x))

theorem read_x (x : Accepted hd seed i T k) (j : Fin d) :
    let r := index hd mul hp hf seed i F hF x
    x.1 (xBits hd j) = (w3_fpResidue (((w3_fpFB F).blocks i).get r).toMul).val.testBit j.val := by
  dsimp only; rw [residue_eq hd mul hp hf seed i F hF x]; exact residue_read hd x.1 j

theorem read_z (x : Accepted hd seed i T k) (j : Fin k) :
    let r := index hd mul hp hf seed i F hF x
    x.1 (zBits hd j) = (w3_fpHashWord seed i (w3_fpResidue (((w3_fpFB F).blocks i).get r).toMul).val).testBit j.val := by
  dsimp only; rw [residue_eq hd mul hp hf seed i F hF x,hash_bits hd x.2]
  have ha : (seed i).1.val+1 < p := by have := (seed i).1.isLt; omega
  exact congrArg (fun n : ℕ => n.testBit j.val) (hash_value hd mul hp hf ha (seed i).2.isLt x.2)

open S8C S8L.FpPair.Stage S8L.FpPair.Stage.Links w4_M5PortTensor

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
    simp only [rowTest,col,Equiv.symm_apply_apply,AddLayout.layout,AddLayout.bit_pos,Row,FpSlotRows.get]
    have pr (hi : i.val ≠ 0) : AddLayout.prev (finProdFinEquiv (j,i)) = finProdFinEquiv (j,AddLayout.prev i) := pred j i hi
    by_cases hj : j.val=7 <;> simp only [hj,if_true,if_false,decide_eq_true_eq] <;>
      by_cases hi : i.val=0 <;> simp (config := {decide := true}) only [hi,if_true,if_false,false_implies,not_false_eq_true,dif_pos,dif_neg] <;> first | rfl | (rw [pr hi]; rfl)
  constructor
  · exact fun h j i => (atcol j i).mp (h _)
  · intro h g; obtain ⟨⟨j,i⟩,rfl⟩ := finProdFinEquiv.surjective g; exact (atcol j i).mpr (h j i)

private def pack (v : Fin 8 → Fin 4 → Fin (d+1) → Bool) (n : Fin ((8*(d+1))*4)) :=
  let cl : Fin (8*(d+1)) × Fin 4 := finProdFinEquiv.symm n
  let ji : Fin 8 × Fin (d+1) := finProdFinEquiv.symm cl.1
  v ji.1 cl.2 ji.2

private theorem reg_eq {n : ℕ} (i : Fin n) (l : Fin 4) : AddLayout.reg i l = finProdFinEquiv (i,l) :=
  Fin.ext (by simp [AddLayout.reg,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm])

@[local simp] private theorem get_pack (v : Fin 8 → Fin 4 → Fin (d+1) → Bool) (j l i) :
    get (pack v) j l i = v j l i := by simp [FpSlotRows.get,pack,col,reg_eq]

private theorem ext_rows {w v : Rows d} (h : ∀ j l i, get w j l i = get v j l i) : w = v := by
  funext n; obtain ⟨⟨c,l⟩,rfl⟩ := finProdFinEquiv.surjective n
  obtain ⟨⟨j,i⟩,rfl⟩ := finProdFinEquiv.surjective c
  simpa only [FpSlotRows.get,col,reg_eq] using h j l i

abbrev Table := Fin 7 → Fin 3 → ℕ
def Specs (N : Table) (f : Bool) (w : Rows d) :=
  (∀ (j : Fin 7) (l : Fin 3), number w j.castSucc l.castSucc = N j l) ∧ get w 7 0 0 = f

theorem rowsLift (N : Table) (f : Bool) (B : ℕ)
    (bounds : ∀ j l, N j l < 2^(d+1))
    (eqs : ∀ j : Fin 7, N j 0 + N j 1 + (decide (j.val<5)).toNat = N j 2)
    (zeros : N 0 1 = 0 ∧ N 1 1 = 0) (tops : N 0 2 < 2^d ∧ N 1 2 < 2^d ∧ N 0 0 < 2^d ∧ N 5 0 < 2^d ∧ N 5 1 < 2^d)
    (outs : N 2 2 = p ∧ N 4 2 = p ∧ N 3 2 = B) (hpb : p < 2^(d+1)) (hB : B < 2^(d+1)) :
    ∃! w : Rows d, Accept _ (rowTest d p B) w ∧ Specs N f w := by
  have cu (j : Fin 7) := w3_addColumns_unique (bounds j 0) (bounds j 1) (bounds j 2) (eqs j)
  choose c hc uc using cu
  let v : Fin 8 → Fin 4 → Fin (d+1) → Bool := Fin.lastCases
    (fun l i => if l=0 ∨ l=3 then f else if l=1 then f && p.testBit i.val else false)
    (fun j => Fin.lastCases (c j) (fun l i => (N j l).testBit i.val))
  let w := pack v
  have rd (j : Fin 7) (l : Fin 3) (i : Fin (d+1)) : get w j.castSucc l.castSucc i = (N j l).testBit i.val := by simp [w,v]
  have ca (j : Fin 7) (i : Fin (d+1)) : get w j.castSucc 3 i = c j i := by
    change get (pack v) j.castSucc (Fin.last 3) i = _; simp only [get_pack,v,Fin.lastCases_castSucc,Fin.lastCases_last]
  have fr (l : Fin 4) (i : Fin (d+1)) : get w 7 l i = (if l=0 ∨ l=3 then f else if l=1 then f && p.testBit i.val else false) := by
    change get (pack v) (Fin.last 7) l i = _; simp only [get_pack,v,Fin.lastCases_castSucc,Fin.lastCases_last]
  have nums (j l) : number w (Fin.castSucc j) (Fin.castSucc l) = N j l :=
    congrArg Fin.val ((congrArg readWord (funext (rd j l))).trans (read_word (⟨N j l,bounds j l⟩ : Fin (2^(d+1)))))
  have ok : Accept _ (rowTest d p B) w := by
    apply (row_iff ..).mpr; intro j i; induction j using Fin.lastCases with
    | last => simp [Row,fr,show Fin.last 7 = (7:Fin 8) by rfl]
    | cast j =>
      have col := ((AddLayout.columns_iff (by omega : 0 < d+1) ..).mpr (hc j)) i
      have r (l : Fin 3) := rd j l i
      have r0 := r 0; have r1 := r 1; have r2 := r 2
      change get w j.castSucc 0 i = _ at r0; change get w j.castSucc 1 i = _ at r1; change get w j.castSucc 2 i = _ at r2
      simp only [Row,Fin.val_castSucc,if_neg (show j.val ≠ 7 by omega),r0,r1,r2,ca]
      refine ⟨col.1,fun hi => col.2 (by omega),?_,?_,?_,?_,?_⟩
      · intro hj; have hj' : j=0 ∨ j=1 := by omega
        rcases hj' with rfl|rfl <;> simp [zeros.1,zeros.2] <;> intro hi <;> rw [hi] <;> exact Nat.testBit_lt_two_pow (by first | exact tops.1 | exact tops.2.1)
      · rintro ⟨hj,hi⟩; have : j=0 := Fin.ext hj; subst j; rw [hi]; exact Nat.testBit_lt_two_pow tops.2.2.1
      · rintro (hj|hj) <;> first | (have : j=2 := Fin.ext hj; subst j; rw [outs.1]) | (have : j=4 := Fin.ext hj; subst j; rw [outs.2.1])
      · intro hj; have : j=3 := Fin.ext hj; subst j; rw [outs.2.2]
      · rintro ⟨hj,hi⟩; have : j=5 := Fin.ext hj; subst j; rw [hi]; exact ⟨Nat.testBit_lt_two_pow tops.2.2.2.1,Nat.testBit_lt_two_pow tops.2.2.2.2⟩
  refine ⟨w,⟨ok,nums,by simp [fr]⟩,?_⟩
  rintro y ⟨hy,hn,hyf⟩; apply ext_rows; intro j l i
  induction j using Fin.lastCases with
  | last =>
    have h := (FpSlotRows.sound hpb hB hy).2.2.2.2.2.2.2.2.2.2.2 i
    rw [hyf] at h; change get y 7 l i = get w 7 l i; rw [fr]; fin_cases l <;> simp_all
  | cast j => induction l using Fin.lastCases with
    | cast l => exact (read_bit (get y j.castSucc l.castSucc) i).symm.trans ((congrArg (fun n : ℕ => n.testBit i.val) (hn j l)).trans (rd j l i).symm)
    | last =>
      have bits (l : Fin 3) (t : Fin (d+1)) := (read_bit (get y j.castSucc l.castSucc) t).symm.trans (congrArg (fun n : ℕ => n.testBit t.val) (hn j l))
      have cols : AddLayout.Columns (decide (j.val<5)) (fun t : Fin (d+1) => (N j 0).testBit t.val) (fun t => (N j 1).testBit t.val) (fun t => (N j 2).testBit t.val) (get y j.castSucc 3) := by
        intro t; have hh := (if_neg (show j.castSucc.val ≠ 7 by change j.val ≠ 7; omega)).mp (((row_iff ..).mp hy) j.castSucc t)
        dsimp only; rw [←bits 0 t,←bits 1 t,←bits 2 t]; exact ⟨hh.1,fun hi => hh.2.1 (by omega)⟩
      exact (congrFun (uc j _ ((AddLayout.columns_iff (by omega : 0 < d+1) ..).mp cols)) i).trans (ca j i).symm

end DetDLP.M3A.FpSlotRowLift
noncomputable abbrev DetDLP_M3A_FpSlotRowLift := @DetDLP.M3A.FpSlotRowLift.rowsLift


