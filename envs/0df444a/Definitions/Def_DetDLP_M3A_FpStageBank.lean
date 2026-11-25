-- Prove2me | Definitions.Def_DetDLP_M3A_FpStageBank
-- name    : DetDLP_M3A_FpStageBank
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T20:33:14.546273+00:00
-- url     : https://prove2.me/theorems/8e98ab01-8e31-488f-befd-d8baa0b0783d
-- title:
--   Bounded multiplication stages and joined physical banks
-- statement:
--   Strict range witnesses are unique. Fixed-operand physical stages correspond to certified modular multiplication stages, and two pinned banks with the physical predecessor and final-output ties correspond bijectively to checked joined runs.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3A_FpArithNet
import Definitions.Def_DetDLP_W3_FpWire2

set_option autoImplicit false
namespace DetDLP.M3A.FpStageBank
open S8C S8J S8L.FpPair S8L.FpPair.Stage S8L.FpPair.Stage.Links FpArithNet
open HashGateLayout (addBits addBits_iff appendL appendR)
attribute [-simp] Fin.natAdd_eq_addNat
variable {d p m : ℕ} (hd : 1 ≤ d)

abbrev W := Vec (boundedStage hd).nb
abbrev core (w : W hd) : StageBits hd := w ∘ Fin.castAdd _
abbrev extra (w : W hd) : Vec ((d+1)*4) := w ∘ Fin.natAdd _
abbrev pinsAt (f : Fin d → Fin (boundedStage hd).nb) (w : W hd) (n : ℕ) := ∀ i, w (f i) = n.testBit i.val
abbrev inWord (w : W hd) (b : Bool) := readWord (fun i => w (operand hd b i))
abbrev outWord (w : W hd) := readWord (fun i => w (stageOut hd i))
abbrev Range (p z : ℕ) (v : Vec ((d+1)*4)) := Accept _ (AddLayout.test true) v ∧
  (∀ i : Fin (d+1), v (AddLayout.reg i 0) = z.testBit i.val) ∧ ∀ i : Fin (d+1), v (AddLayout.reg i 2) = p.testBit i.val

/-- The other input row is the slack p-z-1. The carry row is then unique. -/
theorem range_spec {z : ℕ} (hf : p < 2^d) (hz : z < 2^d) : w3_slotLift (z < p) (Range (d:=d) p z) := by
  have wide : 2^d ≤ 2^(d+1) := Nat.pow_le_pow_right (by decide) (by omega)
  let b (v : Vec ((d+1)*4)) := readWord (fun i : Fin (d+1) => v (AddLayout.reg i 1))
  let c (v : Vec ((d+1)*4)) := fun i : Fin (d+1) => v (AddLayout.reg i 3)
  have cols (v) (h : Range (d:=d) p z v) : w3_addColumns (d+1) z (b v).val p true (c v) := by
    apply (AddLayout.columns_iff (by omega) ..).mp
    simpa only [b,read_bit,← h.2.1,← h.2.2] using (AddLayout.test_iff true v).mp h.1
  have eqn (v) (h : Range (d:=d) p z v) : z+(b v).val+1 = p :=
    w3_addColumns_sound (hz.trans_le wide) (b v).isLt (hf.trans_le wide) (cols v h)
  refine ⟨fun v h => by have := eqn v h; omega,?_⟩
  intro hlt; let slack := p-z-1
  obtain ⟨t,ht,ut⟩ := w3_addColumns_unique (hz.trans_le wide) (by dsimp [slack]; omega : slack < 2^(d+1))
    (hf.trans_le wide) (cin:=true) (by change z+slack+1=p; dsimp [slack]; omega)
  refine ⟨addBits z slack p t,⟨(addBits_iff (by omega) ..).mpr ht,fun i => (addRegs z slack p t i).1,fun i => (addRegs z slack p t i).2.2.1⟩,?_⟩
  intro v hv; have hb : (b v).val = slack := by have := eqn v hv; dsimp [slack]; omega
  have hc := cols v hv; rw [hb] at hc; have he := ut _ hc
  funext j; let i : Fin (d+1) := ⟨j.val/4,by omega⟩
  have hr (l : Fin 4) (h : j.val%4=l.val) : j=AddLayout.reg i l := Fin.ext (by change j.val=4*(j.val/4)+l.val; omega)
  have hj := Nat.mod_lt j.val (by decide : 0<4); interval_cases e : j.val%4
  · rw [hr 0 rfl]; exact (hv.2.1 i).trans (addRegs z slack p t i).1.symm
  · rw [hr 1 rfl]; exact (read_bit _ i).symm.trans ((congrArg (fun n : ℕ => n.testBit i.val) hb).trans (addRegs z slack p t i).2.1.symm)
  · rw [hr 2 rfl]; exact (hv.2.2 i).trans (addRegs z slack p t i).2.2.1.symm
  · rw [hr 3 rfl]; exact (congrFun he i).trans (addRegs z slack p t i).2.2.2.symm

abbrev Phys (x y : ℕ) (w : W hd) := Accept _ (stageTest hd p) w ∧ pinsAt hd (operand hd false) w x ∧ pinsAt hd (operand hd true) w y
abbrev Split (p x y z : ℕ) (w : W hd) := (Accept _ (Stage.tests hd) (core hd w) ∧ buses hd p x y z (core hd w)) ∧ Range p z (extra hd w)

theorem split_iff {x y z : ℕ} (hz : z < 2^d) (w : W hd) :
    Phys (p:=p) hd x y w ∧ pinsAt hd (stageOut hd) w z ↔ Split hd p x y z w := by
  unfold Phys stageTest; erw [links_iff,join_iff,atPins_iff,atPins_iff]
  change (((((Accept _ (linkedTests hd) _ ∧ _) ∧ _) ∧ Accept (AddLayout.layout (d+1)) (atPins (atPins _ _ _) _ _) (extra hd w)) ∧ _) ∧ _ ∧ _) ∧ _ ↔ _
  erw [atPins_iff,atPins_iff]; unfold Split; rw [← linked_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨hl,hp⟩,hh⟩,⟨⟨ha,hm⟩,ht⟩⟩,tie⟩,hx,hy⟩,ho⟩
    refine ⟨⟨hl,hx,hy,hp,fun i => ?_⟩,ha,fun i => ?_,hm⟩
    · by_cases h : i.val < d
      · exact (tie ⟨i.val,h⟩).symm.trans (ho ⟨i.val,h⟩)
      · let j : Fin d := ⟨i.val-d,by omega⟩
        have e : i = ⟨d+j.val,by have := j.isLt; omega⟩ := Fin.ext (by dsimp [j];omega)
        exact e ▸ (hh j).trans (Nat.testBit_lt_two_pow (hz.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))).symm
    · cases i using Fin.lastCases with
      | last => exact (ht 0).trans (Nat.testBit_lt_two_pow hz).symm
      | cast j => exact ho j
  · rintro ⟨⟨hl,hx,hy,hp,ho⟩,ha,hz',hm⟩
    refine ⟨⟨⟨⟨⟨⟨hl,hp⟩,fun i => (ho _).trans (Nat.testBit_lt_two_pow (hz.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right d i.val))))⟩,
      ⟨⟨ha,hm⟩,fun _ => (hz' (Fin.last d)).trans (Nat.testBit_lt_two_pow hz)⟩⟩,fun i => (hz' i.castSucc).trans (ho ⟨i.val,by omega⟩).symm⟩,hx,hy⟩,fun i => hz' i.castSucc⟩

/-- A semantic stage already includes its remainder as the first projection. -/
noncomputable def stageEquiv (hf : p < 2^d) (x y : Fin p) : {w // Phys (p:=p) hd x.val y.val w} ≃
    {s : w3_mulStage d hd p // w3_modTwo hd p x.val y.val s.1.val s.2} := by
  have sp (w : {w // Phys (p:=p) hd x.val y.val w}) := (split_iff hd (outWord hd w.val).isLt w.val).mp ⟨w.prop,fun i => (read_bit (fun j => w.val (stageOut hd j)) i).symm⟩
  have wide : 2^d ≤ 2^(2*d) := Nat.pow_le_pow_right (by decide) (by omega)
  let z (w : {w // Phys (p:=p) hd x.val y.val w}) : Fin p := ⟨_,(range_spec hf (outWord hd w.val).isLt).1 _ (sp w).2⟩
  apply Equiv.ofBijective (fun w => ⟨(z w,certificate hd (core hd w.val)),Stage.decode hd ((outWord hd w.val).isLt.trans_le wide) _ (sp w).1.1 (sp w).1.2⟩)
  constructor
  · intro v w he; have e := congrArg Subtype.val he
    have h : (outWord hd v.val).val = (outWord hd w.val).val := congrArg (fun s : w3_mulStage d hd p => s.1.val) e
    have hv := sp v; rw [h] at hv
    have a := Stage.inject hd ((outWord hd w.val).isLt.trans_le wide) hv.1 (sp w).1 (congrArg Prod.snd e)
    have b := ((range_spec hf (outWord hd w.val).isLt).2 (z w).isLt).unique hv.2 (sp w).2
    apply Subtype.ext; funext i; induction i using Fin.addCases with
    | left i => exact congrFun a i
    | right i => exact congrFun b i
  · rintro ⟨⟨r,s⟩,hs⟩; have hr := r.isLt.trans hf
    obtain ⟨u,hu,he⟩ := Stage.lift hd (hr.trans_le wide) hs
    obtain ⟨v,hv,_⟩ := (range_spec hf hr).2 r.isLt
    have H := (split_iff hd hr (Fin.append u v)).mpr (by unfold Split core extra; erw [appendL,appendR]; exact ⟨hu,hv⟩)
    refine ⟨⟨_,H.1⟩,Subtype.ext (Prod.ext (Fin.ext ?_) ?_)⟩
    · change (outWord hd (Fin.append u v)).val = r.val
      exact congrArg (Fin.val (n:=2^d)) ((congrArg readWord (funext H.2)).trans (read_word (⟨_,hr⟩ : Fin (2^d))))
    · change certificate hd (Fin.append u v ∘ Fin.castAdd _) = s; rw [appendL,he]

theorem stage_read (hf : p < 2^d) (x y : Fin p) (w : {w // Phys (p:=p) hd x.val y.val w}) :
    ((stageEquiv hd hf x y w).val.1).val = (outWord hd w.val).val := rfl

private theorem stages_length {ys : List (Fin p)} {ss : List (w3_mulStage d hd p)} {x z : Fin p}
    (h : w3_checkStages hd x ys ss z) : ss.length = ys.length := by
  induction ys generalizing x ss with
  | nil => cases ss with | nil => rfl | cons => exact False.elim h
  | cons y ys ih => cases ss with
    | nil => exact False.elim h
    | cons a ss => exact congrArg Nat.succ (ih h.2)

def before {n : ℕ} {α : Type} (x : α) (v : Fin n → α) (i : Fin n) : α := Fin.cons (α:=fun _ => α) x v i.castSucc
def finish {n : ℕ} {α : Type} (x : α) (v : Fin n → α) : α := Fin.cons (α:=fun _ => α) x v (Fin.last n)
private theorem checks {n : ℕ} (x z : Fin p) (y : Fin n → Fin p) (s : Fin n → w3_mulStage d hd p) :
    w3_checkStages hd x (List.ofFn y) (List.ofFn s) z ↔
    (∀ i, w3_modTwo hd p (before x (fun j => (s j).1) i).val (y i).val (s i).1.val (s i).2) ∧ finish x (fun i => (s i).1) = z := by
  induction n generalizing x with
  | zero => simp [List.ofFn_zero,w3_checkStages,finish,eq_comm]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,w3_checkStages,ih,Fin.forall_fin_succ]
    simp only [before,finish,Fin.castSucc_zero,Fin.cons_zero,Fin.castSucc_succ,Fin.cons_succ,← Fin.succ_last]
    have eta : (Fin.cons (α:=fun _ => Fin p) (s 0).1 (fun j => (s j.succ).1)) = (fun j => (s j).1) := funext fun i => by cases i using Fin.cases <;> simp
    rw [eta]; tauto

abbrev Inputs {n : ℕ} (x : Fin p) (ys : Fin n → Fin p) (w : Fin n → W hd) := ∀ i,
  Phys (p:=p) hd (before x.val (fun j => (outWord hd (w j)).val) i) (ys i).val (w i)

theorem bounded (hf : p < 2^d) (w : W hd) (h : Accept _ (stageTest hd p) w) : (outWord hd w).val < p := by
  have a := (split_iff (x:=(inWord hd w false).val) (y:=(inWord hd w true).val) hd (outWord hd w).isLt w).mp
    ⟨⟨h,fun i => (read_bit (fun j => w (operand hd false j)) i).symm,fun i => (read_bit (fun j => w (operand hd true j)) i).symm⟩,
      fun i => (read_bit (fun j => w (stageOut hd j)) i).symm⟩
  exact (range_spec hf (outWord hd w).isLt).1 _ a.2

private theorem cons_map {n : ℕ} {α β : Type} (f : α → β) (x : α) (v : Fin n → α) (i : Fin (n+1)) :
    Fin.cons (α:=fun _ => β) (f x) (fun j => f (v j)) i = f (Fin.cons (α:=fun _ => α) x v i) := by cases i using Fin.cases <;> simp

noncomputable def oneBank (hf : p < 2^d) {n : ℕ} (x z : Fin p) (ys : Fin n → Fin p) :
    {w // Inputs hd x ys w ∧ finish x.val (fun j => (outWord hd (w j)).val) = z.val} ≃
    {ss // w3_checkStages hd x (List.ofFn ys) ss z} := by
  let residue (w : Fin n → W hd) (h : Inputs hd x ys w) (i : Fin n) : Fin p := ⟨_,bounded hd hf _ (h i).1⟩
  have prev (w) (h : Inputs hd x ys w) (i) : before x.val (fun j => (outWord hd (w j)).val) i = (before x (residue w h) i).val := cons_map Fin.val x (residue w h) i.castSucc
  let step (w) (h : Inputs hd x ys w) (i) := stageEquiv hd hf (before x (residue w h) i) (ys i) ⟨w i,prev w h i ▸ h i⟩
  let pack (w) (h : Inputs hd x ys w) (i) := (step w h i).val
  apply Equiv.ofBijective (fun w => ⟨List.ofFn (pack w.val w.prop.1),(checks hd ..).mpr ⟨fun i => (step w.val w.prop.1 i).prop,
    Fin.ext ((cons_map Fin.val x (residue w.val w.prop.1) _).symm.trans w.prop.2)⟩⟩)
  constructor
  · intro a b e; have eq := List.ofFn_injective (congrArg Subtype.val e)
    have er : residue a.val a.prop.1 = residue b.val b.prop.1 := funext fun i => congrArg Prod.fst (congrFun eq i)
    apply Subtype.ext; funext i
    have ea := congrFun eq i
    let E := stageEquiv hd hf (before x (residue b.val b.prop.1) i) (ys i)
    have ha : Phys (p:=p) hd (before x (residue b.val b.prop.1) i).val (ys i).val (a.val i) := by rw [← er,← prev a.val a.prop.1 i]; exact a.prop.1 i
    exact congrArg Subtype.val (E.injective (show E ⟨a.val i,ha⟩ = step b.val b.prop.1 i from Subtype.ext ea))
  · rintro ⟨ss,hs⟩; have len : ss.length=n := (stages_length hd hs).trans (List.length_ofFn ..)
    let s (i : Fin n) := ss.get (i.cast len.symm)
    have se : List.ofFn s = ss := by apply List.ext_getElem <;> simp [s,len]
    rw [← se] at hs; obtain ⟨ok,fin⟩ := (checks hd ..).mp hs
    let v (i) := (stageEquiv hd hf (before x (fun j => (s j).1) i) (ys i)).symm ⟨s i,ok i⟩
    have val (i) : (outWord hd (v i).val).val = (s i).1.val := congrArg (fun t => t.val.1.val) ((stageEquiv hd hf _ _).apply_symm_apply ⟨s i,ok i⟩)
    have hv : Inputs hd x ys (fun i => (v i).val) := by intro i; simp only [val,before,cons_map]; exact (v i).prop
    refine ⟨⟨_,hv,by simp only [val,finish,cons_map]; exact congrArg Fin.val fin⟩,Subtype.ext ((congrArg List.ofFn (funext fun i => ?_)).trans se)⟩
    exact congrArg Subtype.val ((stageEquiv hd hf _ _).apply_symm_apply ⟨s i,ok i⟩)

variable [NeZero p] (FB : IndexedFactorBase (Additive (ZMod p)ˣ) m)
def factor (X : FB.BlockTuple) (i : Fin (2*m)) := (w3_fpFactors FB X).get (i.cast (w3_fpFactors_length FB X).symm)
@[simp] theorem factors (X : FB.BlockTuple) : List.ofFn (factor FB X) = w3_fpFactors FB X := by
  apply List.ext_getElem <;> simp [factor,w3_fpFactors_length]

abbrev Banks := Bool → Fin (2*m) → W hd
def Joined (P : (ZMod p)ˣ) (X Y : FB.BlockTuple) (w : Banks (m:=m) hd) :=
  Inputs hd (w3_fpResidue P) (factor FB X) (w false) ∧ Inputs hd (w3_fpResidue 1) (factor FB Y) (w true) ∧
  finish (w3_fpResidue P).val (fun i => (outWord hd (w false i)).val) = finish (w3_fpResidue (p:=p) 1).val (fun i => (outWord hd (w true i)).val)

noncomputable def bankEquiv (hf : p < 2^d) (P : (ZMod p)ˣ) (X Y : FB.BlockTuple) :
    {w // Joined hd FB P X Y w} ≃ {r : w3_fpJoinedRun p d hd // w3_fpJoinedOK hd FB P X Y r} := by
  let A := w3_fpResidue P; let B := w3_fpResidue (p:=p) 1
  let endAt (a : Fin p) (v : Fin (2*m) → W hd) := finish a.val (fun i => (outWord hd (v i)).val)
  let E (a z : Fin p) (V : FB.BlockTuple) := (oneBank hd hf a z (factor FB V)).trans
    (Equiv.subtypeEquivRight (fun _ => by rw [factors]))
  let z (w : {w // Joined hd FB P X Y w}) : Fin p := ⟨endAt A (w.val false),by
    dsimp [endAt,finish]; cases e : Fin.last (2*m) using Fin.cases with
    | zero => simpa only [Fin.cons_zero] using A.isLt
    | succ i => exact bounded hd hf _ (w.prop.1 i).1⟩
  let L (w : {w // Joined hd FB P X Y w}) := E A (z w) X ⟨w.val false,w.prop.1,rfl⟩
  let R (w : {w // Joined hd FB P X Y w}) := E B (z w) Y ⟨w.val true,w.prop.2.1,w.prop.2.2.symm⟩
  apply Equiv.ofBijective (fun w => ⟨(z w,(L w).val,(R w).val),(L w).prop,(R w).prop⟩)
  constructor
  · intro v w e; have eq := congrArg Subtype.val e
    have ez : z v=z w := congrArg Prod.fst eq
    apply Subtype.ext; funext side; cases side
    · have hv := v.prop.1; have endv : endAt A (v.val false) = (z w).val := congrArg Fin.val ez
      apply congrArg Subtype.val ((E A (z w) X).injective (a₁:=⟨v.val false,hv,endv⟩) (a₂:=⟨w.val false,w.prop.1,rfl⟩) _)
      apply Subtype.ext; exact congrArg (fun r : w3_fpJoinedRun p d hd => r.2.1) eq
    · have endv := v.prop.2.2.symm.trans (congrArg Fin.val ez)
      apply congrArg Subtype.val ((E B (z w) Y).injective (a₁:=⟨v.val true,v.prop.2.1,endv⟩) (a₂:=⟨w.val true,w.prop.2.1,w.prop.2.2.symm⟩) _)
      apply Subtype.ext; exact congrArg (fun r : w3_fpJoinedRun p d hd => r.2.2) eq
  · rintro ⟨⟨r,s,t⟩,hs,ht⟩
    let l := (E A r X).symm ⟨s,hs⟩; let u := (E B r Y).symm ⟨t,ht⟩
    let w : {w // Joined hd FB P X Y w} := ⟨fun b => if b then u.val else l.val,l.prop.1,u.prop.1,l.prop.2.trans u.prop.2.symm⟩
    refine ⟨w,Subtype.ext (Prod.ext (Fin.ext l.prop.2) (Prod.ext ?_ ?_))⟩
    · exact congrArg Subtype.val ((E A r X).apply_symm_apply ⟨s,hs⟩)
    · exact congrArg Subtype.val ((E B r Y).apply_symm_apply ⟨t,ht⟩)

def lastStep (hm : 1 ≤ m) : Fin (2*m) := ⟨2*m-1,by clear * - hm; omega⟩
def prevStep (i : Fin (2*m)) : Fin (2*m) := ⟨i.val-1,by clear * - i; have := i.isLt; omega⟩
private theorem before_zero {α : Type} (x : α) (v : Fin (2*m) → α) (i) (hi : i.val=0) : before x v i=x := by
  have e : i.castSucc = 0 := Fin.ext hi; simp [before,e]
private theorem before_prev {α : Type} (x : α) (v : Fin (2*m) → α) (i) (hi : i.val≠0) : before x v i=v (prevStep i) := by
  have e : i.castSucc = (prevStep i).succ := Fin.ext (by change i.val=i.val-1+1; omega); simp [before,e]
private theorem finish_last {α : Type} (hm : 1 ≤ m) (x : α) (v : Fin (2*m) → α) : finish x v=v (lastStep hm) := by
  have e : Fin.last (2*m) = (lastStep hm).succ := Fin.ext (by change 2*m=2*m-1+1;omega); simp [finish,e]

noncomputable def firstTest (p start : ℕ) (i : Fin (2*m)) : w3_factorTest (boundedStage hd) :=
  if i.val=0 then atPins (stageTest hd p) (operand hd false) (fun j => start.testBit j.val) else stageTest hd p

def BankTies (hm : 1 ≤ m) (w : Banks (m:=m) hd) := ∀ b i j, if i.val=0 then
  w b (lastStep hm) (stageOut hd j) = w (!b) (lastStep hm) (stageOut hd j)
  else w b (prevStep i) (stageOut hd j) = w b i (operand hd false j)

theorem chainTie_iff {k : ℕ} (hm : 1 ≤ m) (a : Vec (base hd m k).nb) :
    (∀ u, a ((chainTie hd u).1) = a ((chainTie hd u).2)) ↔ BankTies hd hm (fun b i j => a (stagePort hd b i j)) := by
  have side (b) (i : Fin (2*m)) : whichSide (slotNumber (d:=d) b i)=b := by cases b <;> simp [whichSide,slotNumber,i.isLt.not_ge]
  have step (b) (i : Fin (2*m)) : whichStep (slotNumber (d:=d) b i)=i := by apply Fin.ext; cases b <;> simp [whichStep,slotNumber,Nat.mod_eq_of_lt i.isLt]
  constructor
  · intro h b i j; have H := h (finProdFinEquiv (slotNumber (d:=d) b i,j)); simp only [chainTie,Equiv.symm_apply_apply,step,side] at H
    split <;> rename_i hi <;> simpa only [hi,if_true,if_false,lastStep,prevStep] using H
  · intro h u; obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective u; simp only [chainTie,Equiv.symm_apply_apply]
    have H := h (whichSide s) (whichStep s) j; split <;> rename_i hi <;> simpa only [hi,if_true,if_false,lastStep,prevStep] using H

def BankOK (hm : 1 ≤ m) (P : (ZMod p)ˣ) (X Y : FB.BlockTuple) (w : Banks (m:=m) hd) :=
  (∀ b i, Accept _ (firstTest hd p (if b then 1 else (P : ZMod p).val) i) (w b i) ∧
    pinsAt hd (operand hd true) (w b i) (factor FB (if b then Y else X) i).val) ∧ BankTies hd hm w

private theorem inputs_iff (start : Fin p) (ys : Fin (2*m) → Fin p) (v : Fin (2*m) → W hd) : Inputs hd start ys v ↔
    (∀ i, Accept _ (firstTest hd p start.val i) (v i) ∧ pinsAt hd (operand hd true) (v i) (ys i).val) ∧
    ∀ i, i.val≠0 → ∀ j, v (prevStep i) (stageOut hd j) = v i (operand hd false j) := by
  have dispatch (i : Fin (2*m)) := before_prev (m:=m) start.val (fun j => (outWord hd (v j)).val) i
  constructor
  · intro h; constructor
    · intro i; specialize h i; by_cases hi : i.val=0 <;> simp [firstTest,hi]
      · exact ⟨(atPins_iff ..).mpr ⟨h.1,by simpa only [before_zero _ _ _ hi] using h.2.1⟩,h.2.2⟩
      · exact ⟨h.1,h.2.2⟩
    · intro i hi j; have H := (h i).2.1 j; rw [dispatch i hi] at H; exact (read_bit _ j).symm.trans H.symm
  · rintro ⟨h,t⟩ i; obtain ⟨ha,hy⟩ := h i; by_cases hi : i.val=0 <;> simp [firstTest,hi] at ha
    · obtain ⟨ha,hx⟩ := (atPins_iff ..).mp ha; exact ⟨ha,(before_zero _ _ _ hi).symm ▸ hx,hy⟩
    · exact ⟨ha,fun j => (t i hi j).symm.trans ((read_bit _ j).symm.trans (congrArg (fun n : ℕ => n.testBit j.val) (dispatch i hi).symm)),hy⟩

theorem bankOK_iff (hm : 1 ≤ m) (hp : 2 ≤ p) (P : (ZMod p)ˣ) (X Y : FB.BlockTuple) (w : Banks (m:=m) hd) :
    BankOK hd FB hm P X Y w ↔ Joined hd FB P X Y w := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  have one : (w3_fpResidue (p:=p) 1).val=1 := by simp [w3_fpResidue,ZMod.val_one]
  unfold Joined; rw [inputs_iff,inputs_iff,finish_last hm,finish_last hm,one]
  constructor
  · rintro ⟨ht,hl⟩
    have prev (b) (i : Fin (2*m)) (h : i.val≠0) (j : Fin d) := (if_neg h).mp (hl b i j)
    refine ⟨⟨ht false,prev false⟩,⟨ht true,prev true⟩,?_⟩
    let i : Fin (2*m) := ⟨0,by omega⟩
    exact congrArg (fun v : Vec d => (readWord v).val) (funext fun j => (if_pos (show i.val=0 from rfl)).mp (hl false i j))
  · rintro ⟨⟨a,b⟩,⟨c,e⟩,f⟩
    refine ⟨fun s => by cases s <;> first | exact a | exact c,?_⟩
    intro s i j; split <;> rename_i hi
    · have H := congrArg (fun n : ℕ => n.testBit j.val) f
      simp only [outWord,read_bit] at H
      cases s <;> first | exact H | exact H.symm
    · cases s <;> first | exact b i hi j | exact e i hi j

/-- Physical banks with the first operands pinned and every chain tie enforced. -/
noncomputable def physicalEquiv (hm : 1 ≤ m) (hp : 2 ≤ p) (hf : p < 2^d) (P : (ZMod p)ˣ) (X Y : FB.BlockTuple) :
    {w // BankOK hd FB hm P X Y w} ≃ {r : w3_fpJoinedRun p d hd // w3_fpJoinedOK hd FB P X Y r} :=
  (Equiv.subtypeEquivRight (bankOK_iff hd FB hm hp P X Y)).trans (bankEquiv hd FB hf P X Y)

attribute [simp] Fin.natAdd_eq_addNat
end DetDLP.M3A.FpStageBank
noncomputable abbrev DetDLP_M3A_FpStageBank := @DetDLP.M3A.FpStageBank.physicalEquiv


