-- Prove2me | Definitions.Def_DetDLP_M3A_FpChainBijection
-- name    : DetDLP_M3A_FpChainBijection
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T20:49:47.147383+00:00
-- url     : https://prove2.me/theorems/92559245-59f1-43d8-8ba3-aed93459d0c2
-- title:
--   Native finite-field chain decoding and address readout
-- statement:
--   Physical assignments of the native layout decode bijectively to tuple pairs satisfying the group equation and the requested bit prefix. Each lookup bus reads the corresponding affine hash word.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3A_FpStageBank
import Definitions.Def_DetDLP_M3A_FpSlotBijection

set_option autoImplicit false
namespace DetDLP.M3A.FpChainBijection
open S8J S8C S8G.FpMoment S8L.FpPair.Stage FpSlotTile FpArithNet FpStageBank
attribute [-simp] Fin.natAdd_eq_addNat
variable {d p m k T : ℕ} (hd : 1 ≤ d)

private theorem tile_iff {n : ℕ} {A : w3_FactorLayout} (t : Fin n → w3_factorTest A) (x : Vec (tiles n A).nb) :
    Accept _ (tileTests t) x ↔ ∀ i, Accept A (t i) (atTile x i) := tileTests_iff t x

/-- Split the physical chain test into slot gates, stage gates, factor links and bank links. -/
theorem chains_iff (hm : 1 ≤ m) (start : ℕ) (seed : FpSeed p m) (a : Vec (base hd m k).nb) :
    Accept _ (chainTest hd p T start seed) a ↔
    (∀ s, Accept _ (slotTest hd p T (seed (blockIndex s)).1.val (seed (blockIndex s)).2.val) (fun j => a (slotPort hd s j))) ∧
    (∀ b i, Accept _ (firstTest hd p (if b then 1 else start) i) (fun j => a (stagePort hd b i j))) ∧
    (∀ u, a ((factorTie hd u).1) = a ((factorTie hd u).2)) ∧ BankTies hd hm (fun b i j => a (stagePort hd b i j)) := by
  rw [← chainTie_iff]; unfold chainTest; erw [links_iff,join_iff,join_iff,tile_iff,tile_iff,tile_iff]
  constructor
  · rintro ⟨⟨hs,hf,ht⟩,tiesOk⟩; refine ⟨hs,fun b => ?_,fun u => ?_,fun u => ?_⟩
    · cases b <;> first | exact hf | exact ht
    · simpa only [ties,Fin.addCases_left] using tiesOk (Fin.castAdd _ u)
    · simpa only [ties,Fin.addCases_right] using tiesOk (Fin.natAdd _ u)
  · rintro ⟨hs,hb,hf,ht⟩; refine ⟨⟨hs,hb false,hb true⟩,fun u => ?_⟩
    induction u using Fin.addCases with
    | left i => simpa only [ties,Fin.addCases_left] using hf i
    | right i => simpa only [ties,Fin.addCases_right] using ht i

abbrev N (m d : ℕ) (pre : List Bool) := min pre.length (4*m*d)
abbrev Prefix (pre : List Bool) (a : Vec (chains hd m k).nb) := pre.length ≤ 4*m*d ∧
  ∀ i : Fin (N m d pre), a (prefixPort hd (Fin.castLE (min_le_right ..) i)) = pre[i.val]?.getD false

set_option backward.isDefEq.respectTransparency false in
theorem accept_iff (start : ℕ) (seed : FpSeed p m) (pre : List Bool) (a : Vec (layout hd m k pre).nb) :
    Accept _ (test hd p T start seed pre) a ↔ Accept _ (chainTest hd p T start seed) (a ∘ Fin.castAdd _) ∧
    Prefix hd pre (a ∘ Fin.castAdd _) ∧ (∀ i : Fin (N m d pre), a (rhs hd pre i) = pre[i.val]?.getD false) ∧
    a (Fin.natAdd (chains hd m k).nb (Fin.last (N m d pre))) = false := by
  unfold test; erw [M3B.ECLayout.accept_iff]; unfold arithTest; erw [links_iff,join_iff]
  let n := N m d pre
  change ((Accept _ _ _ ∧ (∀ i : Fin (n+1), (if i.val<n then decide (a (Fin.natAdd _ i) = pre[i.val]?.getD false)
    else decide (pre.length ≤ 4*m*d ∧ a (Fin.natAdd _ i) = false)) = true)) ∧ _) ↔ _
  constructor
  · rintro ⟨⟨hc,hr⟩,ht⟩; have last := hr (Fin.last n); simp only [Fin.val_last,lt_self_iff_false,if_false,decide_eq_true_eq] at last
    have h (i : Fin n) : a (rhs hd pre i) = pre[i.val]?.getD false := by simpa only [rhs,Fin.val_castSucc,i.isLt,if_true,decide_eq_true_eq] using hr i.castSucc
    exact ⟨hc,⟨last.1,fun i => (ht i).trans (h i)⟩,h,last.2⟩
  · rintro ⟨hc,⟨hlen,hp⟩,hr,hl⟩; refine ⟨⟨hc,fun i => ?_⟩,fun i => (hp i).trans (hr i).symm⟩
    cases i using Fin.lastCases with
    | last => simpa only [Fin.val_last,lt_self_iff_false,if_false,decide_eq_true_eq] using And.intro hlen hl
    | cast i => simpa only [rhs,Fin.val_castSucc,i.isLt,if_true,decide_eq_true_eq] using hr i

set_option backward.isDefEq.respectTransparency false in
noncomputable def prefixEquiv (start : ℕ) (seed : FpSeed p m) (pre : List Bool) :
    {a : Vec (layout hd m k pre).nb // Accept _ (test hd p T start seed pre) a} ≃
    {a : Vec (chains hd m k).nb // Accept _ (chainTest hd p T start seed) a ∧ Prefix hd pre a} := by
  let n := N m d pre
  let rows : Vec (n+1) := Fin.lastCases false (fun i => pre[i.val]?.getD false)
  have extRows {a : Vec (layout hd m k pre).nb} (ha : Accept _ (test hd p T start seed pre) a) : a ∘ Fin.natAdd _ = rows := by
    have h := (accept_iff hd start seed pre a).mp ha; change (fun i : Fin (n+1) => a (Fin.natAdd (chains hd m k).nb i)) = rows
    funext i; cases i using Fin.lastCases with
    | last => simpa only [rows,Fin.lastCases_last] using h.2.2.2
    | cast i => simpa only [rhs,rows,Fin.lastCases_castSucc] using h.2.2.1 i
  apply Equiv.ofBijective (fun a => ⟨a.val ∘ Fin.castAdd _,((accept_iff hd start seed pre a.val).mp a.prop).1,
    ((accept_iff hd start seed pre a.val).mp a.prop).2.1⟩)
  constructor
  · intro a b eq; apply Subtype.ext; funext i; induction i using Fin.addCases with
    | left j => exact congrFun (congrArg Subtype.val eq) j
    | right j => exact congrFun ((extRows a.prop).trans (extRows b.prop).symm) j
  · rintro ⟨a,ha,hp⟩; let w := Fin.append a rows
    have hw : w ∘ Fin.castAdd _ = a := HashGateLayout.appendL ..
    have hr : w ∘ Fin.natAdd _ = rows := HashGateLayout.appendR ..
    refine ⟨⟨w,(accept_iff hd start seed pre w).mpr ⟨hw.symm ▸ ha,hw.symm ▸ hp,fun i => ?_,?_⟩⟩,Subtype.ext hw⟩
    · exact (congrFun hr i.castSucc).trans (Fin.lastCases_castSucc ..)
    · exact (congrFun hr (Fin.last n)).trans (Fin.lastCases_last ..)

set_option backward.isDefEq.respectTransparency false

def step (i : Fin m) (j : Fin 2) : Fin (2*m) := ⟨j.val*m+i.val,by clear * - i j; fin_cases j <;> simp <;> omega⟩
def row (b : Bool) (i : Fin m) (j : Fin 2) := slotNumber (d:=0) b (step i j)
@[simp] theorem row_block (b : Bool) (i : Fin m) (j : Fin 2) : blockIndex (row b i j)=i := by
  apply Fin.ext; cases b <;> fin_cases j <;> simp [blockIndex,row,slotNumber,step,Nat.add_mod,Nat.mod_eq_of_lt i.isLt]
@[simp] theorem row_side (b : Bool) (i : Fin m) (j : Fin 2) : whichSide (row b i j)=b := by
  cases b <;> simp [row,slotNumber,whichSide,(step i j).isLt.not_ge]
@[simp] theorem row_step (b : Bool) (i : Fin m) (j : Fin 2) : whichStep (row b i j)=step i j := by
  apply Fin.ext; cases b <;> simp [row,slotNumber,whichStep,Nat.mod_eq_of_lt (step i j).isLt]
def coord (s : Fin (4*m)) : Fin 2 := if (whichStep s).val < m then 0 else 1
@[simp] theorem row_coord (b : Bool) (i : Fin m) (j : Fin 2) : coord (row b i j)=j := by
  fin_cases j <;> simp [coord,step,i.isLt]
theorem step_surj (n : Fin (2*m)) : ∃ i j, step i j=n := by
  by_cases h : n.val < m
  · exact ⟨⟨_,h⟩,0,Fin.ext (by simp [step])⟩
  · exact ⟨⟨n.val-m,by omega⟩,1,Fin.ext (by simp [step];omega)⟩
theorem row_surj (s : Fin (4*m)) : ∃ b i j, row b i j=s := by
  by_cases h : s.val < 2*m
  · obtain ⟨i,j,e⟩ := step_surj (⟨s.val,h⟩ : Fin (2*m)); exact ⟨false,i,j,Fin.ext (by simp [row,slotNumber,e])⟩
  · obtain ⟨i,j,e⟩ := step_surj (⟨s.val-2*m,by omega⟩ : Fin (2*m)); exact ⟨true,i,j,Fin.ext (by simp [row,slotNumber,e];omega)⟩

variable [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ)
abbrev Pair := (w3_fpFB F).BlockTuple × (w3_fpFB F).BlockTuple
def pick (t : Pair F) (b : Bool) := if b then t.2 else t.1
noncomputable abbrev value (t : Pair F) (b : Bool) (i : Fin m) (j : Fin 2) := w3_fpResidue (((w3_fpFB F).blocks i).get (pick F t b i j)).toMul
@[simp] theorem factor_step (t : Pair F) (b : Bool) (i : Fin m) (j : Fin 2) :
    factor (w3_fpFB F) (pick F t b) (step i j) = value F t b i j := by
  fin_cases j <;> simp [factor,step,w3_fpFactors,List.get_eq_getElem,value,i.isLt]

variable (mul : w3_modMulInterface) (hp : 2 ≤ p) (hf : p < 2^d) (seed : FpSeed p m)
variable (hF : ∀ i, (F i).Nodup ∧ (F i).toFinset = fpFactorBlock T seed i)
abbrev Slot (i : Fin m) := FpSlotBijection.Accepted hd seed i T k
noncomputable def slotsEquiv : ((s : Fin (4*m)) → Slot (k:=k) (T:=T) hd seed (blockIndex s)) ≃ Pair F := by
  let E (i : Fin m) := FpSlotBijection.slotEquiv (k:=k) hd mul hp hf seed i F (hF i)
  apply (Equiv.piCongrRight fun s => E (blockIndex s)).trans
  refine {toFun := fun a => (fun i j => Fin.cast (by rw [row_block]) (a (row false i j)),fun i j => Fin.cast (by rw [row_block]) (a (row true i j))),
          invFun := fun t s => pick F t (whichSide s) (blockIndex s) (coord s), left_inv := ?_,right_inv := ?_}
  · intro a; funext s; obtain ⟨b,i,j,rfl⟩ := row_surj s; apply Fin.ext; cases b <;> simp [pick] <;> apply congrArg (fun s => (a s).val) <;> simp
  · intro t; apply Prod.ext <;> funext i j <;> apply Fin.ext <;> simp [pick] <;> first | exact congrArg (fun i => (t.1 i j).val) (row_block ..) | exact congrArg (fun i => (t.2 i j).val) (row_block ..)

local notation "E" => slotsEquiv (k:=k) hd F mul hp hf seed hF
abbrev Slots := (s : Fin (4*m)) → Slot (k:=k) (T:=T) hd seed (blockIndex s)
private theorem cast_read {i l : Fin m} (h : l=i) (r : Fin ((w3_fpFB F).blocks l).length) :
    w3_fpResidue (((w3_fpFB F).blocks l).get r).toMul = w3_fpResidue (((w3_fpFB F).blocks i).get (r.cast (by rw [h]))).toMul := by subst i; rfl
private theorem slot_x (v : Slots (k:=k) (T:=T) hd seed) (b i j u) :
    (v (row b i j)).val (xBits hd u) = (value F (E v) b i j).val.testBit u.val := by
  apply (FpSlotBijection.read_x hd mul hp hf seed _ F (hF _) _ _).trans
  cases b <;> exact congrArg (fun z : Fin p => z.val.testBit u.val) (cast_read F (row_block _ i j) _)
private theorem slot_z (v : Slots (k:=k) (T:=T) hd seed) (b i j u) :
    (v (row b i j)).val (zBits hd u) = (w3_fpHashWord seed i (value F (E v) b i j).val).testBit u.val := by
  apply (FpSlotBijection.read_z hd mul hp hf seed _ F (hF _) _ _).trans
  have R (s : Bool) := cast_read F (row_block s i j) (FpSlotBijection.index hd mul hp hf seed _ F (hF _) (v (row s i j)))
  cases b <;> first | exact congrArg₂ (fun i (z : Fin p) => (w3_fpHashWord seed i z.val).testBit u.val) (row_block _ i j) (R false) | exact congrArg₂ (fun i (z : Fin p) => (w3_fpHashWord seed i z.val).testBit u.val) (row_block _ i j) (R true)

abbrev Sw := Fin (4*m) → Vec (slotLayout d k hd).nb
abbrev Parts := Sw (m:=m) (k:=k) hd × Banks (m:=m) hd
private def splitW : Vec (base hd m k).nb ≃ Parts (m:=m) (k:=k) hd where
  toFun a := (fun s j => a (slotPort hd s j),fun b i j => a (stagePort hd b i j))
  invFun v := Fin.append (fun i => v.1 (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
    (Fin.append (fun i => v.2 false (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) (fun i => v.2 true (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2))
  left_inv a := by
    funext u; induction u using Fin.addCases with
    | left i => obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective i; simp only [Fin.append_left,Equiv.symm_apply_apply,slotPort]
    | right i => induction i using Fin.addCases with
      | left i => obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective i; simp only [Fin.append_left,Fin.append_right,Equiv.symm_apply_apply,stagePort,Bool.false_eq_true,if_false]
      | right i => obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective i; simp only [Fin.append_right,Equiv.symm_apply_apply,stagePort,if_true]
  right_inv v := by
    apply Prod.ext
    · funext s i; simp only [slotPort,Fin.append_left,Equiv.symm_apply_apply]
    · funext b s i; cases b <;> simp only [stagePort,Fin.append_left,Fin.append_right,Equiv.symm_apply_apply,Bool.false_eq_true,if_false,if_true]

private theorem tied_iff (v : Slots (k:=k) (T:=T) hd seed) (w : Banks (m:=m) hd) :
    (∀ s j, (v s).val (xBits hd j) = w (whichSide s) (whichStep s) (operand hd true j)) ↔
    ∀ b n, pinsAt hd (operand hd true) (w b n) (factor (w3_fpFB F) (pick F (E v) b) n).val := by
  constructor
  · intro h b n; obtain ⟨i,j,rfl⟩ := step_surj n; intro u; have H := h (row b i j) u
    simpa only [row_side,row_step,factor_step,slot_x hd F mul hp hf seed hF] using H.symm
  · intro h s u; obtain ⟨b,i,j,rfl⟩ := row_surj s; simpa only [row_side,row_step,factor_step,slot_x hd F mul hp hf seed hF] using (h b (step i j) u).symm

noncomputable abbrev word (t : Pair F) := w3_tupleWord (w3_fpFB F) (fun A => w3_bits d ((A.toMul : (ZMod p)ˣ) : ZMod p).val) t.1 t.2
private theorem prefix_list (a : Vec (chains hd m k).nb) (t : Pair F)
    (h : ∀ b i j u, a (slotPort hd (row b i j) (xBits hd u)) = (value F t b i j).val.testBit u.val) :
    List.ofFn (fun u => a (prefixPort hd u)) = word (d:=d) F t := by
  let f (s : Fin 2) (i : Fin m) (j : Fin 2) (u : Fin d) := (value F t (decide (s.val=1)) i j).val.testBit u.val
  let g (s : Fin 2) (i : Fin m) (j : Fin 2) : Fin (4*m) := ⟨s.val*(2*m)+i.val*2+j.val,by fin_cases s <;> simp <;> omega⟩
  have port (s i j u) : a (prefixPort hd (finProdFinEquiv (g s i j,u))) = f s i j u := by
    apply Eq.trans _ (h (decide (s.val=1)) i j u)
    unfold prefixPort; simp only [Equiv.symm_apply_apply]; congr 2
    have e : s.val*(2*m)+i.val*2+j.val = (s.val*m+i.val)*2+j.val := by ring
    have hi : i.val*2+j.val < 2*m := by omega
    have hm : 0 < m := by omega
    have bound := (row (decide (s.val=1)) i j).isLt
    have hs : (s.val*(2*m)+i.val*2+j.val)/(2*m) = s.val := by rw [Nat.add_assoc,Nat.mul_comm s.val,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hi,Nat.add_zero]
    apply Fin.ext; dsimp only [g]; rw [hs]
    rw [e,Nat.mul_comm (s.val*m+i.val) 2,Nat.mul_add_div (by decide : 0<2),Nat.div_eq_of_lt j.isLt,Nat.add_zero,Nat.mul_comm s.val m,Nat.mul_add_mod,Nat.mul_add_mod,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt]
    fin_cases s <;> simp [row,slotNumber,step,Nat.add_assoc] at bound ⊢ <;> apply Nat.mod_eq_of_lt <;> omega
  have G : List.ofFn (fun s : Fin (4*m) => List.ofFn (fun u : Fin d => a (prefixPort hd (finProdFinEquiv (s,u))))) =
      ((List.ofFn fun s : Fin 2 => (List.ofFn fun i : Fin m => List.ofFn fun j : Fin 2 => List.ofFn (f s i j)).flatten)).flatten := by
    let v (n : Fin ((2*m)*2)) := List.ofFn fun u : Fin d => a (prefixPort hd (finProdFinEquiv ((n.cast (by omega) : Fin (4*m)),u)))
    have vv : (List.ofFn v) = List.ofFn (fun s : Fin (4*m) => List.ofFn (fun u : Fin d => a (prefixPort hd (finProdFinEquiv (s,u))))) := by apply List.ext_getElem <;> simp [v] <;> omega
    rw [← vv,List.ofFn_mul,List.ofFn_mul]; simp only [List.flatten_flatten]; congr 1
    rw [List.map_ofFn]; apply congrArg List.ofFn; funext s; apply congrArg List.flatten; apply congrArg List.ofFn; funext i; apply congrArg List.ofFn; funext j; apply congrArg List.ofFn; funext u
    convert port s i j u using 1; congr 4; apply Fin.ext; dsimp [g]; ring
  have two (i : Fin (4*m)) (j : Fin d) : (⟨i.val*d+j.val,by nlinarith [i.isLt,j.isLt,Nat.mul_le_mul_right d i.isLt]⟩ : Fin (4*m*d)) = finProdFinEquiv (i,j) := Fin.ext (by simp only [finProdFinEquiv_apply_val];ring)
  rw [List.ofFn_mul]; simp only [two]; change (List.ofFn (fun s : Fin (4*m) => List.ofFn (fun u : Fin d => a (prefixPort hd (finProdFinEquiv (s,u)))))).flatten = _
  rw [G]; simp only [List.ofFn_succ,List.ofFn_zero,List.flatten_cons,List.flatten_nil,List.append_nil] at * <;> simp [word,w3_tupleWord,w3_bits,List.flatMap_def,← List.ofFn_eq_map,f,value,pick,w3_fpResidue,List.flatten_flatten,List.map_ofFn,Function.comp_def]

private theorem prefix_iff (a : Vec (chains hd m k).nb) (pre : List Bool) :
    Prefix hd pre a ↔ pre <+: List.ofFn (fun u => a (prefixPort hd u)) := by
  rw [List.prefix_iff_getElem]; constructor
  · rintro ⟨hl,h⟩; refine ⟨by simpa using hl,fun i hi => ?_⟩
    simpa only [Fin.castLE,List.getElem_ofFn,List.getElem?_eq_getElem hi,Option.getD_some] using (h ⟨i,lt_min hi (hi.trans_le hl)⟩).symm
  · rintro ⟨hl,h⟩; simp only [List.length_ofFn] at hl; refine ⟨hl,fun i => ?_⟩
    have hi : i.val < pre.length := i.isLt.trans_le (min_le_left ..)
    simpa only [Fin.castLE,List.getElem_ofFn,List.getElem?_eq_getElem hi,Option.getD_some] using (h i.val hi).symm

variable (P : (ZMod p)ˣ) (pre : List Bool) (hm : 1 ≤ m)
private abbrev Good (t : Pair F) (w : Banks (m:=m) hd) := BankOK hd (w3_fpFB F) hm P t.1 t.2 w ∧ pre <+: word (d:=d) F t
private abbrev Acc := {a : Vec (chains hd m k).nb // Accept _ (chainTest hd p T (P : ZMod p).val seed) a ∧ Prefix hd pre a}
private def entries (a : Acc (k:=k) (T:=T) hd seed P pre) : Slots (k:=k) (T:=T) hd seed := fun s =>
  ⟨_,((chains_iff hd hm _ seed _).mp a.prop.1).1 s⟩
private theorem good_iff (a : Vec (chains hd m k).nb) (v : Slots (k:=k) (T:=T) hd seed)
    (hs : ∀ s, (v s).val = (splitW hd a).1 s) :
    Accept _ (chainTest hd p T (P : ZMod p).val seed) a ∧ Prefix hd pre a ↔ Good hd F P pre hm (E v) ((splitW hd a).2) := by
  have hx (b i j u) := (congrFun (hs (row b i j)) (xBits hd u)).symm.trans (slot_x hd F mul hp hf seed hF v b i j u)
  rw [chains_iff hd hm,prefix_iff,prefix_list hd F a (E v) hx]
  have ft : (∀ u, a ((factorTie hd u).1) = a ((factorTie hd u).2)) ↔
      ∀ b n, pinsAt hd (operand hd true) ((splitW hd a).2 b n) (factor (w3_fpFB F) (pick F (E v) b) n).val := by
    rw [← tied_iff hd F mul hp hf seed hF]; constructor
    · intro h s j; rw [hs]; simpa only [splitW,Equiv.coe_fn_mk,factorTie,Equiv.symm_apply_apply] using h (finProdFinEquiv (s,j))
    · intro h u; obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective u; simpa only [hs,splitW,Equiv.coe_fn_mk,factorTie,Equiv.symm_apply_apply] using h s j
  rw [ft]; constructor
  · rintro ⟨⟨_,h,b,c⟩,l⟩; exact ⟨⟨fun s i => ⟨h s i,b s i⟩,c⟩,l⟩
  · rintro ⟨⟨a',b⟩,c⟩; exact ⟨⟨fun s => by change Accept _ _ ((splitW hd a).1 s); rw [← hs]; exact (v s).prop,fun s i => (a' s i).1,fun s i => (a' s i).2,b⟩,c⟩

private noncomputable def unpack : Acc (k:=k) (T:=T) hd seed P pre ≃ {v : Slots (k:=k) (T:=T) hd seed × Banks (m:=m) hd // Good hd F P pre hm (E v.1) v.2} := by
  let V (a : Acc (k:=k) (T:=T) hd seed P pre) := entries hd seed P pre hm a
  apply Equiv.ofBijective (fun a => ⟨(V a,(splitW hd a.val).2),(good_iff hd F mul hp hf seed hF P pre hm _ _ (fun _ => rfl)).mp a.prop⟩)
  constructor
  · intro a b eq; have e := congrArg Subtype.val eq; apply Subtype.ext; apply (splitW hd).injective; refine Prod.ext ?_ (show (splitW hd a.val).2 = (splitW hd b.val).2 from congrArg (fun z : Slots (k:=k) (T:=T) hd seed × Banks (m:=m) hd => z.2) e)
    exact funext fun s => congrArg Subtype.val (congrFun (congrArg Prod.fst e) s)
  · rintro ⟨⟨v,w⟩,hv⟩; let a := (splitW (k:=k) hd).symm (fun s => (v s).val,w)
    have e := (splitW hd).apply_symm_apply (fun s => (v s).val,w)
    have hs (s) := (congrFun (congrArg Prod.fst e) s).symm
    have ha := (good_iff hd F mul hp hf seed hF P pre hm a v hs).mpr (by rw [show (splitW hd a).2=w from congrArg Prod.snd e];exact hv)
    exact ⟨⟨a,ha⟩,Subtype.ext (Prod.ext (funext fun s => Subtype.ext (hs s).symm) (show (splitW hd a).2 = w from congrArg Prod.snd e))⟩

noncomputable def netEquiv : {a // Accept (layout hd m k pre) (test hd p T (P : ZMod p).val seed pre) a} ≃
    {t : Pair F // (w3_fpFB F).tupleVal t.2 = (w3_fpFB F).tupleVal t.1 + Additive.ofMul P ∧ pre <+: word (d:=d) F t} := by
  apply (prefixEquiv hd _ seed pre).trans; apply (unpack hd F mul hp hf seed hF P pre hm).trans
  apply ((Equiv.prodCongr E (Equiv.refl _)).subtypeEquiv (q:=fun z => Good hd F P pre hm z.1 z.2) (fun _ => Iff.rfl)).trans
  apply Equiv.trans _ (w3_fpJoinedEquiv hd hp hf mul (w3_fpFB F) P (fun t => pre <+: word (d:=d) F t))
  let B (t : Pair F) := physicalEquiv hd (w3_fpFB F) hm hp hf P t.1 t.2
  refine {toFun := fun w => ⟨(w.val.1,(B w.val.1 ⟨w.val.2,w.prop.1⟩).val),w.prop.2,(B w.val.1 ⟨w.val.2,w.prop.1⟩).prop⟩,
          invFun := fun r => ⟨(r.val.1,((B r.val.1).symm ⟨r.val.2,r.prop.2⟩).val),((B r.val.1).symm ⟨r.val.2,r.prop.2⟩).prop,r.prop.1⟩,
          left_inv := fun w => Subtype.ext (Prod.ext rfl (congrArg Subtype.val ((B w.val.1).symm_apply_apply _))),
          right_inv := fun r => Subtype.ext (Prod.ext rfl (congrArg Subtype.val ((B r.val.1).apply_symm_apply _)))}

theorem bus_address (hT : T ≤ 2^k) (a : {a // Accept (layout hd m k pre) (test hd p T (P : ZMod p).val seed pre) a}) (b i j) :
    bitsToNat (fun u => a.val (bus hd pre (row b i j) u)) = w3_fpHashWord seed i (value F ((netEquiv hd F mul hp hf seed hF P pre hm) a).val b i j).val := by
  let v := entries hd seed P pre hm ((prefixEquiv (T:=T) hd _ seed pre) a)
  have bits := slot_z hd F mul hp hf seed hF v b i j
  let t := E v
  have hb := ((w3_fpBlockResidueEquiv seed F i T (hF i)) (pick F t b i j)).prop.2
  have hn : w3_fpHashWord seed i (value F t b i j).val < 2^k := hb.trans_le hT
  exact congrArg (Fin.val (n:=2^k)) ((congrArg readWord (funext bits)).trans (read_word ⟨_,hn⟩))

attribute [simp] Fin.natAdd_eq_addNat
end DetDLP.M3A.FpChainBijection
noncomputable abbrev DetDLP_M3A_FpChainBijection := @DetDLP.M3A.FpChainBijection.netEquiv


