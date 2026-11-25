-- Prove2me | Definitions.Def_DetDLP_W5_M6Harvest
-- name    : DetDLP_W5_M6Harvest
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:49:00.524841+00:00
-- url     : https://prove2.me/theorems/b0e6c4c5-5475-40a0-a717-27f94fa7376a
-- title:
--   M6 Harvest
-- statement:
--   Framed instruction-table calls preserve prefix-space bounds. An output extraction routine reads the true-tag prefix and a sweep erases every owned scratch stack, leaving one clean result word. Adapted from the verified reusable primitive tensor entry call.

import Definitions.Def_DetDLP_W5_M6HeadBit

import Definitions.Def_DetDLP_W5_M6StackOps
set_option linter.all false
namespace DetDLP.w5_M6FramePorts
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking StructuredCalls
theorem embedCfg_eq_of_ports {r s l R S L : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L))
    (frame target : Cfg R S L) (source : Cfg r s l)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (hpc : relocatePc label returnPc source.pc = target.pc)
    (hreg : ∀ i, target.regs (register i) = source.regs i)
    (hregFrame : ∀ i, (¬ ∃ j, register j = i) → target.regs i = frame.regs i)
    (hstack : ∀ i, target.stacks (stack i) = source.stacks i)
    (hstackFrame : ∀ i, (¬ ∃ j, stack j = i) → target.stacks i = frame.stacks i) :
    embedCfg register stack label returnPc frame source = target := by
  have hregs : (embedCfg register stack label returnPc frame source).regs = target.regs := by
    funext i
    classical
    by_cases hi : ∃ j, register j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_register register stack label returnPc frame source hr j).trans
        (hreg j).symm
    · exact (embedCfg_register_frame register stack label returnPc frame source i hi).trans
        (hregFrame i hi).symm
  have hstacks : (embedCfg register stack label returnPc frame source).stacks = target.stacks := by
    funext i
    classical
    by_cases hi : ∃ j, stack j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_stack register stack label returnPc frame source hs j).trans
        (hstack j).symm
    · exact (embedCfg_stack_frame register stack label returnPc frame source i hi).trans
        (hstackFrame i hi).symm
  cases target
  cases he : embedCfg register stack label returnPc frame source
  simp_all [embedCfg]
theorem embedState_eq_of_ports {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame target : State R S) (source : State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (hreg : ∀ i, target.regs (register i) = source.regs i)
    (hregFrame : ∀ i, (¬ ∃ j, register j = i) → target.regs i = frame.regs i)
    (hstack : ∀ i, target.stacks (stack i) = source.stacks i)
    (hstackFrame : ∀ i, (¬ ∃ j, stack j = i) → target.stacks i = frame.stacks i) :
    embedState register stack frame source = target := by
  have h := embedCfg_eq_of_ports register stack (id : Fin 1 → Fin 1) none
    (frame.withPC none) (target.withPC none) (source.withPC none) hr hs rfl
    hreg hregFrame hstack hstackFrame
  exact congrArg StructuredProgram.State.ofCfg h
end DetDLP.w5_M6FramePorts
namespace DetDLP.w5_M6BoundedProgramLoop
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking
/-- A time-indexed run annotated at every visited configuration. -/
inductive SafeTrace {S : Type} (step : S → Option S) (ok : S → Prop) : ℕ → S → S → Prop
  | refl (s : S) : ok s  →  SafeTrace step ok 0 s s
  | cons {s t u k} : ok s  →  step s=some t  →  SafeTrace step ok k t u  →  SafeTrace step ok (k+1) s u
namespace SafeTrace
variable {S T : Type} {f : S → Option S} {g : T → Option T} {P : S → Prop} {Q : T → Prop}
theorem forget {k s t} (tr : SafeTrace f P k s t) : Computation.Trace f k s t := by
  induction tr with
  | refl s _ => exact .refl _
  | cons _ hs _ ih => exact .cons hs ih
theorem trans {n m a b c} (tr : SafeTrace f P n a b) (u : SafeTrace f P m b c) : SafeTrace f P (n+m) a c := by
  induction tr with
  | refl => simpa using u
  | cons h hs _ ih => exact (Nat.succ_add _ _).symm ▸ SafeTrace.cons h hs (ih u)
theorem within {n s t} (tr : SafeTrace f P n s t) :
    ∀ j c,j≤n → Computation.Trace f j s c → P c := by
  induction tr with
  | refl _ h =>
    intro j c hj hp
    obtain rfl : j=0 := by omega
    cases hp; exact h
  | cons h step tail ih =>
    intro j c hj hp; cases hp with
    | refl => exact h
    | cons hs ht => obtain rfl := Option.some.inj (step.symm.trans hs); exact ih _ _ (by omega) ht
theorem of_trace {n s t} (tr : Computation.Trace f n s t)
    (cap : ∀ j c,j≤n → Computation.Trace f j s c → P c) : SafeTrace f P n s t := by
  induction tr with
  | refl => exact .refl _ (cap _ _ (by omega) (.refl _))
  | cons step tail ih =>
    exact .cons (cap _ _ (by omega) (.refl _)) step (ih (fun j c hj tr => cap _ c (by omega) (.cons step tr)))
theorem map {n a b} (tr : SafeTrace f P n a b) (E : S → T)
    (next : ∀ x y,f x=some y → g (E x)=some (E y)) (safe : ∀ x,P x → Q (E x)) : SafeTrace g Q n (E a) (E b) := by
  induction tr with
  | refl _ h => exact .refl _ (safe _ h)
  | cons h hs _ ih => exact .cons (safe _ h) (next _ _ hs) ih
end SafeTrace
variable {r s : ℕ}
def cap {L : ℕ} (W : ℕ) (c : Cfg r s L) := ∀ i,(c.stacks i).length≤W
end DetDLP.w5_M6BoundedProgramLoop
namespace DetDLP.w5_M6BoundedProgramLink
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking w5_M6BoundedProgramLoop
variable {r s l m : ℕ} (p : Program r s l) (q : Program r s m)
theorem relabel {L : ℕ} (Q : Program r s L) (labels : Fin l → Fin L) (ret : Option (Fin L))
    (code : CodeEmbedding p Q id id labels ret) {t x y W} (tr : SafeTrace (step p) (cap W) t x y) :
    SafeTrace (step Q) (cap W) t (relabelCfg labels ret x) (relabelCfg labels ret y) := by
  apply tr.map (relabelCfg labels ret) _ (fun _ h => h)
  intro a b h
  let frame := relabelCfg labels ret a
  simpa only [embedCfg_id] using relocate_step p Q id id labels ret frame Function.injective_id Function.injective_id code h

theorem join {n m' W : ℕ} {u v w : Fin r→Bool} {a b c : Fin s→List Bool}
    (left : SafeTrace (step p) (cap W) n ⟨some p.entry,u,a⟩ ⟨none,v,b⟩)
    (right : SafeTrace (step q) (cap W) m' ⟨some q.entry,v,b⟩ ⟨none,w,c⟩) :
    SafeTrace (step (link p q)) (cap W) (n+m') ⟨some (link p q).entry,u,a⟩ ⟨none,w,c⟩ := by
  have tr := relabel p (link p q) (Fin.castAdd m) (some (Fin.natAdd l q.entry)) (linkInto_leftCode p q id id id id) left
  have thenTr := relabel q (link p q) (Fin.natAdd l) none (linkInto_rightCode p q id id id id) right
  exact tr.trans thenTr
end DetDLP.w5_M6BoundedProgramLink
namespace DetDLP.w5_M6CallOnPorts
open w5_M6FramePorts
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking w5_M6BoundedProgramLoop
variable {r s l R S : ℕ} (p : Program r s l) (reg : Fin r→Fin R) (ports : Fin s→Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective ports)
include hr hs in
theorem run {W n : ℕ} (a b : Fin S→List Bool) (small big : Fin s→List Bool) (r₀ : Fin R→Bool) (rf : Fin r→Bool)
    (pre : ∀ i,a (ports i)=small i) (post : ∀ i,b (ports i)=big i)
    (frameEq : ∀ i,(¬∃ j,ports j=i)→b i=a i)
    (room : ∀ i,(¬∃ j,ports j=i)→(a i).length≤W)
    (tr : SafeTrace (step p) (cap W) n ⟨some p.entry,r₀ ∘ reg,small⟩ ⟨none,rf,big⟩) :
    ∃ r',SafeTrace (step (liftProgram p reg ports)) (cap W) n
      ⟨some (liftProgram p reg ports).entry,r₀,a⟩ ⟨none,r',b⟩ := by
  classical
  let Q := liftProgram p reg ports
  let start : Cfg R S l := ⟨some Q.entry,r₀,a⟩
  let emb := embedCfg reg ports id none start
  have applyTr := tr.map emb (g:=step Q) (Q:=cap W) (by
    intro u v eq
    exact relocate_step p Q reg ports id none start hr hs (fun _ => rfl) eq)
    (by intro c hc i; by_cases mem : ∃ j,ports j=i
        · obtain ⟨j,rfl⟩ := mem; dsimp only [emb]; rw [embedCfg_stack _ _ _ _ _ _ hs]; exact hc j
        · dsimp only [emb]; rw [embedCfg_stack_frame _ _ _ _ _ _ _ mem]; exact room i mem)
  let r' := Function.extend reg rf r₀
  have e₀ : emb ⟨some p.entry,r₀ ∘ reg,small⟩=start := by
    apply embedCfg_eq_of_ports _ _ _ _ _ _ _ hr hs
    · rfl
    · intro i; rfl
    · intro i hi; rfl
    · exact pre
    · intro i hi; rfl
  have e₁ : emb ⟨none,rf,big⟩=⟨none,r',b⟩ := by
    apply embedCfg_eq_of_ports _ _ _ _ _ _ _ hr hs
    · rfl
    · intro i; exact hr.extend_apply .. 
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · exact post
    · exact frameEq
  rw [e₀,e₁] at applyTr
  exact ⟨r',applyTr⟩
end DetDLP.w5_M6CallOnPorts
namespace DetDLP.w5_M6QueryOutputZip
open OAI.Algorithms.SubexponentialSAT BitProgram
def machine : Program 2 3 7 where
  inputStack:=0
  outputStack:=2
  entry:=0
  code:=![.pop 0 0 1 1,.branch 1 2 6,.branch 0 3 6,.pop 1 0 1 4,.branch 1 5 6,.push 2 0 0,.halt]
private def cfg (pc : Option (Fin 7)) (r : Fin 2→Bool) (t v a : List Bool) : Cfg 2 3 7 := ⟨pc,r,![t,v,a]⟩
private def empty (r : Fin 2→Bool) := readRegs r 0 1 none
private def reg (r : Fin 2→Bool) (b : Bool) := readRegs r 0 1 (some b)
private theorem popT (r : Fin 2→Bool) (t v a : List Bool) :
    step machine (cfg (some 0) r t v a)=some (cfg (some 1) (readRegs r 0 1 t.head?) t.tail v a) := by
  have eq : Function.update ![t,v,a] (0:Fin 3) t.tail=![t.tail,v,a] := by funext i; fin_cases i <;> rfl
  change some (⟨some 1,readRegs r 0 1 t.head?,Function.update ![t,v,a] 0 t.tail⟩ : Cfg 2 3 7)=some (cfg (some 1) _ t.tail v a); rw [eq] <;> rfl
private theorem popV (r : Fin 2→Bool) (t v a : List Bool) :
    step machine (cfg (some 3) r t v a)=some (cfg (some 4) (readRegs r 0 1 v.head?) t v.tail a) := by
  have eq : Function.update ![t,v,a] (1:Fin 3) v.tail=![t,v.tail,a] := by funext i; fin_cases i <;> rfl
  change some (⟨some 4,readRegs r 0 1 v.head?,Function.update ![t,v,a] 1 v.tail⟩ : Cfg 2 3 7)=some (cfg (some 4) _ t v.tail a); rw [eq] <;> rfl
private theorem push (r : Fin 2→Bool) (t v a : List Bool) (b : Bool) (h : r 0=b) :
    step machine (cfg (some 5) r t v a)=some (cfg (some 0) r t v (b::a)) := by
  have eq : Function.update ![t,v,a] (2:Fin 3) (r 0::a)=![t,v,b::a] := by rw [h]; funext i; fin_cases i <;> rfl
  change some (⟨some 0,r,Function.update ![t,v,a] 2 (r 0::a)⟩ : Cfg 2 3 7)=some (cfg (some 0) r t v (b::a)); rw [eq] <;> rfl
private theorem test (i : Fin 2) (j k : Fin 7) (r : Fin 2→Bool) (t v a : List Bool) (b : Bool)
    (pc : Fin 7) (code : machine.code pc=.branch i j k) (h : r i=b) :
    step machine (cfg (some pc) r t v a)=some (cfg (some (if b then j else k)) r t v a) := by
  simp [step,cfg,code,execInstr,h]
private theorem last (r : Fin 2→Bool) (t v a : List Bool) :
    Trace machine 1 (cfg (some 6) r t v a) (cfg none r t v a) := .cons (by rfl) (.refl _)
def value (t v : List Bool) := (((t.zip v).takeWhile Prod.fst).map Prod.snd)
theorem run (tags vals acc : List Bool) (r₀ : Fin 2→Bool) :
    ∃ t rf ts vs,t ≤ 6*(value tags vals).length+6 ∧ Trace machine t (cfg (some 0) r₀ tags vals acc)
      (cfg none rf ts vs ((value tags vals).reverse++acc)) := by
  induction tags generalizing vals acc r₀ with
  | nil =>
    have q := popT r₀ [] vals acc
    have t := test 1 2 6 (empty r₀) [] vals acc false 1 rfl (by simp [empty,readRegs])
    exact ⟨3,empty r₀,[],vals,by simp [value],.cons q (.cons t (last ..))⟩
  | cons tag tags ih =>
    have q := popT r₀ (tag::tags) vals acc
    let r := reg r₀ tag
    have first := test 1 2 6 r tags vals acc true 1 rfl (by simp [r,reg,readRegs])
    have second := test 0 3 6 r tags vals acc tag 2 rfl (by simp [r,reg,readRegs])
    cases tag with
    | false =>
      refine ⟨4,r,tags,vals,by omega,?_⟩
      have ev : value (false::tags) vals=[] := by cases vals <;> rfl
      rw [ev]; exact .cons q (.cons first (.cons second (last ..)))
    | true =>
      have pop := popV r tags vals acc
      cases vals with
      | nil =>
        have v := test 1 5 6 (empty r) tags [] acc false 4 rfl (by simp [empty,readRegs])
        exact ⟨6,empty r,tags,[],by simp [value],.cons q (.cons first (.cons second (.cons pop (.cons v (last ..)))))⟩
      | cons bit vals =>
        let rf := reg r bit
        have yes := test 1 5 6 rf tags vals acc true 4 rfl (by simp [rf,reg,readRegs])
        have ins := push rf tags vals acc bit (by simp [rf,reg,readRegs])
        obtain ⟨t,fin,ts,vs,ht,tail⟩ := ih vals (bit::acc) rf
        have eq : value (true::tags) (bit::vals)=bit::value tags vals := rfl
        rw [eq,List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
        refine ⟨t+6,fin,ts,vs,by omega,?_⟩
        exact .cons q (.cons first (.cons second (.cons pop (.cons yes (.cons ins tail)))))
end DetDLP.w5_M6QueryOutputZip
namespace DetDLP.w5_M6EntryCallFrame
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking w5_M6BoundedProgramLoop SqrtLogSpace
open w5_M6StackOps
variable {e : ℕ} (it iv : Fin e)
abbrev Bank (n : ℕ) := Fin n→List Bool
def join (a : Bank e) (b : Bank 3) : Bank (e+3) := Fin.addCases a b
@[simp] theorem low (a : Bank e) (b : Bank 3) (j : Fin e) : join a b (j.castAdd 3)=a j := Fin.addCases_left ..
@[simp] theorem high (a : Bank e) (b : Bank 3) (j : Fin 3) : join a b (Fin.natAdd e j)=b j := Fin.addCases_right ..
abbrev lo (j : Fin e) := j.castAdd 3
abbrev up (j : Fin 3) := Fin.natAdd e j
theorem disjoint (j : Fin e) (k : Fin 3) : lo j≠up (e:=e) k := by
  intro h; have eq := congrArg Fin.val h; change j.val=e+k.val at eq; have := j.isLt; omega
def preports : Fin 5→Fin (e+3) := ![lo it,up 0,up 1,up 2,lo iv]
def zipports : Fin 3→Fin (e+3) := ![lo it,lo iv,up 2]
theorem distinguish (h : it≠iv) : Function.Injective (preports it iv) := by
  have d (k) (l) := disjoint (e:=e) k l
  intro j k hk
  fin_cases j <;> fin_cases k <;> simp_all [preports,lo,up,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd] <;> omega
theorem distinguishZip (h : it≠iv) : Function.Injective (zipports it iv) := by
  have d (k) (l) := disjoint (e:=e) k l
  intro j k hk
  fin_cases j <;> fin_cases k <;> simp_all [zipports,lo,up,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd] <;> omega

def source (desc vert bits : List Bool) : Bank (e+3) :=
  join (fun j => if j=it then desc else []) ![vert,bits,[]]
def initQ (w : List Bool) : Bank e :=
  fun j => if j=it then List.replicate w.length true else if j=iv then w else []
end DetDLP.w5_M6EntryCallFrame
namespace DetDLP.w5_M6EntryScratchReset
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls w5_M6StackOps
open w5_M6StackOps
def sweep {n : ℕ} : List (Fin n)→Cmd 8 n
  | [] => .base .skip
  | i::is => (clearCmd i).seq (sweep is)
def swept {n : ℕ} (is : List (Fin n)) (s : Fin n→List Bool) (j : Fin n) := if j∈is then [] else s j
theorem sweep_eval {n : ℕ} (is : List (Fin n)) (s : Fin n→List Bool) (r : Regs) (U : ℕ) (bound : ∀ i,(s i).length≤U) :
    ∃ t rf,t ≤ is.length*(2*U+3) ∧ Eval (sweep is) t ⟨r,s⟩ ⟨rf,swept is s⟩ := by
  induction is generalizing s r with
  | nil =>
    have eq : swept [] s=s := by funext j; simp [swept]
    rw [eq]; exact ⟨0,r,by simp,by simpa [swept,sweep] using Eval.base (StructuredProgram.Eval.skip (⟨r,s⟩ : State 8 n))⟩
  | cons i is ih =>
    let s' := Function.update s i []
    have bd (j) : (s' j).length≤U := by by_cases h : j=i <;> simp [s',h,bound]
    have c := clear_eval i (⟨r,s⟩ : State 8 n)
    obtain ⟨t,rf,ht,tail⟩ := ih s' (readRegs r 0 1 none) bd
    have eq : swept is s'=swept (i::is) s := by
      funext j; by_cases h : j=i <;> by_cases k : j∈is <;> simp [swept,s',h,k]
    rw [eq] at tail
    refine ⟨_,rf,?_,.seq c tail⟩
    change 2*(s i).length+3+t ≤ (is.length+1)*(2*U+3)
    rw [Nat.add_mul,one_mul]; have := bound i; omega
def reset {e : ℕ} := sweep ((List.finRange e).map (Fin.castAdd 3))
theorem reset_eval {e : ℕ} (q : Fin e→List Bool) (c : Fin 3→List Bool) (r : Regs) (U : ℕ)
    (bq : ∀ i,(q i).length≤U) (bc : ∀ i,(c i).length≤U) :
    ∃ n rf,n ≤ e*(2*U+3) ∧ Eval (reset (e:=e)) n ⟨r,Fin.addCases q c⟩ ⟨rf,Fin.addCases (fun _ => []) c⟩ := by
  let is := (List.finRange e).map (Fin.castAdd 3)
  have bd (i : Fin (e+3)) : ((Fin.addCases (motive:=fun _=>List Bool) q c) i).length≤U := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using bq j
    · simpa only [Fin.addCases_right] using bc j
  obtain ⟨n,rf,time,tr⟩ := sweep_eval is (Fin.addCases q c) r U bd
  have eq : swept is (Fin.addCases q c)=Fin.addCases (fun _ : Fin e => []) c := by
    funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have mem : j.castAdd 3∈is := List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩
      simp [swept,mem]
    · have nmem : Fin.natAdd e j∉is := by
        intro h; obtain ⟨v,_,eq⟩ := List.mem_map.mp h; have := congrArg Fin.val eq
        change v.val=e+j.val at this; have := v.isLt; omega
      simp [swept,nmem]
  rw [eq] at tr; exact ⟨n,rf,by simpa [is] using time,tr⟩
end DetDLP.w5_M6EntryScratchReset
namespace DetDLP.w5_M6EntryCallHarvest
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking w5_M6BoundedProgramLoop StructuredCalls w5_M6StackOps
open w5_M6StackOps w5_M6EntryCallFrame
variable {e : ℕ} (ot ov : Fin e)
def program := liftProgram w5_M6QueryOutputZip.machine (Fin.castAdd 6) (zipports ot ov)
def middle (w : List Bool) : Bank 3 := ![[],[],w.reverse]
def endBank (w : List Bool) : Bank (e+3) := join (fun _ => []) ![w,[],[]]
theorem word_length (tags vals : List Bool) : (w5_M6QueryOutputZip.value tags vals).length ≤ tags.length := by
  simp only [w5_M6QueryOutputZip.value,List.length_map]
  exact (List.takeWhile_sublist (l:=tags.zip vals) Prod.fst).length_le.trans (by simp)
theorem harvest (h : ot≠ov) (a : Bank e) (r : Regs) (U : ℕ) (bound : ∀ j,(a j).length ≤ U) :
    let word := w5_M6QueryOutputZip.value (a ot) (a ov)
    ∃ n rf b,n ≤ 6*U+6 ∧ (∀ j,(b j).length ≤ 7*U+6) ∧
      SafeTrace (step (program ot ov)) (cap (7*U+6)) n ⟨some (program ot ov).entry,r,join a (fun _ => [])⟩
      ⟨none,rf,join b (middle word)⟩ := by
  intro word
  obtain ⟨n,rf,ts,vs,time,tr⟩ := w5_M6QueryOutputZip.run (a ot) (a ov) [] (r ∘ Fin.castAdd 6)
  let b := Function.update (Function.update a ot ts) ov vs
  have sz := (word_length (a ot) (a ov)).trans (bound ot)
  have hn : n ≤ 6*U+6 := by omega
  have safe := SafeTrace.of_trace tr (P:=cap (7*U+6)) (by
    intro j c hj pref i
    have x := w5_BitTracePolynomial.trace_grows pref i
    have base : (![a ot,a ov,[]] i).length ≤ U := by fin_cases i <;> simp [bound]
    change (c.stacks i).length ≤ (![a ot,a ov,[]] i).length+j at x
    omega)
  have e₁ : ∃ rf',SafeTrace (step (program ot ov)) (cap (7*U+6)) n
      ⟨some (program ot ov).entry,r,join a (fun _ => [])⟩ ⟨none,rf',join b (middle word)⟩ := by
    apply w5_M6CallOnPorts.run w5_M6QueryOutputZip.machine (Fin.castAdd 6) (zipports ot ov) (Fin.castAdd_injective ..)
      (distinguishZip ot ov h) _ _ _ _ r rf _ _ _ _ safe
    · intro j; fin_cases j <;> simp [zipports,lo,up]
    · intro j; fin_cases j <;> simp [zipports,lo,up,b,middle,h,h.symm,word]
    · intro j; refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · intro outside
        have ne : j≠ot := fun eq => outside ⟨0,by subst j; rfl⟩
        have nf : j≠ov := fun eq => outside ⟨1,by subst j; rfl⟩
        simp [b,ne,nf]
      · intro outside; fin_cases j
        · simp [middle]
        · simp [middle]
        · exact False.elim (outside ⟨2,rfl⟩)
    · intro j; refine Fin.addCases (fun j _ => ?_) (fun j _ => ?_) j
      · rw [low]; have := bound j; omega
      · simp
  obtain ⟨rf',tr'⟩ := e₁
  refine ⟨n,rf',b,hn,?_,tr'⟩
  intro j; have bd := (tr'.within n _ le_rfl tr'.forget) (lo j)
  change ((join b (middle word)) (j.castAdd 3)).length ≤ _ at bd; simpa using bd

def cleanCmd (e : ℕ) := (w5_M6EntryScratchReset.reset (e:=e)).seq
  ((.call (transferProgram (up (e:=e) 2) (up 0) 0 1)))
def clean (e : ℕ) := compiled (cleanCmd e) (up 2) (up 0)
theorem cleanup (r : Regs) (b : Bank e) (word : List Bool) (U : ℕ)
    (bd : ∀ i,(b i).length ≤ U) (bw : word.length ≤ U) :
    let budget := e*(2*U+3)+3*U+4
    ∃ n rf,n ≤ budget ∧ SafeTrace (step (clean e)) (cap (U+budget)) n
      ⟨some (clean e).entry,r,join b (middle word)⟩ ⟨none,rf,endBank word⟩ := by
  intro budget
  have bc (j : Fin 3) : (middle word j).length ≤ U := by fin_cases j <;> simp [middle,bw]
  obtain ⟨n,rf,time,tr⟩ := w5_M6EntryScratchReset.reset_eval b (middle word) r U bd bc
  let s := join (fun _ : Fin e => []) (middle word)
  have ne : up (e:=e) 2≠up 0 := by exact fun h => (by decide : (2:Fin 3)≠0) (Fin.natAdd_injective _ _ h)
  have push := w5_M6StackOps.transfer_eval (up (e:=e) 2) (up 0) (0:Fin 8) 1 ne (by decide) rf s
  have eq : transferStacks (up (e:=e) 2) (up 0) s=endBank word := by
    funext j; refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [transferStacks,Function.update_apply,s,endBank,show j.castAdd 3≠up (e:=e) 0 from w5_M6EntryCallFrame.disjoint j 0,
          show j.castAdd 3≠up (e:=e) 2 from w5_M6EntryCallFrame.disjoint j 2]
    · fin_cases j <;> simp [transferStacks,Function.update_apply,s,endBank,middle,up]
  rw [eq] at push
  have whole := compiled_halt_trace (Eval.seq tr push) (up 2) (up 0)
  have len : (s (up 2)).length=word.length := by simp [s,up,middle]
  let t := n+(3*(s (up 2)).length+3)+1
  have cost : t ≤ budget := by dsimp only [t,budget]; rw [len]; omega
  refine ⟨t,_,cost,SafeTrace.of_trace whole ?_⟩
  intro j c hj pref i
  have base : ((join b (middle word)) i).length ≤ U := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using bd j
    · simpa using bc j
  exact (w5_BitTracePolynomial.trace_grows pref i).trans (Nat.add_le_add base (hj.trans cost))
end DetDLP.w5_M6EntryCallHarvest


