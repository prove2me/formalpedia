-- Prove2me | Definitions.Def_DetDLP_W5_M6RawCallback
-- name    : DetDLP_W5_M6RawCallback
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T02:04:08.831177+00:00
-- url     : https://prove2.me/theorems/53f01223-b2c4-4d79-86af-ca56bfb357d9
-- title:
--   M6 Raw Callback
-- statement:
--   An arbitrary primitive word machine on a fixed initial head bit is simulated by a reusable clean word subroutine; steps include the actual simulation plus a linear initialization and scratch cleanup cost.

import Definitions.Def_DetDLP_W5_M6Harvest

set_option autoImplicit false
namespace DetDLP.w5_M6RawCallback
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking
open OAI.Algorithms.SubexponentialSAT.Computation
open w5_EntryTapeCode w5_M6HeadBit w5_M6BoundedProgramLoop
open w5_M6EntryCallFrame
noncomputable section
variable (E : PrimitiveMachine) (out : Fin E.tapeCount)
abbrev it := lane E E.inputTape false true
abbrev iv := lane E E.inputTape false false
abbrev ot := lane E out false true
abbrev ov := lane E out false false
abbrev base := w5_EntryTapeCode.program E out (headBits E false)
def table : Program 3 (S E) (2 + L E) where
  inputStack := iv E
  outputStack := ov E out
  entry := Fin.castAdd _ 0
  code := Fin.addCases (fun i => if i = 0 then .pop (iv E) 0 1 (Fin.castAdd _ 1)
    else .branch 0 (Fin.natAdd 2 (pc E (headBits E true) E.start 0))
                   (Fin.natAdd 2 (pc E (headBits E false) E.start 0)))
    (fun i => relocateInstr id id (Fin.natAdd 2) none ((base E out).code i))
def input (b : Bool) (w : List Bool) : w5_M6EntryCallFrame.Bank (S E) := fun i =>
  if i=it E then List.replicate w.length true else if i=iv E then b::w else []

theorem run (b : Bool) (w output : List Bool) (T M : ℝ)
    (exec : RunsWithin E out (b::w) output T M) (r : Fin 3 → Bool) :
    ∃ (n : ℕ) (rf : Fin 3 → Bool) (a : w5_M6EntryCallFrame.Bank (S E)), (n:ℝ) ≤ 8*T+2 ∧
      SafeTrace (step (table E out)) (cap (⌊M⌋₊+9)) n
        ⟨some (table E out).entry,r,input E b w⟩ ⟨none,rf,a⟩ ∧
      w5_M6QueryOutputZip.value (a (ot E out)) (a (ov E out)) = output := by
  let r' := readRegs r 0 1 (some b)
  obtain ⟨k,⟨p,rf,a⟩,hk,hpc,hw,hs⟩ := call E out (b::w) output T M exec r' (headBits E false)
  dsimp only at hpc; subst p
  rw [initial_headBits,initial_body] at hs
  have safe := SafeTrace.of_trace (P:=cap (⌊M⌋₊+8)) hs.trace (fun _ _ h tr => hs.prefix h tr)
  have rel := w5_M6BoundedProgramLink.relabel (base E out) (table E out) (Fin.natAdd 2) none
    (fun _ => by simp [table]) safe
  let st := initQ (it E) (iv E) w
  have hi : it E ≠ iv E := by simp [it,iv]
  have hlen : w.length ≤ ⌊M⌋₊+8 := by
    have h := hs.prefix (Nat.zero_le _) (.refl _) (iv E)
    simpa [cf,hi.symm,it,iv] using h
  have upd : Function.update (input E b w) (iv E) w = st := by
    funext i; by_cases h : i=iv E <;> simp [st,initQ,input,h,hi.symm]
  have a0 : cap (⌊M⌋₊+9) (⟨some (table E out).entry,r,input E b w⟩ : Cfg 3 _ _) := by
    intro i; change (input E b w i).length ≤ _; unfold input; split_ifs <;> simp_all <;> omega
  let mid : Cfg 3 (S E) (2+L E) := ⟨some (Fin.castAdd _ 1),r',st⟩
  have a1 : cap (⌊M⌋₊+9) mid := by
    intro i; change (st i).length ≤ _; dsimp [st,initQ]; split_ifs <;> simp_all <;> omega
  have start : step (table E out) ⟨some (table E out).entry,r,input E b w⟩ = some mid := by
    have v : input E b w (iv E)=b::w := by simp [input,hi.symm]
    simp [table,step,execInstr,v,upd,mid,r']
  have enter : step (table E out) mid = some (relabelCfg (Fin.natAdd 2) none
      (cf E (headBits E b) E.start 0 r' st)) := by
    cases b <;> simp [table,step,execInstr,mid,r',readRegs,cf,relabelCfg,relocatePc]
  have wider := rel.map (Q:=cap (⌊M⌋₊+9)) id (fun _ _ h => h) (fun _ h i => Nat.le_trans (h i) (by omega : ⌊M⌋₊+8 ≤ ⌊M⌋₊+9))
  exact ⟨k+1+1,rf,a,by push_cast; linarith,
    SafeTrace.cons a0 start (SafeTrace.cons a1 enter wider), (extract_eq _ _).symm.trans hw⟩
abbrev inner := liftProgram (table E out) (Fin.castAdd 5) (Fin.castAdd 3)
noncomputable def cleanTable := link (inner E out) (link (w5_M6EntryCallHarvest.program (ot E out) (ov E out)) (w5_M6EntryCallHarvest.clean (S E)))
abbrev budget (e U : ℕ) := (e+4)*(20*(U+10))

theorem widen {r s l W V : ℕ} {p : Program r s l} {n : ℕ} {a b : Cfg r s l}
    (tr : SafeTrace (step p) (cap W) n a b) (h : W ≤ V) : SafeTrace (step p) (cap V) n a b :=
  tr.map id (fun _ _ h => h) (fun _ h' j => (h' j).trans h)

theorem cleanRun (b : Bool) (w word : List Bool) (T M : ℝ)
    (exec : RunsWithin E out (b::w) word T M) (r : Fin 8 → Bool) :
    let V := budget (S E) (⌊M⌋₊+9)
    ∃ (n : ℕ) (rf : Fin 8 → Bool), (n:ℝ) ≤ 8*T+V ∧
      SafeTrace (step (cleanTable E out)) (cap V) n
        ⟨some (cleanTable E out).entry,r,join (input E b w) (fun _ => [])⟩
        ⟨none,rf,w5_M6EntryCallHarvest.endBank word⟩ := by
  intro V
  let U := ⌊M⌋₊+9
  obtain ⟨n,rf,a,time,tr,output⟩ := run E out b w word T M exec (r ∘ Fin.castAdd 5)
  have bd (j : Fin (S E)) : (a j).length ≤ U := tr.within n _ le_rfl tr.forget j
  have body : ∃ r', SafeTrace (step (inner E out)) (cap U) n
      ⟨some (inner E out).entry,r,join (input E b w) (fun _ => [])⟩ ⟨none,r',join a (fun _ => [])⟩ := by
    apply w5_M6CallOnPorts.run (table E out) (Fin.castAdd 5) (Fin.castAdd 3)
      (Fin.castAdd_injective ..) (Fin.castAdd_injective ..) _ _ _ _ r rf _ _ _ _ tr
    · intro j; simp
    · intro j; simp
    · intro j; refine Fin.addCases (fun j h => False.elim (h ⟨j,rfl⟩)) (fun j _ => ?_) j; simp
    · intro j; refine Fin.addCases (fun j h => False.elim (h ⟨j,rfl⟩)) (fun j _ => ?_) j; simp
  obtain ⟨r₂,tr₂⟩ := body
  obtain ⟨k,r₃,z,hk,hz,tr₃⟩ := w5_M6EntryCallHarvest.harvest (ot E out) (ov E out) (by simp [ot,ov]) a r₂ U bd
  rw [output] at tr₃
  have wl := (w5_M6EntryCallHarvest.word_length (a (ot E out)) (a (ov E out))).trans (bd _)
  rw [output] at wl
  let Z := 7*U+6
  obtain ⟨f,r₄,hf,tr₄⟩ := w5_M6EntryCallHarvest.cleanup r₃ z word Z hz (by dsimp [Z]; omega)
  have huge : U+Z+((S E)*(2*Z+3)+3*Z+4)+6*U+8 ≤ V := by
    change _ ≤ (S E+4)*(20*(U+10))
    have p := Nat.mul_le_mul_left (S E) (show 2*Z+3 ≤ 20*(U+10) by dsimp [Z]; omega)
    rw [Nat.add_mul]; dsimp only [Z] at *; omega
  have block := w5_M6BoundedProgramLink.join _ _ (widen tr₂ (show U≤V by omega))
    (w5_M6BoundedProgramLink.join _ _ (widen tr₃ (show 7*U+6≤V by omega)) (widen tr₄ (show Z+(S E*(2*Z+3)+3*Z+4)≤V by omega)))
  refine ⟨_,r₄,?_,block⟩
  change f ≤ S E * (2*Z+3)+3*Z+4 at hf
  have oh : 2+(k+f)≤V := by omega
  have oh' : (2:ℝ)+(k+f)≤V := by exact_mod_cast oh
  push_cast; linarith
end
end DetDLP.w5_M6RawCallback


