-- Prove2me | solution 1 for AffinePrefixEnumeration.solver_exists
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:26:01.720534+00:00
-- url     : https://prove2.me/submissions/65c8ef2b-b308-4be3-917e-758bfd170cfe

import Definitions.Def_AffineCounting_RAMInterfaces
import Theorems.Thm_EditGV897_Main_affine_count_correct
import Theorems.Thm_EditGV897_Main_affine_counter_program

set_option autoImplicit false

section StructuredLogCostRAM

/-! Structured, relocatable programs for the Prove2Me log-cost machine. All costs count
the primitive steps of the published instruction list, including jumps. -/

namespace TargetedSamplers.Structured

theorem Exec.post {τ inv c s t k} (e : Exec τ inv c s t k) (hs : inv s) : inv t := by
  induction e <;> solve_by_elim

/-- A live, ordinary machine state at the specified instruction, memory and output. -/
structure Located (st : State) (pc : ℕ) (s : Store) : Prop where
  counter : st.pc = pc
  live : st.halted = false
  normal : st.bot = false
  memory : st.mem = s.mem
  output : st.out = s.out

private theorem step_op {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (p : Op) (hp : P[pc]? = some p.instruction) : Located (P.step τ st) (pc+1) (p.eval τ s) := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  cases p <;> constructor <;> simp_all [Op.instruction, Op.eval, Program.step, State.write, Store.write]

end TargetedSamplers.Structured

end StructuredLogCostRAM

section StructuredLogCostFragments

namespace TargetedSamplers.Structured

theorem Store.write_fits {s : Store} {width v : ℕ} (h : s.Fits width) (d : ℕ) (hv : v.size ≤ width) :
    (s.write d v).Fits width := by
  intro a
  by_cases he : a = d
  · simpa [Store.write, he] using hv
  · simpa [Store.write, he] using h a

@[simp] theorem Store.write_overwrite (s : Store) (a x y : ℕ) : (s.write a x).write a y = s.write a y := by
  simp [Store.write]

def Op.written (τ : Tapes) (s : Store) : Op → ℕ
  | .const _ c => c
  | .add _ a b => s.mem a + s.mem b
  | .sub _ a b => s.mem a - s.mem b
  | .load _ a => s.mem (s.mem a)
  | .store _ b => s.mem b
  | .input _ a => bitVal τ.input[s.mem a]?
  | .coin _ a => bitVal τ.coins[s.mem a]?
  | .output _ => 0

theorem Op.eval_fits (p : Op) (τ : Tapes) {s : Store} {b : ℕ}
    (hi : s.Fits b) (hw : (p.written τ s).size ≤ b) : (p.eval τ s).Fits b := by
  cases p <;> first | exact Store.write_fits hi _ hw | exact hi

structure Result where
  last : Store
  steps : ℕ
  writeWidth : ℕ

/-- Evaluation charges the actual control transfers and records the largest value written. -/
def Fragment.run (τ : Tapes) (s : Store) : Fragment → Result
  | .skip => ⟨s,0,0⟩
  | .op o => ⟨o.eval τ s,1,(o.written τ s).size⟩
  | .seq x y =>
    let p := x.run τ s
    let q := y.run τ p.last
    ⟨q.last,p.steps+q.steps,max p.writeWidth q.writeWidth⟩
  | .branch a b yes no =>
    if s.mem a ≤ s.mem b then
      let p := yes.run τ s
      ⟨p.last,1+p.steps,p.writeWidth⟩
    else
      let p := no.run τ s
      ⟨p.last,1+p.steps+1,p.writeWidth⟩

theorem Fragment.exec (f : Fragment) (τ : Tapes) (s : Store) (b : ℕ)
    (hs : s.Fits b) (hw : (f.run τ s).writeWidth ≤ b) :
    Exec τ (fun st => st.Fits b) f.cmd s (f.run τ s).last (f.run τ s).steps := by
  induction f generalizing s with
  | skip => exact .skip s
  | op o => exact .op s o (o.eval_fits τ hs hw)
  | seq x y ix iy =>
    obtain ⟨hx,hy⟩ := max_le_iff.mp hw
    have first := ix s hs hx
    exact .seq first (iy _ (first.post hs) hy)
  | branch a b y n iy ino =>
    by_cases h : s.mem a ≤ s.mem b
    · simp only [run,h,if_true] at hw ⊢
      exact .yes h (iy s hs hw)
    · simp only [run,h,if_false] at hw ⊢
      exact .no h (ino s hs hw)

theorem dispatch_select {τ : Tapes} {inv : Store → Prop} (key scratch : ℕ) (hne : key ≠ scratch)
    (cs : List Cmd) (base : ℕ) (s t : Store) (j : Fin cs.length) (steps : ℕ)
    (tag : s.mem key = base+j.val) (safe : ∀ v ≤ base+j.val, inv (s.write scratch v))
    (branch : Exec τ inv cs[j.val] (s.write scratch (base+j.val)) t steps) :
    Exec τ inv (dispatch key scratch base cs) s t (3*j.val+2+steps) := by
  induction cs generalizing base s with
  | nil => exact Fin.elim0 j
  | cons c cs ih =>
    cases j using Fin.cases with
    | zero =>
      have h := safe base (by simp)
      have ht : (s.write scratch base).mem key ≤ (s.write scratch base).mem scratch := by
        simp [Store.write, hne, tag]
      have he : Exec τ inv c (s.write scratch base) t steps := by simpa using branch
      simpa [dispatch, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Exec.seq (Exec.op s (.const scratch base) h) (Exec.yes (n := dispatch key scratch (base+1) cs) ht he)
    | succ i =>
      let m := s.write scratch base
      have hm : inv m := safe _ (by simp)
      have hg : ¬m.mem key ≤ m.mem scratch := by
        simp [m, Store.write, hne, tag]
      have htag : m.mem key = base+1+i.val := by
        simpa [m, Store.write, Function.update_apply, hne, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tag
      have he := ih (base+1) m i htag (fun v hv => by
        simpa [m] using safe v (by simp at hv ⊢; omega)) (by
        simpa [m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using branch)
      have run := Exec.seq (Exec.op s (.const scratch base) hm) (Exec.no (y := c) hg he)
      convert run using 1 <;> simp [dispatch] <;> omega

end TargetedSamplers.Structured

end StructuredLogCostFragments

section LogCostRAMRanges

namespace TargetedSamplers.Structured

/-- An ascending loop can charge each iteration separately. A cumulative cost
bound permits output-sensitive enumeration even when one trial returns many words. -/
theorem forRange_exec_budget {τ : Tapes} {b : ℕ} (ptr stop one lo count : ℕ) (budget : ℕ → ℕ) (body : Cmd)
    (state : ℕ → Store → Prop)
    (control : ∀ i ≤ count, ∀ s, state i s → s.mem ptr = lo+i ∧ s.mem stop = lo+count)
    (bodyRun : ∀ i < count, ∀ s, state i s → s.Fits b →
      ∃ u k, Exec τ (fun st => st.Fits b) body s u k ∧ budget i+k+3 ≤ budget (i+1) ∧ u.mem ptr = lo+i ∧ u.mem one = 1 ∧
        state (i+1) (u.write ptr (lo+i+1)))
    (width : (lo+count).size ≤ b) (s : Store) (start : state 0 s) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) s t j ∧
      budget 0+j ≤ budget count+1 ∧ state count t := by
  have run (left i : ℕ) (he : i+left = count) (u : Store) (hi : state i u) (hf : u.Fits b) :
      ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) u t j ∧
        budget i+j ≤ budget count+1 ∧ state count t := by
    induction left generalizing i u with
    | zero =>
      have eq : i = count := by omega
      obtain ⟨hp,hs⟩ := control i (by omega) u hi
      exact ⟨u,1,.done (by rw [hs,hp,eq]),by rw [eq],eq ▸ hi⟩
    | succ left ih =>
      obtain ⟨hp,hs⟩ := control i (by omega) u hi
      obtain ⟨v,k,ex,hk,hp',h1,hn⟩ := bodyRun i (by omega) u hi hf
      have hnext : (Op.add ptr ptr one).eval τ v = v.write ptr (lo+i+1) := by simp [Op.eval,hp',h1]
      have hiw := (Nat.size_le_size (show lo+i+1 ≤ lo+count by omega)).trans width
      have inc : Exec τ (fun st => st.Fits b) (.op (.add ptr ptr one)) v (v.write ptr (lo+i+1)) 1 := by
        simpa only [hnext] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) v (.add ptr ptr one)
          (by rw [hnext]; exact Store.write_fits (ex.post hf) ptr hiw))
      obtain ⟨t,j,loop,hj,ret⟩ := ih (i+1) (by omega) _ hn (inc.post (ex.post hf))
      refine ⟨t,_,.again (by rw [hs,hp]; omega) (ex.seq inc) loop,?_,ret⟩
      omega
  exact run count 0 (by simp) s start fit

/-- A constant bound on the loop body gives three further primitive instructions
per iteration for the comparison, increment and back edge. -/
theorem forRange_exec {τ : Tapes} {b : ℕ} (ptr stop one lo count bound : ℕ) (body : Cmd)
    (state : ℕ → Store → Prop)
    (control : ∀ i ≤ count, ∀ s, state i s → s.mem ptr = lo+i ∧ s.mem stop = lo+count)
    (bodyRun : ∀ i < count, ∀ s, state i s → s.Fits b →
      ∃ u k, Exec τ (fun st => st.Fits b) body s u k ∧ k ≤ bound ∧ u.mem ptr = lo+i ∧ u.mem one = 1 ∧
        state (i+1) (u.write ptr (lo+i+1)))
    (width : (lo+count).size ≤ b) (s : Store) (start : state 0 s) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) s t j ∧
      j ≤ count*(bound+3)+1 ∧ state count t := by
  obtain ⟨t,j,run,cost,final⟩ := forRange_exec_budget (τ := τ) ptr stop one lo count
    (fun i => i*(bound+3)) body state control (fun i hi u hu fu => by
      obtain ⟨v,k,ex,work,ptr,unit,next⟩ := bodyRun i hi u hu fu
      exact ⟨v,k,ex,by rw [Nat.succ_mul]; omega,ptr,unit,next⟩) width s start fit
  exact ⟨t,j,run,by simpa using cost,final⟩

/-- The outer loop pays once per trial and once per returned word. The result keeps
both counts separate so that a cap on their total gives a linear trial budget. -/
theorem forRange_exec_reported {τ : Tapes} {b : ℕ} (ptr stop one count setup perWord : ℕ)
    (reports : ℕ → ℕ) (body : Cmd) (state : ℕ → Store → Prop)
    (control : ∀ i ≤ count, ∀ s, state i s → s.mem ptr=i ∧ s.mem stop=count)
    (bodyRun : ∀ i < count, ∀ s, state i s → s.Fits b →
      ∃ u k, Exec τ (fun st => st.Fits b) body s u k ∧ k ≤ setup+reports i*perWord ∧
        u.mem ptr=i ∧ u.mem one=1 ∧ state (i+1) (u.write ptr (i+1)))
    (width : count.size ≤ b) (s : Store) (start : state 0 s) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) s t j ∧
      j ≤ count*(setup+3)+prefixReports reports count*perWord+1 ∧ state count t := by
  let budget := fun i => i*(setup+3)+prefixReports reports i*perWord
  obtain ⟨t,j,ex,cost,post⟩ := forRange_exec_budget (τ := τ) ptr stop one 0 count budget body state
    (by simpa only [Nat.zero_add] using control) (fun i hi u hu fu => by
      obtain ⟨v,k,run,work,ptr,unit,next⟩ := bodyRun i hi u hu fu
      refine ⟨v,k,run,?_,by simpa using ptr,unit,by simpa using next⟩
      simp only [budget,prefixReports,Nat.succ_mul,Nat.add_mul]
      omega) (by simpa using width) s start fit
  exact ⟨t,j,ex,by simpa [budget,prefixReports] using cost,post⟩

def fillRange (ptr stop one value : ℕ) : Cmd := forRange ptr stop one (.op (.store ptr value))

/-- Fill exactly the specified consecutive addresses in an arbitrary surrounding store.
The cursor is advanced to the end; other caller registers and all other cells are framed. -/
theorem fillRange_exec {τ : Tapes} {b : ℕ} (ptr stop one value lo count : ℕ) (s : Store)
    (init : s.mem ptr = lo) (endAt : s.mem stop = lo+count) (unit : s.mem one = 1)
    (distinct : ptr ≠ stop ∧ ptr ≠ one ∧ ptr ≠ value)
    (sep : ptr < lo ∧ stop < lo ∧ one < lo ∧ value < lo) (fit : s.Fits b) (width : (lo+count).size ≤ b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (fillRange ptr stop one value) s t j ∧ j ≤ 4*count+1 ∧
      t.mem ptr = lo+count ∧ t.out = s.out ∧
      ∀ a, a ≠ ptr → t.mem a = if lo ≤ a ∧ a < lo+count then s.mem value else s.mem a := by
  let state (i : ℕ) (u : Store) : Prop :=
    u.mem ptr = lo+i ∧ u.out = s.out ∧
      ∀ a, a ≠ ptr → u.mem a = if lo ≤ a ∧ a < lo+i then s.mem value else s.mem a
  obtain ⟨dstop,done',dval⟩ := distinct
  obtain ⟨lp,ls,lu,lv⟩ := sep
  have ctrl (i : ℕ) (_ : i ≤ count) (u : Store) (h : state i u) :
      u.mem ptr = lo+i ∧ u.mem stop = lo+count := by
    exact ⟨h.1,by rw [h.2.2 stop dstop.symm, if_neg (by omega), endAt]⟩
  have body (i : ℕ) (_ : i < count) (u : Store) (h : state i u) (hf : u.Fits b) :
      ∃ v k, Exec τ (fun st => st.Fits b) (.op (.store ptr value)) u v k ∧ k ≤ 1 ∧
        v.mem ptr = lo+i ∧ v.mem one = 1 ∧ state (i+1) (v.write ptr (lo+i+1)) := by
    have val : u.mem value = s.mem value := by rw [h.2.2 value dval.symm, if_neg (by omega)]
    let v := u.write (lo+i) (s.mem value)
    have ev : (Op.store ptr value).eval τ u = v := by simp [Op.eval,v,h.1,val]
    have ex : Exec τ (fun st => st.Fits b) (.op (.store ptr value)) u v 1 := by
      simpa only [ev] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) u (.store ptr value)
        (by rw [ev]; exact Store.write_fits hf _ (fit value)))
    refine ⟨v,1,ex,le_rfl,?_,?_,?_,h.2.1,?_⟩
    · simpa [v,Store.write,show ptr ≠ lo+i by omega] using h.1
    · simp [v,Store.write,show one ≠ lo+i by omega,h.2.2 one done'.symm,show ¬lo ≤ one by omega,unit]
    · simp [Store.write,Nat.add_assoc]
    · intro a ha
      by_cases eq : a = lo+i
      · subst a
        simp [v,Store.write,show lo+i ≠ ptr by omega,show lo ≤ lo+i by omega,show lo+i < lo+(i+1) by omega]
      · simp only [Store.write, Function.update_of_ne ha, v, Function.update_of_ne eq]
        have same : (lo ≤ a ∧ a < lo+i) ↔ (lo ≤ a ∧ a < lo+(i+1)) := by omega
        rw [h.2.2 a ha]
        simp only [same]
  have first : state 0 s := ⟨by simpa using init,rfl,fun a _ => by simp⟩
  obtain ⟨t,j,ex,hj,post⟩ := forRange_exec (τ := τ) ptr stop one lo count 1 (.op (.store ptr value))
    state ctrl body width s first fit
  exact ⟨t,j,ex,by omega,post⟩

end TargetedSamplers.Structured

end LogCostRAMRanges

section LogCostRAMScale

namespace TargetedSamplers.Structured.Word

theorem addRepeatedly_exec {τ : Tapes} (r : Fin 5 ↪ ℕ) {b : ℕ} (n v a : ℕ) (s : Store)
    (count : s.mem (r 0) = n) (value : s.mem (r 1) = v) (acc : s.mem (r 2) = a)
    (zero : s.mem (r 3) = 0) (one : s.mem (r 4) = 1) (fit : s.Fits b) (width : (a+n*v).size ≤ b) :
    ∃ t, Exec τ (fun st => st.Fits b) (addRepeatedly r) s t (4*n+1) ∧ t.mem (r 0) = 0 ∧
      t.mem (r 2) = a+n*v ∧ t.out = s.out ∧ ∀ k, k ≠ r 0 → k ≠ r 2 → t.mem k = s.mem k := by
  have ne {i j : Fin 5} (h : i ≠ j) := r.injective.ne h
  induction n generalizing s a with
  | zero => exact ⟨s,.done (by rw [count,zero]),count,by simpa using acc,rfl,fun _ _ _ => rfl⟩
  | succ n ih =>
    let u := s.write (r 2) (a+v)
    let t := u.write (r 0) n
    have put : (Op.add (r 2) (r 2) (r 1)).eval τ s = u := by simp [Op.eval,u,acc,value]
    have total : a+v+n*v = a+(n+1)*v := by rw [Nat.succ_mul]; omega
    have w := (Nat.size_le_size (show a+v ≤ a+(n+1)*v by omega)).trans width
    have fu : u.Fits b := Store.write_fits fit _ w
    have ex : Exec τ (fun st => st.Fits b) (.op (.add (r 2) (r 2) (r 1))) s u 1 := by
      simpa only [put] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) s (.add (r 2) (r 2) (r 1)) (by rwa [put]))
    have prior (i : Fin 5) (h : i ≠ 2) : u.mem (r i) = s.mem (r i) := by simp [u,Store.write,ne h]
    have dec : (Op.sub (r 0) (r 0) (r 4)).eval τ u = t := by
      simp [Op.eval,t,prior 0 (by decide),prior 4 (by decide),count,one]
    have wn := (Nat.size_le_size (show n ≤ n+1 by omega)).trans (count ▸ fit (r 0))
    have ft : t.Fits b := Store.write_fits fu _ wn
    have ed : Exec τ (fun st => st.Fits b) (.op (.sub (r 0) (r 0) (r 4))) u t 1 := by
      simpa only [dec] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) u (.sub (r 0) (r 0) (r 4)) (by rwa [dec]))
    have kept (k : ℕ) (h0 : k ≠ r 0) (h2 : k ≠ r 2) : t.mem k = s.mem k := by simp [t,u,Store.write,h0,h2]
    obtain ⟨z,loop,zc,zv,out,frame⟩ := ih (a+v) t (by simp [t,Store.write]) ((kept _ (ne (by decide)) (ne (by decide))).trans value)
      (by simp [t,u,Store.write,ne (by decide : (2:Fin 5) ≠ 0)]) ((kept _ (ne (by decide)) (ne (by decide))).trans zero)
      ((kept _ (ne (by decide)) (ne (by decide))).trans one) ft (by rwa [total])
    have g : ¬s.mem (r 0) ≤ s.mem (r 3) := by rw [count,zero]; omega
    refine ⟨z,?_,zc,zv.trans total,out,fun k h0 h2 => (frame k h0 h2).trans (kept k h0 h2)⟩
    rw [show 4*(n+1)+1 = 1+(1+1)+1+(4*n+1) by omega]
    exact .again g (ex.seq ed) loop

end TargetedSamplers.Structured.Word

end LogCostRAMScale

section AffinePrefixEnumeration

/-! Output-sensitive enumeration of affine Boolean systems using the registered Gaussian counter. -/

namespace AffinePrefixEnumeration

open EditGV897.Main BoundedEnumeration

def wordBits {n : ℕ} (x : Word n) : List Bool := List.ofFn fun i => finTwoEquiv (x i)

@[simp] theorem length_wordBits {n : ℕ} (x : Word n) : (wordBits x).length = n := by simp [wordBits]

private theorem dot_unit {n : ℕ} (x : Word n) (i : Fin n) :
    dot (unitWord n i.val) x = x i := by
  simp [dot, unitWord, ← Fin.ext_iff, ite_mul]

private theorem pins_iff {n k : ℕ} (x : Word n) (p : List Bool) (hlen : k+p.length = n) :
    (∀ e ∈ pins n k p, equationHolds e x) ↔ (wordBits x).drop k = p := by
  have hp (j : Fin p.length) : k+j.val < n := by have := j.isLt; omega
  have he (j : Fin p.length) : equationHolds (unitWord n (k+j.val), finTwoEquiv.symm p[j.val]) x ↔
      finTwoEquiv (x ⟨k+j.val,hp j⟩) = p[j.val] := by
    change dot (unitWord n (k+j.val)) x = _ ↔ _
    rw [dot_unit x ⟨k+j.val,hp j⟩]
    exact finTwoEquiv.eq_symm_apply
  have hs : (∀ e ∈ pins n k p, equationHolds e x) ↔
      ∀ j : Fin p.length, finTwoEquiv (x ⟨k+j.val,hp j⟩) = p[j.val] := by
    simp [pins, he]
  rw [hs]
  constructor
  · intro h
    apply List.ext_getElem (by simp; omega)
    intro j _ hj
    simpa [wordBits, List.getElem_drop] using h ⟨j,hj⟩
  · intro h j
    have hx := congrArg (fun a : List Bool => a[j.val]?) h
    have h₁ : j.val < ((wordBits x).drop k).length := by simp; omega
    simpa [List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem j.isLt, hp j, wordBits, List.getElem_drop] using hx

/-- The same fixed published multitape program serves every feasible-prefix query. The
number of its input equations is |E|+|p|, including all pinned coordinates. -/
theorem uniform_count_program : ∃ (P : Program) (A d : ℕ), 0 < A ∧
    ∀ (n : ℕ) (E : List (Equation n)) (k : ℕ) (p : List Bool),
      Runs P (unary n ++ equationCode (E ++ pins n k p)) (binary (affineCount (E ++ pins n k p)))
        (polyBudget A d (n + (E.length+p.length))) := by
  obtain ⟨P,A,d,hA,hP⟩ := affine_counter_program
  exact ⟨P,A,d,hA,fun n E k p => by simpa [pins] using hP n (E ++ pins n k p)⟩

end AffinePrefixEnumeration

end AffinePrefixEnumeration

section AffineQueryEncoding

namespace AffinePrefixEnumeration

open EditGV897.Main

/-- A pinned coordinate can be emitted with a single column equality test. -/
def pinPayload (n index : ℕ) (val : Bool) :=
  (List.ofFn fun col : Fin n => decide (col.val = index)) ++ [val]

def queryPayload {n : ℕ} (E : List (Equation n)) (k : ℕ) (p : List Bool) : List Bool :=
  unary n ++ unary (E.length+p.length) ++ E.flatMap rowPayload ++
    (List.finRange p.length).flatMap fun j => pinPayload n (k+j.val) p[j.val]

private theorem finite_word {n : ℕ} (x : Word n) :
    wordCode x = List.ofFn (fun i => decide (x i ≠ 0)) := by
  simp [wordCode,bitCode,wordList,DeletionHash.MixedEdit.letters,Function.comp_def]

private theorem code_pin (n k : ℕ) (b : Bool) :
    rowPayload (unitWord n k,finTwoEquiv.symm b) = pinPayload n k b := by
  have hc (i : Fin n) : decide (unitWord n k i ≠ 0) = decide (i.val = k) := by
    by_cases he : i.val = k <;> simp [unitWord,he]
  have hb : decide (finTwoEquiv.symm b ≠ 0) = b := by cases b <;> decide
  simp only [rowPayload,pinPayload,hc]
  exact congrArg (fun v => (List.ofFn fun i : Fin n => decide (i.val = k)) ++ [v]) hb

/-- Generating the two unary headers, the dense input rows, and the pin rows produces
the exact bit string accepted by the public Gaussian-elimination theorem. -/
theorem queryPayload_eq {n : ℕ} (E : List (Equation n)) (k : ℕ) (p : List Bool) :
    queryPayload E k p = unary n ++ equationCode (E ++ pins n k p) := by
  have he (e : Equation n) : wordCode e.1 ++ [decide (e.2 ≠ 0)] = rowPayload e := by
    simp [rowPayload,finite_word]
  have hpin : (pins n k p).flatMap rowPayload =
      (List.finRange p.length).flatMap fun j => pinPayload n (k+j.val) p[j.val] := by
    rw [pins,List.ofFn_eq_map]
    simp [List.flatMap_map,Function.comp_def,code_pin]
  have hlen : (pins n k p).length = p.length := by simp [pins]
  simp only [queryPayload,equationCode,List.length_append,List.flatMap_append,he,List.append_assoc,hpin,hlen]

theorem queryPayload_length {n : ℕ} (E : List (Equation n)) (k : ℕ) (p : List Bool) :
    (queryPayload E k p).length = n+2+(E.length+p.length)*(n+2) := by
  have h (es : List (Equation n)) : (es.flatMap rowPayload).length = es.length*(n+1) := by
    induction es with
    | nil => simp
    | cons e es ih => simp [rowPayload,List.flatMap_cons,Nat.succ_mul] at *; omega
  have pin (is : List (Fin p.length)) :
      (is.flatMap fun j => pinPayload n (k+j.val) p[j.val]).length = is.length*(n+1) := by
    induction is with
    | nil => simp
    | cons j js ih => simp [pinPayload,List.flatMap_cons,Nat.succ_mul] at *; omega
  simp only [queryPayload,List.length_append,unary,List.length_replicate,List.length_singleton,h,
    pin,List.length_finRange]
  ring

/-- The encoding buffer fits a quadratic bound in the dimension and number of rows. -/
theorem queryPayload_size {n : ℕ} (E : List (Equation n)) (k : ℕ) (p : List Bool) :
    (queryPayload E k p).length ≤ 4*(n+(E.length+p.length)+1)^2 := by
  rw [queryPayload_length]
  nlinarith [Nat.zero_le (n*n),Nat.zero_le ((E.length+p.length)*(E.length+p.length))]

end AffinePrefixEnumeration

end AffineQueryEncoding

section LogCostRAMEmit

namespace TargetedSamplers.Structured

/-- Writing a buffer specifies its exact contents and frames the rest of the store
apart from an explicitly described set of scalar registers. -/
structure Wrote (dirty : ℕ → Prop) (base : ℕ) (xs : List ℕ) (s t : Store) : Prop where
  data : ∀ i (hi : i < xs.length), t.mem (base+i) = xs[i]
  frame : ∀ a, ¬dirty a → (a < base ∨ base+xs.length ≤ a) → t.mem a = s.mem a
  output : t.out = s.out

theorem Wrote.weaken {d e : ℕ → Prop} {base xs s t} (h : Wrote d base xs s t)
    (incl : ∀ a, d a → e a) : Wrote e base xs s t :=
  ⟨h.data,fun a clean => h.frame a (fun v => clean (incl a v)),h.output⟩

theorem Wrote.append {dirty : ℕ → Prop} {base xs ys s t u}
    (h : Wrote dirty base xs s t) (k : Wrote dirty (base+xs.length) ys t u)
    (clean : ∀ i < xs.length, ¬dirty (base+i)) : Wrote dirty base (xs++ys) s u := by
  refine ⟨?_,?_,k.output.trans h.output⟩
  · intro i hi
    simp only [List.length_append] at hi
    by_cases left : i < xs.length
    · rw [k.frame _ (clean i left) (.inl (by omega)),h.data i left,List.getElem_append_left left]
    · have rest : i-xs.length < ys.length := by omega
      rw [List.getElem_append_right (by omega),
        show base+i = base+xs.length+(i-xs.length) by omega,k.data _ rest]
  · intro a free bound
    simp only [List.length_append] at bound
    exact (k.frame a free (by omega)).trans (h.frame a free (by omega))

/-- Append count copies of a word followed by one delimiter. Registers in order
are the destination cursor, count, stop, one, repeated word, and delimiter. -/
def emitRun (r : Fin 6 ↪ ℕ) : Cmd := .seq (.op (.add (r 2) (r 0) (r 1)))
  (.seq (fillRange (r 0) (r 2) (r 3) (r 4))
    (.seq (.op (.store (r 0) (r 5))) (.op (.add (r 0) (r 0) (r 3)))))

theorem emitRun_exec {τ : Tapes} (r : Fin 6 ↪ ℕ) {b : ℕ} (base n x z : ℕ) (s : Store)
    (ptr : s.mem (r 0) = base) (count : s.mem (r 1) = n) (unit : s.mem (r 3) = 1)
    (rep : s.mem (r 4) = x) (delim : s.mem (r 5) = z) (sep : ∀ i, r i < base)
    (fit : s.Fits b) (width : (base+n+1).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (emitRun r) s t j ∧ j ≤ 4*n+4 ∧
      t.mem (r 0) = base+n+1 ∧
      Wrote (fun a => a = r 0 ∨ a = r 2) base (List.replicate n x ++ [z]) s t := by
  have ne {i j : Fin 6} (h : i ≠ j) := r.injective.ne h
  let v := s.write (r 2) (base+n)
  have endWidth := (Nat.size_le_size (Nat.le_succ (base+n))).trans width
  have fv : v.Fits b := Store.write_fits fit _ endWidth
  have initEval : (Op.add (r 2) (r 0) (r 1)).eval τ s = v := by simp [Op.eval,v,ptr,count]
  have init : Exec τ (fun u => u.Fits b) (.op (.add (r 2) (r 0) (r 1))) s v 1 := by
    simpa only [initEval] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) s (.add (r 2) (r 0) (r 1)) (by rwa [initEval]))
  have before (a : ℕ) (h : a ≠ r 2) : v.mem a = s.mem a := by simp [v,Store.write,h]
  obtain ⟨u,j,loop,bound,pos,out,write⟩ := fillRange_exec (τ := τ) (r 0) (r 2) (r 3) (r 4) base n v
    ((before _ (ne (by decide))).trans ptr) (by simp [v,Store.write]) ((before _ (ne (by decide))).trans unit)
    ⟨ne (by decide),ne (by decide),ne (by decide)⟩ ⟨sep 0,sep 2,sep 3,sep 4⟩ fv endWidth
  have vs : v.mem (r 4) = x := (before _ (ne (by decide))).trans rep
  have spare (i : Fin 6) (h₀ : i ≠ 0) (h₂ : i ≠ 2) : u.mem (r i) = s.mem (r i) := by
    rw [write _ (ne h₀),if_neg (by have := sep i; omega),before _ (ne h₂)]
  let w := u.write (base+n) z
  let t := w.write (r 0) (base+n+1)
  have fw : w.Fits b := Store.write_fits (loop.post fv) _ (delim ▸ fit (r 5))
  have ft : t.Fits b := Store.write_fits fw _ width
  have put : (Op.store (r 0) (r 5)).eval τ u = w := by
    simp [Op.eval,w,pos,(spare 5 (by decide) (by decide)).trans delim]
  have step : (Op.add (r 0) (r 0) (r 3)).eval τ w = t := by
    have unchanged (i : Fin 6) : w.mem (r i) = u.mem (r i) := by
      simp [w,Store.write,show r i ≠ base+n by have := sep i; omega]
    simp [Op.eval,t,unchanged,pos,(spare 3 (by decide) (by decide)).trans unit]
  have save : Exec τ (fun a => a.Fits b) (.op (.store (r 0) (r 5))) u w 1 := by
    simpa only [put] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) u (.store (r 0) (r 5)) (by rwa [put]))
  have advance : Exec τ (fun a => a.Fits b) (.op (.add (r 0) (r 0) (r 3))) w t 1 := by
    simpa only [step] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) w (.add (r 0) (r 0) (r 3)) (by rwa [step]))
  refine ⟨t,_,init.seq (loop.seq (save.seq advance)),by omega,by simp [t,Store.write],?_,?_,out⟩
  · intro i hi
    have h₀ : base+i ≠ r 0 := by have := sep 0; omega
    by_cases h : i < n
    · have hrep : i < (List.replicate n x).length := by simpa using h
      rw [List.getElem_append_left hrep,List.getElem_replicate]
      simp only [t,w,Store.write,Function.update_of_ne h₀,Function.update_of_ne (by omega : base+i ≠ base+n),
        write _ h₀,if_pos (by omega : base ≤ base+i ∧ base+i < base+n),vs]
    · have eq : i=n := by simp at hi; omega
      subst i
      rw [List.getElem_append_right (by simp)]
      simp [t,w,Store.write,h₀]
  · intro a free outside
    obtain ⟨h₀,h₂⟩ := not_or.mp free
    simp only [List.length_append,List.length_replicate,List.length_singleton] at outside
    simp [t,w,Store.write,h₀,show a ≠ base+n by omega,write a h₀,
      show ¬(base ≤ a ∧ a < base+n) by omega,before a h₂]

end TargetedSamplers.Structured

end LogCostRAMEmit

section LogCostRAMCopy

namespace TargetedSamplers.Structured

/-- Five distinct registers, in order: destination cursor, destination limit, unit,
source cursor, and temporary value. -/
def copyRange (reg : Fin 5 ↪ ℕ) : Cmd :=
  forRange (reg 0) (reg 1) (reg 2)
    (.seq (.op (.load (reg 4) (reg 3))) (.seq (.op (.store (reg 0) (reg 4))) (.op (.add (reg 3) (reg 3) (reg 2)))))

/-- Copy a disjoint contiguous slice, with an arbitrary starting source and destination.
The returned store preserves the source, the rest of memory, and the output. -/
theorem copyRange_exec {τ : Tapes} {b : ℕ} (reg : Fin 5 ↪ ℕ) (src dst count : ℕ) (s : Store)
    (source : s.mem (reg 3) = src) (dest : s.mem (reg 0) = dst) (stop : s.mem (reg 1) = dst+count)
    (unit : s.mem (reg 2) = 1) (separate : ∀ i, reg i < src ∧ reg i < dst)
    (disjoint : src+count ≤ dst ∨ dst+count ≤ src) (fit : s.Fits b)
    (sourceWidth : (src+count).size ≤ b) (destWidth : (dst+count).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (copyRange reg) s t j ∧ j ≤ 6*count+1 ∧
      t.mem (reg 0) = dst+count ∧ t.mem (reg 3) = src+count ∧ t.out = s.out ∧
      ∀ a, a ≠ reg 0 → a ≠ reg 3 → a ≠ reg 4 →
        t.mem a = if dst ≤ a ∧ a < dst+count then s.mem (src+(a-dst)) else s.mem a := by
  let state (i : ℕ) (u : Store) : Prop := u.mem (reg 0) = dst+i ∧ u.mem (reg 3) = src+i ∧ u.out = s.out ∧
    ∀ a, a ≠ reg 0 → a ≠ reg 3 → a ≠ reg 4 →
      u.mem a = if dst ≤ a ∧ a < dst+i then s.mem (src+(a-dst)) else s.mem a
  have distinct {i j : Fin 5} (h : i ≠ j) : reg i ≠ reg j := reg.injective.ne h
  have fixed {i : ℕ} {u : Store} (h : state i u) (a : Fin 5) (h0 : a ≠ 0) (h3 : a ≠ 3) (h4 : a ≠ 4) :
      u.mem (reg a) = s.mem (reg a) := by
    rw [h.2.2.2 (reg a) (distinct h0) (distinct h3) (distinct h4), if_neg (by have := (separate a).2; omega)]
  have ctrl (i : ℕ) (_ : i ≤ count) (u : Store) (h : state i u) :
      u.mem (reg 0) = dst+i ∧ u.mem (reg 1) = dst+count :=
    ⟨h.1,(fixed h 1 (by decide) (by decide) (by decide)).trans stop⟩
  let body := Cmd.seq (.op (.load (reg 4) (reg 3)))
    (.seq (.op (.store (reg 0) (reg 4))) (.op (.add (reg 3) (reg 3) (reg 2))))
  have work (i : ℕ) (hi : i < count) (u : Store) (h : state i u) (hf : u.Fits b) :
      ∃ v k, Exec τ (fun st => st.Fits b) body u v k ∧ k ≤ 3 ∧ v.mem (reg 0) = dst+i ∧
        v.mem (reg 2) = 1 ∧ state (i+1) (v.write (reg 0) (dst+i+1)) := by
    have ds (a : Fin 5) : dst+i ≠ reg a := by have := (separate a).2; omega
    have ss (a : Fin 5) : src+i ≠ reg a := by have := (separate a).1; omega
    have word : u.mem (src+i) = s.mem (src+i) := by
      rw [h.2.2.2 _ (ss 0) (ss 3) (ss 4), if_neg (by rcases disjoint with hd|hd <;> omega)]
    let val := s.mem (src+i)
    let u₁ := u.write (reg 4) val
    let u₂ := u₁.write (dst+i) val
    let v := u₂.write (reg 3) (src+i+1)
    have load : (Op.load (reg 4) (reg 3)).eval τ u = u₁ := by simp [Op.eval,u₁,h.2.1,word,val]
    have f₁ : u₁.Fits b := Store.write_fits hf _ (fit _)
    have e₁ : Exec τ (fun st => st.Fits b) (.op (.load (reg 4) (reg 3))) u u₁ 1 := by
      simpa only [load] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) u (.load (reg 4) (reg 3))
        (by rwa [load]))
    have save₁ (j : Fin 5) (hj : j ≠ 4) : u₁.mem (reg j) = u.mem (reg j) := by simp [u₁,Store.write,distinct hj]
    have writ : (Op.store (reg 0) (reg 4)).eval τ u₁ = u₂ := by
      simp [Op.eval,u₂,h.1,u₁,Store.write,distinct (by decide : (0:Fin 5) ≠ 4)]
    have f₂ : u₂.Fits b := Store.write_fits f₁ _ (fit _)
    have e₂ : Exec τ (fun st => st.Fits b) (.op (.store (reg 0) (reg 4))) u₁ u₂ 1 := by
      simpa only [writ] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) u₁ (.store (reg 0) (reg 4))
        (by rwa [writ]))
    have save₂ (j : Fin 5) (hj : j ≠ 4) : u₂.mem (reg j) = u.mem (reg j) := by
      simpa [u₂,Store.write,(ds j).symm] using save₁ j hj
    have unit' := (fixed h 2 (by decide) (by decide) (by decide)).trans unit
    have inc : (Op.add (reg 3) (reg 3) (reg 2)).eval τ u₂ = v := by
      simp [Op.eval,v,save₂ 3 (by decide),save₂ 2 (by decide),h.2.1,unit']
    have f₃ : v.Fits b := Store.write_fits f₂ _ ((Nat.size_le_size (show src+i+1 ≤ src+count by omega)).trans sourceWidth)
    have e₃ : Exec τ (fun st => st.Fits b) (.op (.add (reg 3) (reg 3) (reg 2))) u₂ v 1 := by
      simpa only [inc] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) u₂ (.add (reg 3) (reg 3) (reg 2))
        (by rwa [inc]))
    have save₃ (j : Fin 5) (h3 : j ≠ 3) (h4 : j ≠ 4) : v.mem (reg j) = u.mem (reg j) := by
      simpa [v,Store.write,distinct h3] using save₂ j h4
    refine ⟨v,3,e₁.seq (e₂.seq e₃),le_rfl,(save₃ 0 (by decide) (by decide)).trans h.1,
      (save₃ 2 (by decide) (by decide)).trans unit',?_,?_,h.2.2.1,?_⟩
    · simp [Store.write,Nat.add_assoc]
    · simp [v,Store.write,distinct (by decide : (3:Fin 5) ≠ 0),Nat.add_assoc]
    · intro a n0 n3 n4
      simp only [Store.write,Function.update_of_ne n0,v,Function.update_of_ne n3,u₂,u₁]
      by_cases e : a = dst+i
      · subst a; simp [val,show dst ≤ dst+i by omega,show dst+i < dst+(i+1) by omega]
      · rw [Function.update_of_ne e,Function.update_of_ne n4,h.2.2.2 a n0 n3 n4]
        have eq : (dst ≤ a ∧ a < dst+i) ↔ (dst ≤ a ∧ a < dst+(i+1)) := by omega
        simp only [eq]
  have init : state 0 s := ⟨by simpa using dest,by simpa using source,rfl,by simp⟩
  obtain ⟨t,j,ex,hj,ret⟩ := forRange_exec (τ := τ) (reg 0) (reg 1) (reg 2) dst count 3 body state ctrl work destWidth s init fit
  exact ⟨t,j,ex,by omega,ret⟩

end TargetedSamplers.Structured

end LogCostRAMCopy

section LogCostRAMQueryParts

namespace TargetedSamplers.Structured.EquationBuffer

def unaryWords (n : ℕ) : List ℕ := List.replicate n 2 ++ [1]

theorem unaryWords_length (n : ℕ) : (unaryWords n).length = n+1 := by simp [unaryWords]

private def dimRegs : Fin 6 ↪ ℕ where
  toFun i := [0,1,2,3,8,4][i.val]'(by simp [i.isLt])
  inj' := by decide

private def rowsRegs : Fin 6 ↪ ℕ where
  toFun i := [0,11,2,3,8,4][i.val]'(by simp [i.isLt])
  inj' := by decide

def emitHeaders := Cmd.seq (emitRun dimRegs) (emitRun rowsRegs)

theorem emitHeaders_exec {τ : Tapes} {b : ℕ} (base n r : ℕ) (s : Store)
    (dst : s.mem 0 = base) (dim : s.mem 1 = n) (rows : s.mem 11 = r) (one : s.mem 3 = 1)
    (falseBit : s.mem 4 = 1) (trueBit : s.mem 8 = 2) (sep : 14 < base) (fit : s.Fits b)
    (width : (base+(n+1)+(r+1)).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) emitHeaders s t j ∧ j ≤ 4*(n+r)+8 ∧
      t.mem 0 = base+(n+1)+(r+1) ∧ Wrote (fun a => a=0 ∨ a=2) base (unaryWords n ++ unaryWords r) s t := by
  have ds (i : Fin 6) : dimRegs i < base := (by decide : ∀ j : Fin 6, dimRegs j ≤ 14) i |>.trans_lt sep
  have rs (i : Fin 6) : rowsRegs i < base+(n+1) := by
    have := (by decide : ∀ j : Fin 6, rowsRegs j ≤ 14) i; omega
  obtain ⟨u,i,first,hi,pos,h₁⟩ := emitRun_exec (τ := τ) dimRegs base n 2 1 s dst dim one trueBit falseBit ds fit
    ((Nat.size_le_size (by omega)).trans width)
  change Wrote (fun a => a=0 ∨ a=2) base (unaryWords n) s u at h₁
  change u.mem 0 = base+n+1 at pos
  have preserve (a : ℕ) (ha : a ≤ 14) (h : ¬(a=0 ∨ a=2)) := h₁.frame a h (.inl (by omega))
  obtain ⟨t,j,second,hj,endAt,h₂⟩ := emitRun_exec (τ := τ) rowsRegs (base+(n+1)) r 2 1 u
    (by rw [← Nat.add_assoc]; exact pos) ((preserve 11 (by decide) (by decide)).trans rows)
    ((preserve 3 (by decide) (by decide)).trans one) ((preserve 8 (by decide) (by decide)).trans trueBit)
    ((preserve 4 (by decide) (by decide)).trans falseBit) rs (first.post fit) (by simpa only [Nat.add_assoc] using width)
  change t.mem 0 = base+(n+1)+r+1 at endAt
  change Wrote (fun a => a=0 ∨ a=2) (base+(n+1)) (unaryWords r) u t at h₂
  refine ⟨t,_,first.seq second,by omega,by omega,h₁.append ?_ ?_⟩
  · rwa [unaryWords_length]
  · intro i _; omega

private def rowCopyRegs : Fin 5 ↪ ℕ where
  toFun i := [0,2,3,12,14][i.val]'(by simp [i.isLt])
  inj' := by decide

def copyRows := Cmd.seq (.op (.add 2 0 13)) (copyRange rowCopyRegs)

theorem copyRows_exec {τ : Tapes} {b : ℕ} (base src : ℕ) (xs : List ℕ) (s : Store)
    (dest : s.mem 0 = base) (fromAddr : s.mem 12 = src) (len : s.mem 13 = xs.length) (one : s.mem 3 = 1)
    (data : ∀ i (hi : i < xs.length), s.mem (src+i) = xs[i])
    (sep : 14 < base) (source : 14 < src) (disjoint : src+xs.length ≤ base ∨ base+xs.length ≤ src)
    (fit : s.Fits b) (width : (base+xs.length).size ≤ b) (sw : (src+xs.length).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) copyRows s t j ∧ j ≤ 6*xs.length+2 ∧
      t.mem 0 = base+xs.length ∧ Wrote (fun a => a=0 ∨ a=2 ∨ a=12 ∨ a=14) base xs s t := by
  let u := s.write 2 (base+xs.length)
  have fu : u.Fits b := Store.write_fits fit _ width
  have set : (Op.add 2 0 13).eval τ s = u := by simp [Op.eval,u,dest,len]
  have init : Exec τ (fun v => v.Fits b) (.op (.add 2 0 13)) s u 1 := by
    simpa only [set] using (Exec.op (τ := τ) (inv := fun v => v.Fits b) s (.add 2 0 13) (by rwa [set]))
  have clean (a : ℕ) (h : a ≠ 2) : u.mem a = s.mem a := by simp [u,Store.write,h]
  have area (i : Fin 5) : rowCopyRegs i < src ∧ rowCopyRegs i < base := by
    have := (by decide : ∀ j : Fin 5, rowCopyRegs j ≤ 14) i; omega
  obtain ⟨t,j,cp,hj,stop,_,out,frame⟩ := copyRange_exec (τ := τ) rowCopyRegs src base xs.length u
    ((clean 12 (by decide)).trans fromAddr) ((clean 0 (by decide)).trans dest)
    (by change u.mem 2 = base+xs.length; simp [u,Store.write])
    ((clean 3 (by decide)).trans one) area disjoint fu sw width
  have atAddr (a : ℕ) (h₀ : a ≠ 0) (h₁ : a ≠ 12) (h₂ : a ≠ 14) := frame a h₀ h₁ h₂
  refine ⟨t,_,init.seq cp,by omega,stop,?_,?_,out⟩
  · intro i hi
    rw [atAddr _ (by omega) (by omega) (by omega),if_pos (by omega),
      show base+i-base = i by omega,clean _ (by omega),data i hi]
  · intro a free bounds
    simp only [not_or] at free
    rw [atAddr a free.1 free.2.2.1 free.2.2.2,if_neg (by omega),clean _ free.2.1]

end TargetedSamplers.Structured.EquationBuffer

end LogCostRAMQueryParts

section LogCostRAMPinRow

namespace TargetedSamplers.Structured.EquationBuffer

/-- One coefficient per column in the solver's ternary alphabet, followed by the RHS. -/
def pinWords (n col rhs : ℕ) : List ℕ :=
  (List.ofFn fun i : Fin n => if i.val = col then 2 else 1) ++ [rhs]

theorem pinWords_length (n col rhs : ℕ) : (pinWords n col rhs).length = n+1 := by
  simp [pinWords]

private def pinRegs : Fin 6 ↪ ℕ := Fin.valEmbedding

/-- Fill a dense unit row, append the specified RHS, and patch the pinned column.
Registers 0 through 8 contain the cursor, dimension, stop, one, false symbol,
RHS symbol, pinned column, patch address, and true symbol. -/
def emitPin : Cmd :=
  .seq (.op (.add 7 0 6)) (.seq (emitRun pinRegs) (.op (.store 7 8)))

theorem emitPin_exec {τ : Tapes} {b : ℕ} (base n col rhs : ℕ) (s : Store) (hc : col < n)
    (ptr : s.mem 0 = base) (dim : s.mem 1 = n) (unit : s.mem 3 = 1) (zeroBit : s.mem 4 = 1)
    (val : s.mem 5 = rhs) (column : s.mem 6 = col) (trueBit : s.mem 8 = 2) (sep : 8 < base)
    (fit : s.Fits b) (width : (base+n+1).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) emitPin s t j ∧ j ≤ 4*n+6 ∧ t.mem 0 = base+n+1 ∧
      Wrote (fun a => a=0 ∨ a=2 ∨ a=7) base (pinWords n col rhs) s t := by
  let v := s.write 7 (base+col)
  have fv : v.Fits b := Store.write_fits fit _ ((Nat.size_le_size (by omega)).trans width)
  have addr : (Op.add 7 0 6).eval τ s = v := by simp [Op.eval,v,ptr,column]
  have start : Exec τ (fun u => u.Fits b) (.op (.add 7 0 6)) s v 1 := by
    simpa only [addr] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) s (.add 7 0 6) (by rwa [addr]))
  have unchanged (i : ℕ) (h : i ≠ 7) : v.mem i = s.mem i := by simp [v,Store.write,h]
  obtain ⟨u,k,run,hk,after,words⟩ := emitRun_exec (τ := τ) pinRegs base n 1 rhs v
    ((unchanged 0 (by decide)).trans ptr) ((unchanged 1 (by decide)).trans dim)
    ((unchanged 3 (by decide)).trans unit) ((unchanged 4 (by decide)).trans zeroBit)
    ((unchanged 5 (by decide)).trans val) (by intro i; change i.val < base; have := i.isLt; omega) fv width
  have saved : u.mem 7 = base+col := (words.frame 7 (by decide) (.inl (by omega))).trans (by simp [v,Store.write])
  have two : u.mem 8 = 2 := (words.frame 8 (by decide) (.inl sep)).trans ((unchanged 8 (by decide)).trans trueBit)
  let t := u.write (base+col) 2
  have ft : t.Fits b := Store.write_fits (run.post fv) _ (trueBit ▸ fit 8)
  have patch : (Op.store 7 8).eval τ u = t := by simp [Op.eval,t,saved,two]
  have put : Exec τ (fun v => v.Fits b) (.op (.store 7 8)) u t 1 := by
    simpa only [patch] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) u (.store 7 8) (by rwa [patch]))
  refine ⟨t,_,start.seq (run.seq put),by omega,?_,?_,?_,words.output⟩
  · change u.mem 0 = base+n+1 at after
    simpa [t,Store.write,show 0 ≠ base+col by omega] using after
  · intro i hi
    have hi' : i < n+1 := by simpa only [pinWords_length] using hi
    have h₀ : i < (List.replicate n 1 ++ [rhs]).length := by simpa using hi'
    have mem := words.data i h₀
    by_cases h : i < n
    · simp only [pinWords,List.getElem_append,List.length_ofFn,dif_pos h,List.getElem_ofFn]
      simp only [List.getElem_append,List.length_replicate,dif_pos h,List.getElem_replicate] at mem
      by_cases eq : i=col
      · subst i; simp [t,Store.write]
      · simp only [t,Store.write,Function.update_of_ne (by omega : base+i ≠ base+col),if_neg eq,mem]
    · have eq : i=n := by omega
      subst i
      simp [pinWords,List.getElem_append_right,t,Store.write,show n ≠ col by omega] at mem ⊢
      exact mem
  · intro a free outside
    rw [pinWords_length] at outside
    have noPatch : a ≠ base+col := by omega
    have clean : a ≠ 0 ∧ a ≠ 2 ∧ a ≠ 7 := by tauto
    rw [show t.mem a = u.mem a by simp [t,Store.write,noPatch],
      words.frame a (not_or.mpr ⟨clean.1,clean.2.1⟩) (by simpa using outside),unchanged a clean.2.2]

end TargetedSamplers.Structured.EquationBuffer

end LogCostRAMPinRow

section LogCostRAMPinList

namespace TargetedSamplers.Structured.EquationBuffer

def pinBlock (n k : ℕ) : List ℕ → List ℕ
  | [] => []
  | x::xs => pinWords n k x ++ pinBlock n (k+1) xs

theorem pinBlock_length (n k : ℕ) (xs : List ℕ) : (pinBlock n k xs).length = xs.length*(n+1) := by
  induction xs generalizing k with
  | nil => simp [pinBlock]
  | cons x xs ih => simp [pinBlock,pinWords_length,ih,Nat.succ_mul,Nat.add_comm]

abbrev pinScratch (a : ℕ) := a=0 ∨ a=2 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=9

private def pinIteration : Cmd := .seq (.op (.load 5 9))
  (.seq emitPin (.seq (.op (.add 6 6 3)) (.op (.add 9 9 3))))

/-- Emit successive fixed-coordinate equations from a disjoint array of right-hand sides. -/
def emitPins : Cmd := .whileGt 10 9 pinIteration

private theorem pinIteration_exec {τ : Tapes} {b : ℕ} (base src n col rhs : ℕ) (s : Store) (hc : col < n)
    (dst : s.mem 0 = base) (dim : s.mem 1 = n) (unit : s.mem 3 = 1) (zeroBit : s.mem 4 = 1)
    (column : s.mem 6 = col) (trueBit : s.mem 8 = 2) (fromAddr : s.mem 9 = src) (val : s.mem src = rhs)
    (sep : 10 < base) (fit : s.Fits b) (width : (base+n+1).size ≤ b)
    (sw : (src+1).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) pinIteration s t j ∧ j ≤ 4*n+9 ∧
      t.mem 0 = base+n+1 ∧ t.mem 6 = col+1 ∧ t.mem 9 = src+1 ∧ Wrote pinScratch base (pinWords n col rhs) s t := by
  let v := s.write 5 rhs
  have fv : v.Fits b := Store.write_fits fit _ (val ▸ fit src)
  have fetch : (Op.load 5 9).eval τ s = v := by simp [Op.eval,v,fromAddr,val]
  have read : Exec τ (fun u => u.Fits b) (.op (.load 5 9)) s v 1 := by
    simpa only [fetch] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) s (.load 5 9) (by rwa [fetch]))
  have before (a : ℕ) (h : a ≠ 5) : v.mem a = s.mem a := by simp [v,Store.write,h]
  obtain ⟨u,k,run,hk,next,words⟩ := emitPin_exec (τ := τ) base n col rhs v hc
    ((before 0 (by decide)).trans dst) ((before 1 (by decide)).trans dim) ((before 3 (by decide)).trans unit)
    ((before 4 (by decide)).trans zeroBit) (by simp [v,Store.write]) ((before 6 (by decide)).trans column)
    ((before 8 (by decide)).trans trueBit) (by omega) fv width
  have small (a : ℕ) (ha : a ≤ 10) (free : ¬(a=0 ∨ a=2 ∨ a=7)) (h5 : a ≠ 5) : u.mem a = s.mem a :=
    (words.frame a free (.inl (by omega))).trans (before a h5)
  have uone := (small 3 (by decide) (by decide) (by decide)).trans unit
  let w := u.write 6 (col+1)
  let t := w.write 9 (src+1)
  have bumpCol : (Op.add 6 6 3).eval τ u = w := by
    simp [Op.eval,w,(small 6 (by decide) (by decide) (by decide)).trans column,uone]
  have fw : w.Fits b := Store.write_fits (run.post fv) _ ((Nat.size_le_size (by omega)).trans width)
  have keep (a : ℕ) (ha : a ≠ 6) : w.mem a = u.mem a := by simp [w,Store.write,ha]
  have bumpSrc : (Op.add 9 9 3).eval τ w = t := by
    simp [Op.eval,t,keep 9 (by decide),keep 3 (by decide),(small 9 (by decide) (by decide) (by decide)).trans fromAddr,uone]
  have cstep : Exec τ (fun u => u.Fits b) (.op (.add 6 6 3)) u w 1 := by
    simpa only [bumpCol] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) u (.add 6 6 3) (by rwa [bumpCol]))
  have sstep : Exec τ (fun u => u.Fits b) (.op (.add 9 9 3)) w t 1 := by
    simpa only [bumpSrc] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) w (.add 9 9 3)
      (by rw [bumpSrc]; exact Store.write_fits fw _ sw))
  refine ⟨t,_,read.seq (run.seq (cstep.seq sstep)),by omega,by simpa [t,w,Store.write] using next,
    by simp [t,w,Store.write],by simp [t,Store.write],?_,?_,words.output⟩
  · intro i hi
    simpa [t,w,Store.write,show base+i ≠ 9 by omega,show base+i ≠ 6 by omega] using words.data i hi
  · intro a free bounds
    have h := free
    simp only [pinScratch,not_or] at h
    simpa [t,w,Store.write,h] using (words.frame a (by tauto) bounds).trans (before a (by tauto))

theorem emitPins_exec {τ : Tapes} {b : ℕ} (n : ℕ) (xs : List ℕ) (base src col : ℕ) (s : Store)
    (cols : col+xs.length ≤ n) (dst : s.mem 0 = base) (dim : s.mem 1 = n) (unit : s.mem 3 = 1)
    (zeroBit : s.mem 4 = 1) (column : s.mem 6 = col) (trueBit : s.mem 8 = 2) (fromAddr : s.mem 9 = src)
    (stop : s.mem 10 = src+xs.length) (data : ∀ i (hi : i < xs.length), s.mem (src+i) = xs[i])
    (sep : 10 < base) (source : 10 < src) (disjoint : src+xs.length ≤ base ∨ base+xs.length*(n+1) ≤ src)
    (fit : s.Fits b) (width : (base+xs.length*(n+1)).size ≤ b) (sw : (src+xs.length).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) emitPins s t j ∧ j ≤ xs.length*(4*n+11)+1 ∧
      t.mem 0 = base+xs.length*(n+1) ∧ t.mem 6 = col+xs.length ∧ t.mem 9 = src+xs.length ∧
      Wrote pinScratch base (pinBlock n col xs) s t := by
  induction xs generalizing base src col s with
  | nil =>
    refine ⟨s,1,.done (by simpa [stop,fromAddr]),by simp,by simpa using dst,by simpa using column,
      by simpa using fromAddr,?_,fun _ _ _ => rfl,rfl⟩
    intro i hi
    simp [pinBlock] at hi
  | cons x xs ih =>
    simp only [List.length_cons,Nat.succ_mul xs.length (n+1),Nat.succ_mul xs.length (4*n+11)] at cols stop disjoint width sw ⊢
    have rowWidth : (base+n+1).size ≤ b := (Nat.size_le_size (by omega)).trans width
    have first : s.mem src = x := by
      have head := data 0 (by simp)
      change s.mem (src+0) = x at head
      exact head
    obtain ⟨u,k,row,hk,dst',col',src',written⟩ := pinIteration_exec (τ := τ) base src n col x s (by omega)
      dst dim unit zeroBit column trueBit fromAddr first sep fit rowWidth ((Nat.size_le_size (by omega)).trans sw)
    have small (a : ℕ) (ha : a ≤ 10) (clean : ¬pinScratch a) : u.mem a = s.mem a :=
      written.frame a clean (.inl (by omega))
    have rest (i : ℕ) (hi : i < xs.length) : u.mem (src+1+i) = xs[i] := by
      have clean : ¬pinScratch (src+1+i) := by dsimp [pinScratch]; omega
      rw [written.frame _ clean (by rw [pinWords_length]; omega)]
      have atNext := data (i+1) (by simpa using hi)
      change s.mem (src+(i+1)) = xs[i] at atNext
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using atNext
    have len : base+n+1+xs.length*(n+1) = base+(xs.length*(n+1)+(n+1)) := by omega
    obtain ⟨t,j,loop,hj,last,atCol,atSrc,result⟩ := ih (base+n+1) (src+1) (col+1) u (by omega) dst'
      ((small 1 (by decide) (by decide)).trans dim) ((small 3 (by decide) (by decide)).trans unit)
      ((small 4 (by decide) (by decide)).trans zeroBit) col' ((small 8 (by decide) (by decide)).trans trueBit) src'
      (by rw [small 10 (by decide) (by decide),stop]; omega) rest (by omega) (by omega) (by omega)
      (row.post fit) (by rwa [len]) (by rwa [show src+1+xs.length = src+(xs.length+1) by omega])
    have guard : ¬s.mem 10 ≤ s.mem 9 := by rw [stop,fromAddr]; omega
    have adj : Wrote pinScratch (base+(pinWords n col x).length) (pinBlock n (col+1) xs) u t := by
      simpa only [pinWords_length,Nat.add_assoc] using result
    refine ⟨t,_,.again guard row loop,by omega,last.trans len,by omega,by omega,written.append adj ?_⟩
    intro i _
    dsimp [pinScratch]; omega

end TargetedSamplers.Structured.EquationBuffer

end LogCostRAMPinList

section LogCostRAMQueryWriter

namespace TargetedSamplers.Structured.EquationBuffer

/-- Serialize two unary headers, a stored dense matrix, and the equations fixing
successive coordinates of a search prefix. Right-hand sides use the solver's alphabet. -/
def writeQuery : Cmd := .seq emitHeaders (.seq copyRows emitPins)

def queryWords (n rows col : ℕ) (dense rhs : List ℕ) : List ℕ :=
  ((unaryWords n ++ unaryWords rows) ++ dense) ++ pinBlock n col rhs

theorem queryWords_length (n rows col : ℕ) (dense rhs : List ℕ) :
    (queryWords n rows col dense rhs).length = ((n+1)+(rows+1))+dense.length+rhs.length*(n+1) := by
  simp only [queryWords,List.length_append,unaryWords_length,pinBlock_length]

/-- The output takes at most eleven primitive steps per buffer word plus three fixed
steps. Arbitrary stale buffer contents are overwritten and all other heap words persist. -/
theorem writeQuery_exec {τ : Tapes} {b : ℕ} (n rows col base rowSrc pinSrc : ℕ)
    (dense rhs : List ℕ) (s : Store) (cols : col+rhs.length ≤ n)
    (dst : s.mem 0 = base) (dim : s.mem 1 = n) (one : s.mem 3 = 1) (zeroBit : s.mem 4 = 1)
    (column : s.mem 6 = col) (trueBit : s.mem 8 = 2) (rsrc : s.mem 12 = rowSrc)
    (rlen : s.mem 13 = dense.length) (rnum : s.mem 11 = rows) (psrc : s.mem 9 = pinSrc)
    (pstop : s.mem 10 = pinSrc+rhs.length)
    (rd : ∀ i (hi : i < dense.length), s.mem (rowSrc+i) = dense[i])
    (pd : ∀ i (hi : i < rhs.length), s.mem (pinSrc+i) = rhs[i])
    (sep : 14 < base) (sr : 14 < rowSrc) (sp : 14 < pinSrc) (fit : s.Fits b)
    (rowWidth : (rowSrc+dense.length).size ≤ b) (pinWidth : (pinSrc+rhs.length).size ≤ b) :
    let xs := queryWords n rows col dense rhs
    (rowSrc+dense.length ≤ base ∨ base+xs.length ≤ rowSrc) →
    (pinSrc+rhs.length ≤ base ∨ base+xs.length ≤ pinSrc) → (base+xs.length).size ≤ b →
    ∃ t j, Exec τ (fun u => u.Fits b) writeQuery s t j ∧ j ≤ 11*xs.length+3 ∧
      t.mem 0 = base+xs.length ∧ Wrote (fun a => a < 15) base xs s t := by
  intro xs rowApart pinApart width
  let H := (n+1)+(rows+1)
  let R := rhs.length*(n+1)
  have hl : (unaryWords n ++ unaryWords rows).length = H := by simp [H,unaryWords_length]
  have len : xs.length = H+dense.length+R := queryWords_length ..
  have short (v : ℕ) (hv : v ≤ base+xs.length) := (Nat.size_le_size hv).trans width
  obtain ⟨u,i,header,hi,pos,head⟩ := emitHeaders_exec (τ := τ) base n rows s dst dim rnum one zeroBit trueBit
    sep fit (short _ (by rw [len]; dsimp [H]; omega))
  have uh : u.mem 0 = base+H := by simpa only [H,Nat.add_assoc] using pos
  have fixedH (a : ℕ) (ha : a ≤ 14) (clean : ¬(a=0 ∨ a=2)) : u.mem a = s.mem a :=
    head.frame a clean (.inl (by omega))
  have rowData (i : ℕ) (hi : i < dense.length) : u.mem (rowSrc+i) = dense[i] := by
    rw [head.frame _ (by omega) (by rw [hl]; omega),rd i hi]
  obtain ⟨v,k,copy,hk,endDense,matrix⟩ := copyRows_exec (τ := τ) (base+H) rowSrc dense u uh
    ((fixedH 12 (by decide) (by decide)).trans rsrc) ((fixedH 13 (by decide) (by decide)).trans rlen)
    ((fixedH 3 (by decide) (by decide)).trans one) rowData (by omega) sr (by omega)
    (header.post fit) (short _ (by omega)) rowWidth
  have keep (a : ℕ) (ha : a ≤ 14) (clean : ¬(a=0 ∨ a=2 ∨ a=12 ∨ a=14)) : v.mem a = s.mem a :=
    (matrix.frame a clean (.inl (by omega))).trans (fixedH a ha (by tauto))
  have pinData (l : ℕ) (hl' : l < rhs.length) : v.mem (pinSrc+l) = rhs[l] := by
    rw [matrix.frame _ (by omega) (by omega),head.frame _ (by omega) (by rw [hl]; omega),pd l hl']
  obtain ⟨t,j,pins,hj,endAll,_,_,pinWords'⟩ := emitPins_exec (τ := τ) n rhs (base+H+dense.length) pinSrc col v
    cols endDense ((keep 1 (by decide) (by decide)).trans dim) ((keep 3 (by decide) (by decide)).trans one)
    ((keep 4 (by decide) (by decide)).trans zeroBit) ((keep 6 (by decide) (by decide)).trans column)
    ((keep 8 (by decide) (by decide)).trans trueBit) ((keep 9 (by decide) (by decide)).trans psrc)
    ((keep 10 (by decide) (by decide)).trans pstop) pinData (by omega) (by omega)
    (by change pinSrc+rhs.length ≤ _ ∨ _+R ≤ pinSrc; omega) (copy.post (header.post fit))
    (by change (base+H+dense.length+R).size ≤ b; apply short; omega) pinWidth
  have hW := head.weaken (e := fun a => a < 15) (by intro a h; omega)
  have dW : Wrote (fun a => a < 15) (base+(unaryWords n ++ unaryWords rows).length) dense u v := by
    rw [hl]; exact matrix.weaken (by intro a h; omega)
  have firstRows := hW.append dW (by intro l h; omega)
  have pW : Wrote (fun a => a < 15) (base+((unaryWords n ++ unaryWords rows)++dense).length)
      (pinBlock n col rhs) v t := by
    rw [List.length_append,hl,← Nat.add_assoc]
    exact pinWords'.weaken (by intro a h; dsimp [pinScratch] at h; omega)
  refine ⟨t,_,header.seq (copy.seq pins),?_,?_,firstRows.append pW (by intro l h; omega)⟩
  · have per := Nat.mul_le_mul_left rhs.length (by omega : 4*n+11 ≤ 11*(n+1))
    rw [show rhs.length*(11*(n+1)) = 11*R by dsimp [R]; ring] at per
    rw [len]; dsimp [H]; omega
  · change t.mem 0 = base+H+dense.length+R at endAll
    rw [endAll,len]; omega

end TargetedSamplers.Structured.EquationBuffer

end LogCostRAMQueryWriter

section MultitapeControl

/-! Compile a finite transition table reading a fixed tuple of ternary tape symbols. -/

namespace TargetedSamplers.Structured

def Reader.after (R : Reader) : {k : ℕ} → (Fin k → Option Bool) → Store → Store
  | 0, _, s => s
  | k+1, x, s => R.after (k := k) (fun i => x i.succ) (s.write R.tag (symbolCode (x 0)))

/-- Number of primitive data and control instructions in the symbol-selection part. -/
def symbolSteps : {k : ℕ} → (Fin k → Option Bool) → ℕ
  | 0, _ => 0
  | k+1, x => (match x 0 with | none => 2 | some false => 4 | some true => 5)
      + symbolSteps (k := k) (fun i => x i.succ)

theorem symbolSteps_le {k : ℕ} (x : Fin k → Option Bool) : symbolSteps x ≤ 5*k := by
  induction k with
  | zero => simp [symbolSteps]
  | succ k ih =>
    have h := ih fun i => x i.succ
    simp only [symbolSteps, Nat.mul_succ]
    cases x 0 with
    | none => dsimp only; omega
    | some b => cases b <;> dsimp only <;> omega

/-- Calling the selected branch reads precisely the actual tape symbols. It preserves the
store width irrespective of how large the addresses of the tape cells are. -/
theorem Reader.symbolTree_exec (R : Reader) {τ : Tapes} {b k : ℕ} (pos : Fin k → ℕ)
    (next : (Fin k → Option Bool) → Cmd) (x : Fin k → Option Bool) (s t : Store) (steps : ℕ)
    (fit : s.Fits b) (hz : s.mem R.zero = 0) (ho : s.mem R.one = 1)
    (reg : ∀ i, pos i ≠ R.tag) (addr : ∀ i, s.mem (pos i) ≠ R.tag)
    (hx : ∀ i, s.mem (s.mem (pos i)) = symbolCode (x i))
    (cont : Exec τ (fun v => v.Fits b) (next x) (R.after x s) t steps) :
    Exec τ (fun v => v.Fits b) (R.symbolTree pos next) s t (symbolSteps x + steps) := by
  induction k generalizing s with
  | zero =>
    have he : x = Fin.elim0 := Subsingleton.elim _ _
    simpa [symbolTree, symbolSteps, after, he] using cont
  | succ k ih =>
    let s' := s.write R.tag (symbolCode (x 0))
    have hload : (Op.load R.tag (pos 0)).eval τ s = s' := by simp [Op.eval, s', hx]
    have hf : s'.Fits b := Store.write_fits fit _ (by rw [← hx 0]; exact fit _)
    have instr : Exec τ (fun v => v.Fits b) (.op (.load R.tag (pos 0))) s s' 1 := by
      simpa only [hload] using (Exec.op (τ := τ) (inv := fun v => v.Fits b) s (.load R.tag (pos 0))
        (by rwa [hload]))
    have hz' : s'.mem R.zero = 0 := by simpa [s',Store.write,R.zero_ne] using hz
    have ho' : s'.mem R.one = 1 := by simpa [s',Store.write,R.one_ne] using ho
    have ht : s'.mem R.tag = symbolCode (x 0) := by simp [s',Store.write]
    have hcons : Fin.cons (x 0) (fun i => x i.succ) = x := by funext i; cases i using Fin.cases <;> rfl
    have actual := ih (fun i : Fin k => pos i.succ) (fun xs => next (Fin.cons (x 0) xs))
      (fun i => x i.succ) s' hf hz' ho' (fun i => reg i.succ)
      (fun i => by simpa [s',Store.write,reg] using addr i.succ)
      (fun i => by simpa [s',Store.write,reg,addr] using hx i.succ)
      (by simpa [hcons,s',after] using cont)
    unfold symbolTree symbolSteps
    let branch (v : Option Bool) := R.symbolTree (fun i : Fin k => pos i.succ) (fun xs => next (Fin.cons v xs))
    change Exec _ _ (.seq (.op (.load R.tag (pos 0)))
      (.branch R.tag R.zero (branch none) (.branch R.tag R.one (branch (some false)) (branch (some true))))) _ _ _
    change Exec _ _ (branch (x 0)) _ _ _ at actual
    cases h : x 0 with
    | none =>
      rw [h] at actual ht
      have g : s'.mem R.tag ≤ s'.mem R.zero := by rw [ht,hz']; decide
      convert instr.seq (Exec.yes (n := .branch R.tag R.one (branch (some false)) (branch (some true))) g actual) using 1 <;> dsimp only <;> omega
    | some v =>
      cases v with
      | false =>
        rw [h] at actual ht
        have g : ¬s'.mem R.tag ≤ s'.mem R.zero := by rw [ht,hz']; decide
        have g' : s'.mem R.tag ≤ s'.mem R.one := by rw [ht,ho']; decide
        convert instr.seq (Exec.no (y := branch none) g (Exec.yes (n := branch (some true)) g' actual)) using 1 <;> dsimp only <;> omega
      | true =>
        rw [h] at actual ht
        have g : ¬s'.mem R.tag ≤ s'.mem R.zero := by rw [ht,hz']; decide
        have g' : ¬s'.mem R.tag ≤ s'.mem R.one := by rw [ht,ho']; decide
        convert instr.seq (Exec.no (y := branch none) g (Exec.no (y := branch (some false)) g' actual)) using 1 <;> dsimp only <;> omega

theorem Reader.after_mem {k : ℕ} (R : Reader) (x : Fin k → Option Bool) (s : Store)
    {addr : ℕ} (ha : addr ≠ R.tag) : (R.after x s).mem addr = s.mem addr := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [after, ih]; simp [Store.write,ha]

theorem Reader.after_out {k : ℕ} (R : Reader) (x : Fin k → Option Bool) (s : Store) :
    (R.after x s).out = s.out := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [after, ih]; rfl

theorem Reader.after_fits {k b : ℕ} (R : Reader) (x : Fin k → Option Bool) (s : Store)
    (fit : s.Fits b) (width : ∀ i, (symbolCode (x i)).size ≤ b) : (R.after x s).Fits b := by
  induction k generalizing s with
  | zero => exact fit
  | succ k ih => exact ih _ _ (Store.write_fits fit _ (width 0)) (fun i => width i.succ)

end TargetedSamplers.Structured

end MultitapeControl

section AffineRAMSerialize

namespace AffinePrefixEnumeration

open EditGV897.Main TargetedSamplers.Structured TargetedSamplers.Structured.EquationBuffer

private theorem map_pin (n k : ℕ) (x : Bool) :
    (pinPayload n k x).map bitWord = pinWords n k (bitWord x) := by
  have atCol (i : Fin n) : bitWord (decide (i.val=k)) = if i.val=k then 2 else 1 := by
    by_cases h : i.val=k <;> simp [bitWord,symbolCode,h]
  simp only [pinPayload,pinWords,List.map_append,List.map_ofFn,List.map_cons,List.map_nil]
  congr 1
  exact congrArg List.ofFn (funext atCol)

private theorem map_pins (n k : ℕ) (p : List Bool) :
    ((List.finRange p.length).flatMap fun j => pinPayload n (k+j.val) p[j.val]).map bitWord =
      pinBlock n k (p.map bitWord) := by
  induction p generalizing k with
  | nil => simp [pinBlock]
  | cons x p ih =>
    simp only [List.length_cons,List.finRange_succ,List.flatMap_cons,List.flatMap_map,List.map_append,
      Fin.val_zero,Nat.add_zero,List.getElem_cons_zero,List.map_cons,pinBlock,map_pin]
    congr 1
    simpa [Function.comp_def,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (k+1)

/-- The RAM words are exactly the ternary input symbols required by the public solver. -/
theorem queryWords_eq {n : ℕ} (E : List (Equation n)) (k : ℕ) (p : List Bool) :
    queryWords n (E.length+p.length) k (denseWords E) (p.map bitWord) = (queryPayload E k p).map bitWord := by
  have header (r : ℕ) : (unary r).map bitWord = unaryWords r := by
    simp [unary,unaryWords,bitWord,symbolCode]
  simp only [queryPayload,queryWords,List.map_append,header,map_pins,denseWords]

/-- On entry the two sources are represented by ordinary half-open memory intervals.
The dimension, row count and next pinned column are the remaining scalar arguments. -/
structure QuerySource {n : ℕ} (E : List (Equation n)) (k : ℕ) (p : List Bool)
    (base rowSrc pinSrc : ℕ) (s : Store) : Prop where
  dest : s.mem 0 = base
  dim : s.mem 1 = n
  column : s.mem 6 = k
  pinStart : s.mem 9 = pinSrc
  pinEnd : s.mem 10 = pinSrc+p.length
  rows : s.mem 11 = E.length
  rowStart : s.mem 12 = rowSrc
  rowEnd : s.mem 13 = rowSrc+(denseWords E).length
  rowData : ∀ i (hi : i < (denseWords E).length), s.mem (rowSrc+i) = (denseWords E)[i]
  pinData : ∀ i (hi : i < p.length), s.mem (pinSrc+i) = bitWord p[i]

private def startWriter : Fragment := TargetedSamplers.Structured.sequence [
  .op (.const 3 1),.op (.const 4 1),.op (.const 8 2),
  .op (.sub 14 10 9),.op (.add 11 11 14),.op (.sub 13 13 12)]

def serializeQuery := Cmd.seq startWriter.cmd writeQuery

set_option maxHeartbeats 600000 in
theorem serializeQuery_exec {τ : TargetedSamplers.Tapes} {b n : ℕ} (E : List (Equation n)) (k : ℕ)
    (p : List Bool) (base rowSrc pinSrc : ℕ) (s : Store) (hp : k+p.length ≤ n)
    (src : QuerySource E k p base rowSrc pinSrc s) (sep : 14 < base) (sr : 14 < rowSrc) (sp : 14 < pinSrc)
    (fit : s.Fits b) (hb : 2 ≤ b) (rowWidth : (rowSrc+(denseWords E).length).size ≤ b)
    (pinWidth : (pinSrc+p.length).size ≤ b) :
    let bits := queryPayload E k p
    (rowSrc+(denseWords E).length ≤ base ∨ base+bits.length ≤ rowSrc) →
    (pinSrc+p.length ≤ base ∨ base+bits.length ≤ pinSrc) → (base+bits.length).size ≤ b →
    ∃ t j, Exec τ (fun v => v.Fits b) serializeQuery s t j ∧ j ≤ 11*bits.length+9 ∧
      t.mem 0 = base+bits.length ∧ Wrote (fun a => a < 15) base (bits.map bitWord) s t := by
  intro bits ra pa width
  let u := (startWriter.run τ s).last
  have hpin := (Nat.size_le_size (show p.length ≤ pinSrc+p.length by omega)).trans pinWidth
  have hrows : (E.length+p.length).size ≤ b := by
    apply (Nat.size_le_size ?_).trans width
    have bitsLen : bits.length = n+2+(E.length+p.length)*(n+2) := queryPayload_length ..
    have enough := Nat.mul_le_mul_left (E.length+p.length) (show 1 ≤ n+2 by omega)
    omega
  have hdata := (Nat.size_le_size (show (denseWords E).length ≤ rowSrc+(denseWords E).length by omega)).trans rowWidth
  have two : (2:ℕ).size ≤ b := (by decide : (2:ℕ).size ≤ 2).trans hb
  have bounds : (startWriter.run τ s).writeWidth ≤ b := by
    simp [startWriter,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      src.pinEnd,src.pinStart,src.rows,src.rowEnd,src.rowStart,hpin,hrows,hdata,two] <;> omega
  have init := startWriter.exec τ s b fit bounds
  have conserved (a : ℕ) (free : a ≠ 3 ∧ a ≠ 4 ∧ a ≠ 8 ∧ a ≠ 14 ∧ a ≠ 11 ∧ a ≠ 13) :
      u.mem a = s.mem a := by
    simp [u,startWriter,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,free]
  have targetRegs : u.mem 3 = 1 ∧ u.mem 4 = 1 ∧ u.mem 8 = 2 ∧
      u.mem 13 = (denseWords E).length ∧ u.mem 11 = E.length+p.length := by
    simp [u,startWriter,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      src.rowEnd,src.rowStart,src.pinEnd,src.pinStart,src.rows]
  have words := queryWords_eq E k p
  have count : (queryWords n (E.length+p.length) k (denseWords E) (p.map bitWord)).length = bits.length := by
    rw [words,List.length_map]
  obtain ⟨t,j,write,hj,atEnd,wrote⟩ := writeQuery_exec (τ := τ) n (E.length+p.length) k base rowSrc pinSrc
    (denseWords E) (p.map bitWord) u (by simpa using hp)
    ((conserved 0 (by decide)).trans src.dest) ((conserved 1 (by decide)).trans src.dim) targetRegs.1 targetRegs.2.1
    ((conserved 6 (by decide)).trans src.column) targetRegs.2.2.1 ((conserved 12 (by decide)).trans src.rowStart)
    targetRegs.2.2.2.1 targetRegs.2.2.2.2 ((conserved 9 (by decide)).trans src.pinStart)
    (by simpa using (conserved 10 (by decide)).trans src.pinEnd)
    (fun i hi => (conserved _ (by omega)).trans (src.rowData i hi))
    (fun i hi => by
      rw [conserved _ (by omega),List.getElem_map,src.pinData i (by simpa using hi)])
    sep sr sp (init.post fit) rowWidth (by simpa using pinWidth)
    (by rwa [count]) (by simpa only [List.length_map,count] using pa) (by rwa [count])
  rw [count] at hj atEnd
  rw [words] at wrote
  have six : (startWriter.run τ s).steps = 6 := rfl
  refine ⟨t,_,init.seq write,by omega,atEnd,wrote.data,?_,wrote.output⟩
  intro a free outside
  exact (wrote.frame a free outside).trans (conserved a (by omega))

end AffinePrefixEnumeration

end AffineRAMSerialize

section LogCostRAMMonomial

namespace TargetedSamplers.Structured.Word

private def seed (r : Fin 5 ↪ ℕ) (a : ℕ) : Fragment := Structured.sequence
  [.op (.const (r 3) 0),.op (.const (r 4) 1),.op (.const (r 2) a)]

private def startProduct (r : Fin 5 ↪ ℕ) (arg : ℕ) : Fragment := Structured.sequence
  [.op (.add (r 0) arg (r 3)),.op (.add (r 1) (r 2) (r 3)),.op (.const (r 2) 0)]

/-- Evaluate a fixed monomial at a positive, run-time dimension. The degree is compiled
into the program; the dimension is the multiplier in each counted addition loop. -/
def evalMonomial (r : Fin 5 ↪ ℕ) (arg a : ℕ) : ℕ → Cmd
  | 0 => (seed r a).cmd
  | d+1 => .seq (evalMonomial r arg a d) (.seq (startProduct r arg).cmd (addRepeatedly r))

theorem evalMonomial_exec {τ : TargetedSamplers.Tapes} (r : Fin 5 ↪ ℕ) (arg a d x : ℕ)
    (sep : ∀ i, arg ≠ r i) (pos : 1 ≤ x) {b : ℕ} (s : Store)
    (input : s.mem arg = x) (fit : s.Fits b) (hb : 1 ≤ b) (bound : (a*x^d).size ≤ b) :
    ∃ t, Exec τ (fun v => v.Fits b) (evalMonomial r arg a d) s t (3+d*(4*x+4)) ∧
      t.mem (r 2) = a*x^d ∧ t.mem (r 3) = 0 ∧ t.mem (r 4) = 1 ∧ t.out = s.out ∧
      ∀ k, (∀ i, k ≠ r i) → t.mem k = s.mem k := by
  have eq (i j : Fin 5) : r i = r j ↔ i=j := r.injective.eq_iff
  induction d with
  | zero =>
    have ha : a.size ≤ b := by simpa using bound
    have safe : ((seed r a).run τ s).writeWidth ≤ b := by
      simp [seed,Structured.sequence,Fragment.run,Op.written,ha,hb]
    let t := ((seed r a).run τ s).last
    have seedSteps : ((seed r a).run τ s).steps = 3 := rfl
    refine ⟨t,by simpa only [evalMonomial,seedSteps,t,Nat.zero_mul,Nat.add_zero] using (seed r a).exec τ s b fit safe,
      ?_,?_,?_,rfl,?_⟩
    · simp [t,seed,Structured.sequence,Fragment.run,Op.eval,Store.write]
    · simp [t,seed,Structured.sequence,Fragment.run,Op.eval,Store.write,eq]
    · simp [t,seed,Structured.sequence,Fragment.run,Op.eval,Store.write,eq]
    · intro k free
      simp [t,seed,Structured.sequence,Fragment.run,Op.eval,Store.write,free]
  | succ d ih =>
    have rising : a*x^d ≤ a*x^(d+1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right pos (Nat.le_succ d))
    obtain ⟨u,first,val,zero,one,out,fr⟩ := ih ((Nat.size_le_size rising).trans bound)
    have saved := (fr arg sep).trans input
    have fu := first.post fit
    have hx := saved ▸ fu arg
    have hv := val ▸ fu (r 2)
    let v := ((startProduct r arg).run τ u).last
    have safe : ((startProduct r arg).run τ u).writeWidth ≤ b := by
      simp [startProduct,Structured.sequence,Fragment.run,Op.written,Op.eval,Store.write,eq,zero,saved,val,hx,hv]
    have setup := (startProduct r arg).exec τ u b fu safe
    have count : v.mem (r 0) = x := by
      simp [v,startProduct,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,zero,saved]
    have term : v.mem (r 1) = a*x^d := by
      simp [v,startProduct,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,zero,val]
    have keep (k : ℕ) (h₀ : k ≠ r 0) (h₁ : k ≠ r 1) (h₂ : k ≠ r 2) : v.mem k = u.mem k := by
      simp [v,startProduct,Structured.sequence,Fragment.run,Op.eval,Store.write,h₀,h₁,h₂]
    have ne {i j : Fin 5} (h : i ≠ j) := r.injective.ne h
    have z₀ := (keep _ (ne (by decide)) (ne (by decide)) (ne (by decide))).trans zero
    have z₁ := (keep _ (ne (by decide)) (ne (by decide)) (ne (by decide))).trans one
    have times : 0+x*(a*x^d) = a*x^(d+1) := by rw [pow_succ]; ring
    obtain ⟨t,loop,_,acc,out',frame⟩ := addRepeatedly_exec (τ := τ) r x (a*x^d) 0 v count term (by simp [v,startProduct,
      Structured.sequence,Fragment.run,Op.eval,Store.write]) z₀ z₁ (setup.post fu) (by rwa [times])
    have sz : ((startProduct r arg).run τ u).steps = 3 := rfl
    refine ⟨t,?_,acc.trans times,(frame _ (ne (by decide)) (ne (by decide))).trans z₀,
      (frame _ (ne (by decide)) (ne (by decide))).trans z₁,out'.trans out,?_⟩
    · rw [show 3+(d+1)*(4*x+4) = (3+d*(4*x+4))+(3+(4*x+1)) by rw [Nat.succ_mul]; omega]
      exact first.seq (setup.seq loop)
    · intro k free
      exact (frame k (free 0) (free 2)).trans ((keep k (free 0) (free 1) (free 2)).trans (fr k free))

end TargetedSamplers.Structured.Word

end LogCostRAMMonomial

section LogCostRAMQueryCall

namespace TargetedSamplers.Structured.EquationBuffer

/-- Fixed call registers above both the query writer and the callee's control area. -/
def callReg (anchor j : ℕ) := anchor+16+j

def budgetRegs (anchor : ℕ) : Fin 5 ↪ ℕ where
  toFun i := callReg anchor (3+i.val)
  inj' _ _ h := Fin.ext (Nat.add_left_cancel (Nat.add_left_cancel h))

@[simp] theorem callReg_eq_iff (a i j : ℕ) : callReg a i = callReg a j ↔ i=j := by simp [callReg]

private theorem before_callReg (a i j : ℕ) (hi : i < 16) : i ≠ callReg a j := by dsimp [callReg]; omega

/-- Save the original destination and the positive size parameter n + rows + pins + 1. -/
def saveQueryArgs (anchor : ℕ) : Fragment := Structured.sequence [
  .op (.const (callReg anchor 2) 0), .op (.add (callReg anchor 0) 0 (callReg anchor 2)),
  .op (.sub (callReg anchor 1) 10 9), .op (.add (callReg anchor 1) (callReg anchor 1) 11),
  .op (.add (callReg anchor 1) (callReg anchor 1) 1), .op (.const (callReg anchor 2) 1),
  .op (.add (callReg anchor 1) (callReg anchor 1) (callReg anchor 2))]

theorem saveQueryArgs_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (anchor base n rows pins src : ℕ)
    (s : Store) (dst : s.mem 0 = base) (dim : s.mem 1 = n) (rowCount : s.mem 11 = rows)
    (start : s.mem 9 = src) (stop : s.mem 10 = src+pins) (fit : s.Fits b)
    (width : (n+(rows+pins)+1).size ≤ b) :
    let u := ((saveQueryArgs anchor).run τ s).last
    Exec τ (fun v => v.Fits b) (saveQueryArgs anchor).cmd s u 7 ∧ u.mem (callReg anchor 0) = base ∧
      u.mem (callReg anchor 1) = n+(rows+pins)+1 ∧ u.out = s.out ∧
      ∀ a, a ≠ callReg anchor 0 → a ≠ callReg anchor 1 → a ≠ callReg anchor 2 → u.mem a = s.mem a := by
  have low (i : ℕ) (hi : i < 16) (j : ℕ) := before_callReg anchor i j hi
  have bw := dst ▸ fit 0
  have w (x : ℕ) (hx : x ≤ n+(rows+pins)+1) := (Nat.size_le_size hx).trans width
  have ww := w pins (by omega)
  have wr := w (pins+rows) (by omega)
  have wn := w (pins+rows+n) (by omega)
  have one : 1 ≤ b := (by decide : 1 ≤ (1:ℕ).size).trans (w 1 (by omega))
  have total : pins+rows+n+1 = n+(rows+pins)+1 := by omega
  have safe : ((saveQueryArgs anchor).run τ s).writeWidth ≤ b := by
    simp [saveQueryArgs,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      low 0 (by decide),low 9 (by decide),low 10 (by decide),low 11 (by decide),low 1 (by decide),
      dst,dim,rowCount,start,stop,bw,ww,wr,wn,total,width,one]
  refine ⟨(saveQueryArgs anchor).exec τ s b fit safe,?_,?_,rfl,?_⟩
  · simp [saveQueryArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,low 0 (by decide),dst]
  · simp [saveQueryArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,low 9 (by decide),
      low 10 (by decide),low 11 (by decide),low 1 (by decide),dim,rowCount,start,stop,total]
  · intro a f₀ f₁ f₂
    simp [saveQueryArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,f₀,f₁,f₂]

/-- Install the serialized buffer, the adjacent workspace, its length, and the running
time of the simulated counter. The polynomial part is supplied by evalMonomial. -/
def installQueryArgs (anchor : ℕ) : Fragment := Structured.sequence [
  .op (.add (anchor+3) (callReg anchor 0) (callReg anchor 6)),
  .op (.add (anchor+5) 0 (callReg anchor 6)), .op (.sub (anchor+7) 0 (anchor+3)),
  .op (.add (anchor+6) (callReg anchor 5) (anchor+7))]

theorem installQueryArgs_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (anchor base len time : ℕ) (s : Store)
    (dst : s.mem 0 = base+len) (start : s.mem (callReg anchor 0) = base)
    (poly : s.mem (callReg anchor 5) = time) (zero : s.mem (callReg anchor 6) = 0)
    (fit : s.Fits b) (width : (time+len).size ≤ b) :
    let t := ((installQueryArgs anchor).run τ s).last
    Exec τ (fun u => u.Fits b) (installQueryArgs anchor).cmd s t 4 ∧ t.mem (anchor+3) = base ∧
      t.mem (anchor+5) = base+len ∧ t.mem (anchor+6) = time+len ∧ t.mem (anchor+7) = len ∧
      t.out = s.out ∧ ∀ a, a ≠ anchor+3 → a ≠ anchor+5 → a ≠ anchor+6 → a ≠ anchor+7 → t.mem a = s.mem a := by
  have same (i j : ℕ) : anchor+i = anchor+j ↔ i=j := by omega
  have high (i j : ℕ) (hj : j < 16) : callReg anchor i ≠ anchor+j := by dsimp [callReg]; omega
  have z (j : ℕ) (hj : 0 < j) : 0 ≠ anchor+j := by omega
  have wb := start ▸ fit (callReg anchor 0)
  have we := dst ▸ fit 0
  have wl := (Nat.size_le_size (show len ≤ time+len by omega)).trans width
  have safe : ((installQueryArgs anchor).run τ s).writeWidth ≤ b := by
    simp [installQueryArgs,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      same,high,z 3 (by decide),z 5 (by decide),z 7 (by decide),dst,start,poly,zero,wb,we,wl,width]
  refine ⟨(installQueryArgs anchor).exec τ s b fit safe,?_,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro a h₃ h₅ h₆ h₇; simp [installQueryArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,h₃,h₅,h₆,h₇])
    | simp [installQueryArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,same,high,
        z 3 (by decide),z 5 (by decide),z 7 (by decide),dst,start,poly,zero]

end TargetedSamplers.Structured.EquationBuffer

end LogCostRAMQueryCall

section AffineRAMPrepareQuery

namespace AffinePrefixEnumeration

open EditGV897.Main TargetedSamplers.Structured TargetedSamplers.Structured.EquationBuffer

/-- A single command constructs the query and computes the simulator's time and memory
arguments from the actual dimensions and buffer. The workspace starts at the buffer end. -/
def prepareQuery (anchor A d : ℕ) : Cmd :=
  .seq (saveQueryArgs anchor).cmd (.seq serializeQuery (.seq (Word.evalMonomial (budgetRegs anchor) (callReg anchor 1) A d)
    (installQueryArgs anchor).cmd))

set_option maxHeartbeats 800000 in
theorem prepareQuery_exec {τ : TargetedSamplers.Tapes} {b n : ℕ} (anchor A d : ℕ) (E : List (Equation n))
    (k : ℕ) (p : List Bool) (base rowSrc pinSrc : ℕ) (s : Store) (hp : k+p.length ≤ n)
    (src : QuerySource E k p base rowSrc pinSrc s)
    (sep : callReg anchor 8 ≤ base) (sr : callReg anchor 8 ≤ rowSrc) (sp : callReg anchor 8 ≤ pinSrc)
    (fit : s.Fits b) (hb : 2 ≤ b) (rowWidth : (rowSrc+(denseWords E).length).size ≤ b)
    (pinWidth : (pinSrc+p.length).size ≤ b) :
    let bits := queryPayload E k p
    let size := n+(E.length+p.length)
    let time := A*(size+1)^d+bits.length
    (rowSrc+(denseWords E).length ≤ base ∨ base+bits.length ≤ rowSrc) →
    (pinSrc+p.length ≤ base ∨ base+bits.length ≤ pinSrc) → (base+bits.length).size ≤ b → time.size ≤ b →
    ∃ t j, Exec τ (fun v => v.Fits b) (prepareQuery anchor A d) s t j ∧
      j ≤ 11*bits.length+d*(4*(size+1)+4)+23 ∧ t.mem (anchor+3) = base ∧
      t.mem (anchor+5) = base+bits.length ∧ t.mem (anchor+6) = time ∧ t.mem (anchor+7) = bits.length ∧
      Wrote (fun a => a < callReg anchor 8) base (bits.map bitWord) s t := by
  intro bits size time rowApart pinApart width timeWidth
  have low : 15 < callReg anchor 8 := by dsimp [callReg]; omega
  have rate : (size+1).size ≤ b := by
    apply (Nat.size_le_size ?_).trans width
    have length : bits.length = n+2+(E.length+p.length)*(n+2) := queryPayload_length ..
    have enough := Nat.mul_le_mul_left (E.length+p.length) (by omega : 1 ≤ n+2)
    dsimp [size]; omega
  obtain ⟨save,baseWord,factorWord,out₀,fr₀⟩ := saveQueryArgs_exec (τ := τ) anchor base n E.length p.length pinSrc s
    src.dest src.dim src.rows src.pinStart src.pinEnd fit rate
  let u := ((saveQueryArgs anchor).run τ s).last
  have small (a : ℕ) (ha : a < 15) : u.mem a = s.mem a :=
    fr₀ a (by dsimp [callReg]; omega) (by dsimp [callReg]; omega) (by dsimp [callReg]; omega)
  have high (a : ℕ) (ha : callReg anchor 8 ≤ a) : u.mem a = s.mem a := by
    apply fr₀ <;> dsimp [callReg] at * <;> omega
  have updated : QuerySource E k p base rowSrc pinSrc u := ⟨(small 0 (by decide)).trans src.dest,
    (small 1 (by decide)).trans src.dim,(small 6 (by decide)).trans src.column,(small 9 (by decide)).trans src.pinStart,
    (small 10 (by decide)).trans src.pinEnd,(small 11 (by decide)).trans src.rows,(small 12 (by decide)).trans src.rowStart,
    (small 13 (by decide)).trans src.rowEnd,fun i hi => (high _ (by omega)).trans (src.rowData i hi),
    fun i hi => (high _ (by omega)).trans (src.pinData i hi)⟩
  obtain ⟨v,j,serialize,work,endAt,table⟩ := serializeQuery_exec (τ := τ) E k p base rowSrc pinSrc u hp updated
    (by omega) (by omega) (by omega) (save.post fit) hb rowWidth pinWidth rowApart pinApart width
  have held (i : ℕ) (hi : i < 8) : v.mem (callReg anchor i) = u.mem (callReg anchor i) :=
    table.frame _ (by dsimp [callReg]; omega) (.inl (by dsimp [callReg] at *; omega))
  have distinct (i : Fin 5) : callReg anchor 1 ≠ budgetRegs anchor i := by
    change callReg anchor 1 ≠ callReg anchor (3+i.val)
    simp only [ne_eq,callReg_eq_iff]; omega
  change j ≤ 11*bits.length+9 at work
  have vfit := serialize.post (save.post fit)
  obtain ⟨w,power,powerVal,zero,_,out₂,fr₂⟩ := Word.evalMonomial_exec (τ := τ) (budgetRegs anchor) (callReg anchor 1)
    A d (size+1) distinct (by omega) v ((held 1 (by decide)).trans factorWord) vfit (by omega)
    ((Nat.size_le_size (show A*(size+1)^d ≤ time by dsimp [time]; omega)).trans timeWidth)
  have register (i : Fin 5) : budgetRegs anchor i = callReg anchor (3+i.val) := rfl
  have preserved (a : ℕ) (ha : callReg anchor 8 ≤ a) : w.mem a = v.mem a := by
    apply fr₂; intro i; rw [register]; have := i.isLt; dsimp [callReg] at *; omega
  have at0 : w.mem 0 = base+bits.length := (fr₂ 0 (by intro i; rw [register]; dsimp [callReg]; omega)).trans endAt
  have atBase : w.mem (callReg anchor 0) = base := (fr₂ _ (by intro i; rw [register]; simp only [ne_eq,callReg_eq_iff]; omega)).trans
    ((held 0 (by decide)).trans baseWord)
  obtain ⟨install,srcA,baseA,timeA,lenA,ret,fr₃⟩ := installQueryArgs_exec (τ := τ) anchor base bits.length
    (A*(size+1)^d) w at0 atBase powerVal zero (power.post vfit) timeWidth
  let t := ((installQueryArgs anchor).run τ w).last
  have heap (a : ℕ) (ha : callReg anchor 8 ≤ a) : t.mem a = v.mem a := by
    apply Eq.trans _ (preserved a ha)
    apply fr₃ <;> dsimp [callReg] at ha <;> omega
  refine ⟨t,_,save.seq (serialize.seq (power.seq install)),by omega,srcA,baseA,timeA,lenA,?_,?_,
    ret.trans (out₂.trans (table.output.trans out₀))⟩
  · intro i hi
    exact (heap _ (by omega)).trans (table.data i hi)
  · intro a clean bounds
    have beyond : callReg anchor 8 ≤ a := by omega
    exact (heap a beyond).trans ((table.frame a (by omega) bounds).trans (high a beyond))

end AffinePrefixEnumeration

end AffineRAMPrepareQuery

section IndexedMultitapeSimulation

/-! An indexed-memory representation of the registered binary multitape machine. -/

namespace EditGV897.Main.Indexed

def displacement : Motion → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

/-- A blank is seen at every position beyond the finite portions of either tape stack. -/
def symbol (t : Tape) : ℤ → Option Bool
  | .ofNat 0 => t.head
  | .ofNat (k+1) => (t.right[k]?).join
  | .negSucc k => (t.left[k]?).join

private theorem headD_blank (xs : List (Option Bool)) : xs.headD none = (xs[0]?).join := by
  cases xs <;> rfl

theorem symbol_writeMove (t : Tape) (a : Option Bool) (m : Motion) (z : ℤ) :
    symbol (t.writeMove a m) z =
      if z + displacement m = 0 then a else symbol t (z + displacement m) := by
  cases m with
  | left =>
    change _ = if z+(-1) = 0 then a else symbol t (z+(-1))
    cases z with
    | ofNat j =>
      cases j with
      | zero => exact headD_blank _
      | succ j =>
        cases j with
        | zero => rfl
        | succ j =>
          rw [show Int.ofNat (j+2) + (-1) = Int.ofNat (j+1) by simp [Int.ofNat_eq_natCast] <;> omega,
            if_neg (show Int.ofNat (j+1) ≠ 0 from fun h => Nat.succ_ne_zero j (Int.ofNat.inj h))]
          rfl
    | negSucc j =>
      rw [show Int.negSucc j + (-1) = Int.negSucc (j+1) by omega, if_neg (by omega)]
      change ((t.left.drop 1)[j]?).join = (t.left[j+1]?).join
      simp only [List.getElem?_drop, Nat.add_comm 1 j]
  | stay =>
    change _ = if z+0 = 0 then a else symbol t (z+0)
    rw [add_zero]
    cases z with
    | ofNat j =>
      cases j with
      | zero => rfl
      | succ j => rw [if_neg (show Int.ofNat (j+1) ≠ 0 from fun h => Nat.succ_ne_zero j (Int.ofNat.inj h))]; rfl
    | negSucc j => rw [if_neg (by omega)]; rfl
  | right =>
    change _ = if z+1 = 0 then a else symbol t (z+1)
    cases z with
    | ofNat j =>
      cases j with
      | zero => exact headD_blank _
      | succ j =>
        rw [show Int.ofNat (j+1) + 1 = Int.ofNat (j+2) by rfl,
          if_neg (show Int.ofNat (j+2) ≠ 0 from fun h => Nat.succ_ne_zero (j+1) (Int.ofNat.inj h))]
        change ((t.right.drop 1)[j]?).join = (t.right[j+1]?).join
        simp only [List.getElem?_drop, Nat.add_comm 1 j]
    | negSucc j =>
      cases j with
      | zero => rfl
      | succ j =>
        rw [show Int.negSucc (j+1) + 1 = Int.negSucc j by omega, if_neg (by omega)]
        rfl

structure Config (P : Program) where
  state : Fin (P.states+1)
  cursor : Fin (P.workTapes+2) → ℤ
  mem : Fin (P.workTapes+2) → ℤ → Option Bool

def Config.read {P : Program} (c : Config P) (i : Fin (P.workTapes+2)) := c.mem i (c.cursor i)

def Config.advance {P : Program} (c : Config P)
    (s : Fin (P.states+1)) (moves : Fin (P.workTapes+2) → Option Bool × Motion) : Config P :=
  ⟨s, fun i => c.cursor i + displacement (moves i).2,
    fun i => Function.update (c.mem i) (c.cursor i) (moves i).1⟩

def arrayStep (P : Program) (c : Config P) : Option (Config P) :=
  (P.transition c.state c.read).map fun act => c.advance act.1 act.2

/-- Positions in an original tape are measured relative to its current head. -/
structure Represents {P : Program} (a : Config P) (c : Configuration P) : Prop where
  state : a.state = c.state
  cell : ∀ i z, a.mem i (a.cursor i + z) = symbol (c.tapes i) z

theorem Represents.read {P : Program} {a : Config P} {c : Configuration P} (h : Represents a c) :
    a.read = fun i => (c.tapes i).head := by
  funext i
  simpa [Config.read, symbol] using h.cell i 0

theorem Represents.advance {P : Program} {a : Config P} {c : Configuration P} (h : Represents a c)
    (s : Fin (P.states+1)) (moves : Fin (P.workTapes+2) → Option Bool × Motion) :
    Represents (a.advance s moves) ⟨s,fun i => (c.tapes i).writeMove (moves i).1 (moves i).2⟩ := by
  refine ⟨rfl,fun i z => ?_⟩
  rw [symbol_writeMove]
  change Function.update _ (a.cursor i) _ (a.cursor i + displacement (moves i).2 + z) = _
  by_cases he : z + displacement (moves i).2 = 0
  · have hpos : a.cursor i + displacement (moves i).2 + z = a.cursor i := by omega
    simp [he, hpos]
  · have hpos : a.cursor i + displacement (moves i).2 + z ≠ a.cursor i := by omega
    rw [Function.update_of_ne hpos, if_neg he,
      show a.cursor i + displacement (moves i).2 + z = a.cursor i + (z + displacement (moves i).2) by omega]
    exact h.cell i _

def arrayExecute (P : Program) : ℕ → Config P → Config P
  | 0, c => c
  | k+1, c => match arrayStep P c with
    | none => c
    | some next => arrayExecute P k next

theorem Represents.execute {P : Program} {a : Config P} {c : Configuration P} (h : Represents a c) (k : ℕ) :
    Represents (arrayExecute P k a) (EditGV897.Main.execute P k c) := by
  induction k generalizing a c with
  | zero => exact h
  | succ k ih =>
    simp only [arrayExecute, arrayStep, EditGV897.Main.execute, EditGV897.Main.step, h.state, h.read]
    cases hr : P.transition c.state (fun i => (c.tapes i).head) with
    | none => exact h
    | some act => exact ih (h.advance act.1 act.2)

def initialArray (P : Program) (input : List Bool) : Config P :=
  ⟨0, fun _ => 0, fun i z => if i.val = 0 then
    match z with
    | .ofNat k => input[k]?
    | .negSucc _ => none
    else none⟩

theorem initial_represents (P : Program) (input : List Bool) :
    Represents (initialArray P input) (initial P input) := by
  refine ⟨rfl,fun i z => ?_⟩
  change (initialArray P input).mem i (0+z) = _
  rw [zero_add]
  unfold initialArray initial
  dsimp only
  by_cases hi : i.val = 0
  · rw [if_pos hi, if_pos hi]
    cases z with
    | negSucc k => rfl
    | ofNat k =>
      cases k with
      | zero => cases input <;> rfl
      | succ k =>
        change input[k+1]? = (((input.map some).drop 1)[k]?).join
        rw [List.getElem?_drop, List.getElem?_map, Nat.add_comm 1 k]
        cases input[k+1]? <;> rfl
  · rw [if_neg hi, if_neg hi]
    cases z with
    | negSucc k => rfl
    | ofNat k => cases k <;> rfl

/-- Every head remains within k positions of its initial position after k simultaneous steps. -/
theorem cursor_bound (P : Program) (k : ℕ) (c : Config P) (i : Fin (P.workTapes+2)) :
    c.cursor i - (k : ℤ) ≤ (arrayExecute P k c).cursor i ∧
      (arrayExecute P k c).cursor i ≤ c.cursor i + k := by
  induction k generalizing c with
  | zero => simp [arrayExecute]
  | succ k ih =>
    simp only [arrayExecute,arrayStep]
    cases h : P.transition c.state c.read with
    | none => simp; omega
    | some act =>
      have hg := ih (c.advance act.1 act.2)
      have hm : -1 ≤ displacement (act.2 i).2 ∧ displacement (act.2 i).2 ≤ 1 := by
        cases (act.2 i).2 <;> decide
      dsimp only [Option.map, Config.advance] at hg ⊢
      omega

/-- In a time-T simulation, one contiguous block of 2T+1 cells suffices for each tape.
The base may lie in a much larger ambient RAM workspace. -/
def tapeAddress (base time tape cell : ℕ) := base + tape*(2*time+1) + cell

theorem tapeAddress_injective {base time i j x y : ℕ} (hx : x < 2*time+1) (hy : y < 2*time+1)
    (h : tapeAddress base time i x = tapeAddress base time j y) : i = j ∧ x = y := by
  have he : x + (2*time+1)*i = y + (2*time+1)*j := by
    simpa [tapeAddress, Nat.add_assoc, Nat.mul_comm, Nat.add_left_comm, Nat.add_comm] using h
  have hx' := congrArg (fun v => v % (2*time+1)) he
  have hxy : x = y := by simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hx'
  have hi' := congrArg (fun v => v / (2*time+1)) he
  have hi : i = j := by simpa [Nat.add_mul_div_left, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy] using hi'
  exact ⟨hi,hxy⟩

theorem tapeAddress_lt {base time tapes i x : ℕ} (hi : i < tapes) (hx : x < 2*time+1) :
    tapeAddress base time i x < base+tapes*(2*time+1) := by
  have h := Nat.mul_le_mul_right (2*time+1) hi
  rw [Nat.succ_mul] at h
  unfold tapeAddress
  omega

end EditGV897.Main.Indexed

end IndexedMultitapeSimulation

section MultitapeWrite

namespace EditGV897.Main.Indexed.RAM

open TargetedSamplers TargetedSamplers.Structured

/-- Registers 0 and 1 hold the constants, 2 is the scratch symbol, 3 holds the state,
4 is the loop flag, and the next k registers hold the k head addresses. -/
def reader : Reader := ⟨2,0,1,by decide,by decide⟩

def headReg {k : ℕ} (i : Fin k) : ℕ := 5+i.val

def shifted (z : ℕ) : Motion → ℕ
  | .left => z-1
  | .stay => z
  | .right => z+1

theorem symbolCode_size (x : Option Bool) : (symbolCode x).size ≤ 2 := by
  cases x with
  | none => decide
  | some v => cases v <;> decide

def moveOp (r : ℕ) : Motion → Op
  | .left => .sub r r 1
  | .stay => .add r r 0
  | .right => .add r r 1

def writeHead (r : ℕ) (act : Option Bool × Motion) : Cmd :=
  .seq (.op (.const 2 (symbolCode act.1))) (.seq (.op (.store r 2)) (.op (moveOp r act.2)))

/-- A simultaneous transition writes the symbol at the old head position, then moves the
pointer by one cell. The three instructions pay for the addresses they actually touch. -/
theorem writeHead_exec {τ : Tapes} {s : Store} {b r z : ℕ} (a : Option Bool × Motion)
    (hr : 2 < r) (hz : 2 < z) (hrz : r ≠ z) (hptr : s.mem r = z)
    (h0 : s.mem 0 = 0) (h1 : s.mem 1 = 1) (hb : 2 ≤ b) (hf : s.Fits b)
    (hm : (shifted z a.2).size ≤ b) :
    let v := symbolCode a.1
    Exec τ (fun st => st.Fits b) (writeHead r a) s (((s.write 2 v).write z v).write r (shifted z a.2)) 3 := by
  let v := symbolCode a.1
  let s₁ := s.write 2 v
  let s₂ := s₁.write z v
  have hv : v.size ≤ b := (symbolCode_size a.1).trans hb
  have f₁ : s₁.Fits b := Store.write_fits hf 2 hv
  have f₂ : s₂.Fits b := Store.write_fits f₁ z hv
  have e₁ : Exec τ (fun st => st.Fits b) (.op (.const 2 v)) s s₁ 1 := .op _ _ f₁
  have hstore : (Op.store r 2).eval τ s₁ = s₂ := by
    simp [Op.eval,s₂,s₁,Store.write,show r ≠ 2 by omega,hptr]
  have e₂ : Exec τ (fun st => st.Fits b) (.op (.store r 2)) s₁ s₂ 1 := by
    simpa only [hstore] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) s₁ (.store r 2) (by rwa [hstore]))
  have hzero : s₂.mem 0 = 0 := by simp [s₂,s₁,Store.write,show 0 ≠ z by omega,h0]
  have hone : s₂.mem 1 = 1 := by simp [s₂,s₁,Store.write,show 1 ≠ z by omega,h1]
  have hreg : s₂.mem r = z := by simp [s₂,s₁,Store.write,hrz,show r ≠ 2 by omega,hptr]
  have hmove : (moveOp r a.2).eval τ s₂ = s₂.write r (shifted z a.2) := by
    cases a.2 <;> simp [moveOp,shifted,Op.eval,hreg,hzero,hone]
  have e₃ : Exec τ (fun st => st.Fits b) (.op (moveOp r a.2)) s₂ (s₂.write r (shifted z a.2)) 1 := by
    simpa only [hmove] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) s₂ (moveOp r a.2)
      (by rw [hmove]; exact Store.write_fits f₂ r hm))
  exact e₁.seq (e₂.seq e₃)

def writeHeads {k : ℕ} (a : Fin k → Option Bool × Motion) : List (Fin k) → Cmd
  | [] => .skip
  | i :: is => .seq (writeHead (headReg i) (a i)) (writeHeads a is)

/-- A frame predicate for a finite set of writes. Apart from the explicitly reserved
scratch register, every address outside the listed pointers and cells is preserved. -/
def Outside {k : ℕ} (cells : Fin k → ℕ) (is : List (Fin k)) (addr : ℕ) : Prop :=
  addr ≠ 2 ∧ ∀ i ∈ is, addr ≠ headReg i ∧ addr ≠ cells i

theorem writeHeads_exec {k b : ℕ} {τ : Tapes} (cells : Fin k → ℕ) (act : Fin k → Option Bool × Motion)
    (hc : Function.Injective cells) (hbase : ∀ i, 5+k ≤ cells i)
    (hw : ∀ i, (shifted (cells i) (act i).2).size ≤ b) (hb : 2 ≤ b)
    (is : List (Fin k)) (nd : is.Nodup) (s : Store) (hf : s.Fits b)
    (h0 : s.mem 0 = 0) (h1 : s.mem 1 = 1) (hp : ∀ i ∈ is, s.mem (headReg i) = cells i) :
    ∃ t, Exec τ (fun st => st.Fits b) (writeHeads act is) s t (3*is.length) ∧
      t.out = s.out ∧
      (∀ i ∈ is, t.mem (headReg i) = shifted (cells i) (act i).2 ∧ t.mem (cells i) = symbolCode (act i).1) ∧
      ∀ addr, Outside cells is addr → t.mem addr = s.mem addr := by
  have hreg (i : Fin k) : 2 < headReg i ∧ headReg i < 5+k := by
    have := i.isLt
    simp [headReg]; omega
  have hsep (i j : Fin k) : headReg i ≠ cells j := Nat.ne_of_lt ((hreg i).2.trans_le (hbase j))
  have hregs : Function.Injective (@headReg k) := by
    intro i j he
    apply Fin.ext
    simpa [headReg] using he
  induction is generalizing s with
  | nil =>
    exact ⟨s, .skip _, rfl, by simp, fun _ _ => rfl⟩
  | cons i is ih =>
    obtain ⟨hi,nis⟩ := List.nodup_cons.mp nd
    let v := symbolCode (act i).1
    let mid := ((s.write 2 v).write (cells i) v).write (headReg i) (shifted (cells i) (act i).2)
    have eg : Exec τ (fun st => st.Fits b) (writeHead (headReg i) (act i)) s mid 3 :=
      writeHead_exec (act i) (hreg i).1 (by have := hbase i; omega) (hsep i i) (hp i (by simp)) h0 h1 hb hf (hw i)
    have save (addr : ℕ) (ht : addr ≠ 2) (hr : addr ≠ headReg i) (hc' : addr ≠ cells i) :
        mid.mem addr = s.mem addr := by simp [mid,Store.write,ht,hr,hc']
    have future (j : Fin k) (hj : j ∈ is) : s.mem (headReg j) = cells j := hp j (by simp [hj])
    have diff (j : Fin k) (hj : j ∈ is) : j ≠ i := by rintro rfl; exact hi hj
    have hmp (j : Fin k) (hj : j ∈ is) : mid.mem (headReg j) = cells j := by
      rw [save _ (by have := hreg j; omega) (hregs.ne (diff j hj)) (hsep j i), future j hj]
    obtain ⟨t,ex,hout,hit,frame⟩ := ih nis mid (eg.post hf)
      ((save 0 (by decide) (by have := hreg i; omega) (by have := hbase i; omega)).trans h0)
      ((save 1 (by decide) (by have := hreg i; omega) (by have := hbase i; omega)).trans h1) hmp
    refine ⟨t, ?_, hout, ?_, ?_⟩
    · simpa [writeHeads,Nat.mul_add,Nat.add_comm] using eg.seq ex
    · intro j hj
      rcases List.mem_cons.mp hj with eq | hj
      · subst j
        have f₁ := frame (headReg i) ⟨by have := hreg i; omega,
          fun j hj => ⟨hregs.ne (diff j hj).symm, hsep i j⟩⟩
        have f₂ := frame (cells i) ⟨by have := hbase i; omega,
          fun j hj => ⟨(hsep j i).symm, hc.ne (diff j hj).symm⟩⟩
        simpa [mid,Store.write,Ne.symm (hsep i i),v] using And.intro f₁ f₂
      · exact hit j hj
    · rintro addr ⟨ht,free⟩
      rw [frame addr ⟨ht,fun j hj => free j (by simp [hj])⟩]
      obtain ⟨hr,hm⟩ := free i (by simp)
      exact save addr ht hr hm

end EditGV897.Main.Indexed.RAM

end MultitapeWrite

section MultitapeTransition

namespace EditGV897.Main.Indexed.RAM

open TargetedSamplers.Structured

abbrev NT (P : EditGV897.Main.Program) := P.workTapes+2

def cellIndex (time : ℕ) (z : ℤ) := (z+(time : ℤ)).toNat

def headAddr {P : Program} (base time : ℕ) (c : Config P) (i : Fin (NT P)) :=
  tapeAddress base time i.val (cellIndex time (c.cursor i))

def Inside {P : Program} (time : ℕ) (c : Config P) : Prop :=
  ∀ i, -(time : ℤ) ≤ c.cursor i ∧ c.cursor i ≤ time

theorem index_spec {time : ℕ} {z : ℤ} (low : -(time : ℤ) ≤ z) (high : z ≤ time) :
    cellIndex time z < 2*time+1 ∧ (cellIndex time z : ℤ) = z+time := by
  have hz : 0 ≤ z+(time : ℤ) := by omega
  have he := Int.toNat_of_nonneg hz
  unfold cellIndex
  exact ⟨by omega,he⟩

theorem moved_address {base time i : ℕ} {z : ℤ} (m : Motion) (lo : -(time : ℤ) ≤ z)
    (lo' : -(time : ℤ) ≤ z+displacement m) :
    shifted (tapeAddress base time i (cellIndex time z)) m =
      tapeAddress base time i (cellIndex time (z+displacement m)) := by
  have h := Int.toNat_of_nonneg (show 0 ≤ z+(time : ℤ) by omega)
  have h' := Int.toNat_of_nonneg (show 0 ≤ z+displacement m+(time : ℤ) by omega)
  cases m <;> simp only [shifted,cellIndex,tapeAddress,displacement] at * <;> omega

/-- The dense cells in each bounded tape window have their ternary symbol codes.
Cells outside these disjoint windows belong to the caller. -/
structure Holds {P : Program} (base time : ℕ) (c : Config P) (s : Store) : Prop where
  zero : s.mem 0 = 0
  one : s.mem 1 = 1
  state : s.mem 3 = c.state.val
  pointer : ∀ i, s.mem (headReg i) = headAddr base time c i
  cell : ∀ i : Fin (NT P), ∀ z : Fin (2*time+1),
    s.mem (tapeAddress base time i.val z.val) = symbolCode (c.mem i ((z.val : ℤ) - time))

theorem cell_ge_base (base time i z : ℕ) : base ≤ tapeAddress base time i z := by
  unfold tapeAddress; omega

theorem Holds.congr {P : Program} {base time : ℕ} {c : Config P} {s u : Store}
    (h : Holds base time c s) (hb : 5+NT P ≤ base) (frame : ∀ a, a ≠ 2 → u.mem a = s.mem a) :
    Holds base time c u := by
  refine ⟨(frame 0 (by decide)).trans h.zero,(frame 1 (by decide)).trans h.one,
    (frame 3 (by decide)).trans h.state,?_,?_⟩
  · intro i; exact (frame _ (by simp [headReg]; omega)).trans (h.pointer i)
  · intro i z
    exact (frame _ (by have := cell_ge_base base time i.val z.val; omega)).trans (h.cell i z)

theorem Holds.read {P : Program} {base time : ℕ} {c : Config P} {s : Store}
    (h : Holds base time c s) (hc : Inside time c) (i : Fin (NT P)) :
    s.mem (s.mem (headReg i)) = symbolCode (c.read i) := by
  obtain ⟨hi,he⟩ := index_spec (hc i).1 (hc i).2
  rw [h.pointer i]
  simpa [headAddr,Config.read,he] using h.cell i ⟨_,hi⟩

def emit {P : Program} : Option (Fin (P.states+1) × (Fin (NT P) → Option Bool × Motion)) → Cmd
  | none => .op (.const 4 0)
  | some (q,act) => .seq (writeHeads act (List.finRange (NT P))) (.op (.const 3 q.val))

def tick (P : Program) : Cmd :=
  dispatch 3 2 0 (List.ofFn fun q => reader.symbolTree headReg fun x => emit (P := P) (P.transition q x))

def tickBound (P : Program) := 3*P.states+8*NT P+3

/-- Outside the control registers and the finite tape allocation, callers may store other
data and later recover them without copying. -/
def Caller (base time tapes addr : ℕ) : Prop :=
  5+tapes ≤ addr ∧ (addr < base ∨ base+tapes*(2*time+1) ≤ addr)

private theorem headReg_lt {k : ℕ} (i : Fin k) : headReg i < 5+k := by
  simpa [headReg] using i.isLt

private theorem addr_outside {P : Program} {base time addr : ℕ} {c : Config P}
    (h : Inside time c) (free : Caller base time (NT P) addr) :
    Outside (headAddr base time c) (List.finRange (NT P)) addr := by
  refine ⟨by obtain ⟨hl,_⟩ := free; omega,fun i _ => ⟨by have := headReg_lt i; obtain ⟨hl,_⟩ := free; omega,?_⟩⟩
  obtain ⟨_,hd | hd⟩ := free
  · exact Nat.ne_of_lt (hd.trans_le (cell_ge_base ..))
  · exact Ne.symm (Nat.ne_of_lt ((tapeAddress_lt i.isLt (index_spec (h i).1 (h i).2).1).trans_le hd))

private theorem headAddr_inj {P : Program} {base time : ℕ} {c : Config P} (h : Inside time c) :
    Function.Injective (headAddr base time c) := by
  intro i j eq
  exact Fin.ext (tapeAddress_injective (index_spec (h i).1 (h i).2).1 (index_spec (h j).1 (h j).2).1 eq).1

/-- Effect of the selected transition on the caller's store, after the state and actual
symbols have been dispatched. A halting instruction clears the loop flag. -/
theorem emit_exec {P : Program} {base time b : ℕ} {s : Store} {τ : TargetedSamplers.Tapes}
    (c : Config P) (repr : Holds base time c s) (inside : Inside time c) (running : s.mem 4 = 1)
    (hb : 2 ≤ b) (hbase : 5+NT P ≤ base) (hstate : P.states.size ≤ b)
    (hwidth : (base+NT P*(2*time+1)).size ≤ b) (hs : s.Fits b)
    (hn : ∀ c', arrayStep P c = some c' → Inside time c') :
    ∃ t k, Exec τ (fun u => u.Fits b) (emit (P := P) (P.transition c.state c.read)) s t k ∧
      k ≤ 3*NT P+1 ∧ Holds base time ((arrayStep P c).getD c) t ∧
      t.mem 4 = (if (arrayStep P c).isSome then 1 else 0) ∧ t.out = s.out ∧
      ∀ a, Caller base time (NT P) a → t.mem a = s.mem a := by
  cases tr : P.transition c.state c.read with
  | none =>
    have het : arrayStep P c = none := by simp [arrayStep,tr]
    let t := s.write 4 0
    have hz : (0:ℕ).size ≤ b := by simp
    refine ⟨t,1, .op s (.const 4 0) (Store.write_fits hs 4 hz),by omega,?_,?_,rfl,?_⟩
    · simp only [het,Option.getD_none]
      refine ⟨by simpa [t,Store.write] using repr.zero,by simpa [t,Store.write] using repr.one,
        by simpa [t,Store.write] using repr.state,?_,?_⟩
      · intro i; simpa [t,Store.write,headReg,show 5+i.val ≠ 4 by omega] using repr.pointer i
      · intro i z
        have hh : tapeAddress base time i.val z.val ≠ 4 := by have := cell_ge_base base time i.val z.val; omega
        simpa [t,Store.write,hh] using repr.cell i z
    · simp [het,t,Store.write]
    · intro a ha
      simp [t,Store.write,show a ≠ 4 by obtain ⟨h,_⟩ := ha; omega]
  | some action =>
    obtain ⟨q,act⟩ := action
    let next := c.advance q act
    have het : arrayStep P c = some next := by simp [arrayStep,tr,next]
    have hin := hn next het
    let cells := headAddr base time c
    have below (i : Fin (NT P)) : 5+NT P ≤ cells i := hbase.trans (cell_ge_base ..)
    have shifted' (i : Fin (NT P)) : shifted (cells i) (act i).2 = headAddr base time next i :=
      moved_address (act i).2 (inside i).1 (hin i).1
    have width (i : Fin (NT P)) : (shifted (cells i) (act i).2).size ≤ b := by
      rw [shifted' i]
      exact (Nat.size_le_size (tapeAddress_lt i.isLt (index_spec (hin i).1 (hin i).2).1).le).trans hwidth
    obtain ⟨mid,ex,ho,hit,frame⟩ := writeHeads_exec (τ := τ) cells act (headAddr_inj inside) below width hb
      (List.finRange (NT P)) (List.nodup_finRange _) s hs repr.zero repr.one (fun i _ => repr.pointer i)
    let t := mid.write 3 q.val
    have hq := (Nat.size_le_size (show q.val ≤ P.states by have := q.isLt; omega)).trans hstate
    have setq : Exec τ (fun u => u.Fits b) (.op (.const 3 q.val)) mid t 1 :=
      .op mid _ (Store.write_fits (ex.post hs) _ hq)
    have e := ex.seq setq
    simp only [List.length_finRange] at e
    have hit' (i : Fin (NT P)) := hit i (List.mem_finRange i)
    have low (a : ℕ) (ha : a < 5) (hne : a ≠ 2) : mid.mem a = s.mem a :=
      frame a ⟨hne,fun j _ => ⟨by simp [headReg]; omega,by have := below j; omega⟩⟩
    refine ⟨t,_,e,le_rfl,?_,?_,ho,?_⟩
    · simp only [het,Option.getD_some]
      refine ⟨?_,?_,?_,?_,?_⟩
      · simpa [t,Store.write] using (low 0 (by decide) (by decide)).trans repr.zero
      · simpa [t,Store.write] using (low 1 (by decide) (by decide)).trans repr.one
      · simp [t,Store.write,next,Config.advance]
      · intro i
        simpa [t,Store.write,headReg,show 5+i.val ≠ 3 by omega] using (hit' i).1.trans (shifted' i)
      · intro i z
        let addr := tapeAddress base time i.val z.val
        have ha : addr ≠ 3 := by have := cell_ge_base base time i.val z.val; dsimp [addr]; omega
        change (mid.write 3 q.val).mem addr = symbolCode (Function.update (c.mem i) (c.cursor i) (act i).1 ((z.val : ℤ)-time))
        simp only [Store.write,Function.update_of_ne ha]
        have hi := index_spec (inside i).1 (inside i).2
        by_cases he : (z.val : ℤ)-time = c.cursor i
        · have hz : z.val = cellIndex time (c.cursor i) := by omega
          have ea : addr = cells i := by simp [addr,cells,headAddr,hz]
          simpa [he,ea] using (hit' i).2
        · rw [Function.update_of_ne he]
          have free : Outside cells (List.finRange _) addr := by
            refine ⟨by have := cell_ge_base base time i.val z.val; dsimp [addr]; omega,fun j _ => ⟨?_,?_⟩⟩
            · have hreg := headReg_lt j
              have hcell := cell_ge_base base time i.val z.val
              dsimp [addr]; omega
            · intro eq
              obtain ⟨hij,hz⟩ := tapeAddress_injective z.isLt (index_spec (inside j).1 (inside j).2).1 eq
              have eij : i = j := Fin.ext hij
              subst j
              omega
          exact (frame addr free).trans (repr.cell i z)
    · simpa [het,t,Store.write] using (low 4 (by decide) (by decide)).trans running
    · intro a ha
      have lower := ha.1
      simpa [t,Store.write,show a ≠ 3 by omega] using frame a (addr_outside inside ha)

end EditGV897.Main.Indexed.RAM

end MultitapeTransition

section MultitapeRun

namespace EditGV897.Main.Indexed.RAM

open TargetedSamplers.Structured

/-- One fixed dispatch table simulates each simultaneous step, even when the embedded
windows are at very large addresses. Its primitive instruction bound depends only on P. -/
theorem tick_exec {P : Program} {base time b : ℕ} {s : Store} {τ : TargetedSamplers.Tapes}
    (c : Config P) (repr : Holds base time c s) (inside : Inside time c) (running : s.mem 4 = 1)
    (hb : 2 ≤ b) (hbase : 5+NT P ≤ base) (hstate : P.states.size ≤ b)
    (hwidth : (base+NT P*(2*time+1)).size ≤ b) (hs : s.Fits b)
    (hn : ∀ c', arrayStep P c = some c' → Inside time c') :
    ∃ t k, Exec τ (fun u => u.Fits b) (tick P) s t k ∧ k ≤ tickBound P ∧
      Holds base time ((arrayStep P c).getD c) t ∧
      t.mem 4 = (if (arrayStep P c).isSome then 1 else 0) ∧ t.out = s.out ∧
      ∀ a, Caller base time (NT P) a → t.mem a = s.mem a := by
  let q := c.state
  let choose := fun q' : Fin (P.states+1) => reader.symbolTree headReg fun x => emit (P := P) (P.transition q' x)
  let table := List.ofFn choose
  let s₁ := s.write 2 q.val
  let s₂ := reader.after c.read s₁
  have hq := (Nat.size_le_size (show q.val ≤ P.states by have := q.isLt; omega)).trans hstate
  have f₁ : s₁.Fits b := Store.write_fits hs 2 hq
  have f₂ : s₂.Fits b := reader.after_fits _ _ f₁ fun i => (symbolCode_size (c.read i)).trans hb
  have frame₁ {a : ℕ} (ha : a ≠ 2) : s₁.mem a = s.mem a := by simp [s₁,Store.write,ha]
  have frame₂ {a : ℕ} (ha : a ≠ 2) : s₂.mem a = s.mem a := (reader.after_mem _ _ ha).trans (frame₁ ha)
  have hr₁ := repr.congr hbase (fun _ ha => frame₁ ha)
  have hr₂ := repr.congr hbase (fun _ ha => frame₂ ha)
  obtain ⟨t,k,ex,hk,hr,flag,out,save⟩ :=
    emit_exec (τ := τ) c hr₂ inside ((frame₂ (by decide : 4 ≠ 2)).trans running) hb hbase hstate hwidth f₂ hn
  have sel := reader.symbolTree_exec (τ := τ) (b := b) headReg (fun x => emit (P := P) (P.transition q x))
    c.read s₁ t k f₁ hr₁.zero hr₁.one (fun i => by simp [reader,headReg]; omega)
    (fun i => by
      rw [hr₁.pointer i]; change tapeAddress _ _ _ _ ≠ 2
      have := cell_ge_base base time i.val (cellIndex time (c.cursor i)); omega)
    (hr₁.read inside) ex
  let j : Fin table.length := ⟨q.val,by simpa [table] using q.isLt⟩
  have eqBranch : table[j.val] = choose q := by simp only [table,j,List.getElem_ofFn]
  have inv (v : ℕ) (h : v ≤ 0+j.val) : (s.write 2 v).Fits b :=
    Store.write_fits hs _ ((Nat.size_le_size (show v ≤ q.val by simpa [j] using h)).trans hq)
  have ev := dispatch_select (τ := τ) (inv := fun u => u.Fits b) 3 2 (by decide) table 0 s t j _
    (by simpa [j,q] using repr.state) inv (by simpa only [eqBranch,Nat.zero_add] using sel)
  refine ⟨t,_,ev,?_,hr,flag,?_,?_⟩
  · have hsym := symbolSteps_le c.read
    have htag : j.val ≤ P.states := by change q.val ≤ P.states; have := q.isLt; omega
    simp only [tickBound,NT] at hk hsym ⊢
    omega
  · exact out.trans (reader.after_out c.read s₁)
  · intro a h
    exact (save a h).trans (frame₂ (by have := h.1; omega))

def simulate (P : Program) := Cmd.whileGt 4 0 (tick P)

theorem inside_mono {P : Program} {u v : ℕ} {c : Config P} (h : Inside u c) (hu : u ≤ v) : Inside v c := by
  intro i; have := h i; omega

theorem inside_next {P : Program} {elapsed : ℕ} {c c' : Config P} (h : Inside elapsed c)
    (step : arrayStep P c = some c') : Inside (elapsed+1) c' := by
  unfold arrayStep at step
  cases ht : P.transition c.state c.read with
  | none => simp [ht] at step
  | some a =>
    simp only [ht,Option.map_some,Option.some.injEq] at step
    subst c'
    intro i
    have hi := h i
    have hd : -1 ≤ displacement (a.2 i).2 ∧ displacement (a.2 i).2 ≤ 1 := by cases (a.2 i).2 <;> decide
    change _ ≤ c.cursor i + displacement (a.2 i).2 ∧ c.cursor i + displacement (a.2 i).2 ≤ _
    omega

/-- Executable RAM loop for a fixed multitape machine. In a time-T window each transition
and the final halt test use only a constant number of primitive instructions. -/
theorem simulate_exec {P : Program} {base time b : ℕ} {τ : TargetedSamplers.Tapes}
    (hb : 2 ≤ b) (hbase : 5+NT P ≤ base) (hstate : P.states.size ≤ b)
    (hwidth : (base+NT P*(2*time+1)).size ≤ b) (k elapsed : ℕ) (window : elapsed+k ≤ time)
    (c : Config P) (s : Store) (repr : Holds base time c s) (inside : Inside elapsed c)
    (running : s.mem 4 = 1) (hs : s.Fits b) (halted : arrayStep P (arrayExecute P k c) = none) :
    ∃ t steps, Exec τ (fun u => u.Fits b) (simulate P) s t steps ∧
      steps ≤ (k+1)*(tickBound P+2)+1 ∧ Holds base time (arrayExecute P k c) t ∧
      t.mem 4 = 0 ∧ t.out = s.out ∧ ∀ a, Caller base time (NT P) a → t.mem a = s.mem a := by
  have terminal {c₀ : Config P} {s₀ : Store} (r : Holds base time c₀ s₀) (ins : Inside time c₀)
      (run : s₀.mem 4 = 1) (fits : s₀.Fits b) (stop : arrayStep P c₀ = none) :
      ∃ t steps, Exec τ (fun u => u.Fits b) (simulate P) s₀ t steps ∧ steps ≤ tickBound P+3 ∧
        Holds base time c₀ t ∧ t.mem 4 = 0 ∧ t.out = s₀.out ∧
        ∀ a, Caller base time (NT P) a → t.mem a = s₀.mem a := by
    obtain ⟨t,j,ex,hj,hr,flag,out,save⟩ := tick_exec (τ := τ) c₀ r ins run hb hbase hstate hwidth fits
      (fun c' he => by rw [stop] at he; contradiction)
    simp only [stop,Option.getD_none,Option.isSome_none,Bool.false_eq_true,if_false] at hr flag
    have done : Exec τ (fun u => u.Fits b) (simulate P) t t 1 :=
      .done (by rw [flag,hr.zero])
    exact ⟨t,_,.again (by rw [run,r.zero]; decide) ex done,by omega,hr,flag,out,save⟩
  induction k generalizing elapsed c s with
  | zero =>
    simpa [arrayExecute] using terminal repr (inside_mono inside (by omega)) running hs halted
  | succ k ih =>
    cases step : arrayStep P c with
    | none =>
      obtain ⟨t,steps,ex,bound,hr,flag,out,save⟩ :=
        terminal repr (inside_mono inside (by omega)) running hs step
      refine ⟨t,steps,ex,?_,by simpa [arrayExecute,step] using hr,flag,out,save⟩
      rw [Nat.succ_mul]; omega
    | some c' =>
      obtain ⟨mid,j,ex,hj,hr,flag,out,save⟩ := tick_exec (τ := τ) c repr (inside_mono inside (by omega))
        running hb hbase hstate hwidth hs
        (fun _ he => inside_mono (inside_next inside he) (by omega))
      simp only [step,Option.getD_some,Option.isSome_some,if_true] at hr flag
      have hh : arrayStep P (arrayExecute P k c') = none := by simpa [arrayExecute,step] using halted
      obtain ⟨t,l,loop,hl,rt,ft,ot,st⟩ := ih (elapsed+1) (by omega) c' mid hr
        (inside_next inside step) flag (ex.post hs) hh
      refine ⟨t,_,.again (by rw [running,repr.zero]; decide) ex loop,?_,
        by simpa [arrayExecute,step] using rt,ft,ot.trans out,fun a ha => (st a ha).trans (save a ha)⟩
      rw [Nat.succ_mul]; omega

end EditGV897.Main.Indexed.RAM

end MultitapeRun

section MultitapeLayout

namespace EditGV897.Main.Indexed.RAM

open TargetedSamplers.Structured

/-- Five copy registers immediately above the tape-head registers. The following four
slots contain the base, time bound, input length, and computed tape stride. -/
def blockReg (P : Program) (j : ℕ) := 5+NT P+j

def copyRegs (P : Program) : Fin 5 ↪ ℕ := ⟨fun j => blockReg P j.val,fun i j eq => Fin.ext (by simpa [blockReg] using eq)⟩

/-- Allocate one pointer per physical tape while advancing the end-of-block register.
The tape count is fixed at compilation; the base, time bound and stride are run-time data. -/
def placeHeads (P : Program) : ℕ → Cmd
  | 0 => .skip
  | i+1 => .seq (placeHeads P i) (.seq (.op (.add (5+i) (blockReg P 1) (blockReg P 6)))
      (.op (.add (blockReg P 1) (blockReg P 1) (blockReg P 8))))

theorem placeHeads_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (P : Program) (base time k : ℕ)
    (hk : k ≤ NT P) (s : Store) (fit : s.Fits b) (start : s.mem (blockReg P 1) = base)
    (ht : s.mem (blockReg P 6) = time) (stride : s.mem (blockReg P 8) = 2*time+1)
    (width : (base+NT P*(2*time+1)).size ≤ b) :
    ∃ u, Exec τ (fun v => v.Fits b) (placeHeads P k) s u (2*k) ∧
      u.mem (blockReg P 1) = base+k*(2*time+1) ∧ u.out = s.out ∧
      (∀ j < k, u.mem (5+j) = tapeAddress base time j time) ∧
      ∀ a, a ≠ blockReg P 1 → (a < 5 ∨ 5+k ≤ a) → u.mem a = s.mem a := by
  induction k with
  | zero =>
    exact ⟨s,.skip _,by simpa using start,rfl,by simp,fun _ _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨u,ex,fin,out,heads,save⟩ := ih (by omega)
    have bound : base+(k+1)*(2*time+1) ≤ base+NT P*(2*time+1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
    have old := ex.post fit
    have rt (j : ℕ) (d : j ≠ 1) : u.mem (blockReg P j) = s.mem (blockReg P j) := by
      apply save
      · simp [blockReg,d]
      · right; unfold blockReg; omega
    let ptr := 5+k
    let u₁ := u.write ptr (tapeAddress base time k time)
    let next := u₁.write (blockReg P 1) (base+(k+1)*(2*time+1))
    have ep : (Op.add ptr (blockReg P 1) (blockReg P 6)).eval τ u = u₁ := by
      simp [Op.eval,fin,rt 6 (by decide),ht,u₁,tapeAddress]
    have hpw : (tapeAddress base time k time).size ≤ b :=
      (Nat.size_le_size (tapeAddress_lt (by omega : k < NT P) (by omega : time < 2*time+1)).le).trans width
    have f₁ : u₁.Fits b := Store.write_fits old _ hpw
    have e₁ : Exec τ (fun v => v.Fits b) (.op (.add ptr (blockReg P 1) (blockReg P 6))) u u₁ 1 := by
      simpa only [ep] using (Exec.op (τ := τ) (inv := fun v => v.Fits b) u (.add ptr (blockReg P 1) (blockReg P 6)) (by rwa [ep]))
    have sep (j : ℕ) : blockReg P j ≠ ptr := by dsimp [blockReg,ptr]; omega
    have pre (j : ℕ) : u₁.mem (blockReg P j) = u.mem (blockReg P j) := by simp [u₁,Store.write,sep]
    have el : (Op.add (blockReg P 1) (blockReg P 1) (blockReg P 8)).eval τ u₁ = next := by
      simp [Op.eval,next,pre,fin,rt 8 (by decide),stride,Nat.succ_mul,Nat.add_assoc]
    have fl : next.Fits b := Store.write_fits f₁ _ ((Nat.size_le_size bound).trans width)
    have e₂ : Exec τ (fun v => v.Fits b) (.op (.add (blockReg P 1) (blockReg P 1) (blockReg P 8))) u₁ next 1 := by
      simpa only [el] using (Exec.op (τ := τ) (inv := fun v => v.Fits b) u₁ (.add (blockReg P 1) (blockReg P 1) (blockReg P 8)) (by rwa [el]))
    refine ⟨next,?_,by simp [next,Store.write],out,?_,?_⟩
    · simpa [placeHeads,Nat.mul_succ] using ex.seq (e₁.seq e₂)
    · intro j h
      have he : 5+j ≠ blockReg P 1 := by dsimp [blockReg]; omega
      by_cases eq : j = k
      · simp [next,u₁,Store.write,ptr,he,eq,Ne.symm (sep 1)]
      · simpa [next,u₁,Store.write,ptr,he,eq] using heads j (by omega)
    · intro a ne outside
      have neq : a ≠ ptr := by dsimp [ptr]; omega
      simpa [next,u₁,Store.write,ne,neq] using save a ne (by omega)

end EditGV897.Main.Indexed.RAM

end MultitapeLayout

section MultitapeInput

namespace EditGV897.Main.Indexed.RAM

open TargetedSamplers.Structured

private theorem source_symbol (input : List Bool) (x time : ℕ) :
    (match ((x : ℤ) - time) with
      | .ofNat j => input[j]?
      | .negSucc _ => none) =
      if time ≤ x ∧ x < time+input.length then input[x-time]? else none := by
  by_cases h : time ≤ x
  · have eq : (x : ℤ) - time = Int.ofNat (x-time) := (Int.natCast_sub h).symm
    rw [eq]
    by_cases h' : x < time+input.length
    · simp [h,h']
    · simp [h,h', List.getElem?_eq_none (show input.length ≤ x-time by omega)]
  · have eq : (x : ℤ) - time = Int.negSucc (time-x-1) := by omega
    simp [eq,h]

/-- The mathematical initial tape restricted to the allocated window is a single copied
interval, on tape zero, with blanks before, after and on all the other tapes. -/
theorem initial_symbol {P : Program} (input : List Bool) (base time : ℕ) (hlen : input.length ≤ time+1)
    (i : Fin (NT P)) (z : Fin (2*time+1)) :
    let addr := tapeAddress base time i.val z.val
    (initialArray P input).mem i ((z.val : ℤ)-time) =
      if base+time ≤ addr ∧ addr < base+time+input.length then input[addr-(base+time)]? else none := by
  dsimp only [initialArray]
  by_cases hi : i.val = 0
  · rw [if_pos hi]
    trans (if time ≤ z.val ∧ z.val < time+input.length then input[z.val-time]? else none)
    · have eq := source_symbol input z.val time
      cases hz : (z.val : ℤ)-(time : ℤ) <;> simp only [hz] at eq ⊢ <;> exact eq
    have e : tapeAddress base time i.val z.val = base+z.val := by simp [tapeAddress,hi]
    rw [e]
    simp [Nat.add_assoc,Nat.add_sub_add_left]
  · have low : 2*time+1 ≤ i.val*(2*time+1) := by
      simpa using Nat.mul_le_mul_right (2*time+1) (show 1 ≤ i.val by omega)
    simp [hi,tapeAddress,show ¬base+i.val*(2*time+1)+z.val < base+time+input.length by omega]

def initializeData (P : Program) : Cmd :=
  let r := copyRegs P
  .seq (fillRange (r 0) (r 1) (r 2) 0)
    (.seq (.op (.add (r 0) (headReg (⟨0,by dsimp [NT]; omega⟩ : Fin (NT P))) 0))
      (.seq (.op (.add (r 1) (r 0) (blockReg P 7))) (copyRange r)))

/-- Caller-provided input bits are stored as 1 for false and 2 for true. Initialize all
tapes even when old data occupy the window, preserving every cell belonging to the caller. -/
theorem initializeData_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (P : Program) (base time src : ℕ)
    (input : List Bool) (s : Store) (fit : s.Fits b) (hlen : input.length ≤ time+1)
    (area : blockReg P 9 ≤ base) (sourceArea : blockReg P 9 ≤ src)
    (disjoint : src+input.length ≤ base ∨ base+NT P*(2*time+1) ≤ src)
    (bw : (base+NT P*(2*time+1)).size ≤ b) (sw : (src+input.length).size ≤ b)
    (zero : s.mem 0 = 0) (one : s.mem 1 = 1) (state : s.mem 3 = 0) (live : s.mem 4 = 1)
    (heads : ∀ i : Fin (NT P), s.mem (headReg i) = tapeAddress base time i.val time)
    (dest : s.mem (copyRegs P 0) = base) (limit : s.mem (copyRegs P 1) = base+NT P*(2*time+1))
    (unit : s.mem (copyRegs P 2) = 1) (source : s.mem (copyRegs P 3) = src)
    (size : s.mem (blockReg P 7) = input.length)
    (bits : ∀ j < input.length, s.mem (src+j) = symbolCode input[j]?) :
    ∃ t j, Exec τ (fun u => u.Fits b) (initializeData P) s t j ∧
      j ≤ 4*(NT P*(2*time+1))+6*input.length+4 ∧ Holds base time (initialArray P input) t ∧
      t.mem 4 = 1 ∧ t.out = s.out ∧
      ∀ a, blockReg P 9 ≤ a → (a < base ∨ base+NT P*(2*time+1) ≤ a) → t.mem a = s.mem a := by
  let r := copyRegs P
  let endPos := base+NT P*(2*time+1)
  let first := base+time
  have regval (i : Fin 5) : r i = blockReg P i.val := rfl
  have rlo (i : Fin 5) : r i < blockReg P 9 := by rw [regval]; have := i.isLt; unfold blockReg; omega
  have hsize : blockReg P 7 < blockReg P 9 := by simp [blockReg]
  have hp (i : Fin (NT P)) : headReg i < blockReg P 0 := by simp [headReg,blockReg]
  have hc (i : Fin 5) : blockReg P 0 ≤ r i := by simp [regval,blockReg]
  have firstBound : first+input.length ≤ endPos := by
    have nt : 1 ≤ NT P := by unfold NT; omega
    have h : 2*time+1 ≤ NT P*(2*time+1) := by simpa using Nat.mul_le_mul_right (2*time+1) nt
    dsimp [first,endPos]; omega
  have dw := (Nat.size_le_size firstBound).trans bw
  have startW := (Nat.size_le_size (show first ≤ first+input.length by omega)).trans dw
  have rne {i j : Fin 5} (ne : i ≠ j) : r i ≠ r j := r.injective.ne ne
  obtain ⟨mid,j,fill,hj,_,out,filled⟩ := fillRange_exec (τ := τ) (r 0) (r 1) (r 2) 0 base (NT P*(2*time+1)) s
    dest limit unit ⟨rne (by decide),rne (by decide),by simp [regval,blockReg]⟩
    ⟨(rlo _).trans_le area,(rlo _).trans_le area,(rlo _).trans_le area,by dsimp [blockReg] at area; omega⟩ fit bw
  have midSave (a : ℕ) (hne : a ≠ r 0) (hl : a < base ∨ endPos ≤ a) : mid.mem a = s.mem a := by
    rw [filled a hne,if_neg (by dsimp [endPos] at hl; omega)]
  have midZero (a : ℕ) (hs : base ≤ a) (he : a < endPos) : mid.mem a = 0 := by
    rw [filled a (by have := rlo 0; omega), if_pos ⟨hs,he⟩,zero]
  let h₀ := headReg (⟨0,by dsimp [NT]; omega⟩ : Fin (NT P))
  have head0 : mid.mem h₀ = first := by
    have low : h₀ < r 0 := by exact (hp _).trans_le (hc 0)
    rw [midSave _ low.ne (.inl (low.trans_le ((rlo 0).trans_le area).le))]
    simpa [h₀,tapeAddress,first] using heads ⟨0,by dsimp [NT]; omega⟩
  have low0 : 0 < blockReg P 0 := by simp [blockReg]
  have mz : mid.mem 0 = 0 := (midSave 0 (by have := hc 0; omega) (.inl (by have := rlo 0; have := hc 0; omega))).trans zero
  let u := mid.write (r 0) first
  let v := u.write (r 1) (first+input.length)
  have eu : (Op.add (r 0) h₀ 0).eval τ mid = u := by simp [Op.eval,u,head0,mz]
  have fu := Store.write_fits (fill.post fit) (r 0) startW
  have exu : Exec τ (fun st => st.Fits b) (.op (.add (r 0) h₀ 0)) mid u 1 := by
    simpa only [eu] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) mid (.add (r 0) h₀ 0) (by rwa [eu]))
  have usize : u.mem (blockReg P 7) = input.length := by
    have ne : blockReg P 7 ≠ r 0 := by simp [regval,blockReg]
    simpa [u,Store.write,ne] using (midSave _ ne (.inl (hsize.trans_le area))).trans size
  have ev : (Op.add (r 1) (r 0) (blockReg P 7)).eval τ u = v := by
    simp only [Op.eval,v,usize,show u.mem (r 0) = first by simp [u,Store.write]]
  have fv : v.Fits b := Store.write_fits fu _ dw
  have exv : Exec τ (fun st => st.Fits b) (.op (.add (r 1) (r 0) (blockReg P 7))) u v 1 := by
    simpa only [ev] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) u (.add (r 1) (r 0) (blockReg P 7)) (by rwa [ev]))
  have frame (a : ℕ) (h0 : a ≠ r 0) (h1 : a ≠ r 1) : v.mem a = mid.mem a := by simp [v,u,Store.write,h0,h1]
  have stable (a : Fin 5) (n0 : a ≠ 0) (n1 : a ≠ 1) : v.mem (r a) = s.mem (r a) :=
    (frame _ (rne n0) (rne n1)).trans (midSave _ (rne n0) (.inl ((rlo a).trans_le area)))
  have ptr : v.mem (r 0) = first := by simp [v,u,Store.write,rne (by decide : (0:Fin 5) ≠ 1)]
  obtain ⟨t,l,copy,hl,_,_,ot,copied⟩ := copyRange_exec (τ := τ) r src first input.length v
    ((stable 3 (by decide) (by decide)).trans source) ptr (by simp [v,Store.write])
    ((stable 2 (by decide) (by decide)).trans unit)
    (fun i => ⟨(rlo i).trans_le sourceArea,by have := (rlo i).trans_le area; dsimp [first]; omega⟩)
    (by rcases disjoint with hd|hd
        · exact .inl (by dsimp [first]; omega)
        · exact .inr (firstBound.trans hd)) fv sw dw
  have boundLow (a : ℕ) (ll : a < blockReg P 0) : t.mem a = s.mem a := by
    have nreg (i : Fin 5) : a ≠ r i := (ll.trans_le (hc i)).ne
    have ha := ll.trans_le ((hc 0).trans ((rlo 0).trans_le area).le)
    rw [copied a (nreg 0) (nreg 3) (nreg 4), if_neg (by dsimp [first]; omega),
      frame a (nreg 0) (nreg 1), midSave a (nreg 0) (.inl ha)]
  have large (a : ℕ) (lo : blockReg P 9 ≤ a) (i : Fin 5) : a ≠ r i := ((rlo i).trans_le lo).ne.symm
  have srcRead (j : ℕ) (hj' : j < input.length) : v.mem (src+j) = symbolCode input[j]? := by
    have low : blockReg P 9 ≤ src+j := by omega
    exact (frame _ (large _ low 0) (large _ low 1)).trans ((midSave _ (large _ low 0)
      (by rcases disjoint with hd|hd
          · exact .inl (by omega)
          · exact .inr (by dsimp [endPos]; omega))).trans (bits j hj'))
  refine ⟨t,_,fill.seq (exu.seq (exv.seq copy)),by omega,?_,
    (boundLow 4 (by dsimp [blockReg]; omega)).trans live,ot.trans out,?_⟩
  · refine ⟨(boundLow 0 low0).trans zero,(boundLow 1 (by dsimp [blockReg]; omega)).trans one,
      (boundLow 3 (by dsimp [blockReg]; omega)).trans state,?_,?_⟩
    · intro i
      simpa [headAddr,initialArray,cellIndex] using (boundLow _ (hp i)).trans (heads i)
    · intro i z
      let addr := tapeAddress base time i.val z.val
      have lo : base ≤ addr := cell_ge_base ..
      have hi : addr < endPos := tapeAddress_lt i.isLt z.isLt
      have free := large addr (area.trans lo)
      change t.mem addr = symbolCode ((initialArray P input).mem i ((z.val : ℤ)-time))
      rw [initial_symbol input base time hlen i z]
      change t.mem addr = symbolCode (if first ≤ addr ∧ addr < first+input.length then input[addr-first]? else none)
      rw [copied addr (free 0) (free 3) (free 4)]
      by_cases yes : first ≤ addr ∧ addr < first+input.length
      · simpa only [if_pos yes] using srcRead (addr-first) (by omega)
      · simp only [if_neg yes]
        exact (frame addr (free 0) (free 1)).trans (midZero addr lo hi)
  · intro a upper outside
    have free := large a upper
    have hn : ¬(first ≤ a ∧ a < first+input.length) := by dsimp [first,endPos] at *; omega
    rw [copied a (free 0) (free 3) (free 4), if_neg hn,frame a (free 0) (free 1)]
    exact midSave a (free 0) outside

end EditGV897.Main.Indexed.RAM

end MultitapeInput

section MultitapePrepare

namespace EditGV897.Main.Indexed.RAM

open TargetedSamplers.Structured

/-- The four scalar arguments are in slots 3, 5, 6 and 7 above the head pointers:
source address, tape-window base, time, and source length. -/
def prepareRegs (P : Program) : Fragment := sequence [
  .op (.const 0 0), .op (.const 1 1), .op (.const 3 0), .op (.const 4 1),
  .op (.const (blockReg P 2) 1), .op (.add (blockReg P 0) (blockReg P 5) 0),
  .op (.add (blockReg P 1) (blockReg P 5) 0), .op (.add (blockReg P 8) (blockReg P 6) (blockReg P 6)),
  .op (.add (blockReg P 8) (blockReg P 8) 1)]

structure Prepared (P : Program) (base time src len : ℕ) (s : Store) : Prop where
  zero : s.mem 0 = 0
  one : s.mem 1 = 1
  state : s.mem 3 = 0
  live : s.mem 4 = 1
  dest : s.mem (blockReg P 0) = base
  limit : s.mem (blockReg P 1) = base
  unit : s.mem (blockReg P 2) = 1
  source : s.mem (blockReg P 3) = src
  timeArg : s.mem (blockReg P 6) = time
  lenArg : s.mem (blockReg P 7) = len
  stride : s.mem (blockReg P 8) = 2*time+1

theorem prepareRegs_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (P : Program) (s : Store)
    (base time src len : ℕ) (baseArg : s.mem (blockReg P 5) = base) (timeArg : s.mem (blockReg P 6) = time)
    (srcArg : s.mem (blockReg P 3) = src) (lenArg : s.mem (blockReg P 7) = len)
    (hb : 2 ≤ b) (bw : (2*time+1).size ≤ b) (fit : s.Fits b) :
    ∃ u, Exec τ (fun st => st.Fits b) (prepareRegs P).cmd s u 9 ∧
      Prepared P base time src len u ∧ u.out = s.out ∧
      ∀ a, blockReg P 9 ≤ a → u.mem a = s.mem a := by
  let r := blockReg P
  have distinct (i j : ℕ) : r i = r j ↔ i = j := by simp [r,blockReg]
  have low (i a : ℕ) (ha : a < 5) : r i ≠ a := by dsimp [r,blockReg]; omega
  have lower (i a : ℕ) (ha : a < 5) : a ≠ r i := (low i a ha).symm
  have hbase : base.size ≤ b := baseArg ▸ fit (r 5)
  have hd : (time+time).size ≤ b := (Nat.size_le_size (by omega : time+time ≤ 2*time+1)).trans bw
  let core := (((s.write 0 0).write 1 1).write 3 0).write 4 1
  let args := ((core.write (r 2) 1).write (r 0) base).write (r 1) base
  let u := (args.write (r 8) (time+time)).write (r 8) (time+time+1)
  have regEq (i j : ℕ) (hne : i ≠ j) : blockReg P i ≠ blockReg P j := fun h => hne ((distinct i j).mp h)
  have core₁ (i : ℕ) : (blockReg P i ≠ 0 ∧ blockReg P i ≠ 1 ∧ blockReg P i ≠ 3 ∧ blockReg P i ≠ 4) :=
    ⟨low i 0 (by decide),low i 1 (by decide),low i 3 (by decide),low i 4 (by decide)⟩
  have privateBelow (a : ℕ) (ha : a < 5) (i : ℕ) : a ≠ blockReg P i := lower i a ha
  have run : ((prepareRegs P).run τ s).last = u := by
    simp (disch := decide) [prepareRegs,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,u,args,core,r,Store.write,Function.update_apply,
      core₁,privateBelow,regEq,baseArg,timeArg]
  have steps : ((prepareRegs P).run τ s).steps = 9 := rfl
  have hd' : (time+time+1).size ≤ b := by simpa [two_mul] using bw
  have width : ((prepareRegs P).run τ s).writeWidth ≤ b := by
    simp (disch := decide) [prepareRegs,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,Function.update_apply,
      core₁,privateBelow,regEq,baseArg,timeArg,hbase,hd,hd'] <;> omega
  have exec := (prepareRegs P).exec τ s b fit width
  rw [run,steps] at exec
  refine ⟨u,exec,?_,rfl,?_⟩
  · constructor <;>
      simp (disch := decide) [u,args,core,r,Store.write,Function.update_apply,core₁,regEq,privateBelow,
        baseArg,timeArg,srcArg,lenArg,two_mul]
  · intro a ha
    have above (i : ℕ) (hi : i < 9) : a ≠ r i := by dsimp [r,blockReg] at *; omega
    have notLow (i : ℕ) (hi : i < 5) : a ≠ i := by dsimp [blockReg] at ha; omega
    simp (disch := decide) [u,args,core,Store.write,Function.update_apply,above,notLow]

def prepare (P : Program) : Cmd :=
  .seq (prepareRegs P).cmd (.seq (placeHeads P (NT P)) (initializeData P))

/-- Build the complete initial configuration in a previously used workspace, starting with
four scalar arguments and the encoded input in caller memory. -/
theorem prepare_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (P : Program) (base time src : ℕ) (input : List Bool)
    (s : Store) (fit : s.Fits b) (hb : 2 ≤ b) (hlen : input.length ≤ time+1)
    (area : blockReg P 9 ≤ base) (sourceArea : blockReg P 9 ≤ src)
    (disjoint : src+input.length ≤ base ∨ base+NT P*(2*time+1) ≤ src)
    (bw : (base+NT P*(2*time+1)).size ≤ b) (sw : (src+input.length).size ≤ b)
    (srcArg : s.mem (blockReg P 3) = src) (baseArg : s.mem (blockReg P 5) = base)
    (timeArg : s.mem (blockReg P 6) = time) (lenArg : s.mem (blockReg P 7) = input.length)
    (bits : ∀ j < input.length, s.mem (src+j) = symbolCode input[j]?) :
    ∃ t j, Exec τ (fun u => u.Fits b) (prepare P) s t j ∧
      j ≤ 4*(NT P*(2*time+1))+6*input.length+2*NT P+13 ∧ Holds base time (initialArray P input) t ∧
      t.mem 4 = 1 ∧ t.out = s.out ∧
      ∀ a, blockReg P 9 ≤ a → (a < base ∨ base+NT P*(2*time+1) ≤ a) → t.mem a = s.mem a := by
  have stride : 2*time+1 ≤ base+NT P*(2*time+1) := by
    have h := Nat.mul_le_mul_right (2*time+1) (show 1 ≤ NT P by dsimp [NT]; omega)
    simp only [Nat.one_mul] at h
    omega
  obtain ⟨u,ex,regs,out,frame⟩ := prepareRegs_exec (τ := τ) P s base time src input.length baseArg timeArg
    srcArg lenArg hb ((Nat.size_le_size stride).trans bw) fit
  obtain ⟨v,heads,limit,hov,pos,save⟩ := placeHeads_exec (τ := τ) P base time (NT P) le_rfl u (ex.post fit)
    regs.limit regs.timeArg regs.stride bw
  have low (a : ℕ) (ha : a < 5) : v.mem a = u.mem a := save a (by dsimp [blockReg]; omega) (.inl ha)
  have same (i : ℕ) (hi : i ≠ 1) : v.mem (blockReg P i) = u.mem (blockReg P i) :=
    save _ (by simp [blockReg,hi]) (.inr (by simp [blockReg]))
  have keep (a : ℕ) (ha : blockReg P 9 ≤ a) : v.mem a = s.mem a := by
    refine (save _ ?_ (.inr ?_)).trans (frame a ha) <;> dsimp [blockReg] at * <;> omega
  obtain ⟨t,j,init,hj,repr,live,ot,fr⟩ := initializeData_exec (τ := τ) P base time src input v
    (heads.post (ex.post fit)) hlen area sourceArea disjoint bw sw
    ((low 0 (by decide)).trans regs.zero) ((low 1 (by decide)).trans regs.one) ((low 3 (by decide)).trans regs.state)
    ((low 4 (by decide)).trans regs.live) (fun i => pos i.val i.isLt) ((same 0 (by decide)).trans regs.dest)
    limit ((same 2 (by decide)).trans regs.unit) ((same 3 (by decide)).trans regs.source)
    ((same 7 (by decide)).trans regs.lenArg) (fun j hj => (keep _ (by omega)).trans (bits j hj))
  exact ⟨t,_,ex.seq (heads.seq init),by omega,repr,live,ot.trans (hov.trans out),
    fun a ha h => (fr a ha h).trans (keep a ha)⟩

end EditGV897.Main.Indexed.RAM

end MultitapePrepare

section AffineRAMBuffer

namespace AffinePrefixEnumeration

open EditGV897.Main EditGV897.Main.Indexed EditGV897.Main.Indexed.RAM

open TargetedSamplers.Structured

/-- The workspace time parameter passed to the machine is bounded by one polynomial in
the matrix dimension and row count, including all fixed-prefix rows. -/
theorem query_window_polynomial (A d n : ℕ) (E : List (Equation n)) (k : ℕ) (p : List Bool) :
    let s := n+(E.length+p.length)
    polyBudget A d s+(queryPayload E k p).length ≤ (A+4)*(s+1)^(d+2) := by
  intro s
  have h₁ := Nat.pow_le_pow_right (show 0 < s+1 by omega) (show d ≤ d+2 by omega)
  have h₂ := Nat.pow_le_pow_right (show 0 < s+1 by omega) (show 2 ≤ d+2 by omega)
  have hi : (queryPayload E k p).length ≤ 4*(s+1)^2 := queryPayload_size E k p
  simpa [polyBudget,Nat.add_mul] using Nat.add_le_add (Nat.mul_le_mul_left A h₁) (hi.trans (Nat.mul_le_mul_left 4 h₂))

end AffinePrefixEnumeration

end AffineRAMBuffer

section AffineRAMFeasibility

namespace AffinePrefixEnumeration

open EditGV897.Main EditGV897.Main.Indexed EditGV897.Main.Indexed.RAM

open TargetedSamplers.Structured TargetedSamplers.Structured.EquationBuffer

/-- A polynomial coefficient for the complete feasibility call, including serialization
and evaluation of the simulator's time allowance at the actual input size. -/
def tableConstant (P : Program) (A d : ℕ) : ℕ :=
  (A+5)*(tickBound P+8*NT P+8)+8*d+2*NT P+82

theorem tableSteps_le (P : Program) (A d n : ℕ) (E : List (Equation n)) (k : ℕ) (p : List Bool) :
    let size := n+(E.length+p.length)
    let len := (queryPayload E k p).length
    let time := polyBudget A d size+len
    11*len+d*(4*(size+1)+4)+23+((time+1)*(tickBound P+8*NT P+8)+2*NT P+15) ≤
      tableConstant P A d*(size+1)^(d+2) := by
  intro size len time
  let X := (size+1)^(d+2)
  have hx : 1 ≤ X := Nat.succ_le_of_lt (pow_pos (by omega : 0 < size+1) _)
  have atSize : size+1 ≤ X := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < size+1) (by omega : 1 ≤ d+2)
  have square : (size+1)^2 ≤ X := Nat.pow_le_pow_right (by omega) (by omega)
  have bits : len ≤ 4*X := (queryPayload_size E k p).trans (Nat.mul_le_mul_left 4 square)
  have timeCap : time ≤ (A+4)*X := query_window_polynomial A d n E k p
  have ticks := Nat.mul_le_mul_right (tickBound P+8*NT P+8)
    (by nlinarith only [timeCap,hx] : time+1 ≤ (A+5)*X)
  have degree := Nat.mul_le_mul_left d (by omega : 4*(size+1)+4 ≤ 8*X)
  have weight (u : ℕ) : u ≤ u*X := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left u hx
  calc
    _ ≤ 44*X + d*(8*X)+23*X + ((A+5)*X*(tickBound P+8*NT P+8)+(2*NT P)*X+15*X) := by
      linarith only [bits,ticks,degree,weight 23,weight 15,weight (2*NT P)]
    _ = tableConstant P A d*(size+1)^(d+2) := by dsimp [tableConstant,X]; ring

end AffinePrefixEnumeration

end AffineRAMFeasibility

section AffineRankEnumeration

namespace AffinePrefixEnumeration

open BoundedEnumeration EditGV897.Main

theorem count_width {n : ℕ} (E : List (Equation n)) : (affineCount E).size ≤ n+1 := by
  have count : affineCount E ≤ 2^n := by
    rw [affine_count_correct]
    simpa [Word] using Finset.card_le_univ (affineSet E)
  apply Nat.size_le.mpr
  rw [pow_succ]
  have := Nat.one_le_two_pow (n := n)
  omega

end AffinePrefixEnumeration

end AffineRankEnumeration

section LogCostBinaryReadback

namespace TargetedSamplers.Structured.BinaryReadback

def eval (v : ℕ) : List Bool → ℕ
  | [] => v
  | bit::bits => eval (v+v+bit.toNat) bits

theorem eval_append (v : ℕ) (xs ys : List Bool) : eval v (xs++ys) = eval (eval v xs) ys := by
  induction xs generalizing v with
  | nil => rfl
  | cons bit xs ih => exact ih _

theorem eval_binary (n : ℕ) : eval 0 n.bits.reverse = n := by
  induction n using Nat.binaryRec with
  | zero => rfl
  | bit bit n ih =>
    by_cases hn : n=0
    · subst n; cases bit <;> rfl
    · rw [Nat.bits_append_bit _ _ (fun h => (hn h).elim),List.reverse_cons,eval_append,ih]
      cases bit <;> simp [eval,Nat.bit] <;> omega

/-- Read ternary cells containing MSB-first binary digits terminated by a blank.
The state uses the simulator's five scratch registers and leaves all tape windows intact. -/
def digit : Fragment := Structured.sequence [
  .op (.add 4 4 4),.branch 2 1 .skip (.op (.add 4 4 1)),
  .op (.add 3 3 1),.op (.load 2 3)]

def scan : Cmd := .whileGt 2 0 digit.cmd

structure State (addr acc : ℕ) (xs : List Bool) (s : Store) : Prop where
  zero : s.mem 0=0
  one : s.mem 1=1
  symbol : s.mem 2=symbolCode xs.head?
  ptr : s.mem 3=addr
  value : s.mem 4=acc
  table : ∀ i ≤ xs.length, s.mem (addr+i)=symbolCode xs[i]?

private theorem digit_exec {τ : Tapes} {b addr acc : ℕ} (bit : Bool) (xs : List Bool) (s : Store)
    (st : State addr acc (bit::xs) s) (above : 5 ≤ addr) (fit : s.Fits b)
    (pa : (addr+1).size ≤ b) (wa : (acc+acc+bit.toNat).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) digit.cmd s t j ∧ j ≤ 6 ∧
      State (addr+1) (acc+acc+bit.toNat) xs t ∧ t.out=s.out ∧ ∀ i ≥ 5, t.mem i=s.mem i := by
  let t := (digit.run τ s).last
  have away (i r : ℕ) (hi : 5 ≤ i) (hr : r < 5) : i ≠ r := by omega
  have atNext : s.mem (addr+1) = symbolCode xs.head? := by
    have h := st.table 1 (by simp)
    simpa [List.head?_eq_getElem?] using h
  have wd := (Nat.size_le_size (show acc+acc ≤ acc+acc+bit.toNat by omega)).trans wa
  have memory (i : ℕ) (hi : 5 ≤ i) : t.mem i = s.mem i := by
    cases bit <;> simp (disch := omega) [t,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,st.ptr,st.symbol,st.one,symbolCode,away]
  have widths : (digit.run τ s).writeWidth ≤ b := by
    cases bit <;> simp (disch := omega) [digit,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,st.ptr,st.symbol,st.one,st.value,symbolCode,pa,wa,wd,away,fit (addr+1)] at * <;> assumption
  refine ⟨t,_,digit.exec τ s b fit widths,?_,⟨?_,?_,?_,?_,?_,?_⟩,?_,memory⟩
  · cases bit <;> simp [digit,Structured.sequence,Fragment.run,Op.eval,Store.write,st.symbol,st.one,symbolCode]
  · cases bit <;> simp [t,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,st.symbol,st.one,symbolCode,st.zero]
  · cases bit <;> simp [t,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,st.symbol,st.one,symbolCode]
  · cases bit <;> simp (disch := omega) [t,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      st.ptr,st.symbol,st.one,symbolCode,away,atNext]
  · cases bit <;> simp [t,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,st.ptr,st.symbol,st.one,symbolCode]
  · cases bit <;> simp [t,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,st.value,st.symbol,st.one,symbolCode]
  · intro j hj
    rw [memory _ (by omega),show addr+1+j = addr+(j+1) by omega,st.table (j+1) (by simp; omega)]
    simp
  · cases bit <;> simp [t,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,st.symbol,st.one,symbolCode]

theorem scan_exec {τ : Tapes} {b : ℕ} (xs : List Bool) (addr acc : ℕ) (s : Store)
    (st : State addr acc xs s) (above : 5 ≤ addr) (fit : s.Fits b)
    (endRoom : (addr+xs.length).size ≤ b) (room : ((acc+1)*2^xs.length).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) scan s t j ∧ j ≤ 8*xs.length+1 ∧
      t.mem 4=eval acc xs ∧ t.out=s.out ∧ ∀ i ≥ 5, t.mem i=s.mem i := by
  induction xs generalizing s addr acc with
  | nil => exact ⟨s,1,.done (by rw [st.zero,st.symbol]; decide),by simp,st.value,rfl,fun _ _ => rfl⟩
  | cons bit xs ih =>
    let a := acc+acc+bit.toNat
    have stepRoom : (a+1)*2^xs.length ≤ (acc+1)*2^(bit::xs).length := by
      have bd := bit.toNat_le
      simp only [List.length_cons,pow_succ]
      rw [show (acc+1)*(2^xs.length*2) = ((acc+1)*2)*2^xs.length by ring]
      exact Nat.mul_le_mul_right _ (by dsimp [a]; omega)
    have width := (Nat.size_le_size stepRoom).trans room
    have small : a.size ≤ b := (Nat.size_le_size (show a ≤ (a+1)*2^xs.length by
      have := Nat.mul_le_mul_left (a+1) (Nat.one_le_two_pow (n := xs.length)); omega)).trans width
    have ep : addr+1+xs.length = addr+(bit::xs).length := by simp; omega
    obtain ⟨u,i,first,wi,next,fo,fr⟩ := digit_exec (τ := τ) bit xs s st above fit
      ((Nat.size_le_size (by simp : addr+1 ≤ addr+(bit::xs).length)).trans endRoom) small
    obtain ⟨t,j,rest,wj,val,out,keep⟩ := ih _ _ u next (by omega) (first.post fit) (ep ▸ endRoom) width
    refine ⟨t,_,.again (by rw [st.zero,st.symbol]; cases bit <;> simp [symbolCode]) first rest,?_,val,out.trans fo,
      fun i h => (keep i h).trans (fr i h)⟩
    simp only [List.length_cons]; omega

end TargetedSamplers.Structured.BinaryReadback

end LogCostBinaryReadback

section MultitapeOutputCells

namespace EditGV897.Main.Indexed

private theorem symbol_at_nat (t : Tape) (i : ℕ) : symbol t (i:ℤ) = ((t.head::t.right)[i]?).join := by
  cases i <;> rfl

private theorem output_at {t : Tape} {bits : List Bool} (h : t.head::t.right = bits.map some ++ [none]) (i : ℕ) :
    symbol t (i:ℤ) = bits[i]? := by
  rw [symbol_at_nat,h]
  by_cases bound : i < bits.length
  · rw [List.getElem?_append_left (by simpa using bound),List.getElem?_map]
    cases bits[i]? <;> rfl
  · have end' : (bits.map some).length ≤ i := by simp; omega
    have absent : bits[i]? = none := List.getElem?_eq_none (by omega)
    rw [absent,List.getElem?_append_right end']
    cases i-(bits.map some).length <;> rfl

def outputIndex (P : Program) : Fin (P.workTapes+2) := ⟨1,by omega⟩

theorem runs_output_cells {P : Program} {input bits : List Bool} {budget : ℕ} (h : Runs P input bits budget) :
    ∃ k ≤ budget, let a := arrayExecute P k (initialArray P input)
      arrayStep P a = none ∧ ∀ i : ℕ, a.mem (outputIndex P) (a.cursor (outputIndex P)+(i:ℤ)) = bits[i]? := by
  obtain ⟨k,hk,c,he,halt,printed⟩ := h
  let a := arrayExecute P k (initialArray P input)
  have rep : Represents a c := he ▸ (initial_represents P input).execute k
  refine ⟨k,hk,?_,fun i => (rep.cell (outputIndex P) (i:ℤ)).trans (output_at printed i)⟩
  change arrayStep P a = none
  simpa [arrayStep,EditGV897.Main.step,rep.state,rep.read] using halt

namespace RAM

open TargetedSamplers.Structured

/-- Every output digit and the first blank are readable in the simulated output-tape window. -/
theorem simulate_output_cells {P : Program} {base budget time b : ℕ} {τ : TargetedSamplers.Tapes}
    {input bits : List Bool} (run : Runs P input bits budget) (window : budget+bits.length ≤ time) (s : Store)
    (repr : Holds base time (initialArray P input) s) (live : s.mem 4 = 1) (fit : s.Fits b) (hb : 2 ≤ b)
    (area : 5+NT P ≤ base) (tagW : P.states.size ≤ b) (space : (base+NT P*(2*time+1)).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (simulate P) s t j ∧ j ≤ (budget+1)*(tickBound P+2)+1 ∧
      (∀ i ≤ bits.length, t.mem (t.mem (headReg (outputIndex P))+i) = symbolCode bits[i]?) ∧
      5 ≤ t.mem (headReg (outputIndex P)) ∧ (t.mem (headReg (outputIndex P))+bits.length).size ≤ b ∧
      t.mem 0=0 ∧ t.mem 1=1 ∧ t.out=s.out ∧ ∀ a, Caller base time (NT P) a → t.mem a=s.mem a := by
  obtain ⟨k,hk,halt,printed⟩ := runs_output_cells run
  let a := arrayExecute P k (initialArray P input)
  have iz : Inside 0 (initialArray P input) := by intro i; simp [initialArray]
  obtain ⟨t,j,ex,w,mem,_,out,fr⟩ := simulate_exec (τ := τ) hb area tagW space k 0 (by omega) _ s repr iz live fit halt
  let z := a.cursor (outputIndex P)
  have displacement := cursor_bound P k (initialArray P input) (outputIndex P)
  change (0:ℤ)-k ≤ z ∧ z ≤ 0+(k:ℤ) at displacement
  have pointer : t.mem (headReg (outputIndex P)) = headAddr base time a (outputIndex P) := mem.pointer _
  obtain ⟨_,head⟩ := index_spec (time := time) (z := z) (by omega) (by omega)
  have loc (i : ℕ) (hi : i ≤ bits.length) :
      let idx := cellIndex time (z+(i:ℤ))
      idx < 2*time+1 ∧ (idx:ℤ)-time=z+i ∧
        t.mem (headReg (outputIndex P))+i=tapeAddress base time (outputIndex P).val idx := by
    intro idx
    obtain ⟨bound,addr⟩ := index_spec (time := time) (z := z+(i:ℤ)) (by omega) (by omega)
    refine ⟨bound,by dsimp [idx]; omega,?_⟩
    rw [pointer]
    change tapeAddress base time (outputIndex P).val (cellIndex time z)+i = _
    dsimp [idx,tapeAddress]; omega
  have low := cell_ge_base base time (outputIndex P).val (cellIndex time z)
  obtain ⟨bound,_,last⟩ := loc bits.length le_rfl
  have top : t.mem (headReg (outputIndex P))+bits.length ≤ base+NT P*(2*time+1) := by
    rw [last]
    change base+1*(2*time+1)+_ ≤ _
    have two := Nat.mul_le_mul_right (2*time+1) (show 2 ≤ NT P by dsimp [NT]; omega)
    omega
  refine ⟨t,j,ex,w.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega : k+1 ≤ budget+1)) 1),?_,
    by rw [pointer]; exact (by omega : 5 ≤ base).trans low,(Nat.size_le_size top).trans space,mem.zero,mem.one,out,fr⟩
  intro i hi
  obtain ⟨bound,shift,addr⟩ := loc i hi
  rw [addr,mem.cell (outputIndex P) ⟨_,bound⟩]
  change symbolCode (a.mem (outputIndex P) ((cellIndex time (z+(i:ℤ)):ℤ)-time)) = _
  rw [shift,printed]

end RAM

end EditGV897.Main.Indexed

end MultitapeOutputCells

section MultitapeBinaryReadback

namespace TargetedSamplers.Structured.BinaryReadback

def start (src : ℕ) : Fragment := Structured.sequence [
  .op (.const 4 0),.op (.add 3 src 0),.op (.load 2 3)]

def fromHead (src : ℕ) : Cmd := .seq (start src).cmd scan

theorem fromHead_exec {τ : Tapes} {b : ℕ} (src x : ℕ) (hsrc : 5 ≤ src) (s : Store)
    (zero : s.mem 0=0) (one : s.mem 1=1) (fit : s.Fits b) (low : 5 ≤ s.mem src)
    (endRoom : (s.mem src+x.bits.length).size ≤ b) (room : x.size+1 ≤ b)
    (data : ∀ i ≤ x.bits.length, s.mem (s.mem src+i) = symbolCode x.bits.reverse[i]?) :
    ∃ t j, Exec τ (fun u => u.Fits b) (fromHead src) s t j ∧ j ≤ 8*x.size+4 ∧
      t.mem 4=x ∧ t.out=s.out ∧ ∀ a ≥ 5, t.mem a=s.mem a := by
  let f := start src
  let u := (f.run τ s).last
  have addr (a : ℕ) (ha : a < 5) : s.mem src ≠ a := by omega
  have reg (a : ℕ) (ha : a < 5) : src ≠ a := by omega
  have ww : (f.run τ s).writeWidth ≤ b := by
    simp (disch := omega) [f,start,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,Function.update_apply,
      zero,reg,addr,fit src,fit (s.mem src)]
  have first : Exec τ (fun q => q.Fits b) f.cmd s u 3 := f.exec τ s b fit ww
  have keep (a : ℕ) (ha : 5 ≤ a) : u.mem a = s.mem a := by
    have far (i : ℕ) (hi : i < 5) : a ≠ i := by omega
    simp (disch := decide) [u,f,start,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,far]
  have head := data 0 (by omega)
  simp only [Nat.add_zero,← List.head?_eq_getElem?] at head
  have st : State (s.mem src) 0 x.bits.reverse u := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simp [u,f,start,Structured.sequence,Fragment.run,Op.eval,Store.write,zero]
    · simp [u,f,start,Structured.sequence,Fragment.run,Op.eval,Store.write,one]
    · simp (disch := omega) [u,f,start,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,reg,addr,zero,head]
    · simp (disch := omega) [u,f,start,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,reg,zero]
    · simp [u,f,start,Structured.sequence,Fragment.run,Op.eval,Store.write]
    · intro i hi; exact (keep _ (by omega)).trans (data _ (by simpa using hi))
  obtain ⟨t,j,read,w,val,out,fr⟩ := scan_exec (τ := τ) x.bits.reverse (s.mem src) 0 u st low (first.post fit)
    (by simpa using endRoom) (by simpa [Nat.size_eq_bits_len,Nat.size_pow] using room)
  exact ⟨t,_,first.seq read,by simp only [List.length_reverse,Nat.size_eq_bits_len] at w; omega,
    val.trans (eval_binary _),out,fun a ha => (fr a ha).trans (keep a ha)⟩

end TargetedSamplers.Structured.BinaryReadback

namespace EditGV897.Main.Indexed.RAM

open TargetedSamplers.Structured

def countOutput (P : Program) : Cmd := .seq (simulate P) (BinaryReadback.fromHead (headReg (outputIndex P)))

theorem countOutput_exec {P : Program} {base budget time b answer : ℕ} {τ : TargetedSamplers.Tapes}
    {input : List Bool} (run : Runs P input (binary answer) budget) (window : budget+answer.size ≤ time)
    (s : Store) (repr : Holds base time (initialArray P input) s) (live : s.mem 4=1)
    (fit : s.Fits b) (hb : 2 ≤ b) (area : 5+NT P ≤ base) (tagW : P.states.size ≤ b)
    (memW : (base+NT P*(2*time+1)).size ≤ b) (answerW : answer.size+1 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (countOutput P) s t j ∧
      j ≤ (budget+1)*(tickBound P+2)+8*answer.size+5 ∧ t.mem 4=answer ∧ t.out=s.out ∧
      ∀ a, Caller base time (NT P) a → t.mem a=s.mem a := by
  obtain ⟨u,i,sim,wi,data,low,span,zero,one,out,fr⟩ := simulate_output_cells (τ := τ) run
    (by simpa [binary,Nat.size_eq_bits_len] using window) s repr live fit hb area tagW memW
  obtain ⟨t,j,read,w,val,fo,keep⟩ := BinaryReadback.fromHead_exec (τ := τ) (headReg (outputIndex P)) answer
    (by dsimp [headReg]; omega) u zero one (sim.post fit) low (by simpa [binary] using span) answerW
    (by simpa [binary] using data)
  exact ⟨t,_,sim.seq read,by omega,val,fo.trans out,fun a ha => (keep a (by have := ha.1; omega)).trans (fr a ha)⟩

end EditGV897.Main.Indexed.RAM

end MultitapeBinaryReadback

section AffineCountBuffer

namespace AffinePrefixEnumeration

open EditGV897.Main EditGV897.Main.Indexed EditGV897.Main.Indexed.RAM

open TargetedSamplers.Structured

def countBuffer (P : Program) : Cmd := .seq (prepare P) (countOutput P)

/-- The same Gaussian program returns the full integer count of a pinned prefix.
The n+1-bit result fits in the existing time window allocated from the unary header. -/
theorem uniform_count_buffer : ∃ (P : Program) (A d : ℕ), 0 < A ∧
    ∀ (n : ℕ) (E : List (Equation n)) (k : ℕ) (p : List Bool),
    let bits := queryPayload E k p
    let budget := polyBudget A d (n+(E.length+p.length))
    let time := budget+bits.length
    ∀ (base src b : ℕ) (s : Store) (τ : TargetedSamplers.Tapes),
      s.Fits b → n+2 ≤ b → P.states.size ≤ b → blockReg P 9 ≤ base → blockReg P 9 ≤ src →
      (src+bits.length ≤ base ∨ base+NT P*(2*time+1) ≤ src) →
      (base+NT P*(2*time+1)).size ≤ b → (src+bits.length).size ≤ b →
      s.mem (blockReg P 3) = src → s.mem (blockReg P 5) = base →
      s.mem (blockReg P 6) = time → s.mem (blockReg P 7) = bits.length →
      (∀ j < bits.length, s.mem (src+j) = symbolCode bits[j]?) →
      ∃ t j, Exec τ (fun u => u.Fits b) (countBuffer P) s t j ∧
        j ≤ (time+1)*(tickBound P+8*NT P+8)+2*NT P+8*(n+1)+18 ∧
        t.mem 4=affineCount (E++pins n k p) ∧ t.out=s.out ∧
        ∀ a, blockReg P 9 ≤ a → (a < base ∨ base+NT P*(2*time+1) ≤ a) → t.mem a=s.mem a := by
  obtain ⟨P,A,d,hA,solver⟩ := uniform_count_program
  refine ⟨P,A,d,hA,?_⟩
  intro n E k p bits budget time base src b s τ fit room tagW low lowSrc regions blockSpace srcSpace srcA baseA timeA lenA table
  have run : Runs P bits (binary (affineCount (E++pins n k p))) budget := by
    simpa only [bits,budget,queryPayload_eq] using solver n E k p
  have wd := count_width (E++pins n k p)
  have header : n+1 ≤ bits.length := by simp [bits,queryPayload_eq,unary]
  have small : bits.length ≤ time := by dsimp [time]; omega
  obtain ⟨u,i,init,wi,rep,live,out,fr⟩ := prepare_exec (τ := τ) P base time src bits s fit (by omega)
    (by omega) low lowSrc regions blockSpace srcSpace srcA baseA timeA lenA table
  obtain ⟨t,j,read,wj,count,ret,keep⟩ := countOutput_exec (τ := τ) run (by dsimp [time]; omega)
    u rep live (init.post fit) (by omega) (by dsimp [blockReg] at low; omega) tagW blockSpace (by omega)
  refine ⟨t,_,init.seq read,?_,count,ret.trans out,?_⟩
  · have timeBud : budget ≤ time := by dsimp [time]; omega
    have m := Nat.mul_le_mul_right (tickBound P+2) (Nat.add_le_add_right timeBud 1)
    nlinarith only [wi,wj,wd,m,small,Nat.zero_le (NT P)]
  · intro a ha zone
    exact (keep a ⟨by dsimp [blockReg] at ha; omega,zone⟩).trans (fr a ha zone)

end AffinePrefixEnumeration

end AffineCountBuffer

section AffineRAMCountTables

namespace AffinePrefixEnumeration

open EditGV897.Main EditGV897.Main.Indexed EditGV897.Main.Indexed.RAM

open TargetedSamplers.Structured TargetedSamplers.Structured.EquationBuffer

def countTables (P : Program) (A d : ℕ) : Cmd :=
  .seq (prepareQuery (5+NT P) A d) (countBuffer P)

/-- From disjoint caller tables to the complete count of a pinned system. The same
workspace is available for the next prefix once the count has been consumed. -/
theorem uniform_table_count : ∃ (P : Program) (A d : ℕ), 0 < A ∧
    ∀ (n : ℕ) (E : List (Equation n)) (k : ℕ) (p : List Bool), k+p.length=n →
    let bits := queryPayload E k p
    let size := n+(E.length+p.length)
    let time := polyBudget A d size+bits.length
    let anchor := 5+NT P
    ∀ (base rowSrc pinSrc b : ℕ) (s : Store) (τ : TargetedSamplers.Tapes),
      QuerySource E k p base rowSrc pinSrc s → s.Fits b → n+2 ≤ b → P.states.size ≤ b →
      callReg anchor 8 ≤ base → callReg anchor 8 ≤ rowSrc → callReg anchor 8 ≤ pinSrc →
      (rowSrc+(denseWords E).length ≤ base ∨ base+bits.length ≤ rowSrc) →
      (pinSrc+p.length ≤ base ∨ base+bits.length ≤ pinSrc) →
      (rowSrc+(denseWords E).length).size ≤ b → (pinSrc+p.length).size ≤ b →
      (base+bits.length+NT P*(2*time+1)).size ≤ b →
      ∃ t j, Exec τ (fun v => v.Fits b) (countTables P A d) s t j ∧
        j ≤ (tableConstant P A d+11)*(size+1)^(d+2) ∧ t.mem 4=affineCount (E++pins n k p) ∧ t.out = s.out ∧
        ∀ a, callReg anchor 8 ≤ a → (a < base ∨ base+bits.length+NT P*(2*time+1) ≤ a) → t.mem a = s.mem a := by
  obtain ⟨P,A,d,hA,solver⟩ := uniform_count_buffer
  refine ⟨P,A,d,hA,?_⟩
  intro n E k p hp bits size time anchor base rowSrc pinSrc b s τ src fit room hstate sep sr sp ra pa rwid pwid width
  have hb : 2 ≤ b := by omega
  have lo : blockReg P 9 ≤ base := by dsimp [blockReg,callReg,anchor] at *; omega
  have bufferWidth : (base+bits.length).size ≤ b := (Nat.size_le_size (by omega)).trans width
  have tapes : 1 ≤ NT P := by dsimp [NT]; omega
  have tapeSpace := Nat.mul_le_mul_right (2*time+1) tapes
  have tw : time.size ≤ b := (Nat.size_le_size (by omega)).trans width
  obtain ⟨u,i,prepare,hi,srcA,baseA,timeA,lenA,data⟩ := prepareQuery_exec (τ := τ) anchor A d E k p
    base rowSrc pinSrc s hp.le src sep sr sp fit hb rwid pwid ra pa bufferWidth tw
  have encoded (j : ℕ) (hj : j < bits.length) : u.mem (base+j) = symbolCode bits[j]? := by
    have entry := data.data j (by simpa using hj)
    simpa only [List.getElem_map,List.getElem?_eq_getElem hj,bitWord] using entry
  obtain ⟨t,j,ask,hj,answer,out,frame⟩ := solver n E k p (base+bits.length) base b u τ (prepare.post fit)
    room hstate (by omega) lo (.inl le_rfl) width bufferWidth srcA baseA timeA lenA encoded
  have old := tableSteps_le P A d n E k p
  change 11*bits.length+d*(4*(size+1)+4)+23+((time+1)*(tickBound P+8*NT P+8)+2*NT P+15) ≤
    tableConstant P A d*(size+1)^(d+2) at old
  change i ≤ 11*bits.length+d*(4*(size+1)+4)+23 at hi
  change j ≤ (time+1)*(tickBound P+8*NT P+8)+2*NT P+8*(n+1)+18 at hj
  have hpow : size+1 ≤ (size+1)^(d+2) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < size+1) (by omega : 1 ≤ d+2)
  have hn : n+1 ≤ size+1 := by dsimp [size]; omega
  refine ⟨t,_,prepare.seq ask,?_,answer,out.trans data.output,?_⟩
  · rw [Nat.add_mul]
    omega
  · intro a high bound
    have floor : blockReg P 9 ≤ a := by dsimp [blockReg,callReg,anchor] at *; omega
    have inBuffer : a < base ∨ base+(bits.map bitWord).length ≤ a := by simp only [List.length_map]; omega
    change ∀ a, blockReg P 9 ≤ a → (a < base+bits.length ∨ base+bits.length+NT P*(2*time+1) ≤ a) → t.mem a = u.mem a at frame
    exact (frame a floor (by omega)).trans (data.frame a (by omega) inBuffer)

end AffinePrefixEnumeration

end AffineRAMCountTables

section AffineRAMCountPort

namespace AffinePrefixEnumeration

open EditGV897.Main EditGV897.Main.Indexed EditGV897.Main.Indexed.RAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.EquationBuffer

/-- The high register bank stores the dimension, source intervals and destination.
Only the first free column and the current suffix pointer vary during unranking. -/
theorem installCount_exec {τ : TargetedSamplers.Tapes} {b n : ℕ} (E : List (Equation n))
    (k : ℕ) (p : List Bool) (base row pin bank : ℕ) (s : Store)
    (size : k+p.length=n) (high : 13 < bank) (rowsHigh : 13 < row) (pinsHigh : 13 < pin)
    (port : Port E base row pin bank s) (free : s.mem (bank+6)=k) (ptr : s.mem (bank+9)=pin+k)
    (pins : ∀ i (hi : i < p.length), s.mem (pin+k+i)=bitWord p[i]) (fit : s.Fits b) :
    let t := ((installCount bank).run τ s).last
    Exec τ (fun u => u.Fits b) (installCount bank).cmd s t 9 ∧
      QuerySource E k p base row (pin+k) t ∧ t.out=s.out ∧ ∀ a, 13 < a → t.mem a=s.mem a := by
  intro t
  have separate (i j : ℕ) (hj : j ≤ 13) : bank+i ≠ j := by omega
  have far (j : ℕ) (hj : j ≤ 13) : bank ≠ j := by omega
  have ww : ((installCount bank).run τ s).writeWidth ≤ b := by
    simp (disch := omega) [installCount,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,separate,far]
    exact ⟨fit _,fit _,fit _,fit _,fit _,fit _,fit _,fit _⟩
  have frame (a : ℕ) (ha : 13 < a) : t.mem a=s.mem a := by
    have ne (j : ℕ) (hj : j ≤ 13) : a ≠ j := by omega
    simp (disch := omega) [t,installCount,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,ne]
  have lastPin : pin+n=pin+k+p.length := by omega
  refine ⟨(installCount bank).exec τ s b fit ww,⟨?_,?_,?_,?_,?_,?_,?_,?_,
    fun i hi => (frame _ (by omega)).trans (port.rowData i hi),
    fun i hi => (frame _ (by omega)).trans (pins i hi)⟩,rfl,frame⟩
  all_goals simp (disch := omega) [t,installCount,Structured.sequence,Fragment.run,Op.eval,Store.write,
    Function.update_apply,separate,far,free,ptr,port.target,port.dimension,port.rows,port.pinEnd,
    port.firstRow,port.afterRows,lastPin,show s.mem bank=base by simpa using port.target]

/-- Read the exact count from the bank and dense tables. The region of the caller
below the solver buffer holds all persistent state of the enumeration. -/
theorem uniform_count_port : ∃ (kernel : Cmd) (floor : ℕ) (stepBound workspace : ℕ → ℕ),
    (∃ c d : ℕ, ∀ N, stepBound N+workspace N ≤ c*(N+1)^d) ∧
    ∀ (n : ℕ) (E : List (Equation n)) (k : ℕ) (p : List Bool), k+p.length=n →
      ∀ (base row pin bank b : ℕ) (s : Store) (τ : TargetedSamplers.Tapes),
      let N := n+(E.length+n)
      floor ≤ bank → bank+20 ≤ row → row+(denseWords E).length ≤ pin → pin+n ≤ base →
      floor.size ≤ b → n+2 ≤ b → (base+workspace N).size ≤ b →
      Port E base row pin bank s → s.mem (bank+6)=k → s.mem (bank+9)=pin+k →
      (∀ i (hi : i < p.length), s.mem (pin+k+i)=bitWord p[i]) → s.Fits b →
      ∃ t j, Exec τ (fun u => u.Fits b) (countPort bank kernel) s t j ∧ j ≤ stepBound N ∧
        t.mem 4=affineCount (E++pins n k p) ∧ t.out=s.out ∧
        ∀ a, floor ≤ a → (a < base ∨ base+workspace N ≤ a) → t.mem a=s.mem a := by
  obtain ⟨P,A,d,hA,call⟩ := uniform_table_count
  let anchor := 5+NT P
  let floor := max (callReg anchor 8) (P.states+14)
  let c := tableConstant P A d+20
  let q := A+4
  let v := 4+NT P*(2*q+1)
  let work := fun N => c*(N+1)^(d+2)
  let span := fun N => v*(N+1)^(d+2)
  refine ⟨countTables P A d,floor,work,span,⟨c+v,d+2,fun N => by simp [work,span,Nat.add_mul]⟩,?_⟩
  intro n E k p size base row pin bank b s τ N reserved rows pinsApart freeMem floorW nw sizeW port col ptr data fit
  let S := n+(E.length+p.length)
  let bits := queryPayload E k p
  let time := polyBudget A d S+bits.length
  let X := (N+1)^(d+2)
  have small : S ≤ N := by dsimp [S,N]; omega
  have lift : (S+1)^(d+2) ≤ X := Nat.pow_le_pow_left (by omega) _
  have one : 1 ≤ X := Nat.succ_le_of_lt (pow_pos (by omega : 0 < N+1) _)
  have bitCount : bits.length ≤ 4*X := (queryPayload_size E k p).trans (Nat.mul_le_mul_left 4
    ((Nat.pow_le_pow_right (by omega : 0 < S+1) (by omega : 2 ≤ d+2)).trans lift))
  have timeCount : time ≤ q*X := (query_window_polynomial A d n E k p).trans (Nat.mul_le_mul_left q lift)
  have cap : bits.length+NT P*(2*time+1) ≤ span N := by
    have t := Nat.mul_le_mul_left (NT P) (by nlinarith only [timeCount,one] : 2*time+1 ≤ (2*q+1)*X)
    change _ ≤ v*X; dsimp [v]; nlinarith only [bitCount,t]
  have lower : callReg anchor 8 ≤ floor := le_max_left ..
  have tag : P.states ≤ floor := (by dsimp [floor]; omega)
  have low : 13 < floor := by dsimp [floor]; omega
  have bounded (x : ℕ) (h : x ≤ base+span N) : x.size ≤ b := (Nat.size_le_size h).trans sizeW
  obtain ⟨set,src,out,keep⟩ := installCount_exec (τ := τ) E k p base row pin bank s size (by omega) (by omega)
    (by omega) port col ptr data fit
  let u := ((installCount bank).run τ s).last
  have fixedLow : callReg (5+NT P) 8 ≤ floor := lower
  have fullW : (base+bits.length+NT P*(2*time+1)).size ≤ b := bounded _ (by omega)
  obtain ⟨t,j,run,used,answer,ret,frame⟩ := call n E k p size base row (pin+k) b u τ src (set.post fit) nw
    ((Nat.size_le_size tag).trans floorW) (by omega) (by omega) (by omega) (.inl (by omega)) (.inl (by omega))
    (bounded _ (by omega)) (bounded _ (by omega)) fullW
  change ∀ a, callReg (5+NT P) 8 ≤ a → (a < base ∨ base+bits.length+NT P*(2*time+1) ≤ a) → t.mem a=u.mem a at frame
  refine ⟨t,_,set.seq run,?_,answer,ret.trans out,fun a ha h => (frame a (by omega) (by omega)).trans (keep a (by omega))⟩
  have w := Nat.mul_le_mul_left (tableConstant P A d+11) lift
  change j ≤ (tableConstant P A d+11)*(S+1)^(d+2) at used
  change 9+j ≤ c*X
  dsimp [c]; nlinarith only [w,used,one]

end AffinePrefixEnumeration

end AffineRAMCountPort

section
open AffinePrefixEnumeration
open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.RankedPrefix EditGV897.Main
open TargetedSamplers.Structured.BinaryStack

theorem solution : Nonempty Solver := by
  obtain ⟨command,floor,work,space,growth,run⟩ := uniform_count_port
  exact ⟨⟨command,floor,work,space,growth,run⟩⟩
end
