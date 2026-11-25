-- Prove2me | Definitions.Def_DetDLP_W1_SavedCall
-- name    : DetDLP_W1_SavedCall
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:17:45.943666+00:00
-- url     : https://prove2.me/theorems/b2ed20f2-3613-47b0-8146-df5046f789c9
-- title:
--   Saving a word across a bounded primitive machine call
-- statement:
--   Given a deterministic primitive multitape machine computing a word r on input s, the wrapper returns the framed list [s,r]. Two fresh ports preserve the input and collect the output. The wrapper adds linear copying and framing time, and its additional visited space depends only on the two word lengths and the fixed tape count, not on the running time of the wrapped machine.

import Definitions.Def_DetDLP_M89_CompileSpace
import Definitions.Def_DetDLP_M89_MachineComp

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP_W1_SavedCall.RelativeMonitor

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP.MachineComposition

private theorem ext {M : PrimitiveMachine} {a b : LocatedCfg M}
    (hc : a.config = b.config) (hp : a.position = b.position)
    (hl : a.lower = b.lower) (hu : a.upper = b.upper) : a = b := by
  cases a; cases b; simp_all

/-- Shift the isolated trace by the caller's actual head positions and keep the union
    of its interval and the previous history. Tapes are already head-relative. -/
def rebase {M : PrimitiveMachine} (base c : LocatedCfg M) : LocatedCfg M where
  config := c.config
  position i := base.position i + c.position i
  lower i := min (base.lower i) (base.position i + c.lower i)
  upper i := max (base.upper i) (base.position i + c.upper i)

@[simp] theorem rebase_monitor {M : PrimitiveMachine} (base c : LocatedCfg M) (cfg : M.Cfg) :
    (rebase base c).monitor cfg = rebase base (c.monitor cfg) := by
  rcases c with ⟨⟨s,w⟩,pos,lo,hi⟩
  cases s with
  | inl b => rfl
  | inr q =>
    cases ha : M.transition q (w (M.scan q)).head with
    | inl b => simp [LocatedCfg.monitor, rebase, ha]
    | inr act =>
      obtain ⟨q',a⟩ := act
      apply ext
      · simp only [LocatedCfg.monitor,rebase,ha,Sum.elim_inr]
      all_goals
        funext i
        simp only [LocatedCfg.monitor,rebase,ha,Sum.elim_inr]
        by_cases he : i = M.scan q
        · subst i; simp only [Function.update_self]; omega
        · simp only [Function.update_of_ne he]

theorem rebase_step {M : PrimitiveMachine} (base : LocatedCfg M) {a b : LocatedCfg M}
    (h : locatedStep M a = some b) : locatedStep M (rebase base a) = some (rebase base b) := by
  obtain ⟨c,hc,rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [locatedStep,show (rebase base a).config = a.config from rfl,hc,Option.map_some,rebase_monitor]

theorem rebase_space {M : PrimitiveMachine} (base c : LocatedCfg M) (hw : LocatedWellFormed base)
    (hz : OriginCovered c) : visitedSpace (rebase base c) ≤ visitedSpace base + visitedSpace c := by
  unfold visitedSpace
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hw' := hw i
  have hz' := hz i
  dsimp only [rebase] at *
  omega

/-- An actual starting monitor may be strictly narrower than the proof envelope.
    In particular the previous run need not have its head at a counted string's origin. -/
structure Inside {M : PrimitiveMachine} (a b : LocatedCfg M) : Prop where
  config : a.config = b.config
  position : a.position = b.position
  lower : ∀ i, b.lower i ≤ a.lower i
  upper : ∀ i, a.upper i ≤ b.upper i

theorem Inside.monitor {M : PrimitiveMachine} {a b : LocatedCfg M} (h : Inside a b) (cfg : M.Cfg) :
    Inside (a.monitor cfg) (b.monitor cfg) := by
  rcases a with ⟨ca,pa,la,ua⟩
  rcases b with ⟨cb,pb,lb,ub⟩
  rcases h with ⟨hc,hp,hl,hu⟩
  dsimp only at hc hp hl hu
  subst cb; subst pb
  rcases ca with ⟨s,w⟩
  cases s with
  | inl _ => exact ⟨rfl,rfl,hl,hu⟩
  | inr q =>
    cases ha : M.transition q (w (M.scan q)).head with
    | inl _ => simpa only [LocatedCfg.monitor,ha,Sum.elim_inr,Sum.elim_inl] using
        (show Inside (⟨cfg,pa,la,ua⟩ : LocatedCfg M) ⟨cfg,pa,lb,ub⟩ from ⟨rfl,rfl,hl,hu⟩)
    | inr act =>
      obtain ⟨q',ac⟩ := act
      simp only [LocatedCfg.monitor,ha,Sum.elim_inr]
      refine ⟨rfl,rfl,?_,?_⟩ <;> intro i
      · by_cases he : i = M.scan q
        · subst i; simp only [Function.update_self]; exact min_le_min_right _ (hl _)
        · simp only [Function.update_of_ne he]; exact hl _
      · by_cases he : i = M.scan q
        · subst i; simp only [Function.update_self]; exact max_le_max_right _ (hu _)
        · simp only [Function.update_of_ne he]; exact hu _

theorem Inside.trace {M : PrimitiveMachine} {b z : LocatedCfg M} {n : ℕ}
    (tr : Computation.Trace (locatedStep M) n b z) {a : LocatedCfg M} (h : Inside a b) :
    ∃ c, Computation.Trace (locatedStep M) n a c ∧ Inside c z := by
  induction tr generalizing a with
  | refl => exact ⟨a,.refl _,h⟩
  | cons st _ ih =>
    obtain ⟨c,hc,rfl⟩ := Option.map_eq_some_iff.mp st
    obtain ⟨d,ht,hd⟩ := ih (h.monitor c)
    exact ⟨d,.cons (by simp only [locatedStep,h.config,hc,Option.map_some]) ht,hd⟩

theorem Inside.space {M : PrimitiveMachine} {a b : LocatedCfg M} (h : Inside a b) :
    visitedSpace a ≤ visitedSpace b := by
  apply Finset.sum_le_sum
  intro i _
  apply Int.toNat_le_toNat
  have hl := h.lower i
  have hu := h.upper i
  omega

/-- Execute a clean relative subtrace at a real caller configuration. Space is
    charged to the old visited interval plus the subtrace's *space*, never its time. -/
theorem call {M : PrimitiveMachine} {entry start finish : LocatedCfg M} {n : ℕ} {σ : ℝ}
    (hw : LocatedWellFormed entry) (hc : entry.config = start.config)
    (h0 : ∀ i, start.position i = 0) (hz : OriginCovered start)
    (h : Segment M start finish n σ) :
    ∃ actual, actual.config = finish.config ∧ Segment M entry actual n ((visitedSpace entry : ℝ)+σ) := by
  have htr := MachineComposition.Trace.map (rebase entry) (fun _ _ => rebase_step entry) h.1
  have hinside : Inside entry (rebase entry start) :=
    ⟨hc,funext (fun i => by simp [rebase,h0]),fun _ => min_le_left ..,fun _ => le_max_left ..⟩
  obtain ⟨actual,ht,ha⟩ := Inside.trace htr hinside
  have hs := ha.space.trans (rebase_space entry finish hw (originCovered_trace hz h.1))
  have hs' : (visitedSpace actual : ℝ) ≤ visitedSpace entry + visitedSpace finish := by exact_mod_cast hs
  exact ⟨actual,ha.config,segment_iff_final_space.mpr ⟨ht,hs'.trans (by linarith [(segment_iff_final_space.mp h).2])⟩⟩

end DetDLP_W1_SavedCall.RelativeMonitor

namespace DetDLP_W1_SavedCall
noncomputable section
abbrev Tape := Turing.Tape (Option Bool)
abbrev Stmt := Turing.TM0.Stmt (Option Bool)
def act (t : Tape) : Stmt → Tape
  | .write s => t.write s
  | .move d => t.move d
structure Code (I : Type) where
  Q : Type
  finiteQ : Fintype Q
  start : Q
  scan : Q → I
  next : Q → Option Bool → Option Q × Stmt
attribute [instance] Code.finiteQ
variable {I : Type} [DecidableEq I]
abbrev Bank (I : Type) := I → Tape
def exec (P : Code I) : Option P.Q × Bank I → Option (Option P.Q × Bank I)
  | (none,_) => none
  | (some q,t) => let i := P.scan q; let r := P.next q (t i).head
                   some (r.1, Function.update t i (act (t i) r.2))
abbrev Run (P : Code I) (n : ℕ) (t u : Bank I) := Computation.Trace (exec P) n (some P.start,t) (none,u)
def seq (P R : Code I) : Code I where
  Q := P.Q ⊕ R.Q
  finiteQ := inferInstance
  start := .inl P.start
  scan := Sum.elim P.scan R.scan
  next := Sum.elim (fun q s => let r := P.next q s; (some (r.1.elim (.inr R.start) Sum.inl),r.2))
    (fun q s => let r := R.next q s; (r.1.map Sum.inr,r.2))
infixr:62 " ;; " => seq
private theorem sim {P R : Code I} (f : Option P.Q → Option R.Q)
    (g : P.Q → R.Q) (hg : ∀ q, f (some q) = some (g q))
    (hscan : ∀ q, R.scan (g q) = P.scan q)
    (hnext : ∀ q s, R.next (g q) s = (f (P.next q s).1,(P.next q s).2))
    {s e : Option P.Q × Bank I} {n : ℕ} (h : Computation.Trace (exec P) n s e) :
    Computation.Trace (exec R) n (f s.1,s.2) (f e.1,e.2) := by
  apply MachineComposition.Trace.map (fun c => (f c.1,c.2)) _ h
  rintro ⟨_|q,t⟩ b hb
  · simp [exec] at hb
  · simp [exec] at hb; subst b; simp [hg,exec,hscan,hnext]
theorem seq_run {P R : Code I} {t u v : Bank I} {n m : ℕ} (h : Run P n t u) (h' : Run R m u v) : Run (P ;; R) (n+m) t v := by
  let f := fun q : Option P.Q => some (q.elim (.inr R.start) Sum.inl)
  exact MachineComposition.Trace.append (sim (R:=P ;; R) f Sum.inl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) h)
    (sim (R:=P ;; R) (Option.map Sum.inr) Sum.inr (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) h')

def word (w : List Bool) : Tape := Turing.Tape.mk₁ (w.map some)
def initBank (input : I) (w : List Bool) : Bank I := fun i => if i = input then word w else word []
def cur (l r : List Bool) : Tape := Turing.Tape.mk₂ (l.map some) (r.map some)
@[simp] theorem cur_right (l r : List Bool) (b : Bool) : (cur l (b::r)).move .right = cur (b::l) r := by simp [cur,Turing.Tape.mk₂]
@[simp] theorem cur_left (l r : List Bool) (b : Bool) : (cur (b::l) r).move .left = cur l (b::r) := by rw [← cur_right,Turing.Tape.move_right_left]
@[simp] theorem cur_head (l r : List Bool) (b : Bool) : (cur l (b::r)).head = some b := rfl
@[simp] theorem cur_blank (l : List Bool) : (cur l []).head = none := rfl
@[simp] theorem cur_write (l : List Bool) (b : Bool) : (cur l []).write (some b) = cur l [b] := rfl
@[simp] theorem cur_at_left (r : List Bool) : ((cur [] r).move .left).head = none := rfl

def single (i : I) (a : Stmt) : Code I := ⟨Unit,inferInstance,(),fun _ => i,fun _ _ => (none,a)⟩
def emit (i : I) (b : Bool) := single i (.write (some b)) ;; single i (.move .right)
theorem single_run (t : Bank I) (i : I) (a : Stmt) : Run (single i a) 1 t (Function.update t i (act (t i) a)) := .cons rfl (.refl _)
theorem emit_run (t : Bank I) (i : I) (l : List Bool) (b : Bool) (h : t i = cur l []) :
    Run (emit i b) 2 t (Function.update t i (cur (b::l) [])) := by
  simpa [act,h,emit] using seq_run (single_run t i (.write (some b))) (single_run _ i (.move .right))

def rewind (i : I) : Code I where
  Q := Bool
  finiteQ := inferInstance
  start := false
  scan _ := i
  next q s := if q then if s.isNone then (none,.move .right) else (some false,.write s) else (some true,.move .left)
theorem rewind_run (i : I) (l r : List Bool) (t : Bank I) (h : t i = cur l r) :
    Run (rewind i) (2*l.length+2) t (Function.update t i (word (l.reverse ++ r))) := by
  induction l generalizing r t with
  | nil =>
    apply Computation.Trace.cons (b := (some true,Function.update t i ((cur [] r).move .left))) (by simp [exec,rewind,h,act])
    exact .cons (by simp [exec,rewind,act]; rfl) (.refl _)
  | cons b l ih =>
    let t' := Function.update t i (cur l (b::r))
    have h1 : exec (rewind i) (some false,t) = some (some true,t') := by simp [exec,rewind,act,t',h]
    have h2 : exec (rewind i) (some true,t') = some (some false,t') := by simp [exec,rewind,act,t']; rfl
    unfold Run; change Computation.Trace _ _ (some false,t) _
    simpa [t',Nat.mul_add,List.append_assoc,Nat.add_assoc] using Computation.Trace.cons h1 (.cons h2 (ih (b::r) t' (by simp [t'])))

def scan (i j : I) (fr : Bool) : Code I where
  Q := Option (Fin 4 × Bool)
  finiteQ := inferInstance
  start := none
  scan q := q.elim i (fun _ => j)
  next q s := match q with
    | none => match s with
      | none => (none,.write none)
      | some b => (some (some (if fr then 0 else 2,b)),.move .right)
    | some (q,b) => match q.val with
      | 0 => (some (some (1,b)),.write (some true))
      | 1 => (some (some (2,b)),.move .right)
      | 2 => (some (some (3,b)),.write (some b))
      | _ => (some none,.move .right)
def chunk (fr : Bool) (b : Bool) : List Bool := if fr then [true,b] else [b]
def rate (fr : Bool) : ℕ := if fr then 5 else 3
private theorem scan_bit (i j : I) (hne : i ≠ j) (fr b : Bool) (l r a : List Bool) (t : Bank I)
    (hi : t i = cur l (b::r)) (hj : t j = cur a []) :
    Computation.Trace (exec (scan i j fr)) (rate fr) (some none,t) (some none,
      Function.update (Function.update t i (cur (b::l) r)) j (cur ((chunk fr b).reverse ++ a) [])) := by
  cases fr <;> apply Computation.Trace.of_iterate <;>
    simp [rate,Function.iterate_succ_apply,exec,scan,act,hi,hj,hne,Ne.symm hne,chunk]
private theorem scan_loop (i j : I) (hne : i ≠ j) (fr : Bool) (r l a : List Bool) (t : Bank I)
    (hi : t i = cur l r) (hj : t j = cur a []) :
    ∃ u, Run (scan i j fr) (rate fr*r.length+1) t u ∧ u i = cur (r.reverse ++ l) [] ∧
      u j = cur ((r.flatMap (chunk fr)).reverse ++ a) [] ∧ ∀ z, z ≠ i → z ≠ j → u z = t z := by
  induction r generalizing l a t with
  | nil =>
    refine ⟨t,?_,by simpa using hi,by simpa using hj,fun _ _ _ => rfl⟩
    simp only [List.length_nil,Nat.mul_zero,Nat.zero_add]; apply Computation.Trace.cons (b := (none,t)) _ (.refl _)
    change exec (scan i j fr) (some none,t) = some (none,t)
    have hw : (t i).write none = t i := by rw [← show (t i).head = none by rw [hi,cur_blank],Turing.Tape.write_self]
    simp [exec,scan,show (t i).head = none by rw [hi,cur_blank],act,hw]
  | cons b r ih =>
    let t' := Function.update (Function.update t i (cur (b::l) r)) j (cur ((chunk fr b).reverse ++ a) [])
    obtain ⟨u,h,h1,h2,h3⟩ := ih (b::l) ((chunk fr b).reverse ++ a) t' (by simp [t',hne]) (by simp [t'])
    refine ⟨u,?_,by simpa [List.append_assoc] using h1,by simpa [List.append_assoc] using h2,?_⟩
    · have tr := MachineComposition.Trace.append (scan_bit i j hne fr b l r a t hi hj) h
      simpa [Run,scan,Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,t'] using tr
    · intro z zi zj; simpa [t',zi,zj] using h3 z zi zj

def copy (i j : I) := scan i j false ;; rewind i ;; rewind j
private theorem copy_run (i j : I) (hne : i ≠ j) (w : List Bool) (t : Bank I) (hi : t i = word w) (hj : t j = word []) :
    ∃ u, Run (copy i j) (7*w.length+5) t u ∧ u j = word w ∧ ∀ z, z ≠ j → u z = t z := by
  obtain ⟨u,h,h1,h2,h3⟩ := scan_loop i j hne false w [] [] t hi hj
  have flat (v : List Bool) : v.flatMap (chunk false) = v := by induction v <;> simp_all [chunk]
  simp [flat] at h1 h2
  have s1 := rewind_run i w.reverse [] u h1
  let v := Function.update u i (word w)
  have s1' : Run (rewind i) (2*w.length+2) u v := by simpa [v] using s1
  have s2 := rewind_run j w.reverse [] v (by simp [v,Ne.symm hne,h2])
  let z := Function.update v j (word w)
  have s2' : Run (rewind j) (2*w.length+2) v z := by simpa [z] using s2
  refine ⟨z,?_,by simp [z],?_⟩
  · convert seq_run h (seq_run s1' s2') using 1 <;> simp [copy,rate] <;> omega
  · intro k hk; by_cases hi' : k = i
    · subst k; simp [z,v,hk,hi]
    · simp [z,v,hk,hi',h3 k hi' hk]

def block (i j : I) := emit j true ;; scan i j true ;; emit j false
def atom (w : List Bool) := true :: Encoding.frame w
private theorem frame_eq (w : List Bool) : Encoding.frame w = w.flatMap (chunk true) ++ [false] := by induction w <;> simp_all [Encoding.frame,chunk,List.foldr]
private theorem block_run (i j : I) (hne : i ≠ j) (w acc : List Bool) (t : Bank I) (hi : t i = word w) (hj : t j = cur acc.reverse []) :
    ∃ u, Run (block i j) (5*w.length+5) t u ∧ u j = cur (acc ++ atom w).reverse [] ∧ ∀ z, z ≠ i → z ≠ j → u z = t z := by
  let t' := Function.update t j (cur (true::acc.reverse) [])
  have h := emit_run t j acc.reverse true hj
  obtain ⟨v,hv,_,hvj,hf⟩ := scan_loop i j hne true w [] (true::acc.reverse) t' (by rw [show t' i = t i by simp [t',hne]]; exact hi) (by simp [t'])
  let l := (w.flatMap (chunk true)).reverse ++ true :: acc.reverse
  have he := emit_run v j l false hvj
  refine ⟨Function.update v j (cur (false::l) []),?_,?_,?_⟩
  · convert seq_run h (seq_run hv he) using 1 <;> simp [block,rate] <;> omega
  · simp [l,atom,frame_eq,List.append_assoc]
  · intro z zi zj; simp [zj,hf z zi zj,t']

def pair (i k j : I) := block i j ;; block k j ;; emit j false ;; rewind j

theorem pair_run (i k j : I) (hi : i ≠ j) (hk : k ≠ j) (hki : k ≠ i)
    (s r : List Bool) (t : Bank I) (ti : t i = word s) (tk : t k = word r) (tj : t j = word []) :
    let p := Encoding.encodeList id [s,r]
    ∃ u, Run (pair i k j) (5*(s.length+r.length)+2*p.length+14) t u ∧ u j = word p := by
  intro p
  obtain ⟨u,h1,uj,uf⟩ := block_run i j hi s [] t ti tj
  obtain ⟨v,h2,vj,_⟩ := block_run k j hk r (atom s) u (by rw [uf k hki hk,tk]) (by simpa using uj)
  have h3 := emit_run v j (atom s ++ atom r).reverse false vj
  rw [show false :: (atom s ++ atom r).reverse = p.reverse by simp [p,Encoding.encodeList,atom,List.append_assoc]] at h3
  let t' := Function.update v j (cur p.reverse [])
  have h4 := rewind_run j p.reverse [] t' (by simp [t'])
  refine ⟨Function.update t' j (word (p.reverse.reverse ++ [])),?_,by simp⟩
  convert seq_run h1 (seq_run h2 (seq_run h3 h4)) using 1 <;> simp [pair] <;> omega

open MachineComposition
variable {T : ℕ}

def program (P : Code (Fin T)) : Program T where
  stateCount := Fintype.card P.Q + 1
  start := (Fintype.equivFin P.Q P.start).castSucc
  scan := Fin.lastCases (P.scan P.start) (fun j => P.scan ((Fintype.equivFin P.Q).symm j))
  transition := Fin.lastCases (fun _ => .inl true) (fun j s => let r := P.next ((Fintype.equivFin P.Q).symm j) s
    .inr (r.1.elim (Fin.last _) (fun q => (Fintype.equivFin P.Q q).castSucc),r.2))

def pack (P : Code (Fin T)) (i : Fin T) (c : Option P.Q × Bank (Fin T)) : ((program P).machine i).Cfg :=
  ⟨.inr (c.1.elim (Fin.last _) (fun q => (Fintype.equivFin P.Q q).castSucc)), c.2⟩

theorem packTrace (P : Code (Fin T)) (i : Fin T) {c d : Option P.Q × Bank (Fin T)} {n : ℕ}
    (h : Computation.Trace (exec P) n c d) : Computation.Trace ((program P).machine i).step n (pack P i c) (pack P i d) := by
  apply MachineComposition.Trace.map _ _ h
  rintro ⟨_|q,t⟩ d hd
  · simp [exec] at hd
  · simp [exec] at hd; subst d
    simp only [PrimitiveMachine.step,pack,program,Program.machine,Option.elim_some,Fin.lastCases_castSucc,Equiv.symm_apply_apply]
    cases hh : (P.next q (t (P.scan q)).head).2 <;> simp [hh,act]

theorem codeTrace (P : Code (Fin T)) (i : Fin T) {n : ℕ} {t u} (h : Run P n t u)
    {c : LocatedCfg ((program P).machine i)} (hc : c.config = ⟨.inr (program P).start,t⟩) :
    ∃ d, Computation.Trace (locatedStep ((program P).machine i)) (n+1) c d ∧ d.config = ⟨.inl true,u⟩ := by
  have h1 := packTrace P i h
  have h2 : ((program P).machine i).step (pack P i (none,u)) = some ⟨.inl true,u⟩ := by simp [PrimitiveMachine.step,pack,program,Program.machine]
  apply locatedTrace_lift
  rw [hc]; exact MachineComposition.Trace.append h1 (.cons h2 (.refl _))

theorem growth {A : PrimitiveMachine} {c d : LocatedCfg A} {n : ℕ}
    (hw : LocatedWellFormed c) (tr : Computation.Trace (locatedStep A) n c d) :
    visitedSpace d ≤ visitedSpace c + A.tapeCount*(2*n) := by
  let lo := fun i => c.lower i - n
  let hi := fun i => c.upper i + n
  have h := locatedTrace_envelope_of_margin tr (le_refl n) lo hi
    (fun i => by dsimp [lo,hi]; omega) (fun i => by have := hw i; dsimp [lo,hi]; omega)
  apply (visitedSpace_le_of_envelope d lo hi h).trans
  unfold visitedSpace
  rw [← show (∑ _ : Fin A.tapeCount, 2*n) = A.tapeCount*(2*n) by simp, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _; have := hw i; dsimp [lo,hi]; omega

variable (A : PrimitiveMachine)
abbrev source : Fin (A.tapeCount+2) := Fin.natAdd A.tapeCount (0 : Fin 2)
abbrev dest : Fin (A.tapeCount+2) := Fin.natAdd A.tapeCount (1 : Fin 2)
abbrev active (i : Fin A.tapeCount) := Fin.castAdd 2 i
private theorem disjoint (i : Fin A.tapeCount) (j : Fin 2) : active A i ≠ Fin.natAdd A.tapeCount j := by
  intro h; have := congrArg Fin.val h; simp only [active,Fin.val_castAdd,Fin.val_natAdd] at this; omega
private theorem ports_ne : source A ≠ dest A := fun h => (by decide : (0:Fin 2) ≠ 1) ((Fin.natAdd_inj _).mp h)
def pre := (program (copy (active A A.inputTape) (source A))).machine (active A A.inputTape)
def middle := Program.ofMachine (addTapes A 2)
def prior := thenMachine (pre A) (middle A)
def post (o : Fin A.tapeCount) := program (pair (source A) (active A o) (dest A))
def savedCall (o : Fin A.tapeCount) := thenMachine (prior A) (post A o)

def preSteps (s : List Bool) := 7*s.length+6
def postSteps (s r : List Bool) := 5*(s.length+r.length)+2*(Encoding.encodeList id [s,r]).length+15
def extraTime (s r : List Bool) : ℕ := preSteps s + postSteps s r
def extraSpace (s r : List Bool) : ℕ := (A.tapeCount+2)*(s.length+2*preSteps s+1)+2 + (A.tapeCount+2)*(2*postSteps s r)

theorem savedCall_run (o : Fin A.tapeCount) {s r : List Bool} {τ σ : ℝ} (ha : RunsWithin A o s r τ σ) :
    RunsWithin (savedCall A o) (dest A) s (Encoding.encodeList id [s,r]) (τ+extraTime s r) (σ+extraSpace A s r) := by
  let t := initBank (active A A.inputTape) s
  obtain ⟨u,h1,ui,uf⟩ := copy_run (active A A.inputTape) (source A) (disjoint A _ _) s t (by simp [t,initBank]) (by simp [t,initBank,Ne.symm (disjoint A A.inputTape 0)])
  obtain ⟨a,atr,ac⟩ := codeTrace _ (active A A.inputTape) h1 (c := locatedInit (pre A) s) rfl
  let fr : TapeFrame 2 := ⟨fun j => u (Fin.natAdd A.tapeCount j),fun _ => 0,fun _ => 0,fun _ => 0⟩
  have hsfr : fr.space = 2 := by simp [TapeFrame.space,fr]
  obtain ⟨m,b,h2,bh,bo,bm,bf⟩ := runsWithin_framed_call fr ha
  let start := frameLocated A fr (locatedInit A s)
  let entry := restartCfg (pre A) (middle A) a
  have hc : entry.config = start.config := by
    change (⟨.inr A.start,a.config.tapes⟩ : (addTapes A 2).Cfg) = ⟨_,_⟩
    rw [ac]; congr 1; funext j; induction j using Fin.addCases with
    | left k =>
      change u (active A k) = Fin.append (A.init s).tapes fr.tapes (Fin.castAdd 2 k)
      rw [Fin.append_left,uf _ (disjoint A k 0)]; simp [t,initBank,active,PrimitiveMachine.init,word]
    | right k => simp [fr,frameCfg,frameLocated]
  have h0 : ∀ i, start.position i = 0 := by intro i; induction i using Fin.addCases <;> simp [start,frameLocated,fr,locatedInit]
  have hz : OriginCovered start := by
    intro i; induction i using Fin.addCases with
    | left k => simpa [start,frameLocated] using originCovered_init A s k
    | right k => simp [start,frameLocated,fr]
  obtain ⟨b',bc,bseg⟩ := RelativeMonitor.call (M:= (middle A).machine (pre A).inputTape) (entry:=entry)
    (fun i => locatedWellFormed_reachable atr i) hc h0 hz h2
  have bh' : ∃ z, b'.config.state = .inl z := by rw [bc]; exact bh
  have copySpace := locatedTrace_space_le_of_length atr
  let k := (A.tapeCount+2)*(s.length+2*preSteps s+1)
  have has : (visitedSpace a : ℝ) ≤ k := by exact_mod_cast copySpace
  have hbseg : Segment _ entry b' m ((k:ℝ)+σ+2) := bseg.mono (by change (visitedSpace a:ℝ)+(σ+fr.space) ≤ _; rw [hsfr]; push_cast; linarith)
  have haseg : Segment (pre A) (locatedInit (pre A) s) a (preSteps s) k := segment_iff_final_space.mpr ⟨atr,has⟩
  have h12 := thenMachine_segments (pre A) (middle A) (locatedWellFormed_init _ _) haseg (show ∃ z, a.config.state = .inl z from ⟨true,by rw [ac]⟩) hbseg
  let d := rightCfg (pre A) (middle A) b'
  have dseg : Segment (prior A) (locatedInit (prior A) s) d (preSteps s+m) (max (k:ℝ) (k+σ+2)) := h12
  have dh : ∃ z, d.config.state = .inl z := by obtain ⟨z,hz⟩ := bh'; exact ⟨z,by simp [d,rightCfg,hz]⟩
  have inactive (j : Fin 2) : d.config.tapes (Fin.natAdd A.tapeCount j) = u (Fin.natAdd A.tapeCount j) := by
    change b'.config.tapes _ = _; rw [bc,bf]
  obtain ⟨v,h3,vout⟩ := pair_run (source A) (active A o) (dest A) (ports_ne A) (disjoint A o _) (disjoint A o _) s r d.config.tapes
    (by rw [inactive]; exact ui) (by change b'.config.tapes _ = _; rw [bc]; exact bo)
    (by rw [inactive,uf _ (Ne.symm (ports_ne A))]; simp [t,initBank,Ne.symm (disjoint A A.inputTape 1)])
  let restart := restartCfg (prior A) (post A o) d
  obtain ⟨e,etr,ec⟩ := codeTrace _ (prior A).inputTape h3 (c:=restart) rfl
  have es := growth (c:=restart) (fun i => locatedWellFormed_reachable dseg.1 i) etr
  have hdspace := (segment_iff_final_space.mp dseg).2
  have σpos : 0 ≤ σ := by obtain ⟨_,_,_,_,_,_,hs⟩ := ha; exact (Nat.cast_nonneg _).trans (hs 0 _ (Nat.zero_le _) (.refl _))
  have hmax : max (k:ℝ) (k+σ+2) = k+σ+2 := max_eq_right (by linarith)
  rw [hmax] at hdspace
  have he' : (visitedSpace e:ℝ) ≤ σ+extraSpace A s r := by
    have hh : visitedSpace e ≤ visitedSpace d + (A.tapeCount+2)*(2*postSteps s r) := es
    have hh' : (visitedSpace e:ℝ) ≤ visitedSpace d + ((A.tapeCount+2)*(2*postSteps s r):ℕ) := by exact_mod_cast hh
    change (visitedSpace e:ℝ) ≤ σ+((k+2+(A.tapeCount+2)*(2*postSteps s r):ℕ):ℝ)
    push_cast at *; linarith
  have h3seg : Segment _ restart e (postSteps s r) (σ+extraSpace A s r) := segment_iff_final_space.mpr ⟨etr,he'⟩
  apply runsWithin_mono (thenMachine_runsWithin (prior A) (post A o) (dest A) s _ dseg dh h3seg ⟨true,by rw [ec]⟩ (by rw [ec]; exact vout) (τ:=τ+extraTime s r) (by unfold extraTime; push_cast; linarith)) le_rfl
  rw [hmax]; apply max_le _ le_rfl
  change (k:ℝ)+σ+2 ≤ σ+((k+2+(A.tapeCount+2)*(2*postSteps s r):ℕ):ℝ)
  push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) ((A.tapeCount+2)*(2*postSteps s r))]

end
end DetDLP_W1_SavedCall


