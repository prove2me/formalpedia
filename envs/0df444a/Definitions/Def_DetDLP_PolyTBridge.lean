-- Prove2me | Definitions.Def_DetDLP_PolyTBridge
-- name    : DetDLP_PolyTBridge
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:19:59.831966+00:00
-- url     : https://prove2.me/theorems/894978b6-62cd-4226-981d-e317b909b230
-- title:
--   Universal Compiler Bridge from Groundwork PolyT to PrimitiveMachine RunsWithin
-- statement:
--   Simulates any four-stack `Groundwork.TM.Fr` fragment over the four-symbol tree alphabet `Sym` on ten parallel Boolean stacks via `BitProgram` and `GuardedCompiler.primitive`, establishing `polyT_listBool_runsWithin`: every polynomial-time function `f : List Bool → List Bool` certified by `Groundwork.PolyT f` admits a uniform `PrimitiveMachine` computing `f w` within `polyBound K w.length` time and visited space.
-- source:
--   Bridge between Anthropic Groundwork.PolyT (Def_ToTuring_PolyT) and OpenAI GuardedCompiler.primitive (Def_DetDLP_M89_CompileSpace)

import Definitions.Def_ToTuring_PolyT
import Definitions.Def_DetDLP_M89_CompileSpace

/-! A raw-bit interface for the four-stack Groundwork TM2 model. The two bits
of each stack symbol are kept on parallel Boolean stacks, so both peek and
pop have constant cost, including on an empty stack. -/

set_option autoImplicit false
namespace DetDLP.PolyTBridge
open Groundwork Groundwork.TM Turing
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

inductive Port where
  | raw | tmp | hi (k : Stk) | lo (k : Stk)
  deriving DecidableEq, Fintype

abbrev Mem := Port → List Bool
abbrev Reg := Fin 2 → Bool
abbrev SymMem := Stk → List Sym

/-- A finite table, with the bit returned by a read held in finite control. -/
inductive Op (Q : Type) where
  | jump (q : Q)
  | push (k : Port) (b : Bool) (q : Q)
  | read (remove : Bool) (k : Port) (q : Option Bool → Q)
  | stop

section Table
variable {Q : Type} [Fintype Q]
noncomputable abbrev port := Fintype.equivFin Port
noncomputable abbrev addr (q : Q) (i : Fin 3) := Fintype.equivFin (Q × Fin 3) (q, i)
noncomputable def instr (op : Op Q) (q : Q) (i : Fin 3) :
    BitProgram.Instr 2 (Fintype.card Port) (Fintype.card (Q × Fin 3)) :=
  match op with
  | .jump t => .goto (addr t 0)
  | .stop => .halt
  | .push k b t => if i = 0 then .set 0 b (addr q 1) else .push (port k) 0 (addr t 0)
  | .read rm k t => if i = 0 then
      if rm then .pop (port k) 0 1 (addr q 1) else .peek (port k) 0 1 (addr q 1)
    else if i = 1 then .branch 1 (addr q 2) (addr (t none) 0)
    else .branch 0 (addr (t (some true)) 0) (addr (t (some false)) 0)

noncomputable def table (ops : Q → Op Q) (start : Q) :
    BitProgram.Program 2 (Fintype.card Port) (Fintype.card (Q × Fin 3)) where
  inputStack := port .raw
  outputStack := port .raw
  entry := addr start 0
  code j := let qi := (Fintype.equivFin (Q × Fin 3)).symm j; instr (ops qi.1) qi.1 qi.2

@[simp] theorem table_code (ops : Q → Op Q) (start q : Q) (i : Fin 3) :
    (table ops start).code (addr q i) = instr (ops q) q i := by simp [table, addr]

noncomputable def physical (d : Mem) : Fin (Fintype.card Port) → List Bool := d ∘ port.symm
@[simp] theorem physical_get (d : Mem) (k : Port) : physical d (port k) = d k := by
  simp [physical]
@[simp] theorem physical_put (d : Mem) (k : Port) (s : List Bool) :
    Function.update (physical d) (port k) s = physical (Function.update d k s) := by
  funext j
  obtain ⟨i, rfl⟩ := port.surjective j
  by_cases h : i = k
  · subst i; simp
  · simp [Function.update_of_ne h, Function.update_of_ne (port.injective.ne h)]

noncomputable abbrev cfg (q : Option Q) (r : Reg) (d : Mem) :
    BitProgram.Cfg 2 (Fintype.card Port) (Fintype.card (Q × Fin 3)) :=
  ⟨q.map (fun t => addr t 0), r, physical d⟩

/-- Registers are scratch at a macro boundary. Time counts actual bit instructions. -/
def Goes (ops : Q → Op Q) (start : Q) (n : ℕ) (q : Q) (d : Mem)
    (t : Option Q) (e : Mem) : Prop := ∀ r : Reg, ∃ r' : Reg,
  BitProgram.RunsIn (table ops start) n (cfg (some q) r d) (cfg t r' e)

variable {ops : Q → Op Q} {start q t : Q} {u : Option Q} {d e g : Mem} {n m : ℕ}
theorem Goes.refl : Goes ops start 0 q d (some q) d :=
  fun r => ⟨r, RunsIn.refl _ _⟩
theorem Goes.mono (h : Goes ops start n q d u e) (hn : n ≤ m) : Goes ops start m q d u e := by
  intro r; obtain ⟨r', hr⟩ := h r; exact ⟨r', hr.mono hn⟩
theorem Goes.trans (h : Goes ops start n q d (some t) e) (h' : Goes ops start m t e u g) :
    Goes ops start (n + m) q d u g := by
  intro r; obtain ⟨r', hr⟩ := h r; obtain ⟨r'', hr'⟩ := h' r'; exact ⟨r'', hr.trans hr'⟩

theorem go_jump (h : ops q = .jump t) : Goes ops start 1 q d (some t) d := by
  intro r; refine ⟨r, 1, le_rfl, .cons ?_ (.refl _)⟩
  simp [cfg, BitProgram.step, h, instr, BitProgram.execInstr]

theorem go_stop (h : ops q = .stop) : Goes ops start 1 q d none d := by
  intro r; refine ⟨r, 1, le_rfl, .cons ?_ (.refl _)⟩
  simp [cfg, BitProgram.step, h, instr, BitProgram.execInstr]

theorem go_push (k : Port) (b : Bool) (h : ops q = .push k b t) :
    Goes ops start 2 q d (some t) (Function.update d k (b :: d k)) := by
  intro r
  let r' := Function.update r (0 : Fin 2) b
  refine ⟨r', 2, le_rfl, .cons (b := ⟨some (addr q 1), r', physical d⟩) ?_ (.cons ?_ (.refl _))⟩ <;>
    simp [cfg, BitProgram.step, h, instr, BitProgram.execInstr, r']

abbrev afterRead (rm : Bool) (k : Port) (d : Mem) : Mem :=
  if rm then Function.update d k (d k).tail else d

theorem go_read (rm : Bool) (k : Port) (next : Option Bool → Q) (h : ops q = .read rm k next) :
    Goes ops start 3 q d (some (next (d k).head?)) (afterRead rm k d) := by
  intro r
  let r' := BitProgram.readRegs r 0 1 (d k).head?
  let e := afterRead rm k d
  have first : BitProgram.step (table ops start) (cfg (some q) r d) =
      some ⟨some (addr q 1), r', physical e⟩ := by
    cases rm <;> simp [e, r', afterRead, BitProgram.step, h, instr, BitProgram.execInstr]
  refine ⟨r', ?_⟩
  cases hh : (d k).head? with
  | none =>
    refine ⟨2, by decide, .cons first (.cons ?_ (.refl _))⟩
    simp [cfg, e, r', BitProgram.step, h, instr, BitProgram.execInstr, hh]
  | some b =>
    refine ⟨3, le_rfl, .cons first (.cons (b := ⟨some (addr q 2), r', physical e⟩) ?_
      (.cons ?_ (.refl _)))⟩
    · simp [r', BitProgram.step, h, instr, BitProgram.execInstr, hh]
    · cases b <;> simp [cfg, e, r', BitProgram.step, h, instr, BitProgram.execInstr,
        BitProgram.readRegs_value _ _ _ _ (by decide : (0 : Fin 2) ≠ 1), hh]
end Table

/-! ## Symbol planes and finite-control macros -/

def bits : Sym → Bool × Bool
  | .bit b => (false, b)
  | .L => (true, false)
  | .R => (true, true)

def unbits : Option Bool → Option Bool → Option Sym
  | some false, some b => some (.bit b)
  | some true, some false => some .L
  | some true, some true => some .R
  | _, _ => none

abbrev high (s : Sym) := (bits s).1
abbrev low (s : Sym) := (bits s).2

@[simp] theorem unbits_heads (w : List Sym) :
    unbits (w.map high).head? (w.map low).head? = w.head? := by
  cases w with
  | nil => rfl
  | cons s w => cases s <;> rfl

def pack (raw tmp : List Bool) (S : SymMem) : Mem
  | .raw => raw
  | .tmp => tmp
  | .hi k => (S k).map high
  | .lo k => (S k).map low

@[simp] theorem pack_raw (x y z : List Bool) (S : SymMem) :
    Function.update (pack x y S) .raw z = pack z y S := by
  funext i; cases i <;> rfl
@[simp] theorem pack_tmp (x y z : List Bool) (S : SymMem) :
    Function.update (pack x y S) .tmp z = pack x z S := by
  funext i; cases i <;> rfl

theorem pack_pair (x y : List Bool) (S : SymMem) (k : Stk) (z : List Sym) :
    Function.update (Function.update (pack x y S) (.hi k) (z.map high)) (.lo k) (z.map low) =
      pack x y (Function.update S k z) := by
  funext i
  cases i with
  | raw | tmp => rfl
  | hi j | lo j => by_cases h : j = k <;> simp [pack, h]

inductive Macro (Q : Type) where
  | jump (t : Q)
  | pushB (k : Port) (b : Bool) (t : Q)
  | popB (k : Port) (t : Option Bool → Q)
  | pushS (k : Stk) (s : Sym) (t : Q)
  | readS (rm : Bool) (k : Stk) (t : Option Sym → Q)
  | stop

inductive Phase (Q : Type) where
  | run (q : Q) | put (q : Q) | get (q : Q) (h : Option Bool)
  deriving Fintype

variable {Q : Type}

def lower (ops : Q → Macro Q) : Phase Q → Op (Phase Q)
  | .run q => match ops q with
    | .jump t => .jump (.run t)
    | .pushB k b t => .push k b (.run t)
    | .popB k t => .read true k (fun b => .run (t b))
    | .pushS k s _ => .push (.hi k) (high s) (.put q)
    | .readS rm k _ => .read rm (.hi k) (.get q)
    | .stop => .stop
  | .put q => match ops q with
    | .pushS k s t => .push (.lo k) (low s) (.run t)
    | _ => .stop
  | .get q h => match ops q with
    | .readS rm k t => .read rm (.lo k) (fun l => .run (t (unbits h l)))
    | _ => .stop

section Macros
variable [Fintype Q] {ops : Q → Macro Q} {start q t : Q} {d : Mem}

abbrev Executes (ops : Q → Macro Q) (start : Q) (n : ℕ) (q : Q) (d : Mem)
    (t : Option Q) (e : Mem) := Goes (lower ops) (.run start) n (.run q) d (t.map Phase.run) e

theorem exec_jump (h : ops q = .jump t) : Executes ops start 1 q d (some t) d :=
  go_jump (by simp [lower, h])

theorem exec_stop (h : ops q = .stop) : Executes ops start 1 q d none d :=
  go_stop (by simp [lower, h])

theorem exec_pushB (k : Port) (b : Bool) (h : ops q = .pushB k b t) :
    Executes ops start 2 q d (some t) (Function.update d k (b :: d k)) :=
  go_push _ _ (by simp [lower, h])

theorem exec_popB (k : Port) (t : Option Bool → Q) (h : ops q = .popB k t) :
    Executes ops start 3 q d (some (t (d k).head?)) (Function.update d k (d k).tail) :=
  go_read true k (fun b => Phase.run (t b)) (by simp [lower, h])

theorem exec_pushS (x y : List Bool) (S : SymMem) (k : Stk) (s : Sym)
    (h : ops q = .pushS k s t) :
    Executes ops start 4 q (pack x y S) (some t) (pack x y (Function.update S k (s :: S k))) := by
  have a := go_push (ops := lower ops) (start := Phase.run start) (q := .run q) (t := .put q)
    (d := pack x y S) (.hi k) (high s) (by simp [lower, h])
  have b := go_push (ops := lower ops) (start := Phase.run start) (q := .put q) (t := .run t)
    (d := Function.update (pack x y S) (.hi k) (high s :: (S k).map high))
    (.lo k) (low s) (by simp [lower, h])
  rw [← pack_pair]
  exact a.trans b

def adjust (rm : Bool) (S : SymMem) (k : Stk) :=
  if rm then Function.update S k (S k).tail else S

theorem exec_readS (x y : List Bool) (S : SymMem) (rm : Bool) (k : Stk) (t : Option Sym → Q)
    (h : ops q = .readS rm k t) :
    Executes ops start 6 q (pack x y S) (some (t (S k).head?)) (pack x y (adjust rm S k)) := by
  have a := go_read (ops := lower ops) (start := Phase.run start) (q := .run q)
    (d := pack x y S) rm (.hi k) (.get q) (by simp [lower, h])
  let v := ((S k).map high).head?
  let e := afterRead rm (.hi k) (pack x y S)
  have b := go_read (ops := lower ops) (start := Phase.run start) (q := .get q v)
    (d := e) rm (.lo k) (fun l => .run (t (unbits v l))) (by simp [lower, h])
  have ab := a.trans b
  have el : e (.lo k) = (S k).map low := by cases rm <;> rfl
  rw [el, show unbits v ((S k).map low).head? = (S k).head? from unbits_heads _] at ab
  cases rm with
  | false => exact ab
  | true =>
    rw [show afterRead true (.lo k) e = pack x y (adjust true S k) by
      simpa [adjust, afterRead, e, pack, List.map_tail] using pack_pair x y S k (S k).tail] at ab
    exact ab
end Macros

variable {ops : Q → Macro Q} [Fintype Q] {start q t : Q} {d e g : Mem} {n m : ℕ} {u : Option Q}

theorem Executes.trans (h : Executes ops start n q d (some t) e)
    (h' : Executes ops start m t e u g) : Executes ops start (n + m) q d u g := Goes.trans h h'

theorem Executes.mono (h : Executes ops start n q d u e) (hn : n ≤ m) : Executes ops start m q d u e :=
  Goes.mono h hn

/-! ## Finite dispatch table -/

abbrev Statement (P : Fr) := TM2.Stmt (fun _ : Stk => Sym) P.Λ (Option Sym)
abbrev SourceCfg (P : Fr) := TM2.Cfg (fun _ : Stk => Sym) P.Λ (Option Sym)

open scoped Classical in
noncomputable def nodes (P : Fr) : Finset (Statement P) :=
  Finset.univ.biUnion fun l => TM2.stmts₁ (P.m l)

theorem root_mem (P : Fr) (l : P.Λ) : P.m l ∈ nodes P := by
  classical
  exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, TM2.stmts₁_self⟩

theorem child_mem (P : Fr) {s t : Statement P} (hs : s ∈ nodes P) (ht : t ∈ TM2.stmts₁ s) :
    t ∈ nodes P := by
  classical
  obtain ⟨l, hl, hm⟩ := Finset.mem_biUnion.mp hs
  exact Finset.mem_biUnion.mpr ⟨l, hl, TM2.stmts₁_trans hm ht⟩

inductive Label (N : Type) where
  | beginInput | scanRaw | saveBit (b : Bool) | addR | nilMark
  | scanTmp | addBit (b : Bool) | addL
  | sim (node : N) (v : Option Sym)
  | scanMain | extractBit (b : Bool) | flushTmp | outputBit (b : Bool) | done
  deriving Fintype

abbrev Control (P : Fr) := Label (nodes P)

open scoped Classical in
noncomputable def atStmt (P : Fr) (s : Statement P) (v : Option Sym) : Control P :=
  if h : s ∈ nodes P then .sim ⟨s, h⟩ v else .done

noncomputable def atLabel (P : Fr) (l : Option P.Λ) (v : Option Sym) : Control P :=
  match l with
  | none => .scanMain
  | some i => atStmt P (P.m i) v

noncomputable def dispatch (P : Fr) (v : Option Sym) : Statement P → Macro (Control P)
  | .push k f s => .pushS k (f v) (atStmt P s v)
  | .peek k f s => .readS false k (fun o => atStmt P s (f v o))
  | .pop k f s => .readS true k (fun o => atStmt P s (f v o))
  | .load f s => .jump (atStmt P s (f v))
  | .branch p s t => .jump (atStmt P (cond (p v) s t) v)
  | .goto f => .jump (atLabel P (some (f v)) v)
  | .halt => .jump .scanMain

noncomputable def program (P : Fr) : Control P → Macro (Control P)
  | .beginInput => .pushS .main .R .scanRaw
  | .scanRaw => .popB .raw (Option.elim · .nilMark .saveBit)
  | .saveBit b => .pushB .tmp b .addR
  | .addR => .pushS .main .R .scanRaw
  | .nilMark => .pushS .main .L .scanTmp
  | .scanTmp => .popB .tmp (Option.elim · (atLabel P (some P.entry) none) .addBit)
  | .addBit b => .pushS .main (.bit b) .addL
  | .addL => .pushS .main .L .scanTmp
  | .sim node v => dispatch P v node.val
  | .scanMain => .readS true .main fun o => match o with
    | none => .flushTmp
    | some (.bit b) => .extractBit b
    | _ => .scanMain
  | .extractBit b => .pushB .tmp b .scanMain
  | .flushTmp => .popB .tmp (Option.elim · .done .outputBit)
  | .outputBit b => .pushB .raw b .flushTmp
  | .done => .stop

abbrev Travels (P : Fr) := Executes (program P) .beginInput

@[simp] theorem program_atStmt (P : Fr) (s : Statement P) (v : Option Sym) (h : s ∈ nodes P) :
    program P (atStmt P s v) = dispatch P v s := by simp [atStmt, h, program]

/-! ## The raw input and output conventions -/

def front (w : List Bool) : List Sym := w.flatMap fun b => [.L, .bit b]

@[simp] theorem front_append (u v : List Bool) : front (u ++ v) = front u ++ front v :=
  List.flatMap_append

@[simp] theorem wd_nil : wd ([] : List Bool) = [.L, .R] := rfl

theorem wd_cons (b : Bool) (w : List Bool) : wd (b :: w) = .L :: .bit b :: wd w ++ [.R] := rfl

theorem wd_listBool (w : List Bool) :
    wd w = front w ++ [Sym.L] ++ List.replicate (w.length + 1) Sym.R := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [wd_cons, ih]
    simp [front, List.replicate_succ', List.append_assoc]

theorem len_listBool (w : List Bool) : len w = 3 * w.length + 2 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change (wd _).length = _
    rw [wd_cons]
    change (wd w).length = _ at ih
    simp; omega

abbrev frame (x y : List Bool) (z : List Sym) := pack x y (st z [] [] [])

@[simp] theorem main_update (m z : List Sym) : Function.update (st m [] [] []) .main z = st z [] [] [] := by
  funext i; cases i <;> rfl

section Interface
variable {P : Fr} {q t : Control P} (x y : List Bool) (z : List Sym)

theorem popRaw (next : Option Bool → Control P) (h : program P q = .popB .raw next) :
    Travels P 3 q (frame x y z) (some (next x.head?)) (frame x.tail y z) := by
  simpa only [frame, pack_raw, pack] using exec_popB (start := Label.beginInput) (d := frame x y z) .raw next h

theorem popTmp (next : Option Bool → Control P) (h : program P q = .popB .tmp next) :
    Travels P 3 q (frame x y z) (some (next y.head?)) (frame x y.tail z) := by
  simpa only [frame, pack_tmp, pack] using exec_popB (start := Label.beginInput) (d := frame x y z) .tmp next h

theorem pushTmp (b : Bool) (h : program P q = .pushB .tmp b t) :
    Travels P 2 q (frame x y z) (some t) (frame x (b :: y) z) := by
  simpa only [frame, pack_tmp, pack] using exec_pushB (start := Label.beginInput) (d := frame x y z) .tmp b h

theorem pushRaw (b : Bool) (h : program P q = .pushB .raw b t) :
    Travels P 2 q (frame x y z) (some t) (frame (b :: x) y z) := by
  simpa only [frame, pack_raw, pack] using exec_pushB (start := Label.beginInput) (d := frame x y z) .raw b h

theorem pushMain (s : Sym) (h : program P q = .pushS .main s t) :
    Travels P 4 q (frame x y z) (some t) (frame x y (s :: z)) := by
  simpa only [frame, main_update, st] using exec_pushS (start := Label.beginInput) x y (st z [] [] []) .main s h

theorem popMain (next : Option Sym → Control P) (h : program P q = .readS true .main next) :
    Travels P 6 q (frame x y z) (some (next z.head?)) (frame x y z.tail) := by
  simpa only [frame, adjust, Bool.true_eq, if_true, main_update, st] using
    exec_readS (start := Label.beginInput) x y (st z [] [] []) true .main next h
end Interface

section Input
variable (P : Fr)

/-- The first scan reverses the raw bits and counts them in right brackets. -/
theorem collectRaw (x y : List Bool) (z : List Sym) :
    Travels P (9 * x.length + 3) .scanRaw (frame x y z) (some .nilMark)
      (frame [] (x.reverse ++ y) (List.replicate x.length .R ++ z)) := by
  induction x generalizing y z with
  | nil => exact popRaw (P := P) (q := .scanRaw) [] y z _ rfl
  | cons b x ih =>
    have a : Travels P 3 .scanRaw (frame (b :: x) y z) (some (.saveBit b)) (frame x y z) :=
      popRaw (P := P) (q := .scanRaw) (b :: x) y z _ rfl
    have b' := pushTmp (P := P) (q := .saveBit b) x y z b rfl
    have c := pushMain (P := P) (q := .addR) x (b :: y) z .R rfl
    have h := a.trans (b'.trans (c.trans (ih (b :: y) (.R :: z))))
    simpa [List.replicate_succ', List.append_assoc] using
      h.mono (m := 9 * (b :: x).length + 3) (by simp only [List.length_cons]; omega)

/-- Scanning the reversed bits builds the successive left brackets and leaves. -/
theorem buildFront (y : List Bool) (z : List Sym) :
    Travels P (11 * y.length + 3) .scanTmp (frame [] y z) (some (atLabel P (some P.entry) none))
      (frame [] [] (front y.reverse ++ z)) := by
  induction y generalizing z with
  | nil => exact popTmp (P := P) (q := .scanTmp) [] [] z _ rfl
  | cons b y ih =>
    have a : Travels P 3 .scanTmp (frame [] (b :: y) z) (some (.addBit b)) (frame [] y z) :=
      popTmp (P := P) (q := .scanTmp) [] (b :: y) z _ rfl
    have b' := pushMain (P := P) (q := .addBit b) [] y z (.bit b) rfl
    have c := pushMain (P := P) (q := .addL) [] y (.bit b :: z) .L rfl
    have h := a.trans (b'.trans (c.trans (ih (.L :: .bit b :: z))))
    simpa [front, List.append_assoc] using
      h.mono (m := 11 * (b :: y).length + 3) (by simp only [List.length_cons]; omega)

theorem prepass (w : List Bool) :
    Travels P (20 * w.length + 14) .beginInput (frame w [] []) (some (atLabel P (some P.entry) none))
      (frame [] [] (wd w)) := by
  have a := pushMain (P := P) (q := .beginInput) w [] [] .R rfl
  have b := collectRaw P w [] [.R]
  simp only [List.append_nil, ← List.replicate_succ'] at b
  have c := pushMain (P := P) (q := .nilMark) [] w.reverse (List.replicate (w.length + 1) .R) .L rfl
  have h := a.trans (b.trans (c.trans (buildFront P w.reverse (.L :: List.replicate (w.length + 1) .R))))
  simp only [List.length_reverse, List.reverse_reverse] at h
  rw [wd_listBool, List.append_assoc]
  exact h.mono (by omega)
end Input

/-! ## Constant-overhead simulation for each fixed fragment -/

/-- An upper bound for one statement tree, measured in bit instructions. -/
def stmtCost {P : Fr} : Statement P → ℕ
  | .push _ _ s => 4 + stmtCost s
  | .peek _ _ s | .pop _ _ s => 6 + stmtCost s
  | .load _ s => 1 + stmtCost s
  | .branch _ s t => 1 + (stmtCost s + stmtCost t)
  | .goto _ | .halt => 1

noncomputable abbrev labelOf (P : Fr) (a : SourceCfg P) := atLabel P a.l a.var
abbrev memOf {P : Fr} (a : SourceCfg P) := pack [] [] a.stk

section Simulation
variable (P : Fr)

theorem simulate_stmt (s : Statement P) (hs : s ∈ nodes P) (v : Option Sym) (S : SymMem) :
    Travels P (stmtCost s) (atStmt P s v) (pack [] [] S)
      (some (labelOf P (TM2.stepAux s v S))) (memOf (TM2.stepAux s v S)) := by
  classical
  induction s generalizing v S with
  | push k f s ih =>
    have hc := child_mem P (t := s) hs (by simp [TM2.stmts₁, TM2.stmts₁_self])
    have a := exec_pushS (start := Label.beginInput) [] [] S k (f v) (program_atStmt P _ v hs)
    exact a.trans (ih hc v _)
  | peek k f s ih =>
    have hc := child_mem P (t := s) hs (by simp [TM2.stmts₁, TM2.stmts₁_self])
    have a := exec_readS (start := Label.beginInput) [] [] S false k
      (fun o => atStmt P s (f v o)) (program_atStmt P _ v hs)
    exact a.trans (ih hc _ S)
  | pop k f s ih =>
    have hc := child_mem P (t := s) hs (by simp [TM2.stmts₁, TM2.stmts₁_self])
    have a := exec_readS (start := Label.beginInput) [] [] S true k
      (fun o => atStmt P s (f v o)) (program_atStmt P _ v hs)
    exact a.trans (ih hc _ _)
  | load f s ih =>
    have hc := child_mem P (t := s) hs (by simp [TM2.stmts₁, TM2.stmts₁_self])
    have a := exec_jump (start := Label.beginInput) (d := pack [] [] S) (program_atStmt P _ v hs)
    exact a.trans (ih hc (f v) S)
  | branch p s t ih it =>
    cases hp : p v with
    | false =>
      have hc := child_mem P (t := t) hs (by simp [TM2.stmts₁, TM2.stmts₁_self])
      have a : Travels P 1 (atStmt P (.branch p s t) v) (pack [] [] S)
          (some (atStmt P t v)) (pack [] [] S) := by
        apply exec_jump
        simpa only [dispatch, hp, cond_false] using program_atStmt P _ v hs
      simp only [TM2.stepAux, hp, cond_false, stmtCost]
      exact (a.trans (it hc v S)).mono (by omega)
    | true =>
      have hc := child_mem P (t := s) hs (by simp [TM2.stmts₁, TM2.stmts₁_self])
      have a : Travels P 1 (atStmt P (.branch p s t) v) (pack [] [] S)
          (some (atStmt P s v)) (pack [] [] S) := by
        apply exec_jump
        simpa only [dispatch, hp, cond_true] using program_atStmt P _ v hs
      simp only [TM2.stepAux, hp, cond_true, stmtCost]
      exact (a.trans (ih hc v S)).mono (by omega)
  | goto f | halt => exact exec_jump (program_atStmt P _ v hs)

noncomputable def overhead := Finset.univ.sup (fun l => stmtCost (P.m l))

theorem simulate_step {a b : SourceCfg P} (h : TM2.step P.m a = some b) :
    Travels P (overhead P) (labelOf P a) (memOf a) (some (labelOf P b)) (memOf b) := by
  obtain ⟨l, v, S⟩ := a
  cases l with
  | none => cases h
  | some l =>
    obtain rfl : TM2.stepAux (P.m l) v S = b := Option.some.inj h
    exact (simulate_stmt P (P.m l) (root_mem P l) v S).mono
      (Finset.le_sup (f := fun i => stmtCost (P.m i)) (Finset.mem_univ l))

theorem simulate_run {a b : SourceCfg P} {n : ℕ} (h : Run (TM2.step P.m) a n b) :
    Travels P (overhead P * n) (labelOf P a) (memOf a) (some (labelOf P b)) (memOf b) := by
  induction n generalizing a with
  | zero =>
    obtain rfl : a = b := h
    rw [Nat.mul_zero]
    exact Goes.refl
  | succ n ih =>
    obtain ⟨c, hc, hb⟩ := h
    rw [Nat.mul_succ, Nat.add_comm]
    exact (simulate_step P hc).trans (ih hb)
end Simulation

/-! ## Decoding the output word -/

def leaf : Sym → Option Bool
  | .bit b => some b
  | _ => none

@[simp] theorem leaves_wd (w : List Bool) : (wd w).filterMap leaf = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [wd_cons, List.filterMap_cons, leaf, ih]

section Output
variable (P : Fr)

/-- Brackets are discarded; exactly the leaves are transferred to the temporary stack. -/
theorem collectMain (z : List Sym) (y : List Bool) :
    Travels P (8 * z.length + 6) .scanMain (frame [] y z) (some .flushTmp)
      (frame [] ((z.filterMap leaf).reverse ++ y) []) := by
  induction z generalizing y with
  | nil => exact popMain (P := P) (q := .scanMain) [] y [] _ rfl
  | cons s z ih =>
    cases s with
    | bit b =>
      have a : Travels P 6 .scanMain (frame [] y (.bit b :: z)) (some (.extractBit b)) (frame [] y z) :=
        popMain (P := P) (q := .scanMain) [] y (.bit b :: z) _ rfl
      have c := pushTmp (P := P) (q := .extractBit b) [] y z b rfl
      have h := a.trans (c.trans (ih (b :: y)))
      simpa [leaf, List.append_assoc] using
        h.mono (m := 8 * (z.length + 1) + 6) (by omega)
    | L =>
      have a := popMain (P := P) (q := .scanMain) [] y (.L :: z) _ rfl
      exact (a.trans (ih y)).mono (by simp only [List.length_cons]; omega)
    | R =>
      have a := popMain (P := P) (q := .scanMain) [] y (.R :: z) _ rfl
      exact (a.trans (ih y)).mono (by simp only [List.length_cons]; omega)

/-- Reverse the temporary bits onto the raw output stack and halt. -/
theorem flush (y x : List Bool) :
    Travels P (5 * y.length + 4) .flushTmp (frame x y []) none (frame (y.reverse ++ x) [] []) := by
  induction y generalizing x with
  | nil =>
    have a := popTmp (P := P) (q := .flushTmp) x [] [] _ rfl
    exact a.trans (exec_stop (q := Label.done) rfl)
  | cons b y ih =>
    have a := popTmp (P := P) (q := .flushTmp) x (b :: y) [] _ rfl
    have c := pushRaw (P := P) (q := .outputBit b) x y [] b rfl
    have h := a.trans (c.trans (ih (b :: x)))
    simpa [List.append_assoc] using h.mono (m := 5 * (y.length + 1) + 4) (by omega)

theorem postpass (w : List Bool) :
    Travels P (13 * len w + 10) .scanMain (frame [] [] (wd w)) none (frame w [] []) := by
  have a := collectMain P (wd w) []
  simp only [leaves_wd, List.append_nil] at a
  have h := a.trans (flush P w.reverse [])
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h
  have hl := len_listBool w
  change (wd w).length = _ at hl
  exact h.mono (by rw [len_listBool]; omega)
end Output

/-! ## Packaging into `DetDLP.RunsWithin` -/

noncomputable def compiledProgram (P : Fr) :=
  table (lower (program P)) (Phase.run (Label.beginInput : Control P))

theorem initial_eq_cfg (P : Fr) (w : List Bool) :
    BitProgram.initial (compiledProgram P) w =
      cfg (some (Phase.run (Label.beginInput : Control P))) (fun _ => false) (frame w [] []) := by
  refine congrArg (BitProgram.Cfg.mk _ _) ?_
  funext j
  obtain ⟨i, rfl⟩ := port.surjective j
  cases i with
  | raw => simp [compiledProgram, table, physical, frame, pack]
  | tmp => simp [compiledProgram, table, physical, frame, pack]
  | hi k => cases k <;> simp [compiledProgram, table, physical, frame, pack, st]
  | lo k => cases k <;> simp [compiledProgram, table, physical, frame, pack, st]

theorem runsWithin_mono_local {A : PrimitiveMachine} {out : Fin A.tapeCount}
    {input output : List Bool} {τ₁ σ₁ τ₂ σ₂ : ℝ}
    (h : DetDLP.RunsWithin A out input output τ₁ σ₁) (hτ : τ₁ ≤ τ₂) (hσ : σ₁ ≤ σ₂) :
    DetDLP.RunsWithin A out input output τ₂ σ₂ := by
  obtain ⟨time, final, htr, hh, hout, ht, hs⟩ := h
  exact ⟨time, final, htr, hh, hout, ht.trans hτ, fun k c hk hc => (hs k c hk hc).trans hσ⟩

/-- Universal bridge: any polynomial-time function `f : List Bool → List Bool` certified by
`Groundwork.PolyT f` compiles to a uniform `PrimitiveMachine` running within polynomial time
and polynomial visited space `DetDLP.polyBound K w.length`. -/
theorem polyT_listBool_runsWithin (f : List Bool → List Bool) (hf : Groundwork.PolyT f) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ w : List Bool,
        DetDLP.RunsWithin M out w (f w)
          (DetDLP.polyBound K w.length) (DetDLP.polyBound K w.length) := by
  obtain ⟨P, c, hruns, hlen⟩ := hf
  let p := compiledProgram P
  let M_const : ℕ := 44 + (overhead P + 13) * (c * 3 ^ c)
  let K : ℕ := max (max 1 c) (Fintype.card Port * (M_const + 17) + 7 * M_const + 1)
  refine ⟨GuardedCompiler.primitive p, p.outputStack, K, ?_⟩
  intro w
  obtain ⟨n, hn, hrun⟩ := hruns w [] [] [] []
  simp only [List.append_nil] at hrun
  have h1 := prepass P w
  have h2 : Travels P (overhead P * n) (atLabel P (some P.entry) none) (frame [] [] (wd w))
      (some .scanMain) (frame [] [] (wd (f w))) := simulate_run P hrun
  have h3 := postpass P (f w)
  have htot := h1.trans (h2.trans h3)
  obtain ⟨r', sourceSteps, hsteps, htrace⟩ := htot (fun _ => false)
  rw [← initial_eq_cfg P w] at htrace
  have hraw := CompileSpace.compile_runsWithin_from_time p (output := f w) htrace rfl
    (by simp [p, compiledProgram, table, frame, pack])
  have hX1 : 1 ≤ w.length + 1 := by omega
  have hlen1 : len w + 1 = 3 * (w.length + 1) := by rw [len_listBool]; omega
  have hpow_c : (len w + 1) ^ c = 3 ^ c * (w.length + 1) ^ c := by rw [hlen1, mul_pow]
  have hn' : n ≤ (c * 3 ^ c) * (w.length + 1) ^ K := by
    calc n ≤ c * (len w + 1) ^ c := hn
      _ = (c * 3 ^ c) * (w.length + 1) ^ c := by rw [hpow_c]; ring
      _ ≤ (c * 3 ^ c) * (w.length + 1) ^ K :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (le_trans (le_max_right 1 c) (le_max_left _ _)))
  have hlf' : len (f w) ≤ (c * 3 ^ c) * (w.length + 1) ^ K := by
    calc len (f w) ≤ c * (len w + 1) ^ c := hlen w
      _ = (c * 3 ^ c) * (w.length + 1) ^ c := by rw [hpow_c]; ring
      _ ≤ (c * 3 ^ c) * (w.length + 1) ^ K :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (le_trans (le_max_right 1 c) (le_max_left _ _)))
  have hK1 : 1 ≤ K := le_trans (le_max_left 1 c) (le_max_left _ _)
  have hw_le : w.length + 1 ≤ (w.length + 1) ^ K := by
    calc w.length + 1 = (w.length + 1) ^ 1 := (pow_one _).symm
      _ ≤ (w.length + 1) ^ K := Nat.pow_le_pow_right hX1 hK1
  have h1_le : 1 ≤ (w.length + 1) ^ K := le_trans hX1 hw_le
  have hsrc_le : sourceSteps ≤ M_const * (w.length + 1) ^ K := by
    have hsum : (20 * w.length + 14) + (overhead P * n + (13 * len (f w) + 10)) ≤
        M_const * (w.length + 1) ^ K := by
      have ha : 20 * w.length + 24 ≤ 44 * (w.length + 1) ^ K := by nlinarith
      have hb : overhead P * n ≤ overhead P * ((c * 3 ^ c) * (w.length + 1) ^ K) :=
        Nat.mul_le_mul_left _ hn'
      have hc' : 13 * len (f w) ≤ 13 * ((c * 3 ^ c) * (w.length + 1) ^ K) :=
        Nat.mul_le_mul_left _ hlf'
      dsimp only [M_const]
      nlinarith
    exact hsteps.trans hsum
  have hK_big : Fintype.card Port * (M_const + 17) + 7 * M_const ≤ K := by
    dsimp only [K]
    omega
  have htime_nat : 7 * sourceSteps ≤ K * (w.length + 1) ^ K := by
    nlinarith
  have hspace_nat : Fintype.card Port * ((w.length + sourceSteps) + w.length + 15) ≤
      K * (w.length + 1) ^ K := by
    have hinner : (w.length + sourceSteps) + w.length + 15 ≤ (M_const + 17) * (w.length + 1) ^ K := by
      nlinarith
    have hmul := Nat.mul_le_mul_left (Fintype.card Port) hinner
    nlinarith
  refine runsWithin_mono_local hraw ?_ ?_
  · unfold DetDLP.polyBound
    exact_mod_cast htime_nat
  · unfold DetDLP.polyBound
    exact_mod_cast hspace_nat

end DetDLP.PolyTBridge


