-- Prove2me | Definitions.Def_BC1992_Machines
-- name    : BC1992_Machines
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-08T00:36:11.812103+00:00
-- url     : https://prove2.me/theorems/7e07ae04-3b79-4eb2-9ce5-a0491855036f
-- title:
--   Section 2 (Lemma 2.2): Multi-Tape Turing Machines, the Class FP, Multi-Stack Programs, and the BC-to-TM Soundness Compiler
-- statement:
--   Formalizes deterministic multi-tape Turing machines `TM` over finite alphabets `Fin G` (`G >= 3`, blank `0`, bit symbols `1` and `2`) with blank-normalized tape zippers `Tape`, single-step transition `TM.step`, bounded execution `TM.run`, halting predicate `TM.HaltsWithin`, polynomial-time computability `TM.ComputesInTime`, and the complexity class `FP`; together with the intermediate structured multi-stack machine (`Stmt`, big-step cost semantics `Exec`), the flat-instruction compiler `stmtToTM : Stmt -> TM`, and the frame-based compiler `compileBC : Nat -> Fn n m -> Stmt` paired with its syntactic polynomial step bound `Fn.timePoly`, `topCompileBC`, and `topTimePoly`.
-- source:
--   Stephen Bellantoni and Stephen Cook, 'A new recursion-theoretic characterization of the polytime functions', Computational Complexity 2 (1992), pp. 97-110 (doi:10.1007/BF01201998). Section 2, Lemma 2.2, pp. 101-102.

/-
  Source: Stephen Bellantoni and Stephen Cook,
  "A new recursion-theoretic characterization of the polytime functions",
  Computational Complexity 2 (1992), 97–110, DOI: 10.1007/BF01201998.

  Part II (`BC1992_Machines`):
  Deterministic multi-tape Turing machines (`TM`), polynomial-time complexity class `FP`,
  the multi-stack intermediate machine (`Stmt`, `Exec`), and the explicit compiler from
  `Fn n m` via `Stmt` to `TM` (`compileBC`, `topCompileBC`, `stmtToTM`, `Fn.timePoly`, `topTimePoly`).
-/
import Definitions.Def_BC1992_Syntax

namespace BC1992

/-! ## 1. Deterministic Multi-Tape Turing Machines and the Class `FP` -/

/-- Head movement directions: left (`L`), right (`R`), or stationary (`S`). -/
inductive Dir : Type where
  | L
  | R
  | S
  deriving DecidableEq, Repr

/-- A Turing machine tape represented as a canonical zipper `⟨left, head, right⟩`
    (with `left` and `right` listed outwards from the head). -/
structure Tape (Γ : Type) where
  left : List Γ
  head : Γ
  right : List Γ
  deriving DecidableEq, Repr

namespace Tape

variable {Γ : Type} [DecidableEq Γ]

/-- Push a cell onto one side of the zipper, dropping it if it would be an outermost blank. -/
def consB (blank a : Γ) : List Γ → List Γ
  | [] => if a = blank then [] else [a]
  | l => a :: l

/-- Overwrite the head cell. -/
def write (t : Tape Γ) (a : Γ) : Tape Γ := { t with head := a }

/-- Move the head in direction `Dir`. -/
def move (blank : Γ) : Dir → Tape Γ → Tape Γ
  | .L, ⟨[], h, r⟩ => ⟨[], blank, consB blank h r⟩
  | .L, ⟨a :: l, h, r⟩ => ⟨l, a, consB blank h r⟩
  | .R, ⟨l, h, []⟩ => ⟨consB blank h l, blank, []⟩
  | .R, ⟨l, h, a :: r⟩ => ⟨consB blank h l, a, r⟩
  | .S, t => t

end Tape

/-- Deterministic multi-tape Turing machines with `k ≥ 1` tapes, `Q ≥ 1` control states,
    and finite tape alphabet `Fin G` (`G ≥ 3`, where `0` = blank, `1` = bit `0`, `2` = bit `1`). -/
structure TM where
  k : Nat
  Q : Nat
  G : Nat
  hk : 0 < k
  hQ : 0 < Q
  hG : 2 < G
  /-- Finite transition table; `none` means halt. -/
  δ : Fin Q → (Fin k → Fin G) → Option (Fin Q × (Fin k → Fin G) × (Fin k → Dir))

/-- Machine configuration: control state in `Fin Q` and `k` tapes over `Fin G`. -/
structure Cfg (k Q G : Nat) where
  state : Fin Q
  tapes : Fin k → Tape (Fin G)

namespace TM

variable (M : TM)

/-- The blank tape symbol (`0`). -/
def blank : Fin M.G := ⟨0, by have := M.hG; omega⟩

/-- The tape symbol encoding a bit (`1` for `false`, `2` for `true`). -/
def bitSym (b : Bool) : Fin M.G := ⟨if b then 2 else 1, by have := M.hG; split <;> omega⟩

/-- Decode a tape symbol as a bit, or `none` if it is blank / non-bit. -/
def decodeBit (a : Fin M.G) : Option Bool :=
  if a.val = 1 then some false else if a.val = 2 then some true else none

/-- Read the maximal prefix of bit symbols from a list of tape cells. -/
def readBits : List (Fin M.G) → Word
  | [] => []
  | a :: l =>
    match M.decodeBit a with
    | some b => b :: readBits l
    | none => []

/-- Initial tape holding input word `x`, with head on its first symbol (or blank if `x = []`). -/
def inputTape : Word → Tape (Fin M.G)
  | [] => ⟨[], M.blank, []⟩
  | b :: w => ⟨[], M.bitSym b, w.map M.bitSym⟩

/-- All-blank tape. -/
def blankTape : Tape (Fin M.G) := ⟨[], M.blank, []⟩

/-- Initial configuration on input word `x`: state `0`, tape `0` holding `x`, other tapes blank. -/
def init (x : Word) : Cfg M.k M.Q M.G :=
  ⟨⟨0, M.hQ⟩, fun i => if i.val = 0 then M.inputTape x else M.blankTape⟩

/-- Single transition step; returns `none` iff the machine has halted. -/
def step (c : Cfg M.k M.Q M.G) : Option (Cfg M.k M.Q M.G) :=
  match M.δ c.state (fun i => (c.tapes i).head) with
  | none => none
  | some (q, w, d) => some ⟨q, fun i => ((c.tapes i).write (w i)).move M.blank (d i)⟩

/-- Run for at most `n` transitions, stopping early once the machine halts. -/
def run : Nat → Cfg M.k M.Q M.G → Cfg M.k M.Q M.G
  | 0, c => c
  | n + 1, c =>
    match M.step c with
    | none => c
    | some c' => run n c'

/-- Output word of a configuration, read on tape `0` from the head cell rightwards. -/
def output (c : Cfg M.k M.Q M.G) : Word :=
  M.readBits ((c.tapes ⟨0, M.hk⟩).head :: (c.tapes ⟨0, M.hk⟩).right)

/-- `M` halts on input `x` within `t` transitions with output word `y`. -/
def HaltsWithin (x : Word) (t : Nat) (y : Word) : Prop :=
  ∃ s, s ≤ t ∧ M.step (M.run s (M.init x)) = none ∧ M.output (M.run s (M.init x)) = y

/-- `M` computes `f` within polynomial time `p(|x|)`. -/
def ComputesInTime (f : Word → Word) (p : Poly) : Prop :=
  ∀ x : Word, M.HaltsWithin x (p.eval x.length) (f x)

end TM

/-- **The complexity class `FP`** of polynomial-time computable word functions, defined via
    deterministic multi-tape Turing machines with an explicit polynomial time bound. -/
def FP (f : Word → Word) : Prop :=
  ∃ (M : TM) (p : Poly), M.ComputesInTime f p

/-! ## 2. Multi-Stack Intermediate Machine (`Stmt`, `Exec`) and `Stmt`-to-`TM` Compiler -/

/-- A stack assignment maps each stack index `i : Nat` to a binary word `Word`. -/
abbrev Stacks := Nat → Word

/-- Update stack `i` in `σ` to hold `w`. -/
def Stacks.set (σ : Stacks) (i : Nat) (w : Word) : Stacks :=
  fun j => if j = i then w else σ j

/-- Initial stack assignment on input `x`: stack `0` holds `x`, all other stacks are empty. -/
def initStacks (x : Word) : Stacks :=
  fun i => if i = 0 then x else []

/-- Multi-stack imperative programs over binary word stacks. -/
inductive Stmt : Type where
  | skip
  | push (i : Nat) (b : Bool)
  | pop (i : Nat)
  | seq (s₁ s₂ : Stmt)
  | ifTop (i : Nat) (sNil sFalse sTrue : Stmt)
  | whileNE (i : Nat) (body : Stmt)
  deriving DecidableEq, Repr

/-- Big-step operational semantics with explicit unit-cost step accounting:
    `Exec s σ c σ'` means executing `s` from stack state `σ` terminates in `c` steps with `σ'`. -/
inductive Exec : Stmt → Stacks → Nat → Stacks → Prop where
  | skip (σ : Stacks) : Exec .skip σ 0 σ
  | push (i : Nat) (b : Bool) (σ : Stacks) : Exec (.push i b) σ 1 (σ.set i (b :: σ i))
  | pop (i : Nat) (σ : Stacks) : Exec (.pop i) σ 1 (σ.set i (σ i).tail)
  | seq {s t : Stmt} {σ₁ σ₂ σ₃ : Stacks} {c₁ c₂ : Nat} :
      Exec s σ₁ c₁ σ₂ → Exec t σ₂ c₂ σ₃ → Exec (.seq s t) σ₁ (c₁ + c₂) σ₃
  | ifE {i : Nat} {sE s0 s1 : Stmt} {σ σ' : Stacks} {c : Nat} :
      σ i = [] → Exec sE σ c σ' → Exec (.ifTop i sE s0 s1) σ (c + 1) σ'
  | if0 {i : Nat} {sE s0 s1 : Stmt} {σ σ' : Stacks} {c : Nat} {w : Word} :
      σ i = false :: w → Exec s0 σ c σ' → Exec (.ifTop i sE s0 s1) σ (c + 1) σ'
  | if1 {i : Nat} {sE s0 s1 : Stmt} {σ σ' : Stacks} {c : Nat} {w : Word} :
      σ i = true :: w → Exec s1 σ c σ' → Exec (.ifTop i sE s0 s1) σ (c + 1) σ'
  | whileDone {i : Nat} {body : Stmt} {σ : Stacks} :
      σ i = [] → Exec (.whileNE i body) σ 1 σ
  | whileStep {i : Nat} {body : Stmt} {σ σ' σ'' : Stacks} {c c' : Nat} :
      σ i ≠ [] → Exec body σ c σ' → Exec (.whileNE i body) σ' c' σ'' →
      Exec (.whileNE i body) σ (c + c' + 1) σ''

/-- Highest stack index referenced by a `Stmt`. -/
def Stmt.maxStack : Stmt → Nat
  | .skip => 0
  | .push i _ => i
  | .pop i => i
  | .seq s t => max s.maxStack t.maxStack
  | .ifTop i sE s0 s1 => max i (max sE.maxStack (max s0.maxStack s1.maxStack))
  | .whileNE i body => max i body.maxStack

/-- Flat Turing-machine instructions for simulating stack programs. -/
inductive TMInstr : Type where
  | moveL (i : Nat)
  | writeBit (i : Nat) (b : Bool)
  | popR (i : Nat)
  | branch (i : Nat) (pcE pc0 pc1 : Nat)
  deriving DecidableEq, Repr

/-- Unconditional jump instruction. -/
def TMInstr.jump (target : Nat) : TMInstr :=
  .branch 0 target target target

/-- Compile a `Stmt` starting at instruction offset `pc` into a flat list of `TMInstr`. -/
def compileStmt : Stmt → Nat → List TMInstr
  | .skip, _ => []
  | .push i b, _ => [.moveL i, .writeBit i b]
  | .pop i, _ => [.popR i]
  | .seq s t, pc =>
      let cs := compileStmt s pc
      cs ++ compileStmt t (pc + cs.length)
  | .ifTop i sE s0 s1, pc =>
      let pE := pc + 1
      let cE := compileStmt sE pE
      let p0 := pE + cE.length + 1
      let c0 := compileStmt s0 p0
      let p1 := p0 + c0.length + 1
      let c1 := compileStmt s1 p1
      let pEnd := p1 + c1.length
      [.branch i pE p0 p1] ++ cE ++ [.jump pEnd] ++ c0 ++ [.jump pEnd] ++ c1
  | .whileNE i body, pc =>
      let pBody := pc + 1
      let cBody := compileStmt body pBody
      let pEnd := pBody + cBody.length + 1
      [.branch i pEnd pBody pBody] ++ cBody ++ [.jump pc]

/-- Clamp a program counter `pc : Nat` into `Fin (len + 1)`. -/
def clampPC (len pc : Nat) : Fin (len + 1) :=
  if h : pc < len + 1 then ⟨pc, h⟩ else ⟨len, Nat.lt_succ_self len⟩

/-- Bit symbol in `Fin 3`. -/
def bitFin3 (b : Bool) : Fin 3 :=
  ⟨if b then 2 else 1, by cases b <;> decide⟩

/-- Blank symbol in `Fin 3`. -/
def blankFin3 : Fin 3 := ⟨0, by omega⟩

/-- Turn a flat instruction list `code : List TMInstr` over `k` tapes into a `TM`. -/
def codeTM (k : Nat) (hk : 0 < k) (code : List TMInstr) : TM where
  k := k
  Q := code.length + 1
  G := 3
  hk := hk
  hQ := Nat.zero_lt_succ code.length
  hG := by omega
  δ q heads :=
    match code[q.val]? with
    | none => none
    | some (.moveL i) =>
        some (clampPC code.length (q.val + 1),
              heads,
              fun j => if j.val = i then .L else .S)
    | some (.writeBit i b) =>
        some (clampPC code.length (q.val + 1),
              fun j => if j.val = i then bitFin3 b else heads j,
              fun _ => .S)
    | some (.popR i) =>
        some (clampPC code.length (q.val + 1),
              fun j => if j.val = i then blankFin3 else heads j,
              fun j => if j.val = i then .R else .S)
    | some (.branch i pcE pc0 pc1) =>
        let sym := if h : i < k then (heads ⟨i, h⟩).val else 0
        let nextPC := if sym = 0 then pcE else if sym = 1 then pc0 else pc1
        some (clampPC code.length nextPC, heads, fun _ => .S)

/-- Top-level multi-tape `TM` compiled from a stack statement `s : Stmt`. -/
def stmtToTM (s : Stmt) : TM :=
  codeTM (s.maxStack + 1) (Nat.zero_lt_succ _) (compileStmt s 0)

/-! ## 3. Compiler from Bellantoni–Cook Programs `Fn n m` to `Stmt` (`compileBC`) -/

/-- Write a list of words `ws` into consecutive stacks `start, start + 1, …`. -/
def setFrame (σ : Stacks) (start : Nat) : List Word → Stacks
  | [] => σ
  | w :: ws => (setFrame σ (start + 1) ws).set start w

/-- Empty stack `dst`. -/
def clearStack (dst : Nat) : Stmt :=
  .whileNE dst (.pop dst)

/-- Pop `src` until empty, pushing each bit onto `dst` (reversing onto `dst`). -/
def moveRev (src dst : Nat) : Stmt :=
  .whileNE src
    (.ifTop src
      .skip
      (.seq (.pop src) (.push dst false))
      (.seq (.pop src) (.push dst true)))

/-- Pop `tmp` until empty, pushing each bit onto both `src` and `dst`. -/
def dupRev (tmp src dst : Nat) : Stmt :=
  .whileNE tmp
    (.ifTop tmp
      .skip
      (.seq (.pop tmp) (.seq (.push src false) (.push dst false)))
      (.seq (.pop tmp) (.seq (.push src true) (.push dst true))))

/-- Non-destructively copy `src` into an empty `dst` using an empty scratch stack `tmp`. -/
def copyToEmpty (src dst tmp : Nat) : Stmt :=
  .seq (moveRev src tmp) (dupRev tmp src dst)

/-- Move `src` to `dst` using an empty scratch stack `tmp`, leaving `src` and `tmp` empty. -/
def moveStack (src dst tmp : Nat) : Stmt :=
  .seq (moveRev src tmp) (moveRev tmp dst)

/-- Copy `count` consecutive stacks `[src, src + count)` to `[dst, dst + count)`. -/
def copyRange (src dst : Nat) : Nat → Nat → Stmt
  | 0, _ => .skip
  | count + 1, tmp =>
      .seq (copyRange (src + 1) (dst + 1) count tmp)
           (copyToEmpty src dst tmp)

/-- Clear `count` consecutive stacks `[dst, dst + count)`. -/
def clearRange (dst : Nat) : Nat → Stmt
  | 0 => .skip
  | count + 1 => .seq (clearStack dst) (clearRange (dst + 1) count)

/-- Evaluate subprogram `sub` on `count` arguments at `src` into `dst`, using workspace `workBase`. -/
def evalSubTo (src count dst workBase : Nat) (sub : Stmt) : Stmt :=
  .seq (copyRange src (workBase + 1) count (workBase + 1 + count))
    (.seq sub
      (.seq (clearRange (workBase + 1) count)
            (moveStack workBase dst (workBase + 1))))

/-- Evaluate a tuple of `k` subprograms on `count` arguments at `src` into `[dst, dst + k)`. -/
def evalTuple (src count dst workBase : Nat) : {k : Nat} → (Fin k → Stmt) → Stmt
  | 0, _ => .skip
  | _ + 1, subs =>
      .seq (evalTuple src count (dst + 1) workBase (fun i => subs i.succ))
           (evalSubTo src count dst workBase (subs ⟨0, Nat.zero_lt_succ _⟩))

/-- Single step of safe recursion on notation for bit `b : Bool`. -/
def evalRecStep (base n m : Nat) (b : Bool) (sub : Stmt) : Stmt :=
  let revW := base + 2 + n + m
  let workBase := base + 3 + n + m
  let tmp := workBase + 1 + (n + 1) + (m + 1)
  .seq (copyRange (base + 2 + n) (workBase + 1 + (n + 1) + 1) m tmp)
    (.seq (copyToEmpty base (workBase + 1 + (n + 1)) tmp)
      (.seq (copyRange (base + 1) (workBase + 1) (n + 1) tmp)
        (.seq sub
          (.seq (clearRange (workBase + 1) ((n + 1) + (m + 1)))
            (.seq (clearStack base)
              (.seq (moveStack workBase base (workBase + 1))
                (.seq (.pop revW) (.push (base + 1) b))))))))

/-- Loop executing `srec` over the reversed recursion argument on stack `base + 2 + n + m`. -/
def recLoop (base n m : Nat) (sub0 sub1 : Stmt) : Stmt :=
  let revW := base + 2 + n + m
  .whileNE revW
    (.ifTop revW
      .skip
      (evalRecStep base n m false sub0)
      (evalRecStep base n m true sub1))

/-- Compile a Bellantoni–Cook program `f : Fn n m` at frame base `base : Nat` into a `Stmt`. -/
def compileBC (base : Nat) : {n m : Nat} → Fn n m → Stmt
  | _, _, .zero => .skip
  | n, m, .projN i => copyToEmpty (base + 1 + i.val) base (base + 1 + n + m)
  | n, m, .projS j => copyToEmpty (base + 1 + n + j.val) base (base + 1 + n + m)
  | _, _, .s0 => .seq (copyToEmpty (base + 1) base (base + 2)) (.push base false)
  | _, _, .s1 => .seq (copyToEmpty (base + 1) base (base + 2)) (.push base true)
  | _, _, .pred => .seq (copyToEmpty (base + 1) base (base + 2)) (.pop base)
  | _, _, .cond =>
      .ifTop (base + 1)
        (copyToEmpty (base + 2) base (base + 5))
        (copyToEmpty (base + 3) base (base + 5))
        (copyToEmpty (base + 4) base (base + 5))
  | n, m, .comp (k := k) (l := l) h rs ts =>
      .seq (evalTuple (base + 1) (n + m) (base + 1 + n + m + 1 + k) (base + 1 + n + m + 1 + k + l)
              (fun j => compileBC (base + 1 + n + m + 1 + k + l) (ts j)))
        (.seq (evalTuple (base + 1) n (base + 1 + n + m + 1) (base + 1 + n + m + 1 + k + l)
                (fun i => compileBC (base + 1 + n + m + 1 + k + l) (rs i)))
          (.seq (compileBC (base + 1 + n + m) h)
            (.seq (clearRange (base + 1 + n + m + 1) (k + l))
                  (moveStack (base + 1 + n + m) base (base + 1 + n + m + 1)))))
  | n + 1, m, .srec g h0 h1 =>
      .seq (moveRev (base + 1) (base + 2 + n + m))
        (.seq (evalSubTo (base + 2) (n + m) base (base + 3 + n + m) (compileBC (base + 3 + n + m) g))
              (recLoop base n m (compileBC (base + 3 + n + m) h0) (compileBC (base + 3 + n + m) h1)))

/-- Syntactic polynomial time bound for `compileBC base f` when all normal and safe arguments
    have bit-length at most `K`. -/
def Fn.timePoly : {n m : Nat} → Fn n m → Poly
  | _, _, .zero => .const 1
  | _, _, .projN _ => .linear 9 2
  | _, _, .projS _ => .linear 9 2
  | _, _, .s0 => .linear 9 3
  | _, _, .s1 => .linear 9 3
  | _, _, .pred => .linear 9 3
  | _, _, .cond => .linear 9 3
  | n, m, .comp (k := k) (l := l) h rs ts =>
      .add
        (.add
          (.add
            (.add
              (.add (Poly.sumFin fun j => (ts j).timePoly)
                    (.mul (.const l)
                      (.add (.mul (.const (n + m)) (.linear 11 3))
                            ((Poly.linear 8 2).comp
                              (.add (Poly.sumFin fun i => (rs i).fullSizePoly)
                                    (Poly.sumFin fun j => (ts j).fullSizePoly))))))
              (.add (Poly.sumFin fun i => (rs i).timePoly)
                    (.mul (.const k)
                      (.add (.mul (.const n) (.linear 11 3))
                            ((Poly.linear 8 2).comp
                              (.add (Poly.sumFin fun i => (rs i).fullSizePoly)
                                    (Poly.sumFin fun j => (ts j).fullSizePoly)))))))
            (h.timePoly.comp
              (.add (Poly.sumFin fun i => (rs i).fullSizePoly)
                    (Poly.sumFin fun j => (ts j).fullSizePoly))))
          (.mul (.const (k + l))
            ((Poly.linear 2 1).comp
              (.add (Poly.sumFin fun i => (rs i).fullSizePoly)
                    (Poly.sumFin fun j => (ts j).fullSizePoly)))))
        ((Poly.linear 8 2).comp
          (h.fullSizePoly.comp
            (.add (Poly.sumFin fun i => (rs i).fullSizePoly)
                  (Poly.sumFin fun j => (ts j).fullSizePoly))))
  | n + 1, m, .srec g h0 h1 =>
      .add
        (.add (.linear 4 1)
          (.add (.add g.timePoly (.mul (.const (n + m)) (.linear 11 3)))
                ((Poly.linear 8 2).comp (Fn.srec g h0 h1).fullSizePoly)))
        (.add
          (.mul .var
            (.add
              (.add
                ((Poly.add h0.timePoly h1.timePoly).comp (Fn.srec g h0 h1).fullSizePoly)
                (.mul (.const ((n + 1) + (m + 1)))
                  ((Poly.linear 11 3).comp (Fn.srec g h0 h1).fullSizePoly)))
              ((Poly.linear 10 7).comp (Fn.srec g h0 h1).fullSizePoly)))
          (.const 1))

/-- Top-level stack program for a unary BC program `prog : Fn 1 0`. -/
def topCompileBC (prog : Fn 1 0) : Stmt :=
  .seq (moveStack 0 1 2) (compileBC 0 prog)

/-- Syntactic polynomial bounding the TM step count of `stmtToTM (topCompileBC prog)`. -/
def topTimePoly (prog : Fn 1 0) : Poly :=
  .mul (.const 2) (.add (.linear 8 2) prog.timePoly)

end BC1992


