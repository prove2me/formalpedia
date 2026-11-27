-- Prove2me | Definitions.Def_LindbladStructLearn_Alg1Learner
-- name    : LindbladStructLearn_Alg1Learner
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T02:42:29.461745+00:00
-- url     : https://prove2.me/theorems/3a463124-38f3-54a5-b224-3413b4321d88
-- title:
--   Algorithm 1 learner program and its verification vocabulary
-- statement:
--   The learner program used as the witness for Lemma 2.10 (Algorithm 1), together with the vocabulary needed to state its correctness.
--
--   1. **A structured statement language.** `Stmt` has straight-line instructions, sequencing, guarded loops `loop x y b` (run $b$ while $p_x > p_y$) and conditionals `ite x y a b`. It compiles to learner-machine code at a base address (`Stmt.comp`), and `Exec st s s' m` is its big-step semantics: statement $st$ takes state $s$ to $s'$ in $m$ machine steps.
--   2. **The program `prog k`.** For locality $k$ it consists of:
--      - initialisation `S0`, which loads $n$ and $M$ and writes the Pauli multiplication table and the phase-exponent table;
--      - the sampling block `S1`: $M$ rounds, each drawing, per qubit, a uniform letter $A_j$, a uniform bit $v_j$ and a uniform letter $B_j$ from five fair coins, then running one experiment at time $0$;
--      - record enumeration `S2`: an odometer over all digit vectors $(s,i_1,\dots,i_k,a_1,\dots,a_k,b_1,\dots,b_k)$, each written as an output record and marked invalid unless it is the canonical encoding of a Pauli pair;
--      - estimation `S3`: for every valid record, the average over the samples of the single-shot estimator `alg1Sample`, stored in the record's two real cells;
--      - a final `halt`.
--   3. **Auxiliary functions.** The states after initialisation, after each sampling round and at the end of sampling; the record addresses and contents; the enumeration order `Dseq`; the per-round sample probabilities; and the empirical estimates.
--
--   **Formalization Note** The program uses only the machine's own instructions, its real literals are rational, and it never uses `accept`/`reject`, so it is `Admissible`. The definitions are grouped in namespaces `LindbladStructLearn.Mach`, `LindbladStructLearn.Mach.A1` and `LindbladStructLearn.Rec`.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 1 (p.17) and Lemma 2.10 (p.18); machine model of the mission's goal theorem.

import Mathlib
import Definitions.Def_LindbladStructLearn_Reach
import Definitions.Def_LindbladStructLearn_mass
import Definitions.Def_LindbladStructLearn_Halted
import Definitions.Def_LindbladStructLearn_decode
import Definitions.Def_LindbladStructLearn_alg1Input
import Definitions.Def_LindbladStructLearn_IsChannel
import Definitions.Def_LindbladStructLearn_locFourier
import Definitions.Def_LindbladStructLearn_alg1Sample

/-!
# The Algorithm 1 learner program (witness for Lemma 2.10)

Definitions only. A structured statement language `Stmt` compiled to learner-machine code
(`Stmt.comp`) with a big-step semantics `Exec`; the program `prog k` (initialisation `S0`,
sampling block `S1`, record enumeration `S2`, estimation `S3`, `halt`); and the auxiliary
state, record, and sampling functions used to state its correctness lemmas.
-/

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section


namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn
/-- the deterministic successor (meaningful for non-random, non-halting instructions) -/
def dstep (P : Program) (s : MState) : MState :=
  let t : MState := { s with work := s.work + 1, core := { s.core with pc := s.core.pc + 1 } }
  match P[s.core.pc]? with
  | none => { s with work := s.work + 1 }
  | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
  | some (.pointerAdd dst a b) =>
      { t with core := { t.core with
        ptrs := Function.update s.core.ptrs dst (s.core.ptrs a + s.core.ptrs b) } }
  | some (.pointerSub dst a b) =>
      { t with core := { t.core with
        ptrs := Function.update s.core.ptrs dst (s.core.ptrs a - s.core.ptrs b) } }
  | some (.integerLoad dst a) =>
      { t with core := { t.core with
        ptrs := Function.update s.core.ptrs dst (s.intMem (s.core.ptrs a)) } }
  | some (.integerStore a b) =>
      { t with intMem := Function.update s.intMem (s.core.ptrs a) (s.core.ptrs b) }
  | some (.pointerReal dst a) =>
      { t with core := { t.core with
        regs := Function.update s.core.regs dst (s.core.ptrs a : ℝ) } }
  | some _ => s
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn
/-- deterministic instructions -/
def IsDet : Instr → Prop
  | .coin _ => False
  | .experiment _ _ => False
  | .halt _ => False
  | _ => True
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn
/-- `m` deterministic steps from `s` lead to `s'` -/
def DetRun (P : Program) (m : ℕ) (s s' : MState) : Prop :=
  (∀ i < m, ((dstep P)^[i] s).output = none ∧
    ∃ ins, P[((dstep P)^[i] s).core.pc]? = some ins ∧ IsDet ins) ∧ (dstep P)^[m] s = s'
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- the state after a coin with outcome `c` -/
def coinSt (s : MState) (d : ℕ) (c : ℤ) : MState :=
  ⟨⟨s.core.pc + 1, s.core.regs, Function.update s.core.ptrs d c, s.core.mem⟩, s.intMem, s.output,
    s.durations, s.work + 1⟩
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- the state after a halt -/
def haltSt (s : MState) (a : ℕ) : MState :=
  ⟨⟨s.core.pc + 1, s.core.regs, s.core.ptrs, s.core.mem⟩, s.intMem, some (s.core.ptrs a),
    s.durations, s.work + 1⟩
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- experiment decoding of the letters/signs -/
def expA (n : ℕ) (s : MState) (addr : ℕ) : Pauli n := fun i =>
  ⟨(s.intMem (s.core.ptrs addr + i)).toNat % 4, Nat.mod_lt _ (by norm_num)⟩
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
def expV (n : ℕ) (s : MState) (addr : ℕ) : Qubits n := fun i =>
  decide (s.intMem (s.core.ptrs addr + (n + i)) = 1)
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
def expB (n : ℕ) (s : MState) (addr : ℕ) : Pauli n := fun i =>
  ⟨(s.intMem (s.core.ptrs addr + (2 * n + i))).toNat % 4, Nat.mod_lt _ (by norm_num)⟩
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- the state after an experiment with outcome `w` -/
def expSt (n : ℕ) (s : MState) (addr tm : ℕ) (w : Qubits n) : MState :=
  ⟨⟨s.core.pc + 1, s.core.regs, s.core.ptrs, s.core.mem⟩,
    fun z => if h : s.core.ptrs addr + 3 * n ≤ z ∧ z < s.core.ptrs addr + 4 * n then
      (if w ⟨(z - (s.core.ptrs addr + 3 * n)).toNat, by omega⟩ then 1 else 0) else s.intMem z,
    s.output, s.durations ++ [s.core.regs tm], s.work + n + 1⟩
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- validity of an experiment's input cells -/
def ExpValid (n : ℕ) (s : MState) (addr tm : ℕ) : Prop :=
  0 ≤ s.core.regs tm ∧ ∀ i : Fin n, (0 ≤ s.intMem (s.core.ptrs addr + i) ∧
    s.intMem (s.core.ptrs addr + i) ≤ 3) ∧
    (s.intMem (s.core.ptrs addr + (n + i)) = 0 ∨ s.intMem (s.core.ptrs addr + (n + i)) = 1) ∧
    (0 ≤ s.intMem (s.core.ptrs addr + (2 * n + i)) ∧ s.intMem (s.core.ptrs addr + (2 * n + i)) ≤ 3)
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
def setpc (s : MState) (a : ℕ) : MState := ⟨⟨a, s.core.regs, s.core.ptrs, s.core.mem⟩, s.intMem,
  s.output, s.durations, s.work⟩
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- abstract (program-counter-free) action of a deterministic non-jump instruction -/
def ains (i : Instr) (s : MState) : MState :=
  let w := s.work + 1
  let c := s.core
  match i with
  | .core (.const d x) => ⟨⟨c.pc, Function.update c.regs d x, c.ptrs, c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .core (.add d a b) => ⟨⟨c.pc, Function.update c.regs d (c.regs a + c.regs b), c.ptrs, c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .core (.sub d a b) => ⟨⟨c.pc, Function.update c.regs d (c.regs a - c.regs b), c.ptrs, c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .core (.mul d a b) => ⟨⟨c.pc, Function.update c.regs d (c.regs a * c.regs b), c.ptrs, c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .core (.div d a b) => ⟨⟨c.pc, Function.update c.regs d (c.regs a / c.regs b), c.ptrs, c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .core (.load d q) => ⟨⟨c.pc, Function.update c.regs d (c.mem (c.ptrs q)), c.ptrs, c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .core (.store q r) => ⟨⟨c.pc, c.regs, c.ptrs, Function.update c.mem (c.ptrs q) (c.regs r)⟩, s.intMem, s.output, s.durations, w⟩
  | .core (.pset q x) => ⟨⟨c.pc, c.regs, Function.update c.ptrs q x, c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .core (.pcopy q q') => ⟨⟨c.pc, c.regs, Function.update c.ptrs q (c.ptrs q'), c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .core (.pinc q) => ⟨⟨c.pc, c.regs, Function.update c.ptrs q (c.ptrs q + 1), c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .core (.pdec q) => ⟨⟨c.pc, c.regs, Function.update c.ptrs q (c.ptrs q - 1), c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .pointerAdd d a b => ⟨⟨c.pc, c.regs, Function.update c.ptrs d (c.ptrs a + c.ptrs b), c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .pointerSub d a b => ⟨⟨c.pc, c.regs, Function.update c.ptrs d (c.ptrs a - c.ptrs b), c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .integerLoad d a => ⟨⟨c.pc, c.regs, Function.update c.ptrs d (s.intMem (c.ptrs a)), c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | .integerStore a b => ⟨⟨c.pc, c.regs, c.ptrs, c.mem⟩, Function.update s.intMem (c.ptrs a) (c.ptrs b), s.output, s.durations, w⟩
  | .pointerReal d a => ⟨⟨c.pc, Function.update c.regs d (c.ptrs a : ℝ), c.ptrs, c.mem⟩, s.intMem, s.output, s.durations, w⟩
  | _ => s
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- deterministic straight instructions -/
def Plain : Instr → Prop
  | .core (.const _ _) | .core (.add _ _ _) | .core (.sub _ _ _) | .core (.mul _ _ _)
  | .core (.div _ _ _) | .core (.load _ _) | .core (.store _ _) | .core (.pset _ _)
  | .core (.pcopy _ _) | .core (.pinc _) | .core (.pdec _) | .pointerAdd _ _ _ | .pointerSub _ _ _
  | .integerLoad _ _ | .integerStore _ _ | .pointerReal _ _ => True
  | _ => False
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- structured deterministic statements -/
inductive Stmt
  | ins : Instr → Stmt
  | seq : Stmt → Stmt → Stmt
  | loop : ℕ → ℕ → Stmt → Stmt
  | ite : ℕ → ℕ → Stmt → Stmt → Stmt
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
def Stmt.len : Stmt → ℕ
  | .ins _ => 1
  | .seq a b => a.len + b.len
  | .loop _ _ b => b.len + 2
  | .ite _ _ a b => a.len + b.len + 2
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- compilation at a base address -/
def Stmt.comp : Stmt → ℕ → List Instr
  | .ins i, _ => [i]
  | .seq a b, base => a.comp base ++ b.comp (base + a.len)
  | .loop x y b, base => [.core (.pjle x y (base + b.len + 2))] ++ b.comp (base + 1) ++
      [.core (.pjle 0 0 base)]
  | .ite x y a b, base => [.core (.pjle x y (base + b.len + 2))] ++ b.comp (base + 1) ++
      [.core (.pjle 0 0 (base + a.len + b.len + 2))] ++ a.comp (base + b.len + 2)
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- well-formed: only plain instructions -/
def Stmt.WF : Stmt → Prop
  | .ins i => Plain i
  | .seq a b => a.WF ∧ b.WF
  | .loop _ _ b => b.WF
  | .ite _ _ a b => a.WF ∧ b.WF
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
def tick (s : MState) : MState := ⟨s.core, s.intMem, s.output, s.durations, s.work + 1⟩
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- big-step semantics with step counts -/
inductive Exec : Stmt → MState → MState → ℕ → Prop
  | ins (i : Instr) (s : MState) (hp : Plain i) : Exec (.ins i) s (ains i s) 1
  | seq {a b : Stmt} {s s1 s2 : MState} {m1 m2 : ℕ} :
      Exec a s s1 m1 → Exec b s1 s2 m2 → Exec (.seq a b) s s2 (m1 + m2)
  | loopDone {x y : ℕ} {b : Stmt} {s : MState} (h : s.core.ptrs x ≤ s.core.ptrs y) :
      Exec (.loop x y b) s (tick s) 1
  | loopStep {x y : ℕ} {b : Stmt} {s s1 s2 : MState} {m1 m2 : ℕ}
      (h : ¬ s.core.ptrs x ≤ s.core.ptrs y) :
      Exec b (tick s) s1 m1 → Exec (.loop x y b) (tick s1) s2 m2 →
      Exec (.loop x y b) s s2 (m1 + m2 + 2)
  | iteT {x y : ℕ} {a b : Stmt} {s s1 : MState} {m : ℕ} (h : s.core.ptrs x ≤ s.core.ptrs y) :
      Exec a (tick s) s1 m → Exec (.ite x y a b) s s1 (m + 1)
  | iteF {x y : ℕ} {a b : Stmt} {s s1 : MState} {m : ℕ} (h : ¬ s.core.ptrs x ≤ s.core.ptrs y) :
      Exec b (tick s) s1 m → Exec (.ite x y a b) s (tick s1) (m + 2)
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- code placement -/
def Placed (P : Program) (base : ℕ) (code : List Instr) : Prop :=
  ∀ i : ℕ, i < code.length → P[base + i]? = code[i]?
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach.A1
abbrev I' := Instr
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def pset (q : ℕ) (c : ℤ) : Stmt := .ins (.core (.pset q c))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def pinc (q : ℕ) : Stmt := .ins (.core (.pinc q))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def pdec (q : ℕ) : Stmt := .ins (.core (.pdec q))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def pcopy (q q' : ℕ) : Stmt := .ins (.core (.pcopy q q'))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def padd (d a b : ℕ) : Stmt := .ins (.pointerAdd d a b)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def psub (d a b : ℕ) : Stmt := .ins (.pointerSub d a b)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def iload (d a : ℕ) : Stmt := .ins (.integerLoad d a)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def istore (a b : ℕ) : Stmt := .ins (.integerStore a b)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def rconst (d : ℕ) (c : ℝ) : Stmt := .ins (.core (.const d c))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def radd (d a b : ℕ) : Stmt := .ins (.core (.add d a b))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def rsub (d a b : ℕ) : Stmt := .ins (.core (.sub d a b))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def rmul (d a b : ℕ) : Stmt := .ins (.core (.mul d a b))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def rdiv (d a b : ℕ) : Stmt := .ins (.core (.div d a b))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def rstore (q i : ℕ) : Stmt := .ins (.core (.store q i))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def preal (d a : ℕ) : Stmt := .ins (.pointerReal d a)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def skip : Stmt := .ins (.core (.pcopy 0 0))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def seqs : List Stmt → Stmt
  | [] => skip
  | [a] => a
  | a :: l => .seq a (seqs l)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
/-- digit region and sample region -/
def cDIG (k : ℕ) : ℤ := 37 + 3 * k
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def cSAMP (k : ℕ) : ℤ := 38 + 6 * k
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
/-- letter tables: `(address, value)` of the nonzero entries -/
def tableEntries : List (ℤ × ℤ) :=
  [(5, 1), (6, 2), (7, 3), (8, 1), (10, 3), (11, 2), (12, 2), (13, 3), (15, 1), (16, 3), (17, 2),
   (18, 1), (26, 1), (27, 3), (29, 3), (31, 1), (33, 1), (34, 3)]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
/-- initialization -/
def S0 (k : ℕ) : Stmt := seqs ([iload 0 10, pset 6 1, iload 1 6, padd 2 0 0, padd 2 2 2, pset 11 1,
  pset 18 (3 * k + 3), pset 43 3, pset 45 2, pset 46 k, pset 47 4] ++
  (tableEntries.map fun e => seqs [pset 6 e.1, pset 9 e.2, istore 6 9]) ++
  [rconst 4 4, rconst 5 1, preal 8 1, rdiv 6 5 8, pset 4 (cSAMP k), pset 3 0])
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def inval : Stmt := pset 41 0
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def beyond : Stmt := .ite 21 10 (.ite 22 10 (.ite 23 10 skip inval) inval) inval
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def within (k : ℕ) : Stmt := seqs [.ite 22 10 (.ite 23 10 inval skip) skip,
  padd 7 19 11, .ite 20 7 skip (seqs [pset 6 (cDIG k), padd 6 6 7, pinc 6, iload 9 6,
    .ite 9 21 inval skip])]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def validBody (k : ℕ) : Stmt := seqs [pset 6 (cDIG k), padd 6 6 19, pinc 6, iload 21 6,
  padd 6 6 46, iload 22 6, padd 6 6 46, iload 23 6, .ite 20 19 beyond (within k), pinc 19]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def odoBody (k : ℕ) : Stmt := seqs [pset 6 (cDIG k), padd 6 6 15, iload 16 6, pinc 16,
  istore 6 16,
  .ite 15 10 (pset 17 (k + 1)) (.ite 15 46 (pcopy 17 0) (pset 17 4)),
  .ite 17 16 (seqs [pset 9 0, istore 6 9, .ite 15 10 (seqs [pset 40 1, pset 42 0]) (pdec 15)])
    (pset 42 0)]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def copyBody (k : ℕ) : Stmt := seqs [pset 6 (cDIG k), padd 6 6 19, iload 16 6, padd 6 13 19,
  istore 6 16, pinc 19]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def body2 (k : ℕ) : Stmt := seqs [pset 19 0, pset 17 (3 * k + 1), .loop 17 19 (copyBody k),
  pset 6 (cDIG k), iload 20 6, pset 41 1, pset 19 0, .loop 46 19 (validBody k),
  .ite 41 10 (seqs [pset 9 (k + 1), istore 13 9]) skip,
  padd 13 13 18, pinc 14, pset 42 1, pset 15 (3 * k), .loop 42 10 (odoBody k)]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
/-- record enumeration -/
def S2 (k : ℕ) : Stmt := seqs [padd 13 12 11, pset 14 0, pset 40 0, .loop 11 40 (body2 k),
  istore 12 14]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def siteBody : Stmt := seqs [padd 6 13 19, pinc 6, iload 21 6, padd 6 6 46, iload 22 6,
  padd 6 6 46, iload 23 6,
  padd 6 4 21, iload 24 6, padd 6 6 0, iload 25 6, padd 6 6 0, iload 26 6, padd 6 6 0, iload 27 6,
  padd 7 23 23, padd 7 7 7, padd 7 7 24, pset 8 4, padd 8 8 7, iload 28 8,
  pset 8 20, padd 8 8 7, iload 9 8, padd 31 31 9,
  padd 7 28 28, padd 7 7 7, padd 7 7 22, pset 8 4, padd 8 8 7, iload 29 8,
  pset 8 20, padd 8 8 7, iload 9 8, padd 31 31 9,
  .ite 26 29 skip (pset 30 0), .ite 29 26 skip (pset 30 0),
  .ite 24 10 skip (seqs [padd 31 31 25, padd 31 31 25]),
  .ite 26 10 skip (seqs [padd 31 31 27, padd 31 31 27]),
  pinc 19]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def caseE : Stmt := .ite 31 10 (radd 1 1 3) (.ite 31 11 (radd 2 2 3)
  (.ite 31 45 (rsub 1 1 3) (rsub 2 2 3)))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def sampBody : Stmt := seqs [pset 30 1, pset 31 0, pset 19 0, .loop 20 19 siteBody,
  .ite 30 10 skip (seqs [.loop 31 43 (psub 31 31 47), caseE]),
  padd 4 4 2, pinc 34]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def core3 (k : ℕ) : Stmt := seqs [rconst 3 1, pset 19 0,
  .loop 20 19 (seqs [rmul 3 3 4, pinc 19]),
  rconst 1 0, rconst 2 0, pset 4 (cSAMP k), pset 34 0, .loop 1 34 sampBody,
  rmul 1 1 6, rmul 2 2 6, pset 7 (3 * k + 1), padd 6 13 7, rstore 6 1, pinc 6, rstore 6 2]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def body3 (k : ℕ) : Stmt := seqs [iload 20 13, .ite 20 46 (core3 k) skip, padd 13 13 18, pinc 32]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
/-- estimation -/
def S3 (k : ℕ) : Stmt := seqs [padd 13 12 11, pset 32 0, .loop 14 32 (body3 k)]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
/-- the sampling block, at base address `a` -/
def S1 (a : ℕ) : List Instr :=
  [.core (.pjle 1 3 (a + 24)), .core (.pset 5 0),
   .core (.pjle 0 5 (a + 20)),
   .coin 7, .coin 8, .pointerAdd 9 7 7, .pointerAdd 9 9 8, .pointerAdd 6 4 5, .integerStore 6 9,
   .coin 9, .pointerAdd 6 6 0, .integerStore 6 9,
   .coin 7, .coin 8, .pointerAdd 9 7 7, .pointerAdd 9 9 8, .pointerAdd 6 6 0, .integerStore 6 9,
   .core (.pinc 5), .core (.pjle 0 0 (a + 2)),
   .experiment 4 0, .pointerAdd 4 4 2, .core (.pinc 3), .core (.pjle 0 0 a),
   .core (.pcopy 12 4)]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def a1 (k : ℕ) : ℕ := (S0 k).len
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def a2 (k : ℕ) : ℕ := a1 k + 25
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
def a3 (k : ℕ) : ℕ := a2 k + (S2 k).len
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
/-- the learner program for Algorithm 1 -/
def prog (k : ℕ) : Program :=
  (S0 k).comp 0 ++ S1 (a1 k) ++ (S2 k).comp (a2 k) ++ (S3 k).comp (a3 k) ++ [.halt 12]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- loop-free statements -/
def Stmt.NoLoop : Stmt → Prop
  | .ins i => Plain i
  | .seq a b => a.NoLoop ∧ b.NoLoop
  | .loop _ _ _ => False
  | .ite _ _ a b => a.NoLoop ∧ b.NoLoop
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- final state of loop-free statements -/
def Stmt.fin : Stmt → MState → MState
  | .ins i, s => ains i s
  | .seq a b, s => b.fin (a.fin s)
  | .ite x y a b, s => if s.core.ptrs x ≤ s.core.ptrs y then a.fin (tick s) else tick (b.fin (tick s))
  | .loop _ _ _, s => s
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- step count of loop-free statements -/
def Stmt.steps : Stmt → MState → ℕ
  | .ins _, _ => 1
  | .seq a b, s => a.steps s + b.steps (a.fin s)
  | .ite x y a b, s => if s.core.ptrs x ≤ s.core.ptrs y then a.steps (tick s) + 1
      else b.steps (tick s) + 2
  | .loop _ _ _, _ => 0
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- the state after initialization -/
def st0 (k n M : ℕ) (ε δ : ℝ) : MState := (S0 k).fin (alg1Input n M ε δ)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- the integer memory after initialization -/
def mem0 (n M : ℕ) (z : ℤ) : ℤ :=
  if z = 34 then 3 else if z = 33 then 1 else if z = 31 then 1 else if z = 29 then 3 else
  if z = 27 then 3 else if z = 26 then 1 else if z = 18 then 1 else if z = 17 then 2 else
  if z = 16 then 3 else if z = 15 then 1 else if z = 13 then 3 else if z = 12 then 2 else
  if z = 11 then 2 else if z = 10 then 3 else if z = 8 then 1 else if z = 7 then 3 else
  if z = 6 then 2 else if z = 5 then 1 else if z = 0 then n else if z = 1 then M else 0
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- phase exponents: `letterPhase a b = I ^ phexp a b` -/
def phexp (a b : Fin 4) : ℕ :=
  if a = 1 ∧ b = 2 then 1 else if a = 1 ∧ b = 3 then 3 else if a = 2 ∧ b = 1 then 3 else
  if a = 2 ∧ b = 3 then 1 else if a = 3 ∧ b = 1 then 1 else if a = 3 ∧ b = 2 then 3 else 0
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- pc-free coin effect -/
def cset (s : MState) (d : ℕ) (c : ℤ) : MState :=
  ⟨⟨s.core.pc, s.core.regs, Function.update s.core.ptrs d c, s.core.mem⟩, s.intMem, s.output,
    s.durations, s.work + 1⟩
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
def innerPost (s : MState) (c1 c2 c3 c4 c5 : Fin 2) : MState :=
  let t1 := cset (cset (tick s) 7 c1) 8 c2
  let t2 := ains (.integerStore 6 9) (ains (.pointerAdd 6 4 5) (ains (.pointerAdd 9 9 8)
    (ains (.pointerAdd 9 7 7) t1)))
  let t3 := ains (.integerStore 6 9) (ains (.pointerAdd 6 6 0) (cset t2 9 c3))
  let t4 := cset (cset t3 7 c4) 8 c5
  let t5 := ains (.integerStore 6 9) (ains (.pointerAdd 6 6 0) (ains (.pointerAdd 9 9 8)
    (ains (.pointerAdd 9 7 7) t4)))
  tick (ains (.core (.pinc 5)) t5)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- the five coin outcomes of one site -/
abbrev C5 := Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
def innerC (s : MState) (c : C5) : MState := innerPost s c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- `r` iterations of the site loop -/
def iterInner : (r : ℕ) → (Fin r → C5) → MState → MState
  | 0, _, s => s
  | r + 1, g, s => iterInner r (fun j => g j.succ) (innerC s (g 0))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- the three values written for a site -/
def cA (c : C5) : ℤ := (c.1 : ℤ) + c.1 + c.2.1
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
def cV (c : C5) : ℤ := c.2.2.1
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
def cB (c : C5) : ℤ := (c.2.2.2.1 : ℤ) + c.2.2.2.1 + c.2.2.2.2
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- pc-free experiment effect at address register 4 -/
def expSt0 (n : ℕ) (t : MState) (w : Qubits n) : MState :=
  ⟨t.core, fun z => if h : t.core.ptrs 4 + 3 * n ≤ z ∧ z < t.core.ptrs 4 + 4 * n then
      (if w ⟨(z - (t.core.ptrs 4 + 3 * n)).toNat, by omega⟩ then 1 else 0) else t.intMem z,
    t.output, t.durations ++ [t.core.regs 0], t.work + n + 1⟩
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- one sampling round -/
def outerPost (n : ℕ) (s : MState) (g : Fin n → C5) (w : Qubits n) : MState :=
  tick (ains (.core (.pinc 3)) (ains (.pointerAdd 4 4 2)
    (expSt0 n (tick (iterInner n g (ains (.core (.pset 5 0)) (tick s)))) w)))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- the decoded letters of a site choice -/
def letA (c : C5) : Fin 4 := ⟨(cA c).toNat % 4, Nat.mod_lt _ (by norm_num)⟩
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
def letB (c : C5) : Fin 4 := ⟨(cB c).toNat % 4, Nat.mod_lt _ (by norm_num)⟩
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
def bitV (c : C5) : Bool := decide (cV c = 1)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- weight of a round -/
def wt (evo : ℝ → Super (Qubits n) (Qubits n)) (g : Fin n → C5) (w : Qubits n) : ℝ≥0∞ :=
  (1 / 32) ^ n * ENNReal.ofReal (bornAmp (evo 0) (fun j => letA (g j)) (fun j => bitV (g j))
    (fun j => letB (g j)) w).re
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- state before the site loop -/
def pre1 (s : MState) : MState := ains (.core (.pset 5 0)) (tick s)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- state at the experiment -/
def pre2 (n : ℕ) (s : MState) (g : Fin n → C5) : MState := tick (iterInner n g (pre1 s))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- data of one round -/
abbrev Rd (n : ℕ) := (Fin n → C5) × Qubits n
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
def iterOuter : (r : ℕ) → (Fin r → Rd n) → MState → MState
  | 0, _, s => s
  | r + 1, G, s => iterOuter r (fun j => G j.succ) (outerPost n s (G 0).1 (G 0).2)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}
/-- exit of the sampling phase -/
def exitSt (s : MState) : MState := ains (.core (.pcopy 12 4)) (tick s)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- fields untouched by pointer-only code -/
def Same (s t : MState) : Prop :=
  t.output = s.output ∧ t.durations = s.durations ∧ t.core.regs = s.core.regs ∧ t.core.mem = s.core.mem
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- the learner's per-position violation test -/
abbrev badM (s0 r x y z nx : ℤ) : Prop :=
  (s0 ≤ r ∧ ¬ (x ≤ 0 ∧ y ≤ 0 ∧ z ≤ 0)) ∨ (¬ s0 ≤ r ∧ ((y ≤ 0 ∧ z ≤ 0) ∨ (¬ s0 ≤ r + 1 ∧ nx ≤ x)))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
def preV (k : ℕ) (t : MState) : MState :=
  ains (.integerLoad 23 6) (ains (.pointerAdd 6 6 46) (ains (.integerLoad 22 6)
    (ains (.pointerAdd 6 6 46) (ains (.integerLoad 21 6) (ains (.core (.pinc 6))
    (ains (.pointerAdd 6 6 19) (ains (.core (.pset 6 (cDIG k))) t)))))))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Rec
open LindbladTolerant.Testing LindbladStructLearn
/-- radix of digit `i` of a record: `i = 0` the size `s ∈ [0,k]`, `1 ≤ i ≤ k` a site `< n`,
`k < i ≤ 3k` a letter `< 4` -/
def rad (k n i : ℕ) : ℕ := if i = 0 then k + 1 else if i ≤ k then n else 4
end LindbladStructLearn.Rec

namespace LindbladStructLearn.Rec
open LindbladTolerant.Testing LindbladStructLearn
/-- odometer increment starting at position `q` (carrying towards position 0);
the flag is `true` on overflow of position 0 -/
def incAt (k n : ℕ) : ℕ → (ℕ → ℕ) → (ℕ → ℕ) × Bool
  | 0, D => if D 0 + 1 < rad k n 0 then (Function.update D 0 (D 0 + 1), false)
      else (Function.update D 0 0, true)
  | q + 1, D => if D (q + 1) + 1 < rad k n (q + 1) then
        (Function.update D (q + 1) (D (q + 1) + 1), false)
      else incAt k n q (Function.update D (q + 1) 0)
end LindbladStructLearn.Rec

namespace LindbladStructLearn.Rec
open LindbladTolerant.Testing LindbladStructLearn
def succD (k n : ℕ) (D : ℕ → ℕ) : ℕ → ℕ := (incAt k n (3 * k) D).1
end LindbladStructLearn.Rec

namespace LindbladStructLearn.Rec
open LindbladTolerant.Testing LindbladStructLearn
/-- the `j`-th digit vector of the enumeration -/
def Dseq (k n j : ℕ) : ℕ → ℕ := (succD k n)^[j] (fun _ => 0)
end LindbladStructLearn.Rec

namespace LindbladStructLearn.Rec
open LindbladTolerant.Testing LindbladStructLearn
/-- number of records -/
def Kc (k n : ℕ) : ℕ := ∏ i ∈ Finset.range (3 * k + 1), rad k n i
end LindbladStructLearn.Rec

namespace LindbladStructLearn.Rec
open LindbladTolerant.Testing LindbladStructLearn
def InRange (k n : ℕ) (D : ℕ → ℕ) : Prop := ∀ i ≤ 3 * k, D i < rad k n i
end LindbladStructLearn.Rec

namespace LindbladStructLearn.Rec
open LindbladTolerant.Testing LindbladStructLearn
/-- canonical-form check performed by the learner -/
def validD (k : ℕ) (D : ℕ → ℕ) : Prop :=
  ∀ r < k, (D 0 ≤ r → D (1 + r) = 0 ∧ D (1 + k + r) = 0 ∧ D (1 + 2 * k + r) = 0) ∧
    (r < D 0 → ¬ (D (1 + k + r) = 0 ∧ D (1 + 2 * k + r) = 0) ∧
      (r + 1 < D 0 → D (1 + r) < D (1 + (r + 1))))
end LindbladStructLearn.Rec

namespace LindbladStructLearn.Rec
open LindbladTolerant.Testing LindbladStructLearn
/-- the pair of Paulis named by a digit vector (mirrors `recordPair`) -/
def pairOf (n k : ℕ) (D : ℕ → ℕ) : Pauli n × Pauli n := by
  classical
  exact (fun i => if h : ∃ r, r < D 0 ∧ D (1 + r) = (i : ℕ) then
      ⟨D (1 + k + Nat.find h) % 4, Nat.mod_lt _ (by norm_num)⟩ else 0,
    fun i => if h : ∃ r, r < D 0 ∧ D (1 + r) = (i : ℕ) then
      ⟨D (1 + 2 * k + Nat.find h) % 4, Nat.mod_lt _ (by norm_num)⟩ else 0)
end LindbladStructLearn.Rec

namespace LindbladStructLearn.Rec
/-- value of the digit vector restricted to positions `≤ q` (position `q` least significant) -/
def oval (k n : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, D => D 0
  | q + 1, D => oval k n q D * rad k n (q + 1) + D (q + 1)
end LindbladStructLearn.Rec

namespace LindbladStructLearn.Rec
/-- number of digit vectors on positions `≤ q` -/
def oW (k n q : ℕ) : ℕ := ∏ i ∈ Finset.range (q + 1), rad k n i
end LindbladStructLearn.Rec

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
/-- radix as the learner computes it -/
def capZ (k n : ℕ) (q : ℤ) : ℤ := if q ≤ 0 then k + 1 else if q ≤ k then n else 4
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Rec
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.Mach.A1
/-- letter of `P₁` at record position `r` -/
def L1 (k : ℕ) (D : ℕ → ℕ) (r : ℕ) : Fin 4 := ⟨D (1 + k + r) % 4, Nat.mod_lt _ (by norm_num)⟩
end LindbladStructLearn.Rec

namespace LindbladStructLearn.Rec
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.Mach.A1
/-- letter of `P₂` at record position `r` -/
def L2 (k : ℕ) (D : ℕ → ℕ) (r : ℕ) : Fin 4 := ⟨D (1 + 2 * k + r) % 4, Nat.mod_lt _ (by norm_num)⟩
end LindbladStructLearn.Rec

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
def iteS2 (k : ℕ) : Stmt := .ite 41 10 (seqs [pset 9 (k + 1), istore 13 9]) skip
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
open Classical in
def recCell (k n j i : ℕ) : ℤ :=
  if i = 0 then (if validD k (Dseq k n j) then (Dseq k n j 0 : ℤ) else k + 1) else Dseq k n j i
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
/-- address of record `j` -/
def recAddr (k : ℕ) (p : ℤ) (j : ℕ) : ℤ := p + 1 + j * (3 * k + 3)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
def scr2 : Finset ℕ := {6, 7, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 40, 41, 42}
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
/-- straight-line prefix of `siteBody` (as a statement) -/
def preSiteL : List Stmt := [padd 6 13 19, pinc 6, iload 21 6, padd 6 6 46, iload 22 6,
  padd 6 6 46, iload 23 6,
  padd 6 4 21, iload 24 6, padd 6 6 0, iload 25 6, padd 6 6 0, iload 26 6, padd 6 6 0, iload 27 6,
  padd 7 23 23, padd 7 7 7, padd 7 7 24, pset 8 4, padd 8 8 7, iload 28 8,
  pset 8 20, padd 8 8 7, iload 9 8, padd 31 31 9,
  padd 7 28 28, padd 7 7 7, padd 7 7 22, pset 8 4, padd 8 8 7, iload 29 8,
  pset 8 20, padd 8 8 7, iload 9 8, padd 31 31 9]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
def finL : List Stmt → MState → MState
  | [], s => s
  | a :: l, s => finL l (a.fin s)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
def postS : Stmt := seqs [.ite 26 29 skip (pset 30 0), .ite 29 26 skip (pset 30 0),
  .ite 24 10 skip (seqs [padd 31 31 25, padd 31 31 25]),
  .ite 26 10 skip (seqs [padd 31 31 27, padd 31 31 27]), pinc 19]
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
/-- multiplication and phase tables in memory -/
def Tab (im : ℤ → ℤ) : Prop :=
  ∀ x y : Fin 4, im (4 + 4 * (x : ℕ) + (y : ℕ)) = ((letterMul x y : ℕ) : ℤ) ∧
    im (20 + 4 * (x : ℕ) + (y : ℕ)) = (phexp x y : ℤ)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
def siteExp (L1 L2 A B : Fin 4) (V W : Bool) : ℕ :=
  phexp L2 A + phexp (letterMul L2 A) L1 + (if A ≠ 0 ∧ V = true then 2 else 0) +
    (if B ≠ 0 ∧ W = true then 2 else 0)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
def scrS : Finset ℕ := {6, 7, 8, 9, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31}
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
/-- registers change only at the given indices -/
def RegFix (s t : MState) (S : Finset ℕ) : Prop :=
  t.output = s.output ∧ t.durations = s.durations ∧ t.core.mem = s.core.mem ∧
    ∀ q, q ∉ S → t.core.regs q = s.core.regs q
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
open Classical in
/-- contribution of one sample -/
def contrib (S : ℕ) (L1f L2f : ℕ → Fin 4) (Af Bf : ℕ → Fin 4) (Vf Wf : ℕ → Bool) : ℂ :=
  if ∀ r < S, Bf r = letterMul (letterMul (L2f r) (Af r)) (L1f r) then
    (4 : ℂ) ^ S * Complex.I ^ (∑ r ∈ Finset.range S, siteExp (L1f r) (L2f r) (Af r) (Bf r) (Vf r) (Wf r))
  else 0
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
/-- read a Pauli/Bool string at a natural-number site (0 off range) -/
def atP {n : ℕ} (A : Pauli n) (x : ℕ) : Fin 4 := if h : x < n then A ⟨x, h⟩ else 0
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
def atB {n : ℕ} (v : Qubits n) (x : ℕ) : Bool := if h : x < n then v ⟨x, h⟩ else false
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
/-- sample strings of round `i` -/
def sA {n M : ℕ} (smp : Fin M → Rd n) (i : Fin M) : Pauli n := fun x => letA ((smp i).1 x)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
def sV {n M : ℕ} (smp : Fin M → Rd n) (i : Fin M) : Qubits n := fun x => bitV ((smp i).1 x)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
def sB {n M : ℕ} (smp : Fin M → Rd n) (i : Fin M) : Pauli n := fun x => letB ((smp i).1 x)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
def sW {n M : ℕ} (smp : Fin M → Rd n) (i : Fin M) : Qubits n := (smp i).2
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
/-- the sample region of memory -/
def SampMem (k n M : ℕ) (smp : Fin M → Rd n) (im : ℤ → ℤ) : Prop :=
  ∀ i : Fin M, ∀ x : Fin n, im (cSAMP k + 4 * n * i + x) = cA ((smp i).1 x) ∧
    im (cSAMP k + 4 * n * i + (n + x)) = cV ((smp i).1 x) ∧
    im (cSAMP k + 4 * n * i + (2 * n + x)) = cB ((smp i).1 x) ∧
    im (cSAMP k + 4 * n * i + (3 * n + x)) = if (smp i).2 x then 1 else 0
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
/-- the estimate of record `j` -/
def est (k n M : ℕ) (smp : Fin M → Rd n) (j : ℕ) : ℂ :=
  (∑ i : Fin M, alg1Sample (pairOf n k (Dseq k n j)) (sA smp i) (sV smp i) (sB smp i) (sW smp i)) *
    (1 / (M : ℂ))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
def scr3 : Finset ℕ := {4, 6, 7, 8, 9, 13, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34}
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
/-- the sum of the samples' values for record `j` -/
def tsum (k n M : ℕ) (smp : Fin M → Rd n) (j : ℕ) : ℂ :=
  ∑ i : Fin M, alg1Sample (pairOf n k (Dseq k n j)) (sA smp i) (sV smp i) (sB smp i) (sW smp i)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
/-- state after the sampling phase, at the exit test -/
def sEnd (k n M : ℕ) (ε δ : ℝ) (G : Fin M → Rd n) : MState := iterOuter M G (st0 k n M ε δ)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
/-- state entering the record phase (pc 96) -/
def xEnd (k n M : ℕ) (ε δ : ℝ) (G : Fin M → Rd n) : MState := exitSt (sEnd k n M ε δ G)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
/-- the output pointer -/
def pEnd (k n M : ℕ) : ℤ := cSAMP k + 4 * n * M
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.FourierAux
open LindbladTolerant.Testing LindbladStructLearn
/-- tensor product of single-qubit matrices -/
def tens {n : ℕ} (a : Fin n → Op Bool) : Op (Qubits n) := fun x y => ∏ i, a i (x i) (y i)
end LindbladStructLearn.FourierAux

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
variable {n : ℕ}
def xA (x : Rd n) : Pauli n := fun j => letA (x.1 j)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
variable {n : ℕ}
def xV (x : Rd n) : Qubits n := fun j => bitV (x.1 j)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
variable {n : ℕ}
def xB (x : Rd n) : Pauli n := fun j => letB (x.1 j)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
variable {n : ℕ}
/-- probability of one round's data -/
def pw (Φ : Super (Qubits n) (Qubits n)) (x : Rd n) : ℝ :=
  (1 / 32) ^ n * (bornAmp Φ (xA x) (xV x) (xB x) x.2).re
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
variable {n : ℕ}
abbrev JQ (n k : ℕ) := {Q : Pauli n × Pauli n // (pairSupport Q).card ≤ k}
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
variable {n : ℕ}
/-- the empirical estimate of `Q` from rounds `ω` -/
def avg {M : ℕ} (ω : Fin M → Rd n) (Q : Pauli n × Pauli n) : ℂ :=
  (∑ i, alg1Sample Q (xA (ω i)) (xV (ω i)) (xB (ω i)) (ω i).2) * (1 / (M : ℂ))
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
def AdmI (op : Instr) : Prop := match op with
    | .core (.const _ c) => ∃ q : ℚ, c = (q : ℝ)
    | .core .accept => False
    | .core .reject => False
    | _ => True
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
def Stmt.Adm : Stmt → Prop
  | .ins i => AdmI i
  | .seq a b => a.Adm ∧ b.Adm
  | .loop _ _ b => b.Adm
  | .ite _ _ a b => a.Adm ∧ b.Adm
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
variable {n : ℕ}
/-- the tail bound -/
def mB (k n M : ℕ) : ℕ :=
  Kc k n * (130 * k + 62) + 5 + (Kc k n * (M * (70 * k + 32) + 4 * k + 32) + 3) + 1
end LindbladStructLearn.Mach.A1


