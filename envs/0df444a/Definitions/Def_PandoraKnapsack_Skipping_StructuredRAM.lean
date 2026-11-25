-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_StructuredRAM
-- name    : PandoraKnapsack_Skipping_StructuredRAM
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-25T17:32:55.478321+00:00
-- url     : https://prove2.me/theorems/3edc06dc-ae8e-43d4-a2c0-fc1078271cba
-- title:
--   Structured blocks with costed real-RAM execution
-- statement:
--   A command sequences instructions, branches on the sign of a register, or iterates a guarded block. Its compilation fixes every instruction address. The execution relation counts each dynamic instruction, including jumps and oracle calls. A program appends the accepting instruction to the compiled top-level block.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, explicit implementation of Algorithm 1 and the polynomial-time clause of Theorem 5.1 under the machine model in Prove2Me theorem 7898d376-37b2-42fd-8375-13696ef594ef. Derived implementation for the dyadic approximate solver.

import Definitions.Def_PandoraKnapsack_Skipping_Machine

namespace PandoraKnapsack.Skipping.StructuredRAM

/-- Data visible to a structured program. Instruction addresses appear only after compilation. -/
structure Store where
  regs : ℕ → ℝ
  ptrs : ℕ → ℤ
  mem : ℤ → ℝ
  draws : ℕ

def Store.atPC (s : Store) (pc : ℕ) : State :=
  ⟨⟨pc,s.regs,s.ptrs,s.mem⟩,s.draws⟩

noncomputable def initial (n m T : ℕ) : Store :=
  let s := initState n m T
  ⟨s.core.regs,s.core.ptrs,s.core.mem,s.draws⟩

/-- A primitive with a single fall-through successor. -/
inductive Prim where
  | const (dst : ℕ) (c : ℝ)
  | add (dst i j : ℕ)
  | sub (dst i j : ℕ)
  | mul (dst i j : ℕ)
  | div (dst i j : ℕ)
  | load (dst q : ℕ)
  | store (q i : ℕ)
  | pset (q : ℕ) (c : ℤ)
  | pcopy (q q' : ℕ)
  | pinc (q : ℕ)
  | pdec (q : ℕ)
  | value (dst q : ℕ)
  | cost (dst q q' : ℕ)
  | cdf (dst q q' src : ℕ)
  | truncMean (dst q q' src : ℕ)
  | uniform (dst : ℕ)
  | ptrReal (dst q : ℕ)

def Prim.emit : Prim → Instr
  | .const d v => .core (.const d v)
  | .add d i j => .core (.add d i j)
  | .sub d i j => .core (.sub d i j)
  | .mul d i j => .core (.mul d i j)
  | .div d i j => .core (.div d i j)
  | .load d q => .core (.load d q)
  | .store q i => .core (.store q i)
  | .pset q c => .core (.pset q c)
  | .pcopy q q' => .core (.pcopy q q')
  | .pinc q => .core (.pinc q)
  | .pdec q => .core (.pdec q)
  | .value d q => .value d q
  | .cost d q q' => .cost d q q'
  | .cdf d q q' a => .cdf d q q' a
  | .truncMean d q q' a => .truncMean d q q' a
  | .uniform d => .uniform d
  | .ptrReal d q => .ptrReal d q

variable {n m T : ℕ}

def Store.setReg (s : Store) (dst : ℕ) (v : ℝ) :=
  {s with regs := Function.update s.regs dst v}
def Store.setPtr (s : Store) (q : ℕ) (v : ℤ) :=
  {s with ptrs := Function.update s.ptrs q v}

noncomputable def Prim.exec (I : Instance n m T) (ω : ℕ → ℝ) (s : Store) : Prim → Store
  | .const d v => s.setReg d v
  | .add d i j => s.setReg d (s.regs i + s.regs j)
  | .sub d i j => s.setReg d (s.regs i - s.regs j)
  | .mul d i j => s.setReg d (s.regs i * s.regs j)
  | .div d i j => s.setReg d (s.regs i / s.regs j)
  | .load d q => s.setReg d (s.mem (s.ptrs q))
  | .store q i => {s with mem := Function.update s.mem (s.ptrs q) (s.regs i)}
  | .pset q c => s.setPtr q c
  | .pcopy q q' => s.setPtr q (s.ptrs q')
  | .pinc q => s.setPtr q (s.ptrs q + 1)
  | .pdec q => s.setPtr q (s.ptrs q - 1)
  | .value d q => s.setReg d (match ptrIndex n (s.ptrs q) with
      | some i => I.value i | none => 0)
  | .cost d q q' => s.setReg d (match ptrIndex n (s.ptrs q), ptrIndex m (s.ptrs q') with
      | some i,some j => I.cost i j | _,_ => 0)
  | .cdf d q q' a => s.setReg d (match ptrIndex n (s.ptrs q), ptrIndex m (s.ptrs q') with
      | some i,some j => PandoraKnapsack.Skipping.cdf I i j (s.regs a) | _,_ => 0)
  | .truncMean d q q' a => s.setReg d (match ptrIndex n (s.ptrs q), ptrIndex m (s.ptrs q') with
      | some i,some j => PandoraKnapsack.Skipping.truncMean I i j (s.regs a) | _,_ => 0)
  | .uniform d => {s.setReg d (ω s.draws) with draws := s.draws + 1}
  | .ptrReal d q => s.setReg d (s.ptrs q : ℝ)

/-- Structured control over the primitive operations of the MPK machine. -/
inductive Cmd where
  | skip
  | prim (p : Prim)
  | seq (first next : Cmd)
  | itePos (r : ℕ) (yes no : Cmd)
  | whilePos (r : ℕ) (body : Cmd)

/-- Number of emitted instructions, excluding the final accept. -/
def Cmd.size : Cmd → ℕ
  | .skip => 0
  | .prim _ => 1
  | .seq a b => a.size + b.size
  | .itePos _ a b => 1 + a.size + 1 + b.size
  | .whilePos _ a => 1 + a.size + 1

/-- The total cost includes dynamically executed conditional tests and jumps. -/
inductive Exec (I : Instance n m T) (ω : ℕ → ℝ) : Cmd → Store → Store → ℕ → Prop where
  | skip (s) : Exec I ω .skip s s 0
  | prim (s p) : Exec I ω (.prim p) s (p.exec I ω s) 1
  | seq {a b s u v k l} : Exec I ω a s u k → Exec I ω b u v l →
      Exec I ω (.seq a b) s v (k+l)
  | ite_true {r a b s v k} : 0 < s.regs r → Exec I ω a s v k →
      Exec I ω (.itePos r a b) s v (1+k+1)
  | ite_false {r a b s v k} : s.regs r ≤ 0 → Exec I ω b s v k →
      Exec I ω (.itePos r a b) s v (1+k)
  | while_false {r a s} : s.regs r ≤ 0 → Exec I ω (.whilePos r a) s s 1
  | while_true {r a s u v k l} : 0 < s.regs r → Exec I ω a s u k →
      Exec I ω (.whilePos r a) u v l → Exec I ω (.whilePos r a) s v (1+k+1+l)

/-- Jump unconditionally by comparing one pointer with itself. -/
def jump (t : ℕ) : Instr := .core (.pjle 0 0 t)
def testLE (r t : ℕ) : Instr := .core (.jle r t)

def Cmd.compile (base : ℕ) : Cmd → Program
  | .skip => []
  | .prim p => [p.emit]
  | .seq a b => a.compile base ++ b.compile (base + a.size)
  | .itePos r a b =>
    let noStart := base + 1 + a.size + 1
    [testLE r noStart] ++ (a.compile (base+1) ++ ([jump (noStart+b.size)] ++ b.compile noStart))
  | .whilePos r a =>
    [testLE r (base+1+a.size+1)] ++ (a.compile (base+1) ++ [jump base])

def program (c : Cmd) : Program := c.compile 0 ++ [.core .accept]

/-- Compute the signed distance from pointer q to the real-valued address. -/
def gap (q addr tmp : ℕ) : Cmd :=
  .seq (.prim (.ptrReal tmp q)) (.prim (.sub tmp addr tmp))

/-- Walk to a nonnegative integral address held in a real register.
Only pointer q and scratch register tmp are overwritten. -/
def seek (q addr tmp : ℕ) : Cmd :=
  .seq (.prim (.pset q 0)) (.seq (gap q addr tmp)
    (.whilePos tmp (.seq (.prim (.pinc q)) (gap q addr tmp))))

def readAt (dst addr q tmp : ℕ) : Cmd := .seq (seek q addr tmp) (.prim (.load dst q))
def writeAt (addr src q tmp : ℕ) : Cmd := .seq (seek q addr tmp) (.prim (.store q src))

end PandoraKnapsack.Skipping.StructuredRAM


