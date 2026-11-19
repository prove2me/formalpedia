-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
-- name    : DecrAlmostLinearSSSP_RAMFoundation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T11:09:47.93574+00:00
-- url     : https://prove2.me/theorems/83ece2b7-9cbc-4fcb-8947-d3b7f253966e
-- title:
--   Scalar RAM programs and representation interfaces for decremental SSSP
-- statement:
--   This interface describes finite scalar RAM programs used in the decremental source-distance reductions.
--
--   A data state has natural and real register banks and natural and real memory banks. Structured commands consist of individual instructions, sequencing, comparisons, and loops. The relation
--
--   $$
--   \operatorname{Eval}(c,s,t,s')
--   $$
--
--   records execution of command $c$ from data state $s$ to data state $s'$ with exactly $t$ charged instructions. Compilation maps a structured command to a finite list of instructions in the mission's scalar RAM model.
--
--   The interface also defines radix-trie queue data, adjacency records, label-setting and memory-representation predicates, and the concrete native programs used for exact recomputation. For the general-weight reduction it defines dyadic scales, rounded barrier instances, source-program simulation, stored-array observations, cache and pointer states, and the finite wrapper code. All addresses and instructions are concrete; semantic predicates express relationships that subsequent correctness theorems must prove.
--
--   This module supplies data structures, program syntax and operation specifications. Correctness, termination, queue bounds, approximation guarantees and amortized work are separate theorem obligations. The only supporting existence lemma is the elementary power-of-two bound needed to define a least trie height.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, October 2026 submission #912, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf, p.4 unnumbered exact-recomputation and arbitrary-weight reductions; p.18 scalar unit-cost arithmetic model. Concrete compiler, memory interfaces, radix-trie and wrapper code implement these reductions.

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Adapters
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Graph
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Machine
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
section FlattenedModule1
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
def guestReg (j : ℕ) : ℕ := 7 + 2 * j
def guestAddress (base a : ℕ) : ℕ := base + 2 * a + 1
def decodeGuest (c : Machine) : Machine where
  pc := c.natReg 2
  realReg := fun j => c.realReg (guestReg j)
  natReg := fun j => c.natReg (guestReg j)
  realMem := fun a => c.realMem (guestAddress (c.natReg 0) a)
  natMem := fun a => c.natMem (guestAddress (c.natReg 0) a)
  halted := c.natReg 4 == 1
  fault := c.natReg 5 == 1
  work := c.natReg 3
def embeddedInstruction (offset returnPC pc : ℕ) (ins : Instruction) : List Instruction :=
  let next := offset + 8 * (pc + 1)
  let header := [Instruction.natural 2 (pc + 1), .nadd 3 3 1]
  let simple := fun ins => header ++ [ins, .jump next, .jump next, .jump next, .jump next, .jump next]
  let mem := fun ins a => header ++ [.nadd 6 (guestReg a) (guestReg a), .nadd 6 6 0,
    .nadd 6 6 1, ins, .jump next, .jump next]
  match ins with
  | .rational d q => simple (.rational (guestReg d) q)
  | .natural d a => simple (.natural (guestReg d) a)
  | .cast d a => simple (.cast (guestReg d) (guestReg a))
  | .add d a b => simple (.add (guestReg d) (guestReg a) (guestReg b))
  | .sub d a b => simple (.sub (guestReg d) (guestReg a) (guestReg b))
  | .mul d a b => simple (.mul (guestReg d) (guestReg a) (guestReg b))
  | .div d a b => simple (.div (guestReg d) (guestReg a) (guestReg b))
  | .log d a => simple (.log (guestReg d) (guestReg a))
  | .nadd d a b => simple (.nadd (guestReg d) (guestReg a) (guestReg b))
  | .nsub d a b => simple (.nsub (guestReg d) (guestReg a) (guestReg b))
  | .load d a => mem (.load (guestReg d) 6) a
  | .store a d => mem (.store 6 (guestReg d)) a
  | .loadN d a => mem (.loadN (guestReg d) 6) a
  | .storeN a d => mem (.storeN 6 (guestReg d)) a
  | .jump t => header ++ [.natural 2 t, .jump (offset + 8 * t), .jump next, .jump next, .jump next, .jump next]
  | .less a b t => header ++ [.less (guestReg a) (guestReg b) (offset + 8 * pc + 5), .jump next,
    .jump next, .natural 2 t, .jump (offset + 8 * t), .jump next]
  | .lessN a b t => header ++ [.lessN (guestReg a) (guestReg b) (offset + 8 * pc + 5), .jump next,
    .jump next, .natural 2 t, .jump (offset + 8 * t), .jump next]
  | .halt => header ++ [.natural 4 1, .jump returnPC, .jump next, .jump next, .jump next, .jump next]
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule1
section FlattenedModule2
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule2
section FlattenedModule3
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def instructionEffect (ins : Instruction) (c : Machine) : Machine := by
  classical
  exact match ins with
  | .rational a q => {c with realReg := Function.update c.realReg a (q : ℝ)}
  | .natural a b => {c with natReg := Function.update c.natReg a b}
  | .cast a b => {c with realReg := Function.update c.realReg a (c.natReg b : ℝ)}
  | .add a b e => {c with realReg := Function.update c.realReg a (c.realReg b + c.realReg e)}
  | .sub a b e => {c with realReg := Function.update c.realReg a (c.realReg b - c.realReg e)}
  | .mul a b e => {c with realReg := Function.update c.realReg a (c.realReg b * c.realReg e)}
  | .div a b e => {c with realReg := Function.update c.realReg a (c.realReg b / c.realReg e)}
  | .log a b => {c with realReg := Function.update c.realReg a (Real.log (c.realReg b))}
  | .nadd a b e => {c with natReg := Function.update c.natReg a (c.natReg b + c.natReg e)}
  | .nsub a b e => {c with natReg := Function.update c.natReg a (c.natReg b - c.natReg e)}
  | .load a b => {c with realReg := Function.update c.realReg a (c.realMem (c.natReg b))}
  | .store a b => {c with realMem := Function.update c.realMem (c.natReg a) (c.realReg b)}
  | .loadN a b => {c with natReg := Function.update c.natReg a (c.natMem (c.natReg b))}
  | .storeN a b => {c with natMem := Function.update c.natMem (c.natReg a) (c.natReg b)}
  | .jump t => {c with pc := t}
  | .less a b t => if c.realReg a < c.realReg b then {c with pc := t} else c
  | .lessN a b t => if c.natReg a < c.natReg b then {c with pc := t} else c
  | .halt => {c with halted := true}
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule3
section FlattenedModule4
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
def scalarTranslation : Instruction → Option Instruction
  | .rational d q => some (.rational (guestReg d) q)
  | .natural d a => some (.natural (guestReg d) a)
  | .cast d a => some (.cast (guestReg d) (guestReg a))
  | .add d a b => some (.add (guestReg d) (guestReg a) (guestReg b))
  | .sub d a b => some (.sub (guestReg d) (guestReg a) (guestReg b))
  | .mul d a b => some (.mul (guestReg d) (guestReg a) (guestReg b))
  | .div d a b => some (.div (guestReg d) (guestReg a) (guestReg b))
  | .log d a => some (.log (guestReg d) (guestReg a))
  | .nadd d a b => some (.nadd (guestReg d) (guestReg a) (guestReg b))
  | .nsub d a b => some (.nsub (guestReg d) (guestReg a) (guestReg b))
  | _ => none
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule4
section FlattenedModule5
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule5
section FlattenedModule6
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule6
section FlattenedModule7
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def embeddedCodeAux (offset returnPC : ℕ) : ℕ → List Instruction → List Instruction
  | _, [] => []
  | pc, ins :: rest => embeddedInstruction offset returnPC pc ins ++ embeddedCodeAux offset returnPC (pc + 1) rest
def embeddedCode (offset returnPC : ℕ) (code : List Instruction) : List Instruction :=
  embeddedCodeAux offset returnPC 0 code
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule7
section FlattenedModule8
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def headerState (c : Machine) (pc : ℕ) : Machine :=
  { c with
    pc := c.pc + 2
    work := c.work + 2
    natReg := Function.update (Function.update c.natReg 2 (pc + 1)) 3 (c.natReg 3 + 1) }
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule8
section FlattenedModule9
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule9
section FlattenedModule10
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
def branchInstruction (natural : Bool) (a b target : ℕ) : Instruction :=
  if natural then .lessN a b target else .less a b target
def branchTest (natural : Bool) (c : Machine) (a b : ℕ) : Prop :=
  if natural then c.natReg a < c.natReg b else c.realReg a < c.realReg b
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule10
section FlattenedModule11
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def memoryTranslation : Instruction → Option (Instruction × ℕ)
  | .load d a => some (.load (guestReg d) 6, a)
  | .loadN d a => some (.loadN (guestReg d) 6, a)
  | .store a d => some (.store 6 (guestReg d), a)
  | .storeN a d => some (.storeN 6 (guestReg d), a)
  | _ => none
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule11
section FlattenedModule12
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def embeddedDestination (offset returnPC : ℕ) (g : Machine) : ℕ :=
  if g.halted then returnPC else offset + 8 * g.pc
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule12
section FlattenedModule13
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def EmbedsCode (host guest : Program) (offset returnPC : ℕ) : Prop :=
  ∀ pc ins, guest.code[pc]? = some ins → ∀ slot < 8,
    host.code[offset + 8 * pc + slot]? = (embeddedInstruction offset returnPC pc ins)[slot]?
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule13
section FlattenedModule14
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule14
section FlattenedModule15
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def Straight : Instruction → Prop
  | .jump _ | .less _ _ _ | .lessN _ _ _ | .halt => False
  | _ => True
def ModifiesMemory : Instruction → Prop
  | .store _ _ | .storeN _ _ => True
  | _ => False
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule15
section FlattenedModule16
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
attribute [local instance] Classical.propDecidable
structure Data where
  realReg : ℕ → ℝ
  natReg : ℕ → ℕ
  realMem : ℕ → ℝ
  natMem : ℕ → ℕ
def data (c : Machine) : Data := ⟨c.realReg,c.natReg,c.realMem,c.natMem⟩
def Data.machine (s : Data) : Machine := ⟨0,s.realReg,s.natReg,s.realMem,s.natMem,false,false,0⟩
structure Atom where
  instruction : Instruction
  straight : Straight instruction
noncomputable def Atom.effect (a : Atom) (s : Data) : Data := data (instructionEffect a.instruction s.machine)
inductive Test
  | realLess (a b : ℕ)
  | natLess (a b : ℕ)
noncomputable def Test.holds : Test → Data → Prop
  | .realLess a b,s => s.realReg a < s.realReg b
  | .natLess a b,s => s.natReg a < s.natReg b
def Test.emit : Test → ℕ → Instruction
  | .realLess a b,t => .less a b t
  | .natLess a b,t => .lessN a b t
inductive Cmd
  | skip
  | atom (a : Atom)
  | seq (a b : Cmd)
  | branch (test : Test) (yes no : Cmd)
  | loop (test : Test) (body : Cmd)
inductive Eval : Cmd → Data → ℕ → Data → Prop
  | skip (s : Data) : Eval .skip s 0 s
  | atom (a : Atom) (s : Data) : Eval (.atom a) s 1 (a.effect s)
  | seq {a b : Cmd} {s t u : Data} {ta tb : ℕ} :
      Eval a s ta t → Eval b t tb u → Eval (.seq a b) s (ta+tb) u
  | branchYes {test : Test} {yes no : Cmd} {s t : Data} {cost : ℕ} :
      test.holds s → Eval yes s cost t → Eval (.branch test yes no) s (cost+1) t
  | branchNo {test : Test} {yes no : Cmd} {s t : Data} {cost : ℕ} :
      ¬ test.holds s → Eval no s cost t → Eval (.branch test yes no) s (cost+2) t
  | loopNo {test : Test} {body : Cmd} (s : Data) :
      ¬ test.holds s → Eval (.loop test body) s 2 s
  | loopYes {test : Test} {body : Cmd} {s t u : Data} {first rest : ℕ} :
      test.holds s → Eval body s first t → Eval (.loop test body) t rest u →
      Eval (.loop test body) s (first+rest+2) u
def codeSize : Cmd → ℕ
  | .skip => 0
  | .atom _ => 1
  | .seq a b => codeSize a+codeSize b
  | .branch _ yes no => codeSize no+codeSize yes+2
  | .loop _ body => codeSize body+3
def compile : Cmd → ℕ → List Instruction
  | .skip,_ => []
  | .atom a,_ => [a.instruction]
  | .seq a b,start => compile a start ++ compile b (start+codeSize a)
  | .branch test yes no,start =>
      [test.emit (start+codeSize no+2)] ++ (compile no (start+1) ++
      ([.jump (start+codeSize no+codeSize yes+2)] ++ compile yes (start+codeSize no+2)))
  | .loop test body,start =>
      [test.emit (start+2),.jump (start+codeSize body+3)] ++ (compile body (start+2) ++ [.jump start])
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule16
section FlattenedModule17
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
def CodeAt (p : Program) (start : ℕ) (code : List Instruction) : Prop :=
  ∀ j < code.length,p.code[start+j]? = code[j]?
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule17
section FlattenedModule18
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule18
section FlattenedModule19
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule19
section FlattenedModule20
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def FaultWellFormed (c : Machine) : Prop := c.fault = false ∨ c.halted = true
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule20
section FlattenedModule21
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule21
section FlattenedModule22
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
def program (init update : Cmd) : Program where
  code := compile init 0 ++ (.halt :: (compile update (codeSize init+1) ++ [.halt,.loadN 6 5,.load 1 5,.halt]))
  initPC := 0
  update := codeSize init+1
  query := codeSize init+codeSize update+2
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule22
section FlattenedModule23
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
def natural (d q : ℕ) : Cmd := .atom ⟨.natural d q,trivial⟩
def rational (d : ℕ) (q : ℚ) : Cmd := .atom ⟨.rational d q,trivial⟩
def cast (d a : ℕ) : Cmd := .atom ⟨.cast d a,trivial⟩
def add (d a b : ℕ) : Cmd := .atom ⟨.add d a b,trivial⟩
def sub (d a b : ℕ) : Cmd := .atom ⟨.sub d a b,trivial⟩
def mul (d a b : ℕ) : Cmd := .atom ⟨.mul d a b,trivial⟩
def div (d a b : ℕ) : Cmd := .atom ⟨.div d a b,trivial⟩
def logarithm (d a : ℕ) : Cmd := .atom ⟨.log d a,trivial⟩
def nadd (d a b : ℕ) : Cmd := .atom ⟨.nadd d a b,trivial⟩
def nsub (d a b : ℕ) : Cmd := .atom ⟨.nsub d a b,trivial⟩
def load (d a : ℕ) : Cmd := .atom ⟨.load d a,trivial⟩
def store (a d : ℕ) : Cmd := .atom ⟨.store a d,trivial⟩
def loadN (d a : ℕ) : Cmd := .atom ⟨.loadN d a,trivial⟩
def storeN (a d : ℕ) : Cmd := .atom ⟨.storeN a d,trivial⟩
def sequence : List Cmd → Cmd
  | [] => .skip
  | c::rest => .seq c (sequence rest)
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule23
section FlattenedModule24
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule24
section FlattenedModule25
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
def NoStore : Instruction → Prop
  | .store _ _ | .storeN _ _ => False
  | _ => True
def NoMemory : Cmd → Prop
  | .skip => True
  | .atom a => NoStore a.instruction
  | .seq a b | .branch _ a b => NoMemory a ∧ NoMemory b
  | .loop _ a => NoMemory a
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule25
section FlattenedModule26
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def writesNat : Instruction → ℕ → Prop
  | .natural d _, k | .nadd d _ _, k | .nsub d _ _, k | .loadN d _, k => d = k
  | _, _ => False
def writesReal : Instruction → ℕ → Prop
  | .rational d _, k | .cast d _, k | .add d _ _, k | .sub d _ _, k
    | .mul d _ _, k | .div d _ _, k | .log d _, k | .load d _, k => d = k
  | _, _ => False
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule26
section FlattenedModule27
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
def NatFrame : Cmd → ℕ → Prop
  | .skip,_ => True
  | .atom a,k => ¬writesNat a.instruction k
  | .seq a b,k | .branch _ a b,k => NatFrame a k ∧ NatFrame b k
  | .loop _ a,k => NatFrame a k
def RealFrame : Cmd → ℕ → Prop
  | .skip,_ => True
  | .atom a,k => ¬writesReal a.instruction k
  | .seq a b,k | .branch _ a b,k => RealFrame a k ∧ RealFrame b k
  | .loop _ a,k => RealFrame a k
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule27
section FlattenedModule28
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def bankFactor (j : ℕ) : ℕ := 2 ^ (j + 1)
def bankAddress (base j a : ℕ) : ℕ := base + bankFactor j * (2 * a + 1)
def shadowReg (j : ℕ) : ℕ := 9 + 2 * j
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule28
section FlattenedModule29
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
structure ShadowRep (base F : ℕ) (host guest : Machine) : Prop where
  pc : host.natReg 2 = guest.pc
  work : host.natReg 3 = guest.work
  halted : (host.natReg 4 == 1) = guest.halted
  fault : (host.natReg 5 == 1) = guest.fault
  realReg : ∀ j, host.realReg (shadowReg j) = guest.realReg j
  natReg : ∀ j, host.natReg (shadowReg j) = F * guest.natReg j
  realMem : ∀ a, host.realMem (base + F * (2 * a + 1)) = guest.realMem a
  natMem : ∀ a, host.natMem (base + F * (2 * a + 1)) = F * guest.natMem a
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule29
section FlattenedModule30
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def shadowScalarTranslation : Instruction → Option Instruction
  | .rational d q => some (.rational (shadowReg d) q)
  | .add d a b => some (.add (shadowReg d) (shadowReg a) (shadowReg b))
  | .sub d a b => some (.sub (shadowReg d) (shadowReg a) (shadowReg b))
  | .mul d a b => some (.mul (shadowReg d) (shadowReg a) (shadowReg b))
  | .div d a b => some (.div (shadowReg d) (shadowReg a) (shadowReg b))
  | .log d a => some (.log (shadowReg d) (shadowReg a))
  | .nadd d a b => some (.nadd (shadowReg d) (shadowReg a) (shadowReg b))
  | .nsub d a b => some (.nsub (shadowReg d) (shadowReg a) (shadowReg b))
  | _ => none
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule30
section FlattenedModule31
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule31
section FlattenedModule32
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule32
section FlattenedModule33
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
abbrev ShadowDataRep (B F : ℕ) (s : Data) (g : Machine) : Prop := ShadowRep B F s.machine g
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule33
section FlattenedModule34
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
def repeatedAdd (d factor : ℕ) : ℕ → Cmd
  | 0 => .skip
  | q+1 => .seq (nadd d d factor) (repeatedAdd d factor q)
def structuredConstant (d factor q : ℕ) : Cmd := .seq (natural d 0) (repeatedAdd d factor q)
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule34
section FlattenedModule35
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
def appendStoreReport : Cmd := Structured.sequence [storeN 10 6,nadd 10 10 14,nadd 12 12 1]
noncomputable def appendedReport (s : Data) : Data :=
  {s with
    natMem := Function.update s.natMem (s.natReg 10) (s.natReg 6)
    natReg := Function.update (Function.update s.natReg 10 (s.natReg 10+2)) 12 (s.natReg 12+1)}
def ReportLog (start : ℕ) (reports : List ℕ) (s : Data) : Prop :=
  s.natReg 10 = start+2*reports.length ∧ s.natReg 12 = reports.length ∧
    ∀ j (hj : j < reports.length), s.natMem (start+2*j) = reports[j]
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule35
section FlattenedModule36
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
def atoms : List Atom := [
  ⟨.natural 56 0,trivial⟩,⟨.rational 56 0,trivial⟩,⟨.natural 26 1,trivial⟩,⟨.natural 14 2,trivial⟩,
  ⟨.natural 34 0,trivial⟩,⟨.natural 36 1,trivial⟩,
  ⟨.nadd 66 0 56,trivial⟩,⟨.nadd 68 1 56,trivial⟩,⟨.nadd 64 2 56,trivial⟩,
  ⟨.nadd 70 3 56,trivial⟩,⟨.nadd 72 4 56,trivial⟩,⟨.add 64 0 56,trivial⟩,
  ⟨.nadd 74 68 68,trivial⟩,⟨.nadd 74 74 68,trivial⟩,⟨.nadd 74 74 66,trivial⟩,
  ⟨.nadd 74 74 14,trivial⟩,⟨.nadd 48 74 56,trivial⟩,
  ⟨.nadd 58 64 56,trivial⟩,⟨.cast 58 64,trivial⟩]
def code : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def result (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
structure Captured (i : Input) (s : Data) : Prop where
  zeroN : s.natReg 56 = 0
  zeroR : s.realReg 56 = 0
  unit : s.natReg 26 = 1
  two : s.natReg 14 = 2
  scanZero : s.natReg 34 = 0
  scanUnit : s.natReg 36 = 1
  size : s.natReg 64 = i.size
  vertices : s.natReg 66 = i.n
  edges : s.natReg 68 = i.k
  weightBound : s.natReg 70 = i.W
  source : s.natReg 72 = i.source.val
  accuracy : s.realReg 64 = i.accuracy
  base : s.natReg 74 = i.n+3*i.k+2
  utilityBase : s.natReg 48 = i.n+3*i.k+2
  factor : s.natReg 58 = i.size
  argument : s.realReg 58 = (i.size : ℝ)
end DecrAlmostLinearSSSP.Decremental.InputCapture
end FlattenedModule36
section FlattenedModule37
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
structure RawInput (i : Input) (s : Data) : Prop where
  vertices : s.natReg 0 = i.n
  edges : s.natReg 1 = i.k
  size : s.natReg 2 = i.size
  weightBound : s.natReg 3 = i.W
  source : s.natReg 4 = i.source.val
  accuracy : s.realReg 0 = i.accuracy
end DecrAlmostLinearSSSP.Decremental.InputCapture
end FlattenedModule37
section FlattenedModule38
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule38
section FlattenedModule39
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
attribute [local instance] Classical.propDecidable
def initAtoms : List Atom := [⟨.natural 5 0,trivial⟩,⟨.natural 4 1,trivial⟩,⟨.natural 1 0,trivial⟩,
  ⟨.nadd 2 0 5,trivial⟩,⟨.natural 3 0,trivial⟩,⟨.rational 1 1,trivial⟩,
  ⟨.rational 2 0,trivial⟩,⟨.rational 5 0,trivial⟩]
def buildAtoms : List Atom := [⟨.store 1 1,trivial⟩,⟨.storeN 1 2,trivial⟩,
  ⟨.nadd 1 1 4,trivial⟩,⟨.nadd 2 2 2,trivial⟩,⟨.add 1 1 1,trivial⟩]
def greedyPrefixAtoms : List Atom := [⟨.nsub 1 1 4,trivial⟩,⟨.load 3 1,trivial⟩,
  ⟨.loadN 6 1,trivial⟩,⟨.add 4 2 3,trivial⟩]
def chooseAtoms : List Atom := [⟨.add 2 4 5,trivial⟩,⟨.nadd 3 3 6,trivial⟩]
def buildTest : Test := .realLess 1 0
def greedyTest : Test := .natLess 5 1
def chooseTest : Test := .realLess 4 0
def buildBody : Cmd := sequence (buildAtoms.map Cmd.atom)
def buildLoop : Cmd := .loop buildTest buildBody
def chooseBody : Cmd := sequence (chooseAtoms.map Cmd.atom)
def greedyBody : Cmd := .seq (sequence (greedyPrefixAtoms.map Cmd.atom)) (.branch chooseTest chooseBody .skip)
def greedyLoop : Cmd := .loop greedyTest greedyBody
def calculation : Cmd := sequence [buildLoop,greedyLoop,nadd 3 3 0]
def routine : Cmd := .seq (sequence (initAtoms.map Cmd.atom)) (.branch (.realLess 5 0) calculation (natural 3 0))
noncomputable def runAtoms (atoms : List Atom) (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
noncomputable def initial (s : Data) : Data := runAtoms initAtoms s
noncomputable def buildStep (s : Data) : Data := runAtoms buildAtoms s
noncomputable def greedyPrefix (s : Data) : Data := runAtoms greedyPrefixAtoms s
noncomputable def chooseStep (s : Data) : Data := runAtoms chooseAtoms s
noncomputable def greedyStep (s : Data) : Data :=
  let t := greedyPrefix s
  if chooseTest.holds t then chooseStep t else t
structure Constants (P : ℕ) (x : ℝ) (s : Data) : Prop where
  factor : s.natReg 0 = P
  input : s.realReg 0 = x
  one : s.natReg 4 = 1
  zeroN : s.natReg 5 = 0
  zeroR : s.realReg 5 = 0
def StackCorrect (P depth : ℕ) (s : Data) : Prop :=
  ∀ j < depth,s.realMem j = (2 : ℝ)^j ∧ s.natMem j = P*2^j
structure BuildInvariant (P : ℕ) (x : ℝ) (N : ℕ) (s : Data) : Prop extends Constants P x s where
  depth : s.natReg 1 ≤ N
  power : s.realReg 1 = (2 : ℝ)^(s.natReg 1)
  product : s.natReg 2 = P*2^(s.natReg 1)
  lower : s.realReg 2 = 0
  sum : s.natReg 3 = 0
  stack : StackCorrect P (s.natReg 1) s
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule39
section FlattenedModule40
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule40
section FlattenedModule41
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
structure GreedyInvariant (P : ℕ) (x : ℝ) (s : Data) : Prop extends Constants P x s where
  stack : StackCorrect P (s.natReg 1) s
  lower : ∃ q : ℕ,s.realReg 2 = q ∧ s.natReg 3 = P*q ∧
    (q : ℝ) < x ∧ x ≤ (q : ℝ)+(2 : ℝ)^(s.natReg 1)
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule41
section FlattenedModule42
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule42
section FlattenedModule43
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def constantProductCode (d factor q : ℕ) : List Instruction :=
  .natural d 0 :: List.replicate q (.nadd d d factor)
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule43
section FlattenedModule44
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def naturalConstant : Instruction → ℕ
  | .natural _ q => q
  | _ => 0
def shadowWidth (code : List Instruction) : ℕ := 8 + (code.map naturalConstant).sum
def shadowBlock (width offset returnPC pc : ℕ) (ins : Instruction) : List Instruction :=
  let next := offset + width * (pc + 1)
  let header := [Instruction.natural 2 (pc + 1), .nadd 3 3 1]
  let padding := fun used => List.replicate (width - used) (Instruction.jump next)
  let simple := fun tr => header ++ [tr, .jump next] ++ padding 4
  let mem := fun tr a => header ++ [.nadd 6 (shadowReg a) (shadowReg a), .nadd 6 6 0,
    .nadd 6 6 7, tr, .jump next] ++ padding 7
  match ins with
  | .rational d q => simple (.rational (shadowReg d) q)
  | .natural d q => header ++ constantProductCode (shadowReg d) 7 q ++ [.jump next] ++ padding (q + 4)
  | .cast d a => header ++ [.cast (shadowReg d) (shadowReg a), .div (shadowReg d) (shadowReg d) 7,
    .jump next] ++ padding 5
  | .add d a b => simple (.add (shadowReg d) (shadowReg a) (shadowReg b))
  | .sub d a b => simple (.sub (shadowReg d) (shadowReg a) (shadowReg b))
  | .mul d a b => simple (.mul (shadowReg d) (shadowReg a) (shadowReg b))
  | .div d a b => simple (.div (shadowReg d) (shadowReg a) (shadowReg b))
  | .log d a => simple (.log (shadowReg d) (shadowReg a))
  | .nadd d a b => simple (.nadd (shadowReg d) (shadowReg a) (shadowReg b))
  | .nsub d a b => simple (.nsub (shadowReg d) (shadowReg a) (shadowReg b))
  | .load d a => mem (.load (shadowReg d) 6) a
  | .store a d => mem (.store 6 (shadowReg d)) a
  | .loadN d a => mem (.loadN (shadowReg d) 6) a
  | .storeN a d => mem (.storeN 6 (shadowReg d)) a
  | .jump t => header ++ [.natural 2 t, .jump (offset + width * t)] ++ padding 4
  | .less a b t => header ++ [.less (shadowReg a) (shadowReg b) (offset + width * pc + 5),
    .jump next, .jump next, .natural 2 t, .jump (offset + width * t)] ++ padding 7
  | .lessN a b t => header ++ [.lessN (shadowReg a) (shadowReg b) (offset + width * pc + 5),
    .jump next, .jump next, .natural 2 t, .jump (offset + width * t)] ++ padding 7
  | .halt => header ++ [.natural 4 1, .jump returnPC] ++ padding 4
def shadowCodeAux (width offset returnPC : ℕ) : ℕ → List Instruction → List Instruction
  | _, [] => []
  | pc, ins :: rest => shadowBlock width offset returnPC pc ins ++ shadowCodeAux width offset returnPC (pc + 1) rest
def shadowCode (offset returnPC : ℕ) (code : List Instruction) : List Instruction :=
  shadowCodeAux (shadowWidth code) offset returnPC 0 code
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule44
section FlattenedModule45
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule45
section FlattenedModule46
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def ReservedSafe (ins : Instruction) : Prop :=
  ¬ writesNat ins 0 ∧ ¬ writesNat ins 1 ∧ ¬ writesNat ins 7 ∧ ¬ writesReal ins 7
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule46
section FlattenedModule47
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule47
section FlattenedModule48
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule48
section FlattenedModule49
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule49
section FlattenedModule50
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule50
section FlattenedModule51
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule51
section FlattenedModule52
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def shadowMemoryTranslation : Instruction → Option (Instruction × ℕ)
  | .load d a => some (.load (shadowReg d) 6, a)
  | .loadN d a => some (.loadN (shadowReg d) 6, a)
  | .store a d => some (.store 6 (shadowReg d), a)
  | .storeN a d => some (.storeN 6 (shadowReg d), a)
  | _ => none
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule52
section FlattenedModule53
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule53
section FlattenedModule54
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule54
section FlattenedModule55
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
noncomputable def shadowSteps (ins : Instruction) (g : Machine) : ℕ :=
  match ins with
  | .natural _ q => q + 4
  | .cast _ _ => 5
  | .load _ _ | .loadN _ _ | .store _ _ | .storeN _ _ => 7
  | .less a b _ => if g.realReg a < g.realReg b then 5 else 4
  | .lessN a b _ => if g.natReg a < g.natReg b then 5 else 4
  | _ => 4
def IsBranch : Instruction → Prop
  | .less _ _ _ | .lessN _ _ _ => True
  | _ => False
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule55
section FlattenedModule56
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def shadowDestination (width offset returnPC : ℕ) (g : Machine) : ℕ :=
  if g.halted then returnPC else offset + width * g.pc
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule56
section FlattenedModule57
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def ShadowEmbedsCode (host guest : Program) (width offset returnPC : ℕ) : Prop :=
  ∀ pc ins, guest.code[pc]? = some ins → ∀ slot < width,
    host.code[offset + width * pc + slot]? = (shadowBlock width offset returnPC pc ins)[slot]?
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule57
section FlattenedModule58
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule58
section FlattenedModule59
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule59
section FlattenedModule60
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule60
section FlattenedModule61
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule61
section FlattenedModule62
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def WritesAddress (ins : Instruction) (c : Machine) (address : ℕ) : Prop :=
  match ins with
  | .store a _ | .storeN a _ => c.natReg a = address
  | _ => False
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule62
section FlattenedModule63
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def OutsideBank (base F address : ℕ) : Prop := ∀ a, address ≠ base + F*(2*a+1)
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule63
section FlattenedModule64
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def PreservesOutside (base F : ℕ) (c d : Machine) : Prop := ∀ address, OutsideBank base F address →
    d.realMem address = c.realMem address ∧ d.natMem address = c.natMem address
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule64
section FlattenedModule65
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
def ceilingProgram : Program := program routine .skip
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule65
section FlattenedModule66
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
def shadowAction : Instruction → Cmd
  | .rational d q => rational (shadowReg d) q
  | .natural d q => structuredConstant (shadowReg d) 7 q
  | .cast d a => .seq (cast (shadowReg d) (shadowReg a)) (Structured.div (shadowReg d) (shadowReg d) 7)
  | .add d a b => add (shadowReg d) (shadowReg a) (shadowReg b)
  | .sub d a b => sub (shadowReg d) (shadowReg a) (shadowReg b)
  | .mul d a b => mul (shadowReg d) (shadowReg a) (shadowReg b)
  | .div d a b => Structured.div (shadowReg d) (shadowReg a) (shadowReg b)
  | .log d a => logarithm (shadowReg d) (shadowReg a)
  | .nadd d a b => nadd (shadowReg d) (shadowReg a) (shadowReg b)
  | .nsub d a b => nsub (shadowReg d) (shadowReg a) (shadowReg b)
  | .load d a => .seq (Structured.sequence [nadd 6 (shadowReg a) (shadowReg a),nadd 6 6 0,nadd 6 6 7]) (load (shadowReg d) 6)
  | .loadN d a => .seq (Structured.sequence [nadd 6 (shadowReg a) (shadowReg a),nadd 6 6 0,nadd 6 6 7]) (loadN (shadowReg d) 6)
  | .store a d => .seq (Structured.sequence [nadd 6 (shadowReg a) (shadowReg a),nadd 6 6 0,nadd 6 6 7]) (store 6 (shadowReg d))
  | .storeN a d => .seq (Structured.sequence [nadd 6 (shadowReg a) (shadowReg a),nadd 6 6 0,nadd 6 6 7]) (storeN 6 (shadowReg d))
  | .jump pc => natural 2 pc
  | .less a b pc => .branch (.realLess (shadowReg a) (shadowReg b)) (natural 2 pc) .skip
  | .lessN a b pc => .branch (.natLess (shadowReg a) (shadowReg b)) (natural 2 pc) .skip
  | .halt => natural 4 1
def actionBound : Instruction → ℕ
  | .natural _ q => q+4
  | _ => 4
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule66
section FlattenedModule67
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule67
section FlattenedModule68
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
def FlagFrame : Cmd → ℕ → Prop
  | .skip,_ => True
  | .atom a,k => ¬writesNat a.instruction k ∨ ∃ q ≤ 1, a.instruction = .natural k q
  | .seq a b,k | .branch _ a b,k => FlagFrame a k ∧ FlagFrame b k
  | .loop _ a,k => FlagFrame a k
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule68
section FlattenedModule69
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule69
section FlattenedModule70
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
def shadowInstruction (pc : ℕ) (ins : Instruction) : Cmd :=
  .seq (.seq (natural 2 (pc+1)) (nadd 3 3 1)) (shadowAction ins)
def dispatchAux : ℕ → List Instruction → Cmd
  | _,[] => .seq (natural 5 1) (natural 4 1)
  | pc,ins::rest => .seq (natural 8 (pc+1))
      (.branch (.natLess 2 8) (shadowInstruction pc ins) (dispatchAux (pc+1) rest))
def dispatchCharge (code : List Instruction) : ℕ := (code.map (fun ins => actionBound ins+5)).sum
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule70
section FlattenedModule71
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule71
section FlattenedModule72
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule72
section FlattenedModule73
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
def shadowInterpreter (code : List Instruction) : Cmd := .loop (.natLess 4 1) (dispatchAux 0 code)
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule73
section FlattenedModule74
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule74
section FlattenedModule75
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
def observedAction (ins : Instruction) : Cmd :=
  match ins with
  | .store _ _ | .storeN _ _ => .seq (shadowAction ins) appendStoreReport
  | _ => shadowAction ins
def sourceWrite (ins : Instruction) (g : Machine) : List ℕ :=
  match ins with
  | .store a _ | .storeN a _ => [g.natReg a]
  | _ => []
def physicalWrites (B bank : ℕ) (ins : Instruction) (g : Machine) : List ℕ :=
  (sourceWrite ins g).map (fun a => B+bankFactor bank*(2*a+1))
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule75
section FlattenedModule76
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule76
section FlattenedModule77
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
noncomputable def unscaledGuest (base : ℕ) (s : Data) : Machine where
  pc := s.natReg 2
  work := s.natReg 3
  realReg := fun j => s.realReg (shadowReg j)
  natReg := fun j => s.natReg (shadowReg j)
  realMem := fun a => s.realMem (base+2*a+1)
  natMem := fun a => s.natMem (base+2*a+1)
  halted := s.natReg 4 == 1
  fault := s.natReg 5 == 1
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule77
section FlattenedModule78
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
def setupAtoms : List Atom := [
  ⟨.nadd 0 48 56,trivial⟩,⟨.natural 1 1,trivial⟩,⟨.natural 2 0,trivial⟩,
  ⟨.natural 3 0,trivial⟩,⟨.natural 4 0,trivial⟩,⟨.natural 5 0,trivial⟩,
  ⟨.natural 7 1,trivial⟩,⟨.rational 7 1,trivial⟩,
  ⟨.nadd (shadowReg 0) 58 56,trivial⟩,⟨.add (shadowReg 0) 58 56,trivial⟩]
def setup : Cmd := Structured.sequence (setupAtoms.map Cmd.atom)
noncomputable def setupData (s : Data) : Data := setupAtoms.foldl (fun t a => a.effect t) s
def call : Cmd := .seq setup (shadowInterpreter ceilingProgram.code)
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule78
section FlattenedModule79
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
def cube : Cmd := .seq call (.seq (nadd 58 (shadowReg 3) 56) call)
def polynomialReserve (B : ℕ) : Cmd :=
  .seq cube (.seq (structuredConstant 60 (shadowReg 3) B) (nadd 60 60 26))
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule79
section FlattenedModule80
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule80
section FlattenedModule81
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule81
section FlattenedModule82
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule82
section FlattenedModule83
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule83
section FlattenedModule84
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule84
section FlattenedModule85
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule85
section FlattenedModule86
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
def scaleArgumentAtoms : List Atom := [
  ⟨.cast 80 66,trivial⟩,⟨.cast 82 70,trivial⟩,⟨.mul 58 80 82,trivial⟩,⟨.log 58 58,trivial⟩,
  ⟨.rational 84 2,trivial⟩,⟨.log 84 84,trivial⟩,⟨.div 58 58 84,trivial⟩,⟨.natural 58 1,trivial⟩]
def scaleArgument : Cmd := Structured.sequence (scaleArgumentAtoms.map Cmd.atom)
noncomputable def scaleArgumentData (s : Data) : Data := scaleArgumentAtoms.foldl (fun t a => a.effect t) s
def countScales : Cmd := .seq scaleArgument (.seq call (nadd 80 (shadowReg 3) 26))
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule86
section FlattenedModule87
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
def scaleArea : Cmd := .seq (nadd 58 66 56) (.seq (cast 58 80) (.seq call (nadd 82 (shadowReg 3) 56)))
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule87
section FlattenedModule88
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Layout
open Structured
structure Addresses where
  pointers : ℕ
  dirtyFlags : ℕ
  dirtyList : ℕ
  records : ℕ
  caches : ℕ
  reports : ℕ
  utility : ℕ
def addresses (B n S reserve stride : ℕ) : Addresses where
  pointers := B+1
  dirtyFlags := B+2*n+1
  dirtyList := B+4*n+1
  records := B+6*n+1
  caches := B+6*n+1+stride*S
  reports := B+6*n+1+stride*S+2*(n*S)
  utility := B+6*n+1+stride*S+2*(n*S)+2*reserve+1
def preAtoms : List Atom := [
  ⟨.nadd 84 66 66,trivial⟩,⟨.nadd 86 84 84,trivial⟩,⟨.nadd 84 84 86,trivial⟩,
  ⟨.nadd 84 84 74,trivial⟩,⟨.nadd 84 84 26,trivial⟩]
def postAtoms : List Atom := [
  ⟨.nadd 88 84 86,trivial⟩,⟨.nadd 90 82 82,trivial⟩,⟨.nadd 92 88 90,trivial⟩,
  ⟨.nadd 94 60 60,trivial⟩,⟨.nadd 48 92 94,trivial⟩,⟨.nadd 48 48 26,trivial⟩,
  ⟨.nadd 96 74 26,trivial⟩,⟨.nadd 100 66 66,trivial⟩,
  ⟨.nadd 98 96 100,trivial⟩,⟨.nadd 102 98 100,trivial⟩]
noncomputable def preData (s : Data) : Data := preAtoms.foldl (fun t a => a.effect t) s
noncomputable def postData (s : Data) : Data := postAtoms.foldl (fun t a => a.effect t) s
def code (stride : ℕ) : Cmd := .seq (Structured.sequence (preAtoms.map Cmd.atom))
  (.seq (structuredConstant 86 80 stride) (Structured.sequence (postAtoms.map Cmd.atom)))
def Represents (s : Data) (a : Addresses) : Prop :=
  s.natReg 96 = a.pointers ∧ s.natReg 98 = a.dirtyFlags ∧ s.natReg 102 = a.dirtyList ∧
    s.natReg 84 = a.records ∧ s.natReg 88 = a.caches ∧ s.natReg 92 = a.reports ∧ s.natReg 48 = a.utility
def postAddresses (s : Data) : Addresses where
  pointers := s.natReg 74+s.natReg 26
  dirtyFlags := s.natReg 74+s.natReg 26+(s.natReg 66+s.natReg 66)
  dirtyList := s.natReg 74+s.natReg 26+(s.natReg 66+s.natReg 66)+(s.natReg 66+s.natReg 66)
  records := s.natReg 84
  caches := s.natReg 84+s.natReg 86
  reports := (s.natReg 84+s.natReg 86)+(s.natReg 82+s.natReg 82)
  utility := (s.natReg 84+s.natReg 86)+(s.natReg 82+s.natReg 82)+(s.natReg 60+s.natReg 60)+s.natReg 26
end DecrAlmostLinearSSSP.Decremental.Layout
end FlattenedModule88
section FlattenedModule89
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace ScaledCeiling
end ScaledCeiling
namespace Layout
end Layout
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule89
section FlattenedModule90
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def barrierHigh (i : Input) : ℕ := ⌈512*(i.n : ℝ)/i.accuracy⌉₊
noncomputable def barrierWeight (i : Input) (j : ℕ) (e : Fin i.k) : ℕ :=
  if (i.weight e : ℝ) ≤ 2*scale j then ⌈(i.weight e : ℝ)/delta i j⌉₊ else barrierHigh i
noncomputable def barrierInput (i : Input) (j : ℕ) : Input :=
  {i with weight := barrierWeight i j,W := barrierHigh i,accuracy := i.accuracy/16,size := 64*i.size}
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule90
section FlattenedModule91
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def utilityDepth (m : ℕ) : ℕ := 10+2*⌈logarithm2 (max 2 m : ℕ)⌉₊
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule91
section FlattenedModule92
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Prepass
open Structured
open ScaledCeiling
def code (coefficient stride : ℕ) : Cmd := .seq (polynomialReserve coefficient)
  (.seq countScales (.seq scaleArea (Layout.code stride)))
end DecrAlmostLinearSSSP.Decremental.Prepass
end FlattenedModule92
section FlattenedModule93
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Fill
open Structured
def body : Cmd := Structured.sequence [storeN 116 124,store 116 116,nadd 116 116 120,nsub 118 118 26]
def code : Cmd := .loop (.natLess 122 118) body
noncomputable def next (s : Data) : Data :=
  {s with
    natReg := Function.update (Function.update s.natReg 116 (s.natReg 116+s.natReg 120)) 118 (s.natReg 118-s.natReg 26)
    natMem := Function.update s.natMem (s.natReg 116) (s.natReg 124)
    realMem := Function.update s.realMem (s.natReg 116) (s.realReg 116)}
end DecrAlmostLinearSSSP.Decremental.Fill
end FlattenedModule93
section FlattenedModule94
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SnapshotFill
open Structured
def setupAtoms (N : ℕ) : List Atom := [⟨.nadd 116 50 56,trivial⟩,⟨.natural 118 N,trivial⟩,
  ⟨.nadd 120 14 56,trivial⟩,⟨.nadd 122 56 56,trivial⟩,⟨.nadd 124 56 56,trivial⟩,
  ⟨.rational 116 0,trivial⟩]
def setup (N : ℕ) : Cmd := Structured.sequence ((setupAtoms N).map Cmd.atom)
noncomputable def setupData (N : ℕ) (s : Data) : Data := (setupAtoms N).foldl (fun t a => a.effect t) s
def code (N : ℕ) : Cmd := .seq (setup N) Fill.code
end DecrAlmostLinearSSSP.Decremental.SnapshotFill
end FlattenedModule94
section FlattenedModule95
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
def productReal (d p x : ℕ) : Cmd :=
  .seq (nadd 58 p 56) (.seq (add 58 x 56) (.seq call (nadd d (shadowReg 3) 56)))
def productNat (d p x : ℕ) : Cmd := .seq (cast 200 x) (productReal d p 200)
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule95
section FlattenedModule96
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
def batch (ops : List (ℕ × ℕ)) : Cmd := Structured.sequence (ops.map fun op => productNat op.1 112 op.2)
def BatchValid (ops : List (ℕ × ℕ)) : Prop :=
  (ops.map Prod.fst).Nodup ∧
  (∀ op ∈ ops, 10 ≤ op.1 ∧ Even op.1 ∧ op.1 ≠ 58 ∧ op.1 ≠ 48 ∧ op.1 ≠ 56 ∧ op.1 ≠ 112) ∧
  (∀ op ∈ ops, 10 ≤ op.2 ∧ Even op.2 ∧ op.2 ≠ 58 ∧ ∀ other ∈ ops, op.2 ≠ other.1)
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule96
section FlattenedModule97
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
def ordinaryOps : List (ℕ × ℕ) := [(154,66),(156,68),(158,204),(160,72)]
def ordinary : Cmd := .seq (structuredConstant 204 64 64) (ScaledCeiling.batch ordinaryOps)
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end FlattenedModule97
section FlattenedModule98
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
def highAtoms : List Atom := [⟨.rational 202 512,trivial⟩,⟨.cast 204 66,trivial⟩,
  ⟨.mul 202 202 204,trivial⟩,⟨.div 202 202 64,trivial⟩]
def highCode : Cmd := Structured.sequence (highAtoms.map Cmd.atom)
noncomputable def highData (s : Data) : Data := highAtoms.foldl (fun t a => a.effect t) s
def high : Cmd := .seq highCode (ScaledCeiling.productReal 152 112 202)
def prepare : Cmd := .seq ordinary high
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end FlattenedModule98
section FlattenedModule99
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
def fieldAtoms : List Atom := [
  ⟨.nadd 206 50 56,trivial⟩,⟨.storeN 206 154,trivial⟩,
  ⟨.nadd 206 206 14,trivial⟩,⟨.storeN 206 156,trivial⟩,
  ⟨.nadd 206 206 14,trivial⟩,⟨.storeN 206 158,trivial⟩,
  ⟨.nadd 206 206 14,trivial⟩,⟨.storeN 206 152,trivial⟩,
  ⟨.nadd 206 206 14,trivial⟩,⟨.storeN 206 160,trivial⟩,
  ⟨.rational 208 16,trivial⟩,⟨.div 208 64 208,trivial⟩,⟨.store 50 208,trivial⟩]
def writeFields : Cmd := Structured.sequence (fieldAtoms.map Cmd.atom)
noncomputable def fieldData (s : Data) : Data := fieldAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end FlattenedModule99
section FlattenedModule100
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end FlattenedModule100
section FlattenedModule101
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
def initializeSnapshot (N : ℕ) : Cmd := .seq (SnapshotFill.code N) (.seq prepare writeFields)
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end FlattenedModule101
section FlattenedModule102
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def instructionRegisters : Instruction → List ℕ
  | .rational d _ | .natural d _ => [d]
  | .cast d a | .log d a | .load d a | .loadN d a => [d,a]
  | .add d a b | .sub d a b | .mul d a b | .div d a b | .nadd d a b | .nsub d a b => [d,a,b]
  | .store a d | .storeN a d => [a,d]
  | .less a b _ | .lessN a b _ => [a,b]
  | .jump _ | .halt => []
def registerBound (code : List Instruction) : ℕ := 8+(code.flatMap instructionRegisters).sum
def ZeroRegisterTail (bound : ℕ) (c : Machine) : Prop :=
  ∀ j, bound ≤ j → c.natReg j = 0 ∧ c.realReg j = 0
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule102
section FlattenedModule103
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule103
section FlattenedModule104
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
def registersBelow (code : List Instruction) (bound : ℕ) : Bool :=
  code.all (fun ins => (instructionRegisters ins).all (fun j => decide (j < bound)))
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule104
section FlattenedModule105
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end FlattenedModule105
section FlattenedModule106
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
def naturalField : Cmd := .seq (loadN 172 162)
  (.seq (ScaledCeiling.productNat 174 112 172)
    (Structured.sequence [storeN 164 174,nadd 162 162 26,nadd 164 164 170]))
noncomputable def finishNatural (s : Data) : Data :=
  {s with
    natMem := Function.update s.natMem (s.natReg 164) (s.natReg 174)
    natReg := Function.update (Function.update s.natReg 162 (s.natReg 162+s.natReg 26))
      164 (s.natReg 164+s.natReg 170)}
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end FlattenedModule106
section FlattenedModule107
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
def chooseWeight : Cmd := .branch (.realLess 148 202) (nadd 174 152 56)
  (.seq (Structured.div 202 202 70) (ScaledCeiling.productReal 174 112 202))
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end FlattenedModule107
section FlattenedModule108
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
def weightField : Cmd := .seq (loadN 172 162) (.seq (cast 202 172)
  (.seq chooseWeight (Structured.sequence [storeN 164 174,nadd 162 162 26,nadd 164 164 170])))
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end FlattenedModule108
section FlattenedModule109
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceMemory
open Structured
structure Image (B bank : ℕ) (s : Data) (natural : ℕ → ℕ) (real : ℕ → ℝ) : Prop where
  natMem : ∀ a, s.natMem (bankAddress B bank a) = bankFactor bank*natural a
  realMem : ∀ a, s.realMem (bankAddress B bank a) = real a
end DecrAlmostLinearSSSP.Decremental.SourceMemory
end FlattenedModule109
section FlattenedModule110
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end FlattenedModule110
section FlattenedModule111
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
def frozenNat : List ℕ := [26,48,56,112,152,170]
def frozenReal : List ℕ := [56,70,148]
def Stable (cmd : Cmd) : Prop :=
  (∀ k ∈ frozenNat, NatFrame cmd k) ∧ (∀ k ∈ frozenReal, RealFrame cmd k)
def Env (B bank tail high : ℕ) (delta cutoff : ℝ) (s : Data) : Prop :=
  s.natReg 48 = B+2*tail ∧ s.natReg 112 = bankFactor bank ∧
  s.natReg 152 = bankFactor bank*high ∧ s.natReg 170 = 2*bankFactor bank ∧
  s.natReg 26 = 1 ∧ s.natReg 56 = 0 ∧ s.realReg 56 = 0 ∧
  s.realReg 70 = delta ∧ s.realReg 148 = cutoff
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end FlattenedModule111
section FlattenedModule112
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
noncomputable def roundedWeight (delta cutoff : ℝ) (high raw : ℕ) : ℕ :=
  if cutoff < (raw : ℝ) then high else ⌈(raw : ℝ)/delta⌉₊
def edge : Cmd := .seq naturalField (.seq naturalField (.seq weightField (nsub 166 166 26)))
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end FlattenedModule112
section FlattenedModule113
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
def code : Cmd := .loop (.natLess 56 166) edge
noncomputable def edgeImage (raw : ℕ → ℕ) (delta cutoff : ℝ) (high : ℕ)
    (natural : ℕ → ℕ) (origin logical : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update natural logical (raw origin))
    (logical+1) (raw (origin+1))) (logical+2) (roundedWeight delta cutoff high (raw (origin+2)))
noncomputable def tapeImage (raw : ℕ → ℕ) (delta cutoff : ℝ) (high : ℕ) :
    ℕ → (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)
  | 0,natural,_,_ => natural
  | count+1,natural,origin,logical =>
    tapeImage raw delta cutoff high count (edgeImage raw delta cutoff high natural origin logical) (origin+3) (logical+3)
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end FlattenedModule113
section FlattenedModule114
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.RecordHeader
open Structured
def atoms : List Atom := [
  ⟨.nadd 216 106 56,trivial⟩,⟨.storeN 216 108,trivial⟩,
  ⟨.add 148 146 146,trivial⟩,⟨.store 216 148,trivial⟩,
  ⟨.nadd 216 216 14,trivial⟩,⟨.nadd 212 106 134,trivial⟩,⟨.storeN 216 212,trivial⟩,
  ⟨.rational 210 128,trivial⟩,⟨.cast 212 66,trivial⟩,⟨.mul 210 210 212,trivial⟩,
  ⟨.mul 70 64 146,trivial⟩,⟨.div 70 70 210,trivial⟩,⟨.store 216 70,trivial⟩,
  ⟨.nadd 216 216 14,trivial⟩,⟨.storeN 216 112,trivial⟩,
  ⟨.nadd 216 216 14,trivial⟩,⟨.storeN 216 56,trivial⟩,
  ⟨.natural 52 8,trivial⟩,⟨.nadd 50 106 52,trivial⟩]
def code : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def result (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.RecordHeader
end FlattenedModule114
section FlattenedModule115
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
def TailFrame (cmd : Cmd) : Prop := ∀ j, 8 ≤ j → NatFrame cmd (shadowReg j) ∧ RealFrame cmd (shadowReg j)
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule115
section FlattenedModule116
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
def EvenRegisterWrites : Instruction → Prop
  | .rational d _ | .cast d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .div d _ _ |
    .log d _ | .natural d _ | .nadd d _ _ | .nsub d _ _ | .load d _ | .loadN d _ => Even d
  | _ => True
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule116
section FlattenedModule117
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace ScaledCeiling
end ScaledCeiling
namespace Layout
end Layout
namespace Prepass
end Prepass
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule117
section FlattenedModule118
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Layout
open Structured
end DecrAlmostLinearSSSP.Decremental.Layout
end FlattenedModule118
section FlattenedModule119
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
def startAtoms : List Atom := [⟨.nadd 162 66 56,trivial⟩,⟨.nadd 164 154 154,trivial⟩,
  ⟨.nadd 164 164 74,trivial⟩,⟨.nadd 164 164 112,trivial⟩,
  ⟨.nadd 170 112 112,trivial⟩,⟨.nadd 166 68 56,trivial⟩]
def start : Cmd := Structured.sequence (startAtoms.map Cmd.atom)
noncomputable def startData (s : Data) : Data := startAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end FlattenedModule119
section FlattenedModule120
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
def saveOne (j : ℕ) : Cmd := Structured.sequence
  [natural 52 (2*j),nadd 54 50 52,storeN 54 (shadowReg j),store 54 (shadowReg j)]
def restoreOne (j : ℕ) : Cmd := Structured.sequence
  [natural 52 (2*j),nadd 54 50 52,loadN (shadowReg j) 54,load (shadowReg j) 54]
noncomputable def savedOne (s : Data) (j : ℕ) : Data :=
  {s with
    natReg := Function.update (Function.update s.natReg 52 (2*j)) 54 (s.natReg 50+2*j)
    natMem := Function.update s.natMem (s.natReg 50+2*j) (s.natReg (shadowReg j))
    realMem := Function.update s.realMem (s.natReg 50+2*j) (s.realReg (shadowReg j))}
noncomputable def restoredOne (s : Data) (j : ℕ) : Data :=
  {s with
    natReg := Function.update (Function.update (Function.update s.natReg 52 (2*j)) 54 (s.natReg 50+2*j))
      (shadowReg j) (s.natMem (s.natReg 50+2*j))
    realReg := Function.update s.realReg (shadowReg j) (s.realMem (s.natReg 50+2*j))}
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end FlattenedModule120
section FlattenedModule121
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
def saveRegisters : List ℕ → Cmd
  | [] => .skip
  | j::rest => .seq (saveOne j) (saveRegisters rest)
def restoreRegisters : List ℕ → Cmd
  | [] => .skip
  | j::rest => .seq (restoreOne j) (restoreRegisters rest)
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end FlattenedModule121
section FlattenedModule122
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end FlattenedModule122
section FlattenedModule123
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceSetup
open Structured
open RegisterSave
def headerAtoms (entry : ℕ) : List Atom := [
  ⟨.nadd 0 74 56,trivial⟩,⟨.natural 1 1,trivial⟩,⟨.natural 2 entry,trivial⟩,
  ⟨.natural 4 0,trivial⟩,⟨.natural 5 0,trivial⟩,
  ⟨.nadd 7 112 56,trivial⟩,⟨.cast 7 112,trivial⟩,
  ⟨.natural 52 6,trivial⟩,⟨.nadd 54 106 52,trivial⟩,⟨.loadN 3 54,trivial⟩]
def header (entry : ℕ) : Cmd := Structured.sequence ((headerAtoms entry).map Cmd.atom)
noncomputable def headerData (entry : ℕ) (s : Data) : Data := (headerAtoms entry).foldl (fun t a => a.effect t) s
def code (N entry : ℕ) : Cmd := .seq (header entry) (restoreRegisters (List.range N))
end DecrAlmostLinearSSSP.Decremental.SourceSetup
end FlattenedModule123
section FlattenedModule124
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
def observedInstruction (pc : ℕ) (ins : Instruction) : Cmd :=
  .seq (.seq (natural 2 (pc+1)) (nadd 3 3 1)) (observedAction ins)
def observedDispatchAux : ℕ → List Instruction → Cmd
  | _,[] => .seq (natural 5 1) (natural 4 1)
  | pc,ins::rest => .seq (natural 8 (pc+1))
      (.branch (.natLess 2 8) (observedInstruction pc ins) (observedDispatchAux (pc+1) rest))
def observedDispatchCharge (code : List Instruction) : ℕ := (code.map (fun ins => actionBound ins+8)).sum
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule124
section FlattenedModule125
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule125
section FlattenedModule126
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace RegisterSave
end RegisterSave
namespace SourceSetup
end SourceSetup
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule126
section FlattenedModule127
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceSnapshot
open Structured
open RegisterSave
def workAtoms : List Atom := [⟨.natural 52 6,trivial⟩,⟨.nadd 54 106 52,trivial⟩,⟨.storeN 54 3,trivial⟩]
def workCode : Cmd := Structured.sequence (workAtoms.map Cmd.atom)
noncomputable def workData (s : Data) : Data := workAtoms.foldl (fun t a => a.effect t) s
def code (N : ℕ) : Cmd := .seq (saveRegisters (List.range N)) workCode
end DecrAlmostLinearSSSP.Decremental.SourceSnapshot
end FlattenedModule127
section FlattenedModule128
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.SourceCall
open Structured
def code (N entry : ℕ) (p : Program) : Cmd := .seq (SourceSetup.code N entry)
  (.seq (shadowInterpreter p.code) (SourceSnapshot.code N))
end DecrAlmostLinearSSSP.Decremental.SourceCall
end FlattenedModule128
section FlattenedModule129
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.ExtendedMax
open Structured
attribute [local instance] Classical.propDecidable
noncomputable def cell (s : Data) (address : ℕ) : ℝ≥0∞ :=
  if s.natMem address = 1 then ⊤ else ENNReal.ofReal (s.realMem address)
noncomputable def incoming (s : Data) : ℝ≥0∞ :=
  if s.natReg 22 = 1 then ⊤ else ENNReal.ofReal (s.realReg 20)
def code : Cmd := .seq (loadN 24 20)
  (.branch (.natLess 24 26)
    (.branch (.natLess 22 26)
      (.seq (load 22 20) (.branch (.realLess 22 20) (store 20 20) .skip))
      (storeN 20 22))
    .skip)
end DecrAlmostLinearSSSP.Decremental.ExtendedMax
end FlattenedModule129
section FlattenedModule130
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.ScaledReadout
open Structured
def code : Cmd := .seq (Structured.sequence [loadN 130 128,load 20 128,mul 20 20 70])
  (.branch (.natLess 130 132) (natural 22 0) (natural 22 1))
end DecrAlmostLinearSSSP.Decremental.ScaledReadout
end FlattenedModule130
section FlattenedModule131
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CacheCopy
open Structured
def suffix : Cmd := Structured.sequence [storeN 20 22,store 20 20,nadd 20 20 14,
  nadd 128 128 170,nsub 176 176 26]
def body : Cmd := .seq ScaledReadout.code suffix
def code : Cmd := .loop (.natLess 56 176) body
noncomputable def suffixData (s : Data) : Data :=
  {s with
    natMem := Function.update s.natMem (s.natReg 20) (s.natReg 22)
    realMem := Function.update s.realMem (s.natReg 20) (s.realReg 20)
    natReg := Function.update (Function.update (Function.update s.natReg 20
      (s.natReg 20+s.natReg 14)) 128 (s.natReg 128+s.natReg 170)) 176 (s.natReg 176-s.natReg 26)}
end DecrAlmostLinearSSSP.Decremental.CacheCopy
end FlattenedModule131
section FlattenedModule132
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CacheCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CacheCopy
end FlattenedModule132
section FlattenedModule133
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CacheCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CacheCopy
end FlattenedModule133
section FlattenedModule134
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CacheCopy
open Structured
def setupAtoms : List Atom := [⟨.nadd 128 74 112,trivial⟩,⟨.nadd 132 112 56,trivial⟩,
  ⟨.nadd 170 112 112,trivial⟩,⟨.nadd 20 108 56,trivial⟩,⟨.nadd 176 66 56,trivial⟩]
def setup : Cmd := Structured.sequence (setupAtoms.map Cmd.atom)
noncomputable def setupData (s : Data) : Data := setupAtoms.foldl (fun t a => a.effect t) s
def call : Cmd := .seq setup code
end DecrAlmostLinearSSSP.Decremental.CacheCopy
end FlattenedModule134
section FlattenedModule135
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
structure Globals (i : Input) (B utility : ℕ) (s : Data) : Prop where
  zeroN : s.natReg 56 = 0
  zeroR : s.realReg 56 = 0
  unit : s.natReg 26 = 1
  two : s.natReg 14 = 2
  scanZero : s.natReg 34 = 0
  scanUnit : s.natReg 36 = 1
  size : s.natReg 64 = i.size
  vertices : s.natReg 66 = i.n
  edges : s.natReg 68 = i.k
  weightBound : s.natReg 70 = i.W
  source : s.natReg 72 = i.source.val
  accuracy : s.realReg 64 = i.accuracy
  base : s.natReg 74 = B
  utilityBase : s.natReg 48 = utility
def globalNat : List ℕ := [56,26,14,34,36,64,66,68,70,72,74,48]
def globalReal : List ℕ := [56,64]
def GlobalFrame (cmd : Cmd) : Prop :=
  (∀ k ∈ globalNat, NatFrame cmd k) ∧ (∀ k ∈ globalReal, RealFrame cmd k)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule135
section FlattenedModule136
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Prepass
open Structured ScaledCeiling
end DecrAlmostLinearSSSP.Decremental.Prepass
end FlattenedModule136
section FlattenedModule137
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule137
section FlattenedModule138
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
structure BankEnv (j record cache stride : ℕ) (s : Data) : Prop where
  record : s.natReg 106 = record
  cache : s.natReg 108 = cache
  index : s.natReg 110 = j
  factor : s.natReg 112 = bankFactor j
  stride : s.natReg 134 = stride
  scale : s.realReg 146 = DecrAlmostLinearSSSP.Decremental.scale j
def bankNat : List ℕ := [106,108,110,112,134]
def BankFrame (cmd : Cmd) : Prop := (∀ k ∈ bankNat, NatFrame cmd k) ∧ RealFrame cmd 146
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule138
section FlattenedModule139
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
structure Ready (i : Input) (j B utility record cache stride : ℕ) (s : Data) : Prop where
  globals : Globals i B utility s
  bank : BankEnv j record cache stride s
  savebase : s.natReg 50 = record+8
  delta : s.realReg 70 = DecrAlmostLinearSSSP.Decremental.delta i j
  cutoff : s.realReg 148 = 2*scale j
  work : s.natMem (record+6) = 0
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule139
section FlattenedModule140
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule140
section FlattenedModule141
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end FlattenedModule141
section FlattenedModule142
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end FlattenedModule142
section FlattenedModule143
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end FlattenedModule143
section FlattenedModule144
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
def constantsNat : List ℕ := [50,152,154]
def constantsReal : List ℕ := [70,148]
def ConstantFrame (cmd : Cmd) : Prop :=
  (∀ k ∈ constantsNat, NatFrame cmd k) ∧ (∀ k ∈ constantsReal, RealFrame cmd k)
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end FlattenedModule144
section FlattenedModule145
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule145
section FlattenedModule146
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def prepareTape : Cmd := .seq TapeCopy.start TapeCopy.code
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule146
section FlattenedModule147
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
structure RecordImage (i : Input) (j record cache next : ℕ) (s : Data) : Prop where
  cachebase : s.natMem record = cache
  next : s.natMem (record+2) = next
  factor : s.natMem (record+4) = bankFactor j
  cutoff : s.realMem record = 2*scale j
  delta : s.realMem (record+2) = DecrAlmostLinearSSSP.Decremental.delta i j
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule147
section FlattenedModule148
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def prepareBank (N : ℕ) : Cmd := .seq RecordHeader.code (.seq (ScaleParameters.initializeSnapshot N) prepareTape)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule148
section FlattenedModule149
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule149
section FlattenedModule150
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule150
section FlattenedModule151
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.SourceCall
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceCall
end FlattenedModule151
section FlattenedModule152
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace CacheCopy
end CacheCopy
namespace Native
end Native
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule152
section FlattenedModule153
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule153
section FlattenedModule154
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def initializeScale (p : Program) : Cmd := .seq (prepareBank (registerBound p.code))
  (.seq (SourceCall.code (registerBound p.code) p.initPC p) CacheCopy.call)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule154
section FlattenedModule155
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def ControlFrame (cmd : Cmd) : Prop := ∀ k, 60 ≤ k → k ≤ 104 → Even k → NatFrame cmd k
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule155
section FlattenedModule156
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def scaleStartAtoms (N : ℕ) : List Atom := [⟨.nadd 106 84 56,trivial⟩,⟨.nadd 108 88 56,trivial⟩,
  ⟨.natural 110 0,trivial⟩,⟨.natural 112 2,trivial⟩,⟨.rational 146 1,trivial⟩,⟨.natural 134 (2*N+8),trivial⟩]
def scaleStart (N : ℕ) : Cmd := Structured.sequence ((scaleStartAtoms N).map Cmd.atom)
noncomputable def scaleStartData (N : ℕ) (s : Data) : Data := (scaleStartAtoms N).foldl (fun t a => a.effect t) s
def advanceAtoms : List Atom := [⟨.nadd 106 106 134,trivial⟩,⟨.nadd 108 108 100,trivial⟩,
  ⟨.nadd 110 110 26,trivial⟩,⟨.nadd 112 112 112,trivial⟩,⟨.add 146 146 146,trivial⟩]
def scaleAdvance : Cmd := Structured.sequence (advanceAtoms.map Cmd.atom)
noncomputable def advanceData (s : Data) : Data := advanceAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule156
section FlattenedModule157
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
noncomputable def recordAt (base stride j : ℕ) : ℕ := base+stride*j
noncomputable def cacheAt (base n j : ℕ) : ℕ := base+2*(n*j)
structure CacheImage (i : Input) (j cache : ℕ) (b : Fin i.n → ℝ≥0∞) (s : Data) : Prop where
  flags : ∀ v : Fin i.n, s.natMem (cache+2*v.val) ≤ 1
  finite : ∀ v : Fin i.n, s.natMem (cache+2*v.val) = 0 → 0 ≤ s.realMem (cache+2*v.val)
  value : ∀ v : Fin i.n, ExtendedMax.cell s (cache+2*v.val) = ENNReal.ofReal (delta i j)*b v
structure ScaleMemory (i : Input) (p : Program) (B j record cache next : ℕ)
    (g : Machine) (b : Fin i.n → ℝ≥0∞) (s : Data) : Prop where
  metadata : RecordImage i j record cache next s
  source : SourceMemory.Image B j s g.natMem g.realMem
  work : s.natMem (record+6) = g.work
  saved : ∀ r < registerBound p.code, s.natMem (record+8+2*r) = bankFactor j*g.natReg r ∧
    s.realMem (record+8+2*r) = g.realReg r
  cache : CacheImage i j cache b s
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule157
section FlattenedModule158
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Layout
end DecrAlmostLinearSSSP.Decremental.Layout
end FlattenedModule158
section FlattenedModule159
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
abbrev scaleLayout (B n S reserve N : ℕ) : Layout.Addresses := Layout.addresses B n S reserve (2*N+8)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule159
section FlattenedModule160
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
noncomputable def setupCost (i : Input) (coefficient N : ℕ) : ℕ :=
  2*(dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32)+
    2*(dispatchCharge ScaledCeiling.ceilingProgram.code+4)*(16*scaleCount i+32)+coefficient+(2*N+8)+38
def normalSetup (coefficient N : ℕ) : Cmd := .seq InputCapture.code (Prepass.code coefficient (2*N+8))
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule160
section FlattenedModule161
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
def ScaleCell (B n S reserve N j address : ℕ) : Prop :=
  (∃ r < N+4, address = recordAt (scaleLayout B n S reserve N).records (2*N+8) j+2*r) ∨
  (∃ a, address = bankAddress B j a) ∨
  (∃ v < n, address = cacheAt (scaleLayout B n S reserve N).caches n j+2*v)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule161
section FlattenedModule162
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def FootprintFrame (B n S reserve N j : ℕ) (s t : Data) : Prop :=
  ∀ address, ¬ScaleCell B n S reserve N j address →
    (∀ a, address ≠ (scaleLayout B n S reserve N).utility+2*a+1) →
    t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule162
section FlattenedModule163
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule163
section FlattenedModule164
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
noncomputable def initOverhead (i : Input) (p : Program) : ℕ :=
  14*registerBound p.code+5*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32))+
    i.k*(3*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32))+30)+13*i.n+158
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule164
section FlattenedModule165
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
structure InitialFacts (p : Program) (C : ℝ) (a : ℕ → ℝ) (i : Input) (j : ℕ) (g : Machine) : Prop where
  ends : Ends p (initialMachine p (barrierInput i j)) g
  source : stored g i.source.val = 0
  normal : ∀ v : Fin i.n, g.natMem v.val ≤ 1 ∧ (g.natMem v.val = 0 → 0 ≤ g.realMem v.val)
  accurate : ∀ v : Fin i.n, (barrierInput i j).dist [] v ≤ stored g v.val ∧
    stored g v.val ≤ ENNReal.ofReal (1+(barrierInput i j).accuracy)*(barrierInput i j).dist [] v ∧
    (stored g v.val = ⊤ ↔ ¬Reachable i.graph (live []) i.source v)
  work : (g.work : ℝ) ≤ C*(barrierInput i j).size*a (barrierInput i j).size/(barrierInput i j).accuracy
noncomputable def maxInitialWork {i : Input} (f : Fin (scaleCount i) → Machine) : ℕ :=
  Finset.univ.sup (fun j => (f j).work)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule165
section FlattenedModule166
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
structure InitPrefix (i : Input) (p : Program) (B reserve : ℕ)
    (f : Fin (scaleCount i) → Machine) (done : ℕ) (s : Data) : Prop where
  bound : done ≤ scaleCount i
  globals : Globals i B (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).utility s
  bank : BankEnv done
    (recordAt (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).records (2*registerBound p.code+8) done)
    (cacheAt (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).caches i.n done) (2*registerBound p.code+8) s
  count : s.natReg 80 = scaleCount i
  cacheStride : s.natReg 100 = 2*i.n
  completed : ∀ q : Fin (scaleCount i), q.val < done →
    ScaleMemory i p B q.val
      (recordAt (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).records (2*registerBound p.code+8) q.val)
      (cacheAt (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).caches i.n q.val)
      (recordAt (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).records (2*registerBound p.code+8) (q.val+1))
      (f q) (fun v => stored (f q) v.val) s
  fresh : ∀ q : Fin (scaleCount i), done ≤ q.val → SourceMemory.Image B q.val s (fun _ => 0) (fun _ => 0)
  inputTape : ∀ address, address ≤ B → s.natMem address = (initialMachine p i).natMem address
  tail : ∀ r, registerBound p.code ≤ r → s.natReg (shadowReg r) = 0 ∧ s.realReg (shadowReg r) = 0
def scaleInitBody (p : Program) : Cmd := .seq (initializeScale p) scaleAdvance
def scaleInitLoop (p : Program) : Cmd := .loop (.natLess 110 80) (scaleInitBody p)
def scaleInitAll (p : Program) : Cmd := .seq (scaleStart (registerBound p.code)) (scaleInitLoop p)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule166
section FlattenedModule167
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule167
section FlattenedModule168
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule168
section FlattenedModule169
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule169
section FlattenedModule170
set_option autoImplicit false
open scoped ENNReal NNReal
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def clearLastAtoms : List Atom := [⟨.nsub 218 106 134,trivial⟩,⟨.nadd 218 218 14,trivial⟩,⟨.storeN 218 56,trivial⟩]
def clearLast : Cmd := Structured.sequence (clearLastAtoms.map Cmd.atom)
noncomputable def clearLastData (s : Data) : Data := clearLastAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule170
section FlattenedModule171
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
noncomputable def nextRecord (base stride S q : ℕ) : ℕ := if q+1 < S then recordAt base stride (q+1) else 0
structure InitDone (i : Input) (p : Program) (B reserve : ℕ) (f : Fin (scaleCount i) → Machine) (s : Data) : Prop where
  globals : Globals i B (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).utility s
  completed : ∀ q : Fin (scaleCount i), ScaleMemory i p B q.val
    (recordAt (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).records (2*registerBound p.code+8) q.val)
    (cacheAt (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).caches i.n q.val)
    (nextRecord (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).records (2*registerBound p.code+8) (scaleCount i) q.val)
    (f q) (fun v => stored (f q) v.val) s
  inputTape : ∀ address, address ≤ B → s.natMem address = (initialMachine p i).natMem address
  tail : ∀ r, registerBound p.code ≤ r → s.natReg (shadowReg r) = 0 ∧ s.realReg (shadowReg r) = 0
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule171
section FlattenedModule172
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.LinkedScan
open Structured
attribute [local instance] Classical.propDecidable
structure Row where
  address : ℕ
  base : ℕ
  flag : ℕ
  value : ℝ
  bound : ℝ
def headAddress : List Row → ℕ
  | [] => 0
  | r::_ => r.address
def Row.Eligible (r : Row) : Prop := r.flag = 0 ∧ r.value ≤ r.bound
noncomputable def selectedAddress : List Row → ℕ
  | [] => 0
  | r::rest => if r.Eligible then r.address else selectedAddress rest
noncomputable def skipped : List Row → ℕ
  | [] => 0
  | r::rest => if r.Eligible then 0 else skipped rest+1
def RowsView (s : Data) (vertex : ℕ) : List Row → Prop
  | [] => True
  | r::rest => 0 < r.address ∧ s.natMem r.address = r.base ∧ s.realMem r.address = r.bound ∧
      s.natMem (r.base+vertex) = r.flag ∧ s.realMem (r.base+vertex) = r.value ∧ r.flag ≤ 1 ∧
      s.natMem (r.address+2) = headAddress rest ∧ RowsView s vertex rest
def advance : Cmd := Structured.sequence [nadd 46 30 36,nadd 46 46 36,loadN 30 46]
def readRow : Cmd := Structured.sequence [loadN 44 30,nadd 40 44 38,loadN 42 40]
def finiteCheck : Cmd := .seq (load 30 30) (.seq (load 32 40)
  (.branch (.realLess 30 32) advance (natural 32 1)))
def body : Cmd := .branch (.natLess 34 30)
  (.seq readRow (.branch (.natLess 42 36) finiteCheck advance)) (natural 32 1)
def loop : Cmd := .loop (.natLess 32 36) body
def code : Cmd := .seq (natural 32 0) loop
end DecrAlmostLinearSSSP.Decremental.LinkedScan
end FlattenedModule172
section FlattenedModule173
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.LinkedScan
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.LinkedScan
end FlattenedModule173
section FlattenedModule174
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.LinkedScan
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.LinkedScan
end FlattenedModule174
section FlattenedModule175
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
def PointerValid (i : Input) (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (v : Fin i.n) (p : ℕ) : Prop :=
  p ≤ scaleCount i ∧ (∀ j < p, eligible i b v j = false) ∧
    (p < scaleCount i → eligible i b v p = true)
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule175
section FlattenedModule176
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
def OutputConsistent (i : Input) (s : AdapterState i) : Prop :=
  ∀ v, v ∉ s.dirty → s.output v = selected i s.maxima s.pointer v
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule176
section FlattenedModule177
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule177
section FlattenedModule178
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.LinkedScan
attribute [local instance] Classical.propDecidable
def rowsFrom (row : ℕ → Row) : ℕ → ℕ → List Row
  | 0,_ => []
  | fuel+1,p => row p :: rowsFrom row fuel (p+1)
end DecrAlmostLinearSSSP.Decremental.LinkedScan
end FlattenedModule178
section FlattenedModule179
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
attribute [local instance] Classical.propDecidable
structure ScanTable (i : Input) (recordBase cacheBase stride : ℕ)
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (s : Data) : Prop where
  positive : 0 < recordBase
  metadata : ∀ q : Fin (scaleCount i), RecordImage i q.val (recordAt recordBase stride q.val)
    (cacheAt cacheBase i.n q.val) (nextRecord recordBase stride (scaleCount i) q.val) s
  cache : ∀ q : Fin (scaleCount i), CacheImage i q.val (cacheAt cacheBase i.n q.val) (b q) s
noncomputable def scanRecord (i : Input) (base stride j : ℕ) : ℕ := if j < scaleCount i then recordAt base stride j else 0
noncomputable def scanRow (i : Input) (recordBase cacheBase stride : ℕ) (s : Data) (v : Fin i.n) (j : ℕ) : LinkedScan.Row :=
  if j < scaleCount i then
    { address := recordAt recordBase stride j
      base := cacheAt cacheBase i.n j
      flag := s.natMem (cacheAt cacheBase i.n j+2*v.val)
      value := s.realMem (cacheAt cacheBase i.n j+2*v.val)
      bound := 2*scale j }
  else { address := 0,base := 0,flag := 1,value := 0,bound := 0 }
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule179
section FlattenedModule180
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.LinkedScan
open Structured
end DecrAlmostLinearSSSP.Decremental.LinkedScan
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule180
section FlattenedModule181
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.DirtyMark
open Structured
attribute [local instance] Classical.propDecidable
structure View {n : ℕ} (flagBase listBase : ℕ) (xs : List (Fin n)) (s : Data) : Prop where
  nodup : xs.Nodup
  flags : ∀ v : Fin n, s.natMem (flagBase+2*v.val) = if v ∈ xs then 1 else 0
  entries : ∀ j (hj : j < xs.length), s.natMem (listBase+2*j) = (xs[j]).val
  count : s.natReg 182 = xs.length
  pointer : s.natReg 180 = listBase+2*xs.length
def prefixAtoms : List Atom := [⟨.nadd 186 94 94,trivial⟩,⟨.nadd 184 98 186,trivial⟩,⟨.loadN 188 184,trivial⟩]
def prefixCode : Cmd := Structured.sequence (prefixAtoms.map Cmd.atom)
noncomputable def prefixData (s : Data) : Data := prefixAtoms.foldl (fun t a => a.effect t) s
def insertCode : Cmd := Structured.sequence [storeN 184 26,storeN 180 94,nadd 180 180 14,nadd 182 182 26]
def code : Cmd := .seq prefixCode (.branch (.natLess 188 26) insertCode .skip)
noncomputable def inserted (s : Data) : Data :=
  {s with
    natMem := Function.update (Function.update s.natMem (s.natReg 184) 1) (s.natReg 180) (s.natReg 94)
    natReg := Function.update (Function.update s.natReg 180 (s.natReg 180+2)) 182 (s.natReg 182+1)}
end DecrAlmostLinearSSSP.Decremental.DirtyMark
end FlattenedModule181
section FlattenedModule182
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def pointerPrefixAtoms : List Atom := [⟨.nadd 38 94 94,trivial⟩,⟨.nadd 196 96 38,trivial⟩,⟨.nadd 30 84 56,trivial⟩]
def pointerPrefix : Cmd := Structured.sequence (pointerPrefixAtoms.map Cmd.atom)
noncomputable def pointerPrefixData (s : Data) : Data := pointerPrefixAtoms.foldl (fun t a => a.effect t) s
def pointerSuffixAtoms : List Atom := [⟨.storeN 196 30,trivial⟩,⟨.nadd 184 98 38,trivial⟩,⟨.storeN 184 26,trivial⟩,
  ⟨.storeN 180 94,trivial⟩,⟨.nadd 180 180 14,trivial⟩,⟨.nadd 182 182 26,trivial⟩,⟨.nadd 94 94 26,trivial⟩]
def pointerSuffix : Cmd := Structured.sequence (pointerSuffixAtoms.map Cmd.atom)
noncomputable def pointerSuffixData (s : Data) : Data := pointerSuffixAtoms.foldl (fun t a => a.effect t) s
def pointerBody : Cmd := .seq pointerPrefix (.seq LinkedScan.code pointerSuffix)
def pointerLoop : Cmd := .loop (.natLess 94 66) pointerBody
def pointerStartAtoms : List Atom := [⟨.natural 94 0,trivial⟩,⟨.natural 182 0,trivial⟩,⟨.nadd 180 102 56,trivial⟩]
def pointerStart : Cmd := Structured.sequence (pointerStartAtoms.map Cmd.atom)
noncomputable def pointerStartData (s : Data) : Data := pointerStartAtoms.foldl (fun t a => a.effect t) s
def buildPointers : Cmd := .seq pointerStart pointerLoop
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule182
section FlattenedModule183
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule183
section FlattenedModule184
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule184
section FlattenedModule185
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
structure PointerBases (record pointer flags list : ℕ) (s : Data) : Prop where
  record : s.natReg 84 = record
  pointer : s.natReg 96 = pointer
  flags : s.natReg 98 = flags
  list : s.natReg 102 = list
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule185
section FlattenedModule186
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
structure PointerLayout where
  record : ℕ
  cache : ℕ
  pointer : ℕ
  flags : ℕ
  list : ℕ
def pointerLayout (B n S reserve N : ℕ) : PointerLayout where
  record := (scaleLayout B n S reserve N).records
  cache := (scaleLayout B n S reserve N).caches
  pointer := (scaleLayout B n S reserve N).pointers
  flags := (scaleLayout B n S reserve N).dirtyFlags
  list := (scaleLayout B n S reserve N).dirtyList
def PointerArrayCell (l : PointerLayout) (n address : ℕ) : Prop :=
  ∃ v < n, address = l.pointer+2*v ∨ address = l.flags+2*v ∨ address = l.list+2*v
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule186
section FlattenedModule187
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def PublicCell (l : PointerLayout) (n address : ℕ) : Prop := address < n ∨ PointerArrayCell l n address
def PublicFrame (l : PointerLayout) (n : ℕ) (s t : Data) : Prop :=
  ∀ address, ¬PublicCell l n address → t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule187
section FlattenedModule188
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
structure PointerPrefix (i : Input) (B reserve N : ℕ)
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (done : ℕ) (s : Data) : Prop where
  bound : done ≤ i.n
  globals : Globals i B (scaleLayout B i.n (scaleCount i) reserve N).utility s
  bases : PointerBases (pointerLayout B i.n (scaleCount i) reserve N).record
    (pointerLayout B i.n (scaleCount i) reserve N).pointer (pointerLayout B i.n (scaleCount i) reserve N).flags
    (pointerLayout B i.n (scaleCount i) reserve N).list s
  vertex : s.natReg 94 = done
  count : s.natReg 182 = done
  writer : s.natReg 180 = (pointerLayout B i.n (scaleCount i) reserve N).list+2*done
  table : ScanTable i (pointerLayout B i.n (scaleCount i) reserve N).record
    (pointerLayout B i.n (scaleCount i) reserve N).cache (2*N+8) b s
  pointers : ∀ v : Fin i.n, v.val < done →
    s.natMem ((pointerLayout B i.n (scaleCount i) reserve N).pointer+2*v.val) =
      scanRecord i (pointerLayout B i.n (scaleCount i) reserve N).record (2*N+8)
        (DecrAlmostLinearSSSP.Decremental.advance i b v (scaleCount i) 0)
  flags : ∀ v : Fin i.n, v.val < done → s.natMem ((pointerLayout B i.n (scaleCount i) reserve N).flags+2*v.val) = 1
  entries : ∀ r < done, s.natMem ((pointerLayout B i.n (scaleCount i) reserve N).list+2*r) = r
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule188
section FlattenedModule189
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule189
section FlattenedModule190
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule190
section FlattenedModule191
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule191
section FlattenedModule192
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.PointerRead
open Structured
def code : Cmd := .seq (loadN 30 196)
  (.branch (.natLess 56 30)
    (Structured.sequence [loadN 44 30,nadd 20 44 38,loadN 22 20,load 20 20])
    (Structured.sequence [natural 22 1,rational 20 0]))
noncomputable def pointer (s : Data) : ℕ := s.natMem (s.natReg 196)
noncomputable def cellAddress (s : Data) : ℕ := s.natMem (pointer s)+s.natReg 38
end DecrAlmostLinearSSSP.Decremental.PointerRead
end FlattenedModule192
section FlattenedModule193
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.SelectedRead
open Structured
attribute [local instance] Classical.propDecidable
def prefixAtoms : List Atom := [⟨.nadd 38 94 94,trivial⟩,⟨.nadd 196 96 38,trivial⟩]
def prefixCode : Cmd := Structured.sequence (prefixAtoms.map Cmd.atom)
noncomputable def prefixData (s : Data) : Data := prefixAtoms.foldl (fun t a => a.effect t) s
def zeroCode : Cmd := Structured.sequence [natural 22 0,rational 20 0]
def chooseCode : Cmd := .branch (.natLess 94 72) PointerRead.code
  (.branch (.natLess 72 94) PointerRead.code zeroCode)
def code : Cmd := .seq prefixCode chooseCode
noncomputable def value (s : Data) : ℝ≥0∞ :=
  if s.natReg 94 = s.natReg 72 then 0
  else if s.natMem (s.natReg 96+2*s.natReg 94) = 0 then ⊤
  else ExtendedMax.cell s (s.natMem (s.natMem (s.natReg 96+2*s.natReg 94))+2*s.natReg 94)
noncomputable def flag (s : Data) : ℕ :=
  if s.natReg 94 = s.natReg 72 then 0
  else if s.natMem (s.natReg 96+2*s.natReg 94) = 0 then 1
  else s.natMem (s.natMem (s.natMem (s.natReg 96+2*s.natReg 94))+2*s.natReg 94)
noncomputable def realValue (s : Data) : ℝ :=
  if s.natReg 94 = s.natReg 72 then 0
  else if s.natMem (s.natReg 96+2*s.natReg 94) = 0 then 0
  else s.realMem (s.natMem (s.natMem (s.natReg 96+2*s.natReg 94))+2*s.natReg 94)
end DecrAlmostLinearSSSP.Decremental.SelectedRead
end FlattenedModule193
section FlattenedModule194
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.AnswerTable
open Structured
attribute [local instance] Classical.propDecidable
structure Layout (n : ℕ) where
  source : Fin n
  pointerBase : ℕ
  record : Fin n → ℕ
  cacheBase : Fin n → ℕ
  cacheFlag : Fin n → ℕ
  cacheReal : Fin n → ℝ
noncomputable def Layout.flag {n : ℕ} (l : Layout n) (v : Fin n) : ℕ :=
  if v = l.source then 0 else if l.record v = 0 then 1 else l.cacheFlag v
noncomputable def Layout.realValue {n : ℕ} (l : Layout n) (v : Fin n) : ℝ :=
  if v = l.source then 0 else if l.record v = 0 then 0 else l.cacheReal v
structure Image {n : ℕ} (l : Layout n) (s : Data) : Prop where
  pointers : ∀ v, s.natMem (l.pointerBase+2*v.val) = l.record v
  caches : ∀ v, l.record v ≠ 0 → s.natMem (l.record v) = l.cacheBase v ∧
    s.natMem (l.cacheBase v+2*v.val) = l.cacheFlag v ∧
    s.realMem (l.cacheBase v+2*v.val) = l.cacheReal v
def Protected {n : ℕ} (l : Layout n) (address : ℕ) : Prop :=
  (∃ v : Fin n, address = l.pointerBase+2*v.val) ∨
    ∃ v : Fin n, l.record v ≠ 0 ∧ (address = l.record v ∨ address = l.cacheBase v+2*v.val)
end DecrAlmostLinearSSSP.Decremental.AnswerTable
end FlattenedModule194
section FlattenedModule195
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
attribute [local instance] Classical.propDecidable
noncomputable def answerCache (i : Input) (cacheBase : ℕ) (p : Fin i.n → ℕ) (v : Fin i.n) : ℕ :=
  if p v < scaleCount i then cacheAt cacheBase i.n (p v) else 0
noncomputable def answerLayout (i : Input) (recordBase cacheBase stride pointerBase : ℕ)
    (p : Fin i.n → ℕ) (s : Data) : AnswerTable.Layout i.n where
  source := i.source
  pointerBase := pointerBase
  record := fun v => scanRecord i recordBase stride (p v)
  cacheBase := answerCache i cacheBase p
  cacheFlag := fun v => s.natMem (answerCache i cacheBase p v+2*v.val)
  cacheReal := fun v => s.realMem (answerCache i cacheBase p v+2*v.val)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule195
section FlattenedModule196
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule196
section FlattenedModule197
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.DirtyCommit
open Structured
def suffix : Cmd := Structured.sequence [storeN 94 22,store 94 20,nadd 184 98 38,
  storeN 184 56,nadd 192 192 14,nsub 194 194 26]
def body : Cmd := .seq (loadN 94 192) (.seq SelectedRead.code suffix)
def loop : Cmd := .loop (.natLess 56 194) body
noncomputable def loaded (s : Data) : Data :=
  {s with natReg := Function.update s.natReg 94 (s.natMem (s.natReg 192))}
noncomputable def afterStores (s : Data) : Data :=
  {s with
    natMem := Function.update (Function.update s.natMem (s.natReg 94) (s.natReg 22))
      (s.natReg 98+s.natReg 38) (s.natReg 56)
    realMem := Function.update s.realMem (s.natReg 94) (s.realReg 20)
    natReg := Function.update (Function.update (Function.update s.natReg 184
      (s.natReg 98+s.natReg 38)) 192 (s.natReg 192+s.natReg 14))
      194 (s.natReg 194-s.natReg 26)}
end DecrAlmostLinearSSSP.Decremental.DirtyCommit
end FlattenedModule197
section FlattenedModule198
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.DirtyCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.DirtyCommit
end FlattenedModule198
section FlattenedModule199
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.DirtyCommit
open Structured
def beginCode : Cmd := Structured.sequence [nadd 192 102 56,nadd 194 182 56]
def endCode : Cmd := Structured.sequence [natural 182 0,nadd 180 102 56]
def code : Cmd := .seq beginCode (.seq loop endCode)
noncomputable def beginData (s : Data) : Data :=
  {s with natReg := Function.update (Function.update s.natReg 192 (s.natReg 102+s.natReg 56)) 194 (s.natReg 182+s.natReg 56)}
noncomputable def endData (s : Data) : Data :=
  {s with natReg := Function.update (Function.update s.natReg 182 0) 180 (s.natReg 102+s.natReg 56)}
end DecrAlmostLinearSSSP.Decremental.DirtyCommit
end FlattenedModule199
section FlattenedModule200
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace SelectedRead
end SelectedRead
namespace DirtyCommit
end DirtyCommit
namespace Native
end Native
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule200
section FlattenedModule201
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
noncomputable def initialPointers (i : Input) (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) : Fin i.n → ℕ :=
  fun v => DecrAlmostLinearSSSP.Decremental.advance i b v (scaleCount i) 0
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule201
section FlattenedModule202
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule202
section FlattenedModule203
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def shortEdgeLists (n k : ℕ) : Finset (List (Fin k)) :=
  Finset.univ.biUnion fun l : Fin n =>
    Finset.univ.image fun f : Fin l.val → Fin k => List.ofFn f
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule203
section FlattenedModule204
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def scaleOriginal (i : Input) (j : ℕ) (e : Fin (roundedInput i j).k) : Fin i.k :=
  ((Fintype.equivFin (ScaleEdge i j)).symm e).val
noncomputable def scaleActive (i : Input) (j : ℕ) (active : Finset (Fin i.k)) :
    Finset (Fin (roundedInput i j).k) := by
  classical
  exact Finset.univ.filter (fun e => scaleOriginal i j e ∈ active)
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule204
section FlattenedModule205
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule205
section FlattenedModule206
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule206
section FlattenedModule207
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule207
section FlattenedModule208
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule208
section FlattenedModule209
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule209
section FlattenedModule210
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule210
section FlattenedModule211
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule211
section FlattenedModule212
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule212
section FlattenedModule213
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
def singletonProgram : Program where
  code := [.halt, .loadN 6 5, .load 1 5, .halt]
  initPC := 0
  update := 0
  query := 1
def haltState (c : Machine) : Machine :=
  {c with pc := c.pc + 1, work := c.work + 1, halted := true}
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule213
section FlattenedModule214
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule214
section FlattenedModule215
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule215
section FlattenedModule216
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule216
section FlattenedModule217
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule217
section FlattenedModule218
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def initializePublic : Cmd := .seq buildPointers DirtyCommit.code
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule218
section FlattenedModule219
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def PublicControlFrame (cmd : Cmd) : Prop := ∀ k, 60 ≤ k → k ≤ 104 → Even k → k ≠ 94 → NatFrame cmd k
structure Controls (B n S reserve N : ℕ) (s : Data) : Prop where
  capacity : s.natReg 60 = reserve
  count : s.natReg 80 = S
  records : s.natReg 84 = (scaleLayout B n S reserve N).records
  caches : s.natReg 88 = (scaleLayout B n S reserve N).caches
  reports : s.natReg 92 = (scaleLayout B n S reserve N).reports
  pointers : s.natReg 96 = (scaleLayout B n S reserve N).pointers
  flags : s.natReg 98 = (scaleLayout B n S reserve N).dirtyFlags
  vertexStride : s.natReg 100 = 2*n
  list : s.natReg 102 = (scaleLayout B n S reserve N).dirtyList
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule219
section FlattenedModule220
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
structure NormalMemory (i : Input) (p : Program) (B reserve : ℕ)
    (machines : Fin (scaleCount i) → Machine) (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (ptr : Fin i.n → ℕ) (s : Data) : Prop where
  globals : Globals i B (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).utility s
  controls : Controls B i.n (scaleCount i) reserve (registerBound p.code) s
  scales : ∀ q : Fin (scaleCount i), ScaleMemory i p B q.val
    (recordAt (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).records (2*registerBound p.code+8) q.val)
    (cacheAt (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).caches i.n q.val)
    (nextRecord (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).records (2*registerBound p.code+8) (scaleCount i) q.val)
    (machines q) (b q) s
  pointers : ∀ v : Fin i.n, s.natMem ((pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).pointer+2*v.val) =
    scanRecord i (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).record (2*registerBound p.code+8) (ptr v)
  dirty : DirtyMark.View (n := i.n) (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).flags
    (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).list [] s
  normalized : ∀ v : Fin i.n, s.natMem v.val ≤ 1 ∧ (s.natMem v.val = 0 → 0 ≤ s.realMem v.val)
  output : ∀ v : Fin i.n, stored s.machine v.val = selected i b ptr v
  tail : ∀ r, registerBound p.code ≤ r → s.natReg (shadowReg r) = 0 ∧ s.realReg (shadowReg r) = 0
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule220
section FlattenedModule221
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def normalInitialize (coefficient : ℕ) (p : Program) : Cmd := .seq (normalSetup coefficient (registerBound p.code))
  (.seq (scaleInitAll p) (.seq clearLast initializePublic))
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule221
section FlattenedModule222
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule222
section FlattenedModule223
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def normalWrapperOverhead (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  (1+a (64*m))*(3+logarithm2 (max 2 m : ℕ))*(256+32*logarithm2 (max 2 m : ℕ))
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule223
section FlattenedModule224
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
noncomputable def normalInitConstant (p : Program) (coefficient : ℕ) : ℕ :=
  coefficient+16*registerBound p.code+14*dispatchCharge ScaledCeiling.ceilingProgram.code+
    dispatchCharge p.code+500
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule224
section FlattenedModule225
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace CacheRefresh
def atoms : List Atom := [⟨.nadd 128 198 56,trivial⟩,⟨.nadd 132 112 56,trivial⟩,
  ⟨.nadd 38 94 94,trivial⟩,⟨.nadd 20 108 38,trivial⟩]
def prepare : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def prepared (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
def code : Cmd := .seq prepare (.seq ScaledReadout.code ExtendedMax.code)
end CacheRefresh
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule225
section FlattenedModule226
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule226
section FlattenedModule227
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule227
section FlattenedModule228
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace PointerRefresh
def atoms : List Atom := [⟨.nadd 38 94 94,trivial⟩,⟨.nadd 196 96 38,trivial⟩,⟨.loadN 30 196,trivial⟩]
def prepare : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def prepared (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
def code : Cmd := .seq prepare (.seq LinkedScan.code (storeN 196 30))
end PointerRefresh
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule228
section FlattenedModule229
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace Native
structure AdapterMemory (i : Input) (B reserve N : ℕ) (a : AdapterState i) (xs : List (Fin i.n)) (s : Data) : Prop where
  table : ScanTable i (pointerLayout B i.n (scaleCount i) reserve N).record
    (pointerLayout B i.n (scaleCount i) reserve N).cache (2*N+8) a.maxima s
  pointers : ∀ v : Fin i.n, s.natMem ((pointerLayout B i.n (scaleCount i) reserve N).pointer+2*v.val) =
    scanRecord i (pointerLayout B i.n (scaleCount i) reserve N).record (2*N+8) (a.pointer v)
  pending : DirtyMark.View (pointerLayout B i.n (scaleCount i) reserve N).flags
    (pointerLayout B i.n (scaleCount i) reserve N).list xs s
  covered : a.dirty ⊆ xs.toFinset
  output : ∀ v : Fin i.n, stored s.machine v.val = a.output v
end Native
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule229
section FlattenedModule230
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule230
section FlattenedModule231
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
noncomputable def cacheUpdated (i : Input) (a : AdapterState i) (j : Fin (scaleCount i)) (v : Fin i.n)
    (value : ℝ≥0∞) : AdapterState i :=
  {a with maxima := Function.update a.maxima j (Function.update (a.maxima j) v (max (a.maxima j v) value))}
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule231
section FlattenedModule232
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
noncomputable def pointerUpdated (i : Input) (a : AdapterState i) (v : Fin i.n) : AdapterState i :=
  {a with
    pointer := Function.update a.pointer v
      (DecrAlmostLinearSSSP.Decremental.advance i a.maxima v (scaleCount i-a.pointer v) (a.pointer v))}
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule232
section FlattenedModule233
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule233
section FlattenedModule234
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule234
section FlattenedModule235
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule235
section FlattenedModule236
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def reportEvent : Cmd := .seq CacheRefresh.code (.seq PointerRefresh.code DirtyMark.code)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule236
section FlattenedModule237
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
noncomputable def physicalTraceWrites (B bank : ℕ) (guest : Program) : Machine → ℕ → List ℕ
  | _,0 => []
  | g,t+1 => if g.halted then [] else
      match guest.code[g.pc]? with
      | none => []
      | some ins => physicalWrites B bank ins g ++ physicalTraceWrites B bank guest (step guest g) t
def observedInterpreter (code : List Instruction) : Cmd := .loop (.natLess 4 1) (observedDispatchAux 0 code)
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule237
section FlattenedModule238
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule238
section FlattenedModule239
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule239
section FlattenedModule240
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def reportRealIndex (B bank address : ℕ) : ℝ :=
  ((address : ℝ)-(B : ℝ)-(bankFactor bank : ℝ))/(2*(bankFactor bank : ℝ))
noncomputable def reportIndex (B bank address : ℕ) : ℕ := ⌈reportRealIndex B bank address⌉₊
noncomputable def publicReport (i : Input) (B bank address : ℕ) : Option (Fin i.n) :=
  if address < B+bankFactor bank*(2*i.n+1) then
    if h : reportIndex B bank address < i.n then some ⟨reportIndex B bank address,h⟩ else none
  else none
noncomputable def publicReports (i : Input) (B bank : ℕ) (reports : List ℕ) : List (Fin i.n) :=
  reports.filterMap (publicReport i B bank)
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule240
section FlattenedModule241
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ReportDecode
open Structured
def atoms : List Atom := [⟨.cast 202 198,trivial⟩,⟨.cast 204 74,trivial⟩,
  ⟨.sub 202 202 204,trivial⟩,⟨.cast 204 112,trivial⟩,⟨.sub 202 202 204,trivial⟩,
  ⟨.rational 206 2,trivial⟩,⟨.mul 204 204 206,trivial⟩,⟨.div 202 202 204,trivial⟩]
def prepare : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def prepared (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
def code : Cmd := .seq prepare (ScaledCeiling.productReal 94 26 202)
end DecrAlmostLinearSSSP.Decremental.ReportDecode
end FlattenedModule241
section FlattenedModule242
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule242
section FlattenedModule243
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def decodedReportEvent : Cmd := .seq ReportDecode.code reportEvent
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule243
section FlattenedModule244
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
def atoms : List Atom := [⟨.nadd 212 154 154,trivial⟩,⟨.nadd 212 212 112,trivial⟩,
  ⟨.nadd 212 212 74,trivial⟩,⟨.nadd 210 92 56,trivial⟩,⟨.nadd 214 12 56,trivial⟩]
def fields : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def fieldData (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
def setup : Cmd := .seq (ScaledCeiling.productNat 154 112 66) fields
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule244
section FlattenedModule245
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
def finish : Cmd := .seq (nadd 210 210 14) (nsub 214 214 26)
noncomputable def finished (s : Data) : Data :=
  {s with natReg := Function.update (Function.update s.natReg 210 (s.natReg 210+s.natReg 14)) 214 (s.natReg 214-s.natReg 26)}
def action : Cmd := .branch (.natLess 198 212) decodedReportEvent .skip
def body : Cmd := .seq (loadN 198 210) (.seq action finish)
def loop : Cmd := .loop (.natLess 56 214) body
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule245
section FlattenedModule246
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule246
section FlattenedModule247
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def ReportFrame (i : Input) (B reserve N j : ℕ) (s t : Data) : Prop :=
  ∀ address, (∀ v : Fin i.n, address ≠ cacheAt (scaleLayout B i.n (scaleCount i) reserve N).caches i.n j+2*v.val) →
    ¬PointerArrayCell (pointerLayout B i.n (scaleCount i) reserve N) i.n address →
    (∀ r, address ≠ (scaleLayout B i.n (scaleCount i) reserve N).utility+2*r+1) →
    t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule247
section FlattenedModule248
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def pointerEnergy (i : Input) (s : AdapterState i) : ℕ := ∑ v, s.pointer v
abbrev AdapterEvent (i : Input) := Fin (scaleCount i) × Fin i.n × ℝ≥0∞
noncomputable def adapterTrace (i : Input) : AdapterState i → List (AdapterEvent i) → AdapterState i
  | s, [] => s
  | s, (j,v,value) :: rest => adapterTrace i (adapterWrite i s j v value) rest
noncomputable def pointerTravel (i : Input) : AdapterState i → List (AdapterEvent i) → ℕ
  | _, [] => 0
  | s, (j,v,value) :: rest =>
    (adapterWrite i s j v value).pointer v - s.pointer v +
      pointerTravel i (adapterWrite i s j v value) rest
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule248
section FlattenedModule249
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def observedAdapterEvents (i : Input) (j : Fin (scaleCount i))
    (p : Program) (c : Machine) (t : ℕ) : List (AdapterEvent i) :=
  (observedWrites i p c t).map (fun v => (j,v,stored (execute p c t) v.val))
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule249
section FlattenedModule250
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule250
section FlattenedModule251
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
noncomputable def events (i : Input) (B : ℕ) (j : Fin (scaleCount i)) (g : Machine) (address : ℕ) :
    List (AdapterEvent i) := (publicReport i B j.val address).toList.map (fun v => (j,v,stored g v.val))
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule251
section FlattenedModule252
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
structure Environment (i : Input) (B reserve N : ℕ) (j : Fin (scaleCount i)) (g : Machine) (s : Data) : Prop where
  globals : Globals i B (scaleLayout B i.n (scaleCount i) reserve N).utility s
  source : SourceMemory.Image B j.val s g.natMem g.realMem
  factor : s.natReg 112 = bankFactor j.val
  cache : s.natReg 108 = cacheAt (pointerLayout B i.n (scaleCount i) reserve N).cache i.n j.val
  delta : s.realReg 70 = DecrAlmostLinearSSSP.Decremental.delta i j.val
  pointers : s.natReg 96 = (pointerLayout B i.n (scaleCount i) reserve N).pointer
  flags : s.natReg 98 = (pointerLayout B i.n (scaleCount i) reserve N).flags
  limit : s.natReg 212 = B+bankFactor j.val*(2*i.n+1)
def fixedNat : List ℕ := [112,108,96,98,212]
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule252
section FlattenedModule253
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
structure Queue (i : Input) (B reserve N offset : ℕ) (reports : List ℕ) (s : Data) : Prop where
  reader : s.natReg 210 = (scaleLayout B i.n (scaleCount i) reserve N).reports+2*offset
  count : s.natReg 214 = reports.length
  entries : ∀ r (hr : r < reports.length), s.natMem
    ((scaleLayout B i.n (scaleCount i) reserve N).reports+2*(offset+r)) = reports[r]
  capacity : offset+reports.length ≤ reserve
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule253
section FlattenedModule254
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule254
section FlattenedModule255
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
noncomputable def allEvents (i : Input) (B : ℕ) (j : Fin (scaleCount i)) (g : Machine) (reports : List ℕ) :
    List (AdapterEvent i) := reports.flatMap (events i B j g)
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule255
section FlattenedModule256
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule256
section FlattenedModule257
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
def code : Cmd := .seq setup loop
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule257
section FlattenedModule258
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace UpdateHeader
def atoms : List Atom := [⟨.natural 52 4,trivial⟩,⟨.nadd 54 106 52,trivial⟩,⟨.loadN 112 54,trivial⟩,
  ⟨.loadN 108 106,trivial⟩,⟨.natural 52 2,trivial⟩,⟨.nadd 54 106 52,trivial⟩,⟨.load 70 54,trivial⟩,
  ⟨.natural 52 8,trivial⟩,⟨.nadd 50 106 52,trivial⟩,⟨.nadd 10 92 56,trivial⟩,
  ⟨.natural 12 0,trivial⟩,⟨.natural 14 2,trivial⟩]
def code : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def result (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
end UpdateHeader
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule258
section FlattenedModule259
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace SavedDeletion
def suffix : Cmd := Structured.sequence [natural 52 10,nadd 54 50 52,storeN 54 208]
noncomputable def patched (s : Data) : Data :=
  {s with
    natReg := Function.update (Function.update s.natReg 52 10) 54 (s.natReg 50+10),
    natMem := Function.update s.natMem (s.natReg 50+10) (s.natReg 208)}
def code : Cmd := .seq (ScaledCeiling.productNat 208 112 78) suffix
end SavedDeletion
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule259
section FlattenedModule260
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule260
section FlattenedModule261
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule261
section FlattenedModule262
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule262
section FlattenedModule263
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule263
section FlattenedModule264
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ObservedSourceCall
open Structured
def code (N entry : ℕ) (p : Program) : Cmd :=
  .seq (SourceSetup.code N entry) (observedInterpreter p.code)
end DecrAlmostLinearSSSP.Decremental.ObservedSourceCall
end FlattenedModule264
section FlattenedModule265
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ObservedSourceCall
open Structured
end DecrAlmostLinearSSSP.Decremental.ObservedSourceCall
end FlattenedModule265
section FlattenedModule266
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ObservedSourceCall
open Structured
def transaction (N entry : ℕ) (p : Program) : Cmd := .seq (code N entry p) (SourceSnapshot.code N)
end DecrAlmostLinearSSSP.Decremental.ObservedSourceCall
end FlattenedModule266
section FlattenedModule267
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def prepareUpdate : Cmd := .seq UpdateHeader.code SavedDeletion.code
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule267
section FlattenedModule268
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
noncomputable def sourceRecord (i : Input) (B reserve N j : ℕ) : ℕ :=
  recordAt (scaleLayout B i.n (scaleCount i) reserve N).records (2*N+8) j
def SourceUpdateFrame (i : Input) (B reserve N j : ℕ) (s t : Data) : Prop :=
  ∀ address, (∀ v, address ≠ bankAddress B j v) → address ≠ sourceRecord i B reserve N j+6 →
    (∀ r < N, address ≠ sourceRecord i B reserve N j+8+2*r) →
    (∀ r ≤ reserve, address ≠ (scaleLayout B i.n (scaleCount i) reserve N).reports+2*r) →
    (∀ r, address ≠ (scaleLayout B i.n (scaleCount i) reserve N).utility+2*r+1) →
    t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule268
section FlattenedModule269
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule269
section FlattenedModule270
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule270
section FlattenedModule271
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule271
section FlattenedModule272
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def sourceUpdate (p : Program) : Cmd := .seq prepareUpdate
  (ObservedSourceCall.transaction (registerBound p.code) p.update p)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule272
section FlattenedModule273
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule273
section FlattenedModule274
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
noncomputable def scaleUpdateCharge (p : Program) (m : ℕ) : ℕ :=
  3*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth m+32))+
    observedDispatchCharge p.code+8*registerBound p.code+160
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule274
section FlattenedModule275
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule275
section FlattenedModule276
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule276
section FlattenedModule277
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def scaleUpdate (p : Program) : Cmd := .seq (sourceUpdate p) ReportConsume.code
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule277
section FlattenedModule278
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule278
section FlattenedModule279
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def FamilyMemory (i : Input) (p : Program) (B reserve : ℕ) (machines : Fin (scaleCount i) → Machine)
    (a : AdapterState i) (s : Data) : Prop :=
  ∀ q : Fin (scaleCount i), ScaleMemory i p B q.val (sourceRecord i B reserve (registerBound p.code) q.val)
    (cacheAt (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).caches i.n q.val)
    (nextRecord (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).records
      (2*registerBound p.code+8) (scaleCount i) q.val) (machines q) (a.maxima q) s
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule279
section FlattenedModule280
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
def forbiddenNat : List ℕ := [94,58,128,132,38,20,130,22,24,196,30,32,40,42,44,46,186,184,188,180,182,154,210,212,214,198]
end ReportConsume
def PersistentControl (k : ℕ) : Prop := (60 ≤ k ∧ k ≤ 104 ∧ k ≠ 94) ∨ k ∈ ([106,110,134] : List ℕ)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule280
section FlattenedModule281
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
noncomputable def scaleReports (i : Input) (p : Program) (B : ℕ) (e : Fin i.k)
    (before after : Fin (scaleCount i) → Machine) (j : Fin (scaleCount i)) : List ℕ :=
  physicalTraceWrites B j.val p (deletionMachine p (before j) e.val) ((after j).work-(before j).work)
noncomputable def scaleEvents (i : Input) (p : Program) (B : ℕ) (e : Fin i.k)
    (before after : Fin (scaleCount i) → Machine) (j : Fin (scaleCount i)) : List (AdapterEvent i) :=
  ReportConsume.allEvents i B j (after j) (scaleReports i p B e before after j)
noncomputable def updateEventsPrefix (i : Input) (p : Program) (B : ℕ) (e : Fin i.k)
    (before after : Fin (scaleCount i) → Machine) : ℕ → List (AdapterEvent i)
  | 0 => []
  | d+1 => updateEventsPrefix i p B e before after d++
      (if h : d < scaleCount i then scaleEvents i p B e before after ⟨d,h⟩ else [])
noncomputable def updateWorkPrefix (i : Input) (before after : Fin (scaleCount i) → Machine) : ℕ → ℕ
  | 0 => 0
  | d+1 => updateWorkPrefix i before after d+
      (if h : d < scaleCount i then (after ⟨d,h⟩).work-(before ⟨d,h⟩).work else 0)
noncomputable def updateReportsPrefix (i : Input) (p : Program) (B : ℕ) (e : Fin i.k)
    (before after : Fin (scaleCount i) → Machine) : ℕ → ℕ
  | 0 => 0
  | d+1 => updateReportsPrefix i p B e before after d+
      (if h : d < scaleCount i then (scaleReports i p B e before after ⟨d,h⟩).length else 0)
noncomputable def updateMachinesPrefix (i : Input) (before after : Fin (scaleCount i) → Machine)
    (d : ℕ) (q : Fin (scaleCount i)) : Machine := if q.val < d then after q else before q
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule281
section FlattenedModule282
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace UpdateTraversal
def startAtoms (N : ℕ) : List Atom := [⟨.nadd 78 5 56,trivial⟩,⟨.nadd 106 84 56,trivial⟩,
  ⟨.natural 110 0,trivial⟩,⟨.natural 134 (2*N+8),trivial⟩]
def start (N : ℕ) : Cmd := Structured.sequence ((startAtoms N).map Cmd.atom)
noncomputable def started (N : ℕ) (s : Data) : Data := (startAtoms N).foldl (fun t a => a.effect t) s
def advance : Cmd := .seq (nadd 106 106 134) (nadd 110 110 26)
noncomputable def advanced (s : Data) : Data :=
  {s with natReg := Function.update (Function.update s.natReg 106 (s.natReg 106+s.natReg 134)) 110 (s.natReg 110+s.natReg 26)}
end UpdateTraversal
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule282
section FlattenedModule283
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
structure UpdatePrefix (i : Input) (p : Program) (B reserve : ℕ) (e : Fin i.k)
    (before after : Fin (scaleCount i) → Machine) (initial : AdapterState i)
    (done : ℕ) (xs : List (Fin i.n)) (s : Data) : Prop where
  bound : done ≤ scaleCount i
  globals : Globals i B (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).utility s
  controls : Controls B i.n (scaleCount i) reserve (registerBound p.code) s
  adapter : AdapterMemory i B reserve (registerBound p.code)
    (adapterTrace i initial (updateEventsPrefix i p B e before after done)) xs s
  family : FamilyMemory i p B reserve (updateMachinesPrefix i before after done)
    (adapterTrace i initial (updateEventsPrefix i p B e before after done)) s
  record : s.natReg 106 = sourceRecord i B reserve (registerBound p.code) done
  index : s.natReg 110 = done
  stride : s.natReg 134 = 2*registerBound p.code+8
  deletion : s.natReg 78 = e.val
  tail : ∀ r, registerBound p.code ≤ r → s.natReg (shadowReg r) = 0 ∧ s.realReg (shadowReg r) = 0
def scaleUpdateBody (p : Program) : Cmd := .seq (scaleUpdate p) UpdateTraversal.advance
def scaleUpdateLoop (p : Program) : Cmd := .loop (.natLess 110 80) (scaleUpdateBody p)
def scaleUpdateAll (p : Program) : Cmd := .seq (UpdateTraversal.start (registerBound p.code)) (scaleUpdateLoop p)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule283
section FlattenedModule284
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule284
section FlattenedModule285
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule285
section FlattenedModule286
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule286
section FlattenedModule287
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule287
section FlattenedModule288
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
noncomputable def boundaryAdapter (i : Input) (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (ptr : Fin i.n → ℕ) : AdapterState i where
  maxima := b
  pointer := ptr
  dirty := ∅
  output := selected i b ptr
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule288
section FlattenedModule289
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.DirtyCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.DirtyCommit
end FlattenedModule289
section FlattenedModule290
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule290
section FlattenedModule291
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def normalUpdate (p : Program) : Cmd := .seq (scaleUpdateAll p) DirtyCommit.code
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule291
section FlattenedModule292
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
noncomputable def externalInput (s : Data) (e : ℕ) : Data := {s with natReg := Function.update s.natReg 5 e}
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule292
section FlattenedModule293
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def normalProgram (coefficient : ℕ) (p : Program) : Program :=
  program (normalInitialize coefficient p) (normalUpdate p)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule293
section FlattenedModule294
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule294
section FlattenedModule295
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
structure SourceGuide (p : Program) (C : ℝ) (a : ℕ → ℝ) (i : Input) (ds : List (Fin i.k)) where
  machine : Fin (ds.length+1) → Machine
  initial : Ends p (initialMachine p i) (machine 0)
  update : ∀ t : Fin ds.length, Ends p (deletionMachine p (machine t.castSucc) (ds[t]).val) (machine t.succ)
  source : ∀ t, stored (machine t) i.source.val = 0
  normal : ∀ t (v : Fin i.n), (machine t).natMem v.val ≤ 1 ∧ ((machine t).natMem v.val = 0 → 0 ≤ (machine t).realMem v.val)
  accurate : ∀ t (v : Fin i.n), i.dist (ds.take t.val) v ≤ stored (machine t) v.val ∧
    stored (machine t) v.val ≤ ENNReal.ofReal (1+i.accuracy)*i.dist (ds.take t.val) v ∧
    (stored (machine t) v.val = ⊤ ↔ ¬Reachable i.graph (live (ds.take t.val)) i.source v)
  work : ∀ t, ((machine t).work : ℝ) ≤ C*i.size*a i.size/i.accuracy
  tail : ∀ t, ZeroRegisterTail (registerBound p.code) (machine t)
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule295
section FlattenedModule296
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule296
section FlattenedModule297
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule297
section FlattenedModule298
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule298
section FlattenedModule299
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
abbrev BarrierGuides (i : Input) (p : Program) (C : ℝ) (a : ℕ → ℝ) (ds : List (Fin i.k)) :=
  ∀ q : Fin (scaleCount i), SourceGuide p C a (barrierInput i q.val) ds
noncomputable def sourceAt {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) (t : Fin (ds.length+1)) (q : Fin (scaleCount i)) : Machine := (guides q).machine t
noncomputable def historyIndices {i : Input} (ds : List (Fin i.k)) (r : ℕ) : Finset (Fin (ds.length+1)) :=
  Finset.univ.filter (fun t => t.val ≤ r)
noncomputable def historySup {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) (r : ℕ) (q : Fin (scaleCount i)) (v : Fin i.n) : ℝ≥0∞ :=
  (historyIndices ds r).sup (fun t => stored (sourceAt guides t q) v.val)
structure HistoryBoundary {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) (t : Fin (ds.length+1))
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (ptr : Fin i.n → ℕ) : Prop where
  current : ∀ q (v : Fin i.n), stored (sourceAt guides t q) v.val ≤ b q v
  upper : ∀ q v, b q v ≤ historySup guides t.val q v
  valid : ∀ v, PointerValid i b v (ptr v)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule299
section FlattenedModule300
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule300
section FlattenedModule301
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule301
section FlattenedModule302
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
def GoodBoundary (i : Input) (ds : List (Fin i.k)) (t : ℕ) (c : Machine) : Prop :=
  stored c i.source.val = 0 ∧
    (∀ v : Fin i.n, c.natMem v.val ≤ 1 ∧ (c.natMem v.val = 0 → 0 ≤ c.realMem v.val)) ∧
    ∀ v : Fin i.n, i.dist (ds.take t) v ≤ stored c v.val ∧
      stored c v.val ≤ ENNReal.ofReal (1+i.accuracy)*i.dist (ds.take t) v ∧
      (stored c v.val = ⊤ ↔ ¬Reachable i.graph (live (ds.take t)) i.source v)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule302
section FlattenedModule303
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule303
section FlattenedModule304
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
noncomputable def sourceSumWork {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) (t : Fin (ds.length+1)) : ℕ := ∑ q, (sourceAt guides t q).work
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule304
section FlattenedModule305
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
noncomputable def normalMaintenanceCharge (p : Program) (m : ℕ) : ℕ := scaleUpdateCharge p m+36+7
noncomputable def sourceInitialCache {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) (q : Fin (scaleCount i)) (v : Fin i.n) : ℝ≥0∞ := stored (sourceAt guides 0 q) v.val
noncomputable def sourceInitialPointer {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) : Fin i.n → ℕ := initialPointers i (sourceInitialCache guides)
noncomputable def initialPointerEnergy {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) : ℕ := pointerEnergy i (boundaryAdapter i (sourceInitialCache guides) (sourceInitialPointer guides))
structure NormalRunState (i : Input) (p : Program) (C : ℝ) (a : ℕ → ℝ) (ds : List (Fin i.k))
    (guides : BarrierGuides i p C a ds) (coefficient : ℕ) (initial : Machine) (t : Fin (ds.length+1)) where
  machine : Machine
  cache : Fin (scaleCount i) → Fin i.n → ℝ≥0∞
  pointer : Fin i.n → ℕ
  memory : NormalMemory i p (i.n+3*i.k+2) (coefficient*i.size^3+1) (sourceAt guides t) cache pointer (data machine)
  history : HistoryBoundary guides t cache pointer
  log : List Machine
  run : OnlineRun (normalProgram coefficient p) i (ds.take t.val) log
  last : log.getLast? = some machine
  good : ∀ j c, log[j]? = some c → GoodBoundary i ds j c
  credit : machine.work+6*t.val+13*initialPointerEnergy guides+normalMaintenanceCharge p i.size*sourceSumWork guides 0 ≤
    initial.work+normalMaintenanceCharge p i.size*sourceSumWork guides t+13*pointerEnergy i (boundaryAdapter i cache pointer)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule305
section FlattenedModule306
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule306
section FlattenedModule307
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule307
section FlattenedModule308
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
noncomputable def normalUpdateConstant (p : Program) : ℕ :=
  3*dispatchCharge ScaledCeiling.ceilingProgram.code+observedDispatchCharge p.code+8*registerBound p.code+212
noncomputable def normalProgramConstant (p : Program) (coefficient : ℕ) (C : ℝ) : ℝ :=
  ((normalInitConstant p coefficient : ℝ)+(normalUpdateConstant p : ℝ)+14)*(1+1024*C)
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule308
section FlattenedModule309
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end FlattenedModule309
section FlattenedModule310
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RadixQueue
inductive Trie : ℕ → Type
  | empty {height : ℕ} : Trie height
  | leaf (items : List ℕ) : Trie 0
  | node {height : ℕ} (left right : Trie height) : Trie (height+1)
  deriving Repr
def count {height : ℕ} : Trie height → ℕ
  | .empty => 0
  | .leaf items => items.length
  | .node left right => count left + count right
def entries {height : ℕ} : Trie height → ℕ → Multiset (ℕ × ℕ)
  | .empty, _ => 0
  | .leaf items, low => (items.map (fun v => (low,v)) : Multiset (ℕ × ℕ))
  | @Trie.node h left right, low => entries left low + entries right (low+2^h)
def insert : (height key value : ℕ) → Trie height → Trie height
  | 0, _, value, .empty => .leaf [value]
  | 0, _, value, .leaf items => .leaf (value::items)
  | height+1, key, value, .empty =>
      if key < 2^height then .node (insert height key value .empty) .empty
      else .node .empty (insert height (key-2^height) value .empty)
  | height+1, key, value, .node left right =>
      if key < 2^height then .node (insert height key value left) right
      else .node left (insert height (key-2^height) value right)
end DecrAlmostLinearSSSP.Decremental.RadixQueue
end FlattenedModule310
section FlattenedModule311
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RadixQueue
def pop {height : ℕ} : Trie height → Option (ℕ × ℕ × Trie height)
  | .empty => none
  | .leaf [] => none
  | .leaf (value::rest) => some (0,value,.leaf rest)
  | @Trie.node h left right =>
    if count left = 0 then
      match pop right with
      | some (key,value,next) => some (2^h+key,value,.node left next)
      | none => none
    else match pop left with
      | some (key,value,next) => some (key,value,.node next right)
      | none => none
end DecrAlmostLinearSSSP.Decremental.RadixQueue
end FlattenedModule311
section FlattenedModule312
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RadixQueue
def popVisits {height : ℕ} : Trie height → ℕ
  | .empty => 1
  | .leaf _ => 1
  | .node left right => 1 + if count left = 0 then popVisits right else popVisits left
end DecrAlmostLinearSSSP.Decremental.RadixQueue
end FlattenedModule312
section FlattenedModule313
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace Payload
def root : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (address,_)::_ => address
def footprint : List (ℕ × ℕ) → Finset ℕ
  | [] => ∅
  | (address,_)::rest => Finset.Ico address (address+2) ∪ footprint rest
def Image (s : Data) : List (ℕ × ℕ) → Prop
  | [] => True
  | (address,value)::rest => s.natMem address = value ∧ s.natMem (address+1) = root rest ∧ Image s rest
def Separated : List (ℕ × ℕ) → Prop
  | [] => True
  | (address,_)::rest => 0 < address ∧ Disjoint (Finset.Ico address (address+2)) (footprint rest) ∧ Separated rest
end Payload
inductive LocatedTrie : ℕ → Type
  | empty {height : ℕ} : LocatedTrie height
  | leaf (address : ℕ) (items : List (ℕ × ℕ)) : LocatedTrie 0
  | node {height : ℕ} (address : ℕ) (left right : LocatedTrie height) : LocatedTrie (height+1)
def LocatedTrie.root {height : ℕ} : LocatedTrie height → ℕ
  | .empty => 0
  | .leaf address _ => address
  | .node address _ _ => address
def LocatedTrie.abstract {height : ℕ} : LocatedTrie height → RadixQueue.Trie height
  | .empty => .empty
  | .leaf _ items => .leaf (items.map Prod.snd)
  | .node _ left right => .node left.abstract right.abstract
def LocatedTrie.footprint {height : ℕ} : LocatedTrie height → Finset ℕ
  | .empty => ∅
  | .leaf address items => Finset.Ico address (address+4) ∪ Payload.footprint items
  | .node address left right => Finset.Ico address (address+4) ∪ (left.footprint ∪ right.footprint)
def LocatedTrie.Image (s : Data) {height : ℕ} : LocatedTrie height → Prop
  | .empty => True
  | .leaf address items => s.natMem address = items.length ∧ s.natMem (address+3) = Payload.root items ∧ Payload.Image s items
  | .node address left right => s.natMem address = RadixQueue.count left.abstract+RadixQueue.count right.abstract ∧
      s.natMem (address+1) = left.root ∧ s.natMem (address+2) = right.root ∧ left.Image s ∧ right.Image s
def LocatedTrie.Separated {height : ℕ} : LocatedTrie height → Prop
  | .empty => True
  | .leaf address items => 0 < address ∧ Disjoint (Finset.Ico address (address+4)) (Payload.footprint items) ∧ Payload.Separated items
  | .node address left right => 0 < address ∧ Disjoint (Finset.Ico address (address+4)) (left.footprint ∪ right.footprint) ∧
      Disjoint left.footprint right.footprint ∧ left.Separated ∧ right.Separated
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule313
section FlattenedModule314
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
namespace LocatedTrie
def Bounded {height : ℕ} (tree : LocatedTrie height) (low high : ℕ) : Prop :=
  ∀ address ∈ tree.footprint, low ≤ address ∧ address < high
end LocatedTrie
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule314
section FlattenedModule315
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Allocate
open Structured
structure Node where
  count : ℕ
  left : ℕ
  right : ℕ
  payload : ℕ
  deriving DecidableEq
def NodeImage (s : Data) (base : ℕ) (node : Node) : Prop :=
  s.natMem base = node.count ∧ s.natMem (base+1) = node.left ∧
    s.natMem (base+2) = node.right ∧ s.natMem (base+3) = node.payload
def nodeAtoms : List Atom := [⟨.nadd 272 244 56,trivial⟩,⟨.nadd 274 244 56,trivial⟩,
  ⟨.storeN 274 56,trivial⟩,⟨.nadd 274 274 26,trivial⟩,⟨.storeN 274 56,trivial⟩,
  ⟨.nadd 274 274 26,trivial⟩,⟨.storeN 274 56,trivial⟩,⟨.nadd 274 274 26,trivial⟩,
  ⟨.storeN 274 56,trivial⟩,⟨.nadd 244 274 26,trivial⟩]
def node : Cmd := Structured.sequence (nodeAtoms.map Cmd.atom)
noncomputable def nodeData (s : Data) : Data := nodeAtoms.foldl (fun t a => a.effect t) s
def itemAtoms : List Atom := [⟨.nadd 272 244 56,trivial⟩,⟨.storeN 244 262,trivial⟩,
  ⟨.nadd 274 244 26,trivial⟩,⟨.storeN 274 276,trivial⟩,⟨.nadd 244 274 26,trivial⟩]
def item : Cmd := Structured.sequence (itemAtoms.map Cmd.atom)
noncomputable def itemData (s : Data) : Data := itemAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Exact.Allocate
end FlattenedModule315
section FlattenedModule316
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
def ensureNode : Cmd := .seq (loadN 264 278) (.branch (.natLess 264 26)
  (.seq Allocate.node (.seq (storeN 278 272) (nadd 264 272 56))) .skip)
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule316
section FlattenedModule317
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
def LocatedTrie.materialize {height : ℕ} (tree : LocatedTrie height) (fresh : ℕ) : LocatedTrie height :=
  match height,tree with
  | 0,.empty => .leaf fresh []
  | _+1,.empty => .node fresh .empty .empty
  | _,.leaf address items => .leaf address items
  | _,.node address left right => .node address left right
namespace TriePush
noncomputable def loaded (s : Data) : Data := {s with natReg := Function.update s.natReg 264 (s.natMem (s.natReg 278))}
end TriePush
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule317
section FlattenedModule318
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule318
section FlattenedModule319
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
def incrementAtoms : List Atom := [⟨.loadN 266 264,trivial⟩,⟨.nadd 266 266 26,trivial⟩,⟨.storeN 264 266,trivial⟩]
def increment : Cmd := Structured.sequence (incrementAtoms.map Cmd.atom)
noncomputable def incremented (s : Data) : Data := incrementAtoms.foldl (fun t a => a.effect t) s
def leftChild : Cmd := .seq (natural 282 1) (nadd 278 264 282)
def rightChild : Cmd := Structured.sequence [natural 282 2,nadd 278 264 282,nsub 260 260 268]
def descend : Cmd := .seq (loadN 268 258)
  (.seq (.branch (.natLess 260 268) leftChild rightChild)
    (.seq (nsub 256 256 26) (nsub 258 258 26)))
def body : Cmd := .seq ensureNode (.seq increment descend)
def loop : Cmd := .loop (.natLess 56 256) body
def leafAtoms : List Atom := [⟨.natural 282 3,trivial⟩,⟨.nadd 280 264 282,trivial⟩,⟨.loadN 276 280,trivial⟩]
def leafPrepare : Cmd := Structured.sequence (leafAtoms.map Cmd.atom)
noncomputable def leafPrepared (s : Data) : Data := leafAtoms.foldl (fun t a => a.effect t) s
def leaf : Cmd := .seq ensureNode (.seq increment (.seq leafPrepare (.seq Allocate.item (storeN 280 272))))
def core : Cmd := .seq loop leaf
def startAtoms : List Atom := [⟨.nadd 256 236 56,trivial⟩,⟨.nadd 258 238 56,trivial⟩,⟨.nadd 278 246 56,trivial⟩]
def start : Cmd := Structured.sequence (startAtoms.map Cmd.atom)
noncomputable def started (s : Data) : Data := startAtoms.foldl (fun t a => a.effect t) s
def code : Cmd := .seq start core
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule319
section FlattenedModule320
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
def leafFinish : Cmd := .seq increment (.seq leafPrepare (.seq Allocate.item (storeN 280 272)))
noncomputable def leafFinished (s : Data) : Data :=
  let u := incremented s
  let v := leafPrepared u
  let w := Allocate.itemData v
  {w with natMem := Function.update w.natMem (w.natReg 280) (w.natReg 272)}
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule320
section FlattenedModule321
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule321
section FlattenedModule322
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule322
section FlattenedModule323
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
def NoRealStore : Instruction → Prop
  | .store _ _ => False
  | _ => True
def NoRealMemory : Cmd → Prop
  | .skip => True
  | .atom a => NoRealStore a.instruction
  | .seq a b | .branch _ a b => NoRealMemory a ∧ NoRealMemory b
  | .loop _ a => NoRealMemory a
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule323
section FlattenedModule324
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
def registers : Finset ℕ := {244,256,258,260,264,266,268,272,274,276,278,280,282}
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule324
section FlattenedModule325
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
noncomputable def descendLoaded (s : Data) : Data :=
  {s with natReg := Function.update s.natReg 268 (s.natMem (s.natReg 258))}
noncomputable def descendBranched (s : Data) : Data :=
  let u := descendLoaded s
  if s.natReg 260 < s.natMem (s.natReg 258) then
    let v := {u with natReg := Function.update u.natReg 282 1}
    {v with natReg := Function.update v.natReg 278 (v.natReg 264+v.natReg 282)}
  else
    let v := {u with natReg := Function.update u.natReg 282 2}
    let w := {v with natReg := Function.update v.natReg 278 (v.natReg 264+v.natReg 282)}
    {w with natReg := Function.update w.natReg 260 (w.natReg 260-w.natReg 268)}
noncomputable def descended (s : Data) : Data :=
  let u := descendBranched s
  let v := {u with natReg := Function.update u.natReg 256 (u.natReg 256-u.natReg 26)}
  {v with natReg := Function.update v.natReg 258 (v.natReg 258-v.natReg 26)}
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule325
section FlattenedModule326
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
def branch {h : ℕ} (right : Bool) (address : ℕ) (chosen other : LocatedTrie h) : LocatedTrie (h+1) :=
  if right then .node address other chosen else .node address chosen other
def childOffset (right : Bool) : ℕ := if right then 2 else 1
def otherOffset (right : Bool) : ℕ := if right then 1 else 2
end DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end FlattenedModule326
section FlattenedModule327
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule327
section FlattenedModule328
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end FlattenedModule328
section FlattenedModule329
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
structure Result {h : ℕ} (tree : LocatedTrie h) (low : ℕ) (s : Data) where
  cost : ℕ
  final : Data
  next : LocatedTrie h
  eval : Eval core s cost final
  costBound : cost ≤ 40*(h+1)
  slot : final.natMem (s.natReg 278) = next.root
  image : next.Image final
  separated : next.Separated
  bounded : next.Bounded low (final.natReg 244)
  abstract : next.abstract = RadixQueue.insert h (s.natReg 260) (s.natReg 262) tree.abstract
  alloc : s.natReg 244 ≤ final.natReg 244
  footprint : next.footprint ⊆ tree.footprint ∪ Finset.Ico (s.natReg 244) (final.natReg 244)
  realMem : final.realMem = s.realMem
  frame : ∀ address, address ≠ s.natReg 278 → address ∉ tree.footprint →
    (address < s.natReg 244 ∨ final.natReg 244 ≤ address) → final.natMem address = s.natMem address
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule329
section FlattenedModule330
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
structure Ready {h : ℕ} (tree : LocatedTrie h) (low base : ℕ) (s : Data) : Prop where
  zero : s.natReg 56 = 0
  unit : s.natReg 26 = 1
  height : s.natReg 256 = h
  image : tree.Image s
  separated : tree.Separated
  bounded : tree.Bounded low (s.natReg 244)
  slot : s.natMem (s.natReg 278) = tree.root
  slotLow : low ≤ s.natReg 278
  slotHigh : s.natReg 278 < s.natReg 244
  slotNot : s.natReg 278 ∉ tree.footprint
  powers : ∀ j<h, s.natMem (base+j) = 2^j
  powersHigh : base+h ≤ low
  powerPtr : h ≠ 0 → s.natReg 258+1 = base+h
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule330
section FlattenedModule331
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule331
section FlattenedModule332
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule332
section FlattenedModule333
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule333
section FlattenedModule334
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end FlattenedModule334
section FlattenedModule335
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
def decrementAtoms : List Atom := [⟨.loadN 266 264,trivial⟩,⟨.nsub 266 266 26,trivial⟩,⟨.storeN 264 266,trivial⟩]
def decrement : Cmd := Structured.sequence (decrementAtoms.map Cmd.atom)
noncomputable def decremented (s : Data) : Data := decrementAtoms.foldl (fun t a => a.effect t) s
def leftPointerAtoms : List Atom := [⟨.natural 282 1,trivial⟩,⟨.nadd 278 264 282,trivial⟩,⟨.loadN 278 278,trivial⟩]
def leftPointer : Cmd := Structured.sequence (leftPointerAtoms.map Cmd.atom)
noncomputable def leftPointerData (s : Data) : Data := leftPointerAtoms.foldl (fun t a => a.effect t) s
def leftCount : Cmd := .branch (.natLess 56 278) (loadN 284 278) (natural 284 0)
noncomputable def leftCountData (s : Data) : Data :=
  {s with natReg := Function.update s.natReg 284 (if 0 < s.natReg 278 then s.natMem (s.natReg 278) else 0)}
def chooseLeft : Cmd := nadd 264 278 56
def rightAtoms : List Atom := [⟨.natural 282 2,trivial⟩,⟨.nadd 278 264 282,trivial⟩,
  ⟨.loadN 264 278,trivial⟩,⟨.loadN 268 258,trivial⟩,⟨.nadd 260 260 268,trivial⟩]
def chooseRight : Cmd := Structured.sequence (rightAtoms.map Cmd.atom)
noncomputable def rightData (s : Data) : Data := rightAtoms.foldl (fun t a => a.effect t) s
def choose : Cmd := .branch (.natLess 56 284) chooseLeft chooseRight
noncomputable def chosen (s : Data) : Data :=
  if 0 < s.natReg 284 then {s with natReg := Function.update s.natReg 264 (s.natReg 278+s.natReg 56)} else rightData s
def descend : Cmd := .seq leftPointer (.seq leftCount (.seq choose (.seq (nsub 256 256 26) (nsub 258 258 26))))
noncomputable def descended (s : Data) : Data :=
  let u := chosen (leftCountData (leftPointerData s))
  let v := {u with natReg := Function.update u.natReg 256 (u.natReg 256-u.natReg 26)}
  {v with natReg := Function.update v.natReg 258 (v.natReg 258-v.natReg 26)}
def body : Cmd := .seq decrement descend
def loop : Cmd := .loop (.natLess 56 256) body
def leafAtoms : List Atom := [⟨.natural 282 3,trivial⟩,⟨.nadd 286 264 282,trivial⟩,
  ⟨.loadN 288 286,trivial⟩,⟨.loadN 262 288,trivial⟩,⟨.nadd 288 288 26,trivial⟩,
  ⟨.loadN 288 288,trivial⟩,⟨.storeN 286 288,trivial⟩]
def leafFinish : Cmd := Structured.sequence (leafAtoms.map Cmd.atom)
noncomputable def leafFinished (s : Data) : Data := leafAtoms.foldl (fun t a => a.effect t) s
def leaf : Cmd := .seq decrement leafFinish
noncomputable def leafData (s : Data) : Data := leafFinished (decremented s)
def core : Cmd := .seq loop leaf
def startAtoms : List Atom := [⟨.nadd 256 236 56,trivial⟩,⟨.nadd 258 238 56,trivial⟩,
  ⟨.natural 260 0,trivial⟩,⟨.loadN 264 246,trivial⟩]
def start : Cmd := Structured.sequence (startAtoms.map Cmd.atom)
noncomputable def started (s : Data) : Data := startAtoms.foldl (fun t a => a.effect t) s
def code : Cmd := .seq start core
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end FlattenedModule335
section FlattenedModule336
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
def registers : Finset ℕ := {256,258,260,262,264,266,268,278,282,284,286,288}
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end FlattenedModule336
section FlattenedModule337
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end FlattenedModule337
section FlattenedModule338
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end FlattenedModule338
section FlattenedModule339
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
structure Ready {h : ℕ} (tree : LocatedTrie h) (low base : ℕ) (s : Data) : Prop where
  zero : s.natReg 56 = 0
  unit : s.natReg 26 = 1
  height : s.natReg 256 = h
  image : tree.Image s
  separated : tree.Separated
  bounded : tree.Bounded low (s.natReg 244)
  current : s.natReg 264 = tree.root
  positive : 0 < RadixQueue.count tree.abstract
  powers : ∀ j<h, s.natMem (base+j) = 2^j
  powersHigh : base+h ≤ low
  powerPtr : h ≠ 0 → s.natReg 258+1 = base+h
structure Result {h : ℕ} (tree : LocatedTrie h) (s : Data) where
  cost : ℕ
  final : Data
  next : LocatedTrie h
  key : ℕ
  eval : Eval core s cost final
  costBound : cost ≤ 30*(h+1)
  pop : RadixQueue.pop tree.abstract = some (key,final.natReg 262,next.abstract)
  keyReg : final.natReg 260 = s.natReg 260+key
  image : next.Image final
  separated : next.Separated
  root : next.root = tree.root
  footprint : next.footprint ⊆ tree.footprint
  realMem : final.realMem = s.realMem
  frame : ∀ address, address ∉ tree.footprint → final.natMem address = s.natMem address
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end FlattenedModule339
section FlattenedModule340
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace TriePop
end TriePop
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule340
section FlattenedModule341
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end FlattenedModule341
section FlattenedModule342
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end FlattenedModule342
section FlattenedModule343
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end FlattenedModule343
section FlattenedModule344
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma exists_power_above (bound : ℕ) : ∃ h : ℕ, bound < 2^h := by
  refine ⟨bound+1,?_⟩
  have hh : ∀ n : ℕ, n < 2^(n+1) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ];omega
  exact hh bound
noncomputable def height (bound : ℕ) : ℕ := Nat.find (exists_power_above bound)
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule344
section FlattenedModule345
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Powers
open Structured
def bodyAtoms : List Atom := [⟨.storeN 248 250,trivial⟩,⟨.nadd 248 248 26,trivial⟩,
  ⟨.nadd 250 250 250,trivial⟩,⟨.cast 250 250,trivial⟩,⟨.nadd 252 252 26,trivial⟩]
def body : Cmd := Structured.sequence (bodyAtoms.map Cmd.atom)
noncomputable def advanced (s : Data) : Data := bodyAtoms.foldl (fun t a => a.effect t) s
def loop : Cmd := .loop (.realLess 250 248) body
structure Prefix (bound base done : ℕ) (s : Data) : Prop where
  cutoff : s.realReg 248 = (bound : ℝ)+1
  pointer : s.natReg 248 = base+done
  power : s.natReg 250 = 2^done
  realPower : s.realReg 250 = (2 : ℝ)^done
  index : s.natReg 252 = done
  unit : s.natReg 26 = 1
  entries : ∀ j < done, s.natMem (base+j) = 2^j
end DecrAlmostLinearSSSP.Decremental.Exact.Powers
end FlattenedModule345
section FlattenedModule346
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Powers
open Structured
def prepareAtoms : List Atom := [⟨.nadd 248 234 56,trivial⟩,⟨.natural 250 1,trivial⟩,
  ⟨.natural 252 0,trivial⟩,⟨.rational 250 1,trivial⟩,⟨.cast 224 66,trivial⟩,
  ⟨.cast 226 70,trivial⟩,⟨.mul 248 224 226,trivial⟩,⟨.rational 228 1,trivial⟩,⟨.add 248 248 228,trivial⟩]
def prepare : Cmd := Structured.sequence (prepareAtoms.map Cmd.atom)
noncomputable def prepared (s : Data) : Data := prepareAtoms.foldl (fun t a => a.effect t) s
def code : Cmd := .seq prepare loop
end DecrAlmostLinearSSSP.Decremental.Exact.Powers
end FlattenedModule346
section FlattenedModule347
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Layout
open Structured
structure Addresses where
  heads : ℕ
  settled : ℕ
  active : ℕ
  distances : ℕ
  nodes : ℕ
  powers : ℕ
def addresses (B n k : ℕ) : Addresses := ⟨B+1,B+1+n,B+1+2*n,B+1+2*n+k,B+1+3*n+k,B+1+3*n+5*k⟩
def atoms : List Atom := [⟨.nadd 224 74 26,trivial⟩,⟨.nadd 226 224 66,trivial⟩,
  ⟨.nadd 228 226 66,trivial⟩,⟨.nadd 230 228 68,trivial⟩,⟨.nadd 232 230 66,trivial⟩,
  ⟨.nadd 234 68 68,trivial⟩,⟨.nadd 234 234 234,trivial⟩,⟨.nadd 234 232 234,trivial⟩]
def code : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def result (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
structure Image (l : Addresses) (s : Data) : Prop where
  heads : s.natReg 224 = l.heads
  settled : s.natReg 226 = l.settled
  active : s.natReg 228 = l.active
  distances : s.natReg 230 = l.distances
  nodes : s.natReg 232 = l.nodes
  powers : s.natReg 234 = l.powers
end DecrAlmostLinearSSSP.Decremental.Exact.Layout
end FlattenedModule347
section FlattenedModule348
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Clear
open Structured
def body : Cmd := .seq (storeN 290 56) (nadd 290 290 26)
def code : Cmd := .loop (.natLess 290 292) body
noncomputable def advanced (s : Data) : Data :=
  {s with
    natReg := Function.update s.natReg 290 (s.natReg 290+s.natReg 26)
    natMem := Function.update s.natMem (s.natReg 290) (s.natReg 56)}
end DecrAlmostLinearSSSP.Decremental.Exact.Clear
end FlattenedModule348
section FlattenedModule349
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def cappedDistance {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (B : ℝ) (u v : Fin n) : ℝ :=
  (min (ENNReal.ofReal B) (distance g active (fun e => ENNReal.ofReal (w e)) u v)).toReal
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule349
section FlattenedModule350
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule350
section FlattenedModule351
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
structure LabelInvariant {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k)) (w : Fin k → ℕ)
    (source : Fin n) (tentative : Fin n → Option ℕ) (settled : Finset (Fin n)) (queue : Multiset (ℕ × Fin n)) : Prop where
  sourceZero : tentative source = some 0
  pathBound : ∀ v d, tentative v = some d → distance g active (fun e => (w e : ℝ≥0∞)) source v ≤ d
  exactSettled : ∀ v ∈ settled, ∃ d, tentative v = some d ∧ distance g active (fun e => (w e : ℝ≥0∞)) source v = d
  belowQueue : ∀ v ∈ settled, ∀ d, tentative v = some d → ∀ item ∈ queue, d ≤ item.1
  frontier : ∀ e ∈ active, g.tail e ∈ settled → ∃ dt dh, tentative (g.tail e) = some dt ∧
    tentative (g.head e) = some dh ∧ dh ≤ dt+w e
  covered : ∀ v, v ∉ settled → ∀ d, tentative v = some d → (d,v) ∈ queue
  queueValid : ∀ item ∈ queue, ∃ d, tentative item.2 = some d ∧ d ≤ item.1
noncomputable def frontierPotential {n : ℕ} (tentative : Fin n → Option ℕ) (settled : Finset (Fin n)) (key : ℕ) (v : Fin n) : ℕ :=
  if v ∈ settled then (tentative v).getD 0 else key
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule351
section FlattenedModule352
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule352
section FlattenedModule353
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
noncomputable def initialTentative {n : ℕ} (source v : Fin n) : Option ℕ := if v = source then some 0 else none
noncomputable def tentativeValue (value : Option ℕ) : ℝ≥0∞ := match value with | none => ⊤ | some d => d
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule353
section FlattenedModule354
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule354
section FlattenedModule355
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule355
section FlattenedModule356
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
noncomputable def adjacency {n k : ℕ} (g : Digraph n k) : ℕ → Fin n → List (Fin k)
  | 0,_ => []
  | t+1,v => if ht : t<k then
      let e : Fin k := ⟨t,ht⟩
      if g.tail e = v then e::adjacency g t v else adjacency g t v
    else adjacency g t v
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule356
section FlattenedModule357
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
def clearPrepareAtoms : List Atom := [⟨.nadd 290 224 56,trivial⟩,⟨.nadd 292 224 66,trivial⟩]
def clearPrepare : Cmd := Structured.sequence (clearPrepareAtoms.map Cmd.atom)
noncomputable def clearPrepared (s : Data) : Data := clearPrepareAtoms.foldl (fun t a => a.effect t) s
def prepareAtoms : List Atom := [⟨.nadd 294 228 56,trivial⟩,⟨.nadd 296 232 56,trivial⟩,
  ⟨.nadd 298 66 56,trivial⟩,⟨.natural 300 0,trivial⟩]
def prepare : Cmd := Structured.sequence (prepareAtoms.map Cmd.atom)
noncomputable def prepared (s : Data) : Data := prepareAtoms.foldl (fun t a => a.effect t) s
def edgeAtoms : List Atom := [⟨.loadN 304 298,trivial⟩,⟨.nadd 306 224 304,trivial⟩,
  ⟨.loadN 308 306,trivial⟩,⟨.nadd 298 298 26,trivial⟩,⟨.loadN 310 298,trivial⟩,
  ⟨.nadd 298 298 26,trivial⟩,⟨.loadN 312 298,trivial⟩,⟨.nadd 298 298 26,trivial⟩,
  ⟨.storeN 296 310,trivial⟩,⟨.nadd 314 296 26,trivial⟩,⟨.storeN 314 294,trivial⟩,
  ⟨.nadd 314 314 26,trivial⟩,⟨.storeN 314 308,trivial⟩,⟨.nadd 314 314 26,trivial⟩,
  ⟨.storeN 314 312,trivial⟩,⟨.storeN 294 26,trivial⟩,⟨.storeN 306 296,trivial⟩,
  ⟨.nadd 294 294 26,trivial⟩,⟨.nadd 296 314 26,trivial⟩,⟨.nadd 300 300 26,trivial⟩]
def edge : Cmd := Structured.sequence (edgeAtoms.map Cmd.atom)
noncomputable def advanced (s : Data) : Data := edgeAtoms.foldl (fun t a => a.effect t) s
def loop : Cmd := .loop (.natLess 300 68) edge
def code : Cmd := .seq clearPrepare (.seq Clear.code (.seq prepare loop))
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end FlattenedModule357
section FlattenedModule358
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end FlattenedModule358
section FlattenedModule359
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace Adjacency
def nodeAddress (l : Layout.Addresses) {k : ℕ} (e : Fin k) : ℕ := l.nodes+4*e.val
def root (l : Layout.Addresses) {k : ℕ} : List (Fin k) → ℕ
  | [] => 0
  | e::_ => nodeAddress l e
structure Image (i : Input) (l : Layout.Addresses) (upto : ℕ) (s : Data) : Prop where
  heads : ∀ v : Fin i.n, s.natMem (l.heads+v.val) = root l (adjacency i.graph upto v)
  head : ∀ e : Fin i.k, e.val<upto → s.natMem (nodeAddress l e) = (i.graph.head e).val
  flagAddress : ∀ e : Fin i.k, e.val<upto → s.natMem (nodeAddress l e+1) = l.active+e.val
  next : ∀ e : Fin i.k, e.val<upto → s.natMem (nodeAddress l e+2) = root l (adjacency i.graph e.val (i.graph.tail e))
  weight : ∀ e : Fin i.k, e.val<upto → s.natMem (nodeAddress l e+3) = i.weight e
  active : ∀ e : Fin i.k, e.val<upto → s.natMem (l.active+e.val) = 1
def Tape (i : Input) (s : Data) : Prop := ∀ e : Fin i.k,
  s.natMem (i.n+3*e.val) = (i.graph.tail e).val ∧
  s.natMem (i.n+3*e.val+1) = (i.graph.head e).val ∧ s.natMem (i.n+3*e.val+2) = i.weight e
end Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule359
section FlattenedModule360
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
noncomputable def insertMemory (i : Input) (l : Layout.Addresses) (e : Fin i.k) (memory : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update memory (nodeAddress l e) (i.graph.head e).val)
      (nodeAddress l e+1) (l.active+e.val))
      (nodeAddress l e+2) (memory (l.heads+(i.graph.tail e).val)))
      (nodeAddress l e+3) (i.weight e)) (l.active+e.val) 1)
      (l.heads+(i.graph.tail e).val) (nodeAddress l e)
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end FlattenedModule360
section FlattenedModule361
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end FlattenedModule361
section FlattenedModule362
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
structure Prefix (i : Input) (upto : ℕ) (s : Data) : Prop where
  zero : s.natReg 56 = 0
  unit : s.natReg 26 = 1
  vertices : s.natReg 66 = i.n
  edges : s.natReg 68 = i.k
  layout : Layout.Image (Layout.addresses (i.n+3*i.k+2) i.n i.k) s
  tape : Adjacency.Tape i s
  image : Adjacency.Image i (Layout.addresses (i.n+3*i.k+2) i.n i.k) upto s
  activeCursor : s.natReg 294 = (Layout.addresses (i.n+3*i.k+2) i.n i.k).active+upto
  nodeCursor : s.natReg 296 = (Layout.addresses (i.n+3*i.k+2) i.n i.k).nodes+4*upto
  tapeCursor : s.natReg 298 = i.n+3*upto
  index : s.natReg 300 = upto
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end FlattenedModule362
section FlattenedModule363
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end FlattenedModule363
section FlattenedModule364
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
def setup : Cmd := .seq clearPrepare (.seq Clear.code prepare)
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end FlattenedModule364
section FlattenedModule365
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end FlattenedModule365
section FlattenedModule366
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
def resetPrepare : Cmd := natural 340 0
def resetBodyAtoms : List Atom := [⟨.storeN 340 26,trivial⟩,⟨.nadd 342 226 340,trivial⟩,
  ⟨.storeN 342 56,trivial⟩,⟨.nadd 340 340 26,trivial⟩]
def resetBody : Cmd := Structured.sequence (resetBodyAtoms.map Cmd.atom)
def resetLoop : Cmd := .loop (.natLess 340 66) resetBody
def rootAtoms : List Atom := [⟨.nadd 244 246 26,trivial⟩,⟨.storeN 246 56,trivial⟩,
  ⟨.storeN 72 56,trivial⟩,⟨.nadd 342 230 72,trivial⟩,⟨.storeN 342 56,trivial⟩,
  ⟨.store 72 56,trivial⟩,⟨.natural 260 0,trivial⟩,⟨.nadd 262 72 56,trivial⟩]
def rootSetup : Cmd := Structured.sequence (rootAtoms.map Cmd.atom)
def queueCount : Cmd := .seq (loadN 346 246)
  (.branch (.natLess 56 346) (loadN 348 346) (natural 348 0))
def improveAtoms : List Atom := [⟨.storeN 310 56,trivial⟩,⟨.storeN 322 326,trivial⟩,
  ⟨.cast 332 326,trivial⟩,⟨.store 310 332,trivial⟩,
  ⟨.nadd 260 326 56,trivial⟩,⟨.nadd 262 310 56,trivial⟩]
def improve : Cmd := .seq (Structured.sequence (improveAtoms.map Cmd.atom)) TriePush.code
def candidateAtoms : List Atom := [⟨.natural 336 3,trivial⟩,⟨.nadd 312 308 336,trivial⟩,
  ⟨.loadN 312 312,trivial⟩,⟨.nadd 326 304 312,trivial⟩,⟨.loadN 316 310,trivial⟩,
  ⟨.nadd 322 230 310,trivial⟩,⟨.loadN 324 322,trivial⟩]
def candidate : Cmd := .seq (Structured.sequence (candidateAtoms.map Cmd.atom))
  (.branch (.natLess 56 316) improve (.branch (.natLess 326 324) improve .skip))
def activeAtoms : List Atom := [⟨.natural 336 1,trivial⟩,⟨.nadd 314 308 336,trivial⟩,
  ⟨.loadN 314 314,trivial⟩,⟨.loadN 316 314,trivial⟩]
def targetSettledAtoms : List Atom := [⟨.nadd 318 226 310,trivial⟩,⟨.loadN 320 318,trivial⟩]
def nextAtoms : List Atom := [⟨.natural 336 2,trivial⟩,⟨.nadd 308 308 336,trivial⟩,⟨.loadN 308 308,trivial⟩]
def edgeBody : Cmd := .seq (loadN 310 308)
  (.seq (Structured.sequence (activeAtoms.map Cmd.atom))
    (.seq (.branch (.natLess 56 316)
      (.seq (Structured.sequence (targetSettledAtoms.map Cmd.atom))
        (.branch (.natLess 320 26) candidate .skip)) .skip)
      (Structured.sequence (nextAtoms.map Cmd.atom))))
def edgeLoop : Cmd := .loop (.natLess 56 308) edgeBody
def scanPrepareAtoms : List Atom := [⟨.nadd 308 224 306,trivial⟩,⟨.loadN 308 308,trivial⟩]
def settleAtoms : List Atom := [⟨.nadd 318 226 306,trivial⟩,⟨.storeN 318 26,trivial⟩]
def scan : Cmd := .seq (Structured.sequence (scanPrepareAtoms.map Cmd.atom))
  (.seq edgeLoop (Structured.sequence (settleAtoms.map Cmd.atom)))
def poppedAtoms : List Atom := [⟨.nadd 304 260 56,trivial⟩,⟨.nadd 306 262 56,trivial⟩,
  ⟨.nadd 318 226 306,trivial⟩,⟨.loadN 320 318,trivial⟩]
def body : Cmd := .seq TriePop.code (.seq (Structured.sequence (poppedAtoms.map Cmd.atom))
  (.seq (.branch (.natLess 320 26) scan .skip) queueCount))
def loop : Cmd := .loop (.natLess 56 348) body
def code : Cmd := .seq resetPrepare (.seq resetLoop (.seq rootSetup
  (.seq TriePush.code (.seq queueCount loop))))
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule366
section FlattenedModule367
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
namespace Adjacency
def Chain {k : ℕ} (l : Layout.Addresses) (s : Structured.Data) : List (Fin k) → Prop
  | [] => True
  | e::es => s.natMem (nodeAddress l e+2)=root l es ∧ Chain l s es
end Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule367
section FlattenedModule368
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
open Structured
structure StaticImage (i : Input) (l : Layout.Addresses) (s : Data) : Prop where
  heads : ∀ v : Fin i.n, s.natMem (l.heads+v.val) = root l (adjacency i.graph i.k v)
  head : ∀ e : Fin i.k, s.natMem (nodeAddress l e) = (i.graph.head e).val
  flagAddress : ∀ e : Fin i.k, s.natMem (nodeAddress l e+1) = l.active+e.val
  next : ∀ e : Fin i.k, s.natMem (nodeAddress l e+2) = root l (adjacency i.graph e.val (i.graph.tail e))
  weight : ∀ e : Fin i.k, s.natMem (nodeAddress l e+3) = i.weight e
def staticFootprint (i : Input) (l : Layout.Addresses) : Finset ℕ :=
  Finset.Ico l.heads (l.heads+i.n) ∪ Finset.Ico l.nodes (l.nodes+4*i.k)
def ActiveImage (i : Input) (l : Layout.Addresses) (deleted : List (Fin i.k)) (s : Data) : Prop :=
  ∀ e : Fin i.k, s.natMem (l.active+e.val) = if e∈live deleted then 1 else 0
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end FlattenedModule368
section FlattenedModule369
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
def TentativeImage (i : Input) (l : Layout.Addresses) (tentative : Fin i.n → Option ℕ) (s : Data) : Prop :=
  ∀ v : Fin i.n, match tentative v with
  | none => s.natMem v.val = 1
  | some d => s.natMem v.val = 0 ∧ s.natMem (l.distances+v.val) = d ∧ s.realMem v.val = (d : ℝ)
def SettledImage (i : Input) (l : Layout.Addresses) (settled : Finset (Fin i.n)) (s : Data) : Prop :=
  ∀ v : Fin i.n, s.natMem (l.settled+v.val) = if v∈settled then 1 else 0
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule369
section FlattenedModule370
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Layout
end DecrAlmostLinearSSSP.Decremental.Exact.Layout
end FlattenedModule370
section FlattenedModule371
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
def queueMap {n : ℕ} (q : Multiset (ℕ × Fin n)) : Multiset (ℕ × ℕ) := q.map (fun p => (p.1,p.2.val))
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule371
section FlattenedModule372
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
structure Image {n h : ℕ} (base slot : ℕ) (tree : LocatedTrie h) (queue : Multiset (ℕ × Fin n)) (s : Data) : Prop where
  zero : s.natReg 56 = 0
  unit : s.natReg 26 = 1
  height : s.natReg 236 = h
  powerPtr : h ≠ 0 → s.natReg 238+1 = base+h
  slotReg : s.natReg 246 = slot
  allocator : slot < s.natReg 244
  treeImage : tree.Image s
  separated : tree.Separated
  bounded : tree.Bounded (slot+1) (s.natReg 244)
  root : s.natMem slot = tree.root
  powers : ∀ j<h, s.natMem (base+j) = 2^j
  powersHigh : base+h ≤ slot
  entries : queueMap queue = RadixQueue.entries tree.abstract 0
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end FlattenedModule372
section FlattenedModule373
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end FlattenedModule373
section FlattenedModule374
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end FlattenedModule374
section FlattenedModule375
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
def layout (i : Input) : Layout.Addresses := Layout.addresses (i.n+3*i.k+2) i.n i.k
def heapBase (i : Input) : ℕ := (layout i).powers
noncomputable def heapHeight (i : Input) : ℕ := height (i.n*i.W)
noncomputable def heapSlot (i : Input) : ℕ := heapBase i+heapHeight i
structure Memory (i : Input) (deleted : List (Fin i.k)) (tentative : Fin i.n → Option ℕ)
    (settled : Finset (Fin i.n)) (tree : LocatedTrie (heapHeight i))
    (queue : Multiset (ℕ × Fin i.n)) (s : Data) : Prop where
  vertices : s.natReg 66=i.n
  edges : s.natReg 68=i.k
  source : s.natReg 72=i.source.val
  zeroR : s.realReg 56=0
  layoutRegs : Layout.Image (layout i) s
  graph : Adjacency.StaticImage i (layout i) s
  active : Adjacency.ActiveImage i (layout i) deleted s
  tentative : TentativeImage i (layout i) tentative s
  settled : SettledImage i (layout i) settled s
  heap : Heap.Image (heapBase i) (heapSlot i) tree queue s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule375
section FlattenedModule376
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule376
section FlattenedModule377
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end FlattenedModule377
section FlattenedModule378
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule378
section FlattenedModule379
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
noncomputable def counted (s : Data) : Data :=
  let pointer := s.natMem (s.natReg 246)
  {s with
    natReg := Function.update (Function.update s.natReg 346 pointer) 348
      (if 0<pointer then s.natMem pointer else 0)}
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule379
section FlattenedModule380
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
noncomputable def candidateData (s : Data) : Data := candidateAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule380
section FlattenedModule381
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end FlattenedModule381
section FlattenedModule382
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
noncomputable def improved (s : Data) : Data := improveAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule382
section FlattenedModule383
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule383
section FlattenedModule384
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule384
section FlattenedModule385
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule385
section FlattenedModule386
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule386
section FlattenedModule387
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule387
section FlattenedModule388
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
noncomputable def Improves (old : Option ℕ) (candidate : ℕ) : Prop :=
  match old with | none => True | some d => candidate < d
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule388
section FlattenedModule389
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule389
section FlattenedModule390
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
attribute [local instance] Classical.propDecidable
structure ScanState {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k)) (w : Fin k → ℕ)
    (source v : Fin n) (key : ℕ) (settled : Finset (Fin n)) (scanned : List (Fin k))
    (tentative : Fin n → Option ℕ) (queue : Multiset (ℕ × Fin n)) : Prop where
  labels : LabelInvariant g active w source tentative settled ((key,v)::ₘqueue)
  current : tentative v = some key
  minimum : ∀ item ∈ queue, key ≤ item.1
  relaxed : ∀ e ∈ scanned, e ∈ active → g.tail e=v →
    ∃ dh, tentative (g.head e)=some dh ∧ dh ≤ key+w e
noncomputable def relax {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k)) (w : Fin k → ℕ)
    (settled : Finset (Fin n)) (key : ℕ) (e : Fin k)
    (tentative : Fin n → Option ℕ) (queue : Multiset (ℕ × Fin n)) :
    (Fin n → Option ℕ) × Multiset (ℕ × Fin n) :=
  if e∈active ∧ g.head e∉settled ∧ Improves (tentative (g.head e)) (key+w e) then
    (Function.update tentative (g.head e) (some (key+w e)),(key+w e,g.head e)::ₘqueue)
  else (tentative,queue)
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule390
section FlattenedModule391
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule391
section FlattenedModule392
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule392
section FlattenedModule393
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
def edgeHeaderAtoms : List Atom := ⟨.loadN 310 308,trivial⟩::activeAtoms
def edgeHeader : Cmd := .seq (loadN 310 308) (Structured.sequence (activeAtoms.map Cmd.atom))
noncomputable def edgeHeaderData (s : Data) : Data := edgeHeaderAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule393
section FlattenedModule394
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
noncomputable def targetData (s : Data) : Data := targetSettledAtoms.foldl (fun t a => a.effect t) s
noncomputable def nextData (s : Data) : Data := nextAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule394
section FlattenedModule395
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
def edgeGuard : Cmd := .branch (.natLess 56 316)
  (.seq (Structured.sequence (targetSettledAtoms.map Cmd.atom)) (.branch (.natLess 320 26) Dijkstra.candidate .skip)) .skip
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule395
section FlattenedModule396
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule396
section FlattenedModule397
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end FlattenedModule397
section FlattenedModule398
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule398
section FlattenedModule399
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
noncomputable def scanEdges {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k)) (w : Fin k → ℕ)
    (settled : Finset (Fin n)) (key : ℕ) : List (Fin k) →
      (Fin n → Option ℕ) → Multiset (ℕ × Fin n) → (Fin n → Option ℕ) × Multiset (ℕ × Fin n)
  | [],tentative,queue => (tentative,queue)
  | e::es,tentative,queue =>
      let r := relax g active w settled key e tentative queue
      scanEdges g active w settled key es r.1 r.2
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule399
section FlattenedModule400
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule400
section FlattenedModule401
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
noncomputable def settledData (s : Data) : Data := settleAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule401
section FlattenedModule402
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
noncomputable def scanPrepared (s : Data) : Data := scanPrepareAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule402
section FlattenedModule403
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
noncomputable def poppedData (s : Data) : Data := poppedAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule403
section FlattenedModule404
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
attribute [local instance] Classical.propDecidable
noncomputable def remainingDegree {n k : ℕ} (g : Digraph n k) (settled : Finset (Fin n)) : ℕ :=
  ∑ v ∈ Finset.univ\settled, (adjacency g k v).length
noncomputable def queuePotential {n k : ℕ} (g : Digraph n k) (settled : Finset (Fin n)) (queue : Multiset (ℕ × Fin n)) : ℕ :=
  2*remainingDegree g settled+queue.card
end DecrAlmostLinearSSSP.Decremental.Exact
end FlattenedModule404
section FlattenedModule405
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end FlattenedModule405
section FlattenedModule406
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
structure State (i : Input) (deleted : List (Fin i.k)) where
  tentative : Fin i.n → Option ℕ
  settled : Finset (Fin i.n)
  queue : Multiset (ℕ × Fin i.n)
  tree : LocatedTrie (heapHeight i)
  labels : LabelInvariant i.graph (live deleted) i.weight i.source tentative settled queue
def State.memory {i : Input} {deleted : List (Fin i.k)} (q : State i deleted) (s : Data) : Prop :=
  Memory i deleted q.tentative q.settled q.tree q.queue s ∧ s.natReg 348=q.queue.card
noncomputable def State.potential {i : Input} {deleted : List (Fin i.k)} (q : State i deleted) : ℕ :=
  queuePotential i.graph q.settled q.queue
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule406
section FlattenedModule407
set_option autoImplicit false
open scoped ENNReal NNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule407
section FlattenedModule408
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule408
section FlattenedModule409
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule409
section FlattenedModule410
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
noncomputable def resetAdvanced (s : Data) : Data := resetBodyAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule410
section FlattenedModule411
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
structure Ready (i : Input) (deleted : List (Fin i.k)) (s : Data) : Prop where
  zero : s.natReg 56=0
  unit : s.natReg 26=1
  vertices : s.natReg 66=i.n
  edges : s.natReg 68=i.k
  source : s.natReg 72=i.source.val
  zeroR : s.realReg 56=0
  layoutRegs : Layout.Image (layout i) s
  graph : Adjacency.StaticImage i (layout i) s
  active : Adjacency.ActiveImage i (layout i) deleted s
  height : s.natReg 236=heapHeight i
  powerPtr : heapHeight i≠0 → s.natReg 238+1=heapBase i+heapHeight i
  slotReg : s.natReg 246=heapSlot i
  powers : ∀ j<heapHeight i, s.natMem (heapBase i+j)=2^j
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule411
section FlattenedModule412
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end FlattenedModule412
section FlattenedModule413
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
def installAtoms : List Atom := [⟨.nadd 236 252 56,trivial⟩,⟨.nsub 238 248 26,trivial⟩,⟨.nadd 246 248 56,trivial⟩]
def install : Cmd := Structured.sequence (installAtoms.map Cmd.atom)
noncomputable def installed (s : Data) : Data := installAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule413
section FlattenedModule414
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
structure Preparation (i : Input) (s : Data) : Prop where
  captured : InputCapture.Captured i s
  layoutRegs : Layout.Image (layout i) s
  graph : Adjacency.StaticImage i (layout i) s
  active : Adjacency.ActiveImage i (layout i) [] s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule414
section FlattenedModule415
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
def prepareGraph : Cmd := .seq InputCapture.code (.seq Layout.code AdjacencyBuild.code)
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule415
section FlattenedModule416
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule416
section FlattenedModule417
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
noncomputable def rootData (s : Data) : Data := rootAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule417
section FlattenedModule418
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule418
section FlattenedModule419
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule419
section FlattenedModule420
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
def deleteAtoms : List Atom := [⟨.nadd 350 228 5,trivial⟩,⟨.storeN 350 56,trivial⟩]
def deleteCode : Cmd := Structured.sequence (deleteAtoms.map Cmd.atom)
noncomputable def deletedData (s : Data) : Data := deleteAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule420
section FlattenedModule421
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
def initializeCode : Cmd := .seq prepareGraph (.seq (.seq Powers.code install) Dijkstra.code)
def updateCode : Cmd := .seq deleteCode Dijkstra.code
def hostProgram : Program := program initializeCode updateCode
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule421
section FlattenedModule422
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule422
section FlattenedModule423
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
noncomputable def Completed (i : Input) (deleted : List (Fin i.k)) (c : Machine) : Prop :=
  ∃ q : State i deleted, q.memory (Structured.data c) ∧ q.queue=0
def Good (i : Input) (deleted : List (Fin i.k)) (c : Machine) : Prop :=
  stored c i.source.val=0 ∧
    (∀ v : Fin i.n, c.natMem v.val≤1 ∧ (c.natMem v.val=0 → 0 ≤ c.realMem v.val)) ∧
    ∀ v : Fin i.n, i.dist deleted v≤ stored c v.val ∧
      stored c v.val≤ENNReal.ofReal (1+i.accuracy)*i.dist deleted v ∧
      (stored c v.val=⊤ ↔ ¬Reachable i.graph (live deleted) i.source v)
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule423
section FlattenedModule424
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule424
section FlattenedModule425
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
noncomputable def overhead (m : ℕ) : ℝ := 4+logarithm2 (max 2 m : ℕ)
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule425
section FlattenedModule426
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end FlattenedModule426
section FlattenedModule427
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
structure LowData (bound : ℕ) (host guest : Machine) : Prop where
  natural : ∀ j<bound, host.natReg j=guest.natReg j
  real : ∀ j<bound, host.realReg j=guest.realReg j
  natMem : host.natMem=guest.natMem
  realMem : host.realMem=guest.realMem
end DecrAlmostLinearSSSP.Decremental.Relocation
end FlattenedModule427
section FlattenedModule428
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
def block (offset returnPC pc : ℕ) (ins : Instruction) : List Instruction :=
  let next := offset+2*(pc+1)
  match ins with
  | .jump dest => [.jump (offset+2*dest),.jump next]
  | .less a b dest => [.less a b (offset+2*dest),.jump next]
  | .lessN a b dest => [.lessN a b (offset+2*dest),.jump next]
  | .halt => [.jump returnPC,.jump returnPC]
  | ins => [ins,.jump next]
def codeAux (offset returnPC : ℕ) : ℕ → List Instruction → List Instruction
  | _,[] => []
  | pc,ins::rest => block offset returnPC pc ins++codeAux offset returnPC (pc+1) rest
def code (offset returnPC : ℕ) (source : List Instruction) : List Instruction := codeAux offset returnPC 0 source
def Embeds (host guest : Program) (offset returnPC : ℕ) : Prop :=
  ∀ pc ins, guest.code[pc]?=some ins → ∀ slot<2,
    host.code[offset+2*pc+slot]?=(block offset returnPC pc ins)[slot]?
end DecrAlmostLinearSSSP.Decremental.Relocation
end FlattenedModule428
section FlattenedModule429
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
noncomputable def destination (offset returnPC : ℕ) (g : Machine) : ℕ := if g.halted then returnPC else offset+2*g.pc
structure Rep (bound offset returnPC : ℕ) (host guest : Machine) : Prop where
  data : LowData bound host guest
  position : host.pc=destination offset returnPC guest
  running : host.halted=false
  fault : host.fault=false
end DecrAlmostLinearSSSP.Decremental.Relocation
end FlattenedModule429
section FlattenedModule430
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
end DecrAlmostLinearSSSP.Decremental.Relocation
end FlattenedModule430
section FlattenedModule431
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
end DecrAlmostLinearSSSP.Decremental.Relocation
end FlattenedModule431
section FlattenedModule432
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
end DecrAlmostLinearSSSP.Decremental.Relocation
end FlattenedModule432
section FlattenedModule433
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
end DecrAlmostLinearSSSP.Decremental.Relocation
end FlattenedModule433
section FlattenedModule434
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
end DecrAlmostLinearSSSP.Decremental.Relocation
end FlattenedModule434
section FlattenedModule435
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
end DecrAlmostLinearSSSP.Decremental.Relocation
end FlattenedModule435
section FlattenedModule436
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
structure Branches where
  singleton : Program
  small : Program
  normal : Program
def fresh (b : Branches) : ℕ := 8+registerBound b.singleton.code+registerBound b.small.code+registerBound b.normal.code
def singletonOffset (_ : Branches) : ℕ := 19
def exactOffset (b : Branches) : ℕ := 19+2*b.singleton.code.length
def normalOffset (b : Branches) : ℕ := exactOffset b+2*b.small.code.length
def returnPC (b : Branches) : ℕ := normalOffset b+2*b.normal.code.length
def dispatchPrefix (b : Branches) : List Instruction := [
  .natural (fresh b+1) 2,
  .lessN 0 (fresh b+1) 10,
  .cast (fresh b) 2,
  .mul (fresh b) (fresh b) 0,
  .rational (fresh b+1) 1,
  .less (fresh b+1) (fresh b) 8,
  .natural (fresh b) 1,
  .jump (exactOffset b+2*b.small.initPC),
  .natural (fresh b) 2,
  .jump (normalOffset b+2*b.normal.initPC),
  .natural (fresh b) 0,
  .jump (singletonOffset b+2*b.singleton.initPC),
  .natural (fresh b+1) 1,
  .lessN (fresh b) (fresh b+1) 18,
  .natural (fresh b+1) 2,
  .lessN (fresh b) (fresh b+1) 17,
  .jump (normalOffset b+2*b.normal.update),
  .jump (exactOffset b+2*b.small.update),
  .jump (singletonOffset b+2*b.singleton.update)]
def singletonCode (b : Branches) : List Instruction := Relocation.code (singletonOffset b) (returnPC b) b.singleton.code
def exactCode (b : Branches) : List Instruction := Relocation.code (exactOffset b) (returnPC b) b.small.code
def normalCode (b : Branches) : List Instruction := Relocation.code (normalOffset b) (returnPC b) b.normal.code
def program (b : Branches) : Program where
  code := dispatchPrefix b++singletonCode b++exactCode b++normalCode b++[.halt,.loadN 6 5,.load 1 5,.halt]
  initPC := 0
  update := 12
  query := returnPC b+1
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end FlattenedModule436
section FlattenedModule437
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
open Structured
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end FlattenedModule437
section FlattenedModule438
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
inductive Kind where
  | singleton
  | small
  | normal
  deriving DecidableEq
def Kind.tag : Kind → ℕ | .singleton => 0 | .small => 1 | .normal => 2
def source (b : Branches) : Kind → Program | .singleton => b.singleton | .small => b.small | .normal => b.normal
def offset (b : Branches) : Kind → ℕ | .singleton => singletonOffset b | .small => exactOffset b | .normal => normalOffset b
noncomputable def choose (i : Input) : Kind :=
  if i.n<2 then .singleton else if (1 : ℝ)<(i.size : ℝ)*i.accuracy then .normal else .small
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end FlattenedModule438
section FlattenedModule439
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end FlattenedModule439
section FlattenedModule440
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end FlattenedModule440
section FlattenedModule441
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
def initTagPC : Kind → ℕ | .singleton => 10 | .small => 6 | .normal => 8
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end FlattenedModule441
section FlattenedModule442
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end FlattenedModule442
section FlattenedModule443
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end FlattenedModule443
section FlattenedModule444
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end FlattenedModule444
section FlattenedModule445
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
structure Pair (b : Branches) (k : Kind) (j : ℕ) (host guest : Machine) : Prop where
  data : Relocation.LowData (fresh b) host guest
  tag : host.natReg (fresh b)=k.tag
  work : host.work≤2*guest.work+6*j+9
structure Aligned (b : Branches) (k : Kind) (host guest : List Machine) : Prop where
  length : host.length=guest.length
  matching : ∀ j c g, host[j]?=some c → guest[j]?=some g → Pair b k j c g
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end FlattenedModule445
section FlattenedModule446
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end FlattenedModule446
section FlattenedModule447
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end FlattenedModule447
section FlattenedModule448
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule448
section FlattenedModule449
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule449
section FlattenedModule450
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end FlattenedModule450
open DecrAlmostLinearSSSP.Decremental
set_option autoImplicit false


