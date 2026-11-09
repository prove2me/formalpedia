-- Prove2me | Definitions.Def_UniformADProbes_Trace_circuits
-- name    : UniformADProbes_Trace_circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:09.159135+00:00
-- url     : https://prove2.me/theorems/17d52965-8a21-4d0e-86d4-beec8372b976
-- title:
--   Original-order matrix circuits and the charged uniform emitter
-- statement:
--   A circuit stores a finite sequence of identity, first-input, second-input, addition, ordered multiplication, and prescribed integer-scaling instructions. Every operand must reference an earlier register. Evaluation stores matrices of the original input order; polynomial denotation evaluates the same code at $x,y$. Syntactic degree is propagated using maximum for addition and sum for multiplication, with input degrees $0,1,1$ and degree unchanged by scaling.
--
--   For an integer $z$ and a register index $r$, the binary encoding conventions are
--   $$\operatorname{signedBits}(z)=1+\max(1,\operatorname{size}_2|z|),\qquad
--   \operatorname{refBits}(r)=\max(1,\operatorname{size}_2r).$$
--   Thus zero has two signed bits. An instruction has a three-bit opcode plus the encoded operands and literal. The entry-bound predicate quantifies over every stored entry and the final trace for every nonempty tree of order at most $N$.
--
--   The executable emitter takes only $N$. A dual register pair stores a polynomial and its adjoint; multiplication reverses the operands of the second component. It emits the triangular recurrence and distance recurrence, computes the base from equation (10) using binary multiplication, generates its large powers inside the matrix circuit, and uses two shared Horner chains for equation (12). For $N=1$ its single instruction is identity.
--
--   Charged construction counts binary addition by $1+\operatorname{size}_2a+\operatorname{size}_2b$, binary multiplication by $(1+\operatorname{size}_2a)(1+\operatorname{size}_2b)$, and powers by repeated charged multiplication. Reading or extending a stored table pays for copying its binary data. Every emission pays for the whole existing code encoding, the emitted instruction, and its register reference. Loop and index work is charged as specified in the bodies. This is a conservative costed list-construction semantics supporting a persistent-array implementation, not a hypothesis asserting efficient construction.
--
--   These definitions make the simultaneous size, literal, intermediate-entry, and construction-time conclusions explicit and independently auditable. No matrix-dependent branching, trace, inverse, determinant, or rank oracle is an instruction.
-- source:
--   Zhipeng Lu, Uniform adjacency-degree probes from differential rigidity, STOC 2027 submission #25 (October 2026), §1 circuit convention; Theorem 1.1 and §3 equations (10)–(12) and resource proof, p. 1, 9–10 (PDF p. 2, 10–11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/25.pdf

import Definitions.Def_UniformADProbes_Trace_algebra

set_option autoImplicit false

namespace UniformADProbes.Trace

/-- Signed binary length: a sign bit and at least one magnitude bit. -/
def signedBits (z : ℤ) : ℕ := 1 + max 1 z.natAbs.size
def refBits (r : ℕ) : ℕ := max 1 r.size

inductive Instruction where
  | identity | first | second
  | add (a b : ℕ) | mul (a b : ℕ) | scale (c : ℤ) (a : ℕ)
  deriving Inhabited, Repr

def instructionBits : Instruction → ℕ
  | .identity | .first | .second => 3
  | .add a b | .mul a b => 3 + refBits a + refBits b
  | .scale c a => 3 + signedBits c + refBits a

def backward (k : ℕ) : Instruction → Prop
  | .identity | .first | .second => True
  | .add a b | .mul a b => a < k ∧ b < k
  | .scale _ a => a < k

structure Circuit where
  code : Array Instruction
  output : ℕ
  deriving Inhabited, Repr

def Circuit.Valid (C : Circuit) : Prop :=
  C.output < C.code.size ∧ ∀ k : Fin C.code.size, backward k.val C.code[k]

def runInstruction {R : Type} [Ring R] (H K : R) (regs : Array R) : Instruction → R
  | .identity => 1
  | .first => H
  | .second => K
  | .add a b => regs[a]?.getD 0 + regs[b]?.getD 0
  | .mul a b => regs[a]?.getD 0 * regs[b]?.getD 0
  | .scale c a => c • regs[a]?.getD 0

def registers {R : Type} [Ring R] (C : Circuit) (H K : R) : Array R :=
  C.code.foldl (fun regs instr => regs.push (runInstruction H K regs instr)) #[]

def outputValue {R : Type} [Ring R] (C : Circuit) (H K : R) : R :=
  (registers C H K)[C.output]?.getD 0

noncomputable def Circuit.denotation (C : Circuit) : NCPoly := outputValue C x y

def degreeInstruction (d : Array ℕ) : Instruction → ℕ
  | .identity => 0
  | .first | .second => 1
  | .add a b => max (d[a]?.getD 0) (d[b]?.getD 0)
  | .mul a b => d[a]?.getD 0 + d[b]?.getD 0
  | .scale _ a => d[a]?.getD 0

def degrees (C : Circuit) : Array ℕ :=
  C.code.foldl (fun d instr => d.push (degreeInstruction d instr)) #[]

def Circuit.DegreeBound (C : Circuit) (d : ℕ) : Prop :=
  ∀ i : Fin (degrees C).size, (degrees C)[i] ≤ d

def Circuit.LiteralBound (C : Circuit) (b : ℕ) : Prop :=
  ∀ instr ∈ C.code.toList, ∀ c a, instr = .scale c a → signedBits c ≤ b

/-- Every matrix register is at the original order; the only readout is the final trace. -/
def Circuit.EntryBound (C : Circuit) (N bits : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ N → ∀ T : SimpleGraph (Fin n), T.IsTree →
    (∀ r : Fin (registers C (adjacency T) (degreeMatrix T)).size,
      ∀ i j : Fin n,
      signedBits ((registers C (adjacency T) (degreeMatrix T))[r] i j) ≤ bits) ∧
    signedBits (Matrix.trace (outputValue C (adjacency T) (degreeMatrix T))) ≤ bits

/-- Charges use schoolbook binary arithmetic. Payload plus charge, rather than an
uninterpreted assertion that a constructor runs in polynomial time. -/
structure Charged (α : Type) where
  value : α
  cost : ℕ
  deriving Repr

def binaryAdd (a b : ℕ) : Charged ℕ :=
  ⟨a + b, 1 + a.size + b.size⟩
def binaryMul (a b : ℕ) : Charged ℕ :=
  ⟨a * b, (1 + a.size) * (1 + b.size)⟩
def binaryPower (a : ℕ) : ℕ → Charged ℕ
  | 0 => ⟨1, 1⟩
  | k + 1 =>
    let p := binaryPower a k
    let q := binaryMul p.value a
    ⟨q.value, p.cost + q.cost + refBits k + 1⟩

/-- This computes precisely (10); powers are constructed by binary multiplication. -/
def chargedBase (N : ℕ) : Charged ℕ :=
  let a := binaryMul N N
  let c := binaryMul a.value N
  let l := binaryMul 3 c.value
  let r := binaryPower l.value (N - 1)
  let r2 := binaryMul r.value r.value
  let h := binaryMul a.value r2.value
  let t := binaryMul 2 h.value
  let b := binaryAdd t.value 1
  ⟨b.value, a.cost + c.cost + l.cost + r.cost + r2.cost + h.cost + t.cost + b.cost +
    refBits N + 2⟩

structure Builder where
  code : Array Instruction := #[]
  cost : ℕ := 0
  deriving Inhabited, Repr

abbrev Emit := StateM Builder
abbrev DualRef := ℕ × ℕ

/-- Conservative list semantics: even reading or extending a stored array is charged
for copying its entire binary encoding. This permits a plain persistent-list implementation. -/
def builderBits (s : Builder) : ℕ :=
  s.code.foldl (fun b instr => b + instructionBits instr) 1

def charge (c : ℕ) : Emit Unit := modify fun s => {s with cost := s.cost + c + 1}

def emit (instr : Instruction) : Emit ℕ := do
  let s ← get
  let k := s.code.size
  set (Builder.mk (s.code.push instr)
    (s.cost + builderBits s + instructionBits instr + refBits k + 1))
  return k

def dualAdd (a b : DualRef) : Emit DualRef := do
  let u ← emit (.add a.1 b.1)
  let v ← emit (.add a.2 b.2)
  return (u, v)

def dualMul (a b : DualRef) : Emit DualRef := do
  let u ← emit (.mul a.1 b.1)
  let v ← emit (.mul b.2 a.2)
  return (u, v)

def dualScale (c : ℤ) (a : DualRef) : Emit DualRef := do
  let u ← emit (.scale c a.1)
  let v ← emit (.scale c a.2)
  return (u, v)

def dualSwap (a : DualRef) : DualRef := (a.2, a.1)

def initial : Emit (DualRef × DualRef × DualRef × DualRef) := do
  let i ← emit .identity
  let a ← emit .first
  let d ← emit .second
  let z ← emit (.scale 0 i)
  return ((i,i), (a,a), (d,d), (z,z))

/-- Reading a table also pays for copying all indices in that table. -/
def tableGet (a : Array DualRef) (i : ℕ) (fallback : DualRef) : Emit DualRef := do
  charge (1 + refBits i + a.foldl (fun c r => c + refBits r.1 + refBits r.2) 0)
  return a[i]?.getD fallback

def emitProbeRows (N : ℕ) (a d zero : DualRef) :
    ℕ → Array DualRef → Array DualRef → Emit (Array DualRef)
  | 0, _, all => pure all
  | k + 1, row, all => do
    let i := row.size - 1
    let mut next := #[]
    let mut total := all
    for j in List.range (i + 2) do
      let u ← tableGet row j zero
      let v ← if j = 0 then pure zero else tableGet row (j - 1) zero
      let n2 := binaryMul N N
      let coeff : ℤ := (n2.value : ℤ) * ((j : ℤ) - (i : ℤ))
      charge (n2.cost + (1 + refBits j + refBits i) * (1 + refBits n2.value) +
        refBits j + refBits i + 2)
      let du ← dualMul d u
      let cu ← dualScale coeff u
      let av ← dualMul a v
      let nv ← dualScale (n2.value : ℤ) av
      let q ← dualAdd (← dualAdd du cu) nv
      charge (1 + total.size * (1 + refBits q.1 + refBits q.2) +
        next.size * (1 + refBits q.1 + refBits q.2))
      next := next.push q
      total := total.push q
    emitProbeRows N a d zero k next total

def emitProbes (N : ℕ) (i a d z : DualRef) : Emit (Array DualRef) :=
  if N = 0 then pure #[] else emitProbeRows N a d z (N - 1) #[i] #[i]

def emitDistance (N : ℕ) (i a d : DualRef) : Emit DualRef := do
  if N ≤ 1 then return i
  let mut sum ← dualAdd i a
  if N = 2 then return sum
  let p2 ← dualAdd (← dualMul a a) (← dualScale (-1) d)
  sum ← dualAdd sum p2
  let dm ← dualAdd d (← dualScale (-1) i)
  let mut prev := a
  let mut curr := p2
  for k in List.range (N - 3) do
    charge (refBits k + refBits N + 1)
    let q ← dualAdd (← dualMul a curr) (← dualScale (-1) (← dualMul dm prev))
    sum ← dualAdd sum q
    prev := curr
    curr := q
  return sum

def emitPower (base i : DualRef) : ℕ → Emit DualRef
  | 0 => pure i
  | k + 1 => do
    charge (refBits k + 1)
    dualMul (← emitPower base i k) base

def emitHorner (base zero : DualRef) (U : Array DualRef) : Emit DualRef := do
  let mut acc := zero
  for j in (List.range U.size).reverse do
    let u ← tableGet U j zero
    acc ← dualAdd u (← dualMul base acc)
  return acc

def probeProgram (N : ℕ) : (Array DualRef × Builder) :=
  (do
    if N ≤ 1 then
      let i ← emit .identity
      return if N = 0 then #[] else #[(i,i)]
    let (i,a,d,z) ← initial
    emitProbes N i a d z).run {}

/-- The actual deterministic emitter. It never inspects a matrix or a tree. -/
def invariantProgram (N : ℕ) : ℕ × Builder :=
  (do
    if N ≤ 1 then return (← emit .identity)
    let (i,a,d,z) ← initial
    let U ← emitProbes N i a d z
    let J ← emitDistance N i a d
    let b := chargedBase N
    charge b.cost
    let B ← dualScale (b.value : ℤ) i
    let BM ← emitPower B i U.size
    let BM2 ← emitPower BM i U.size
    let B2M2 ← dualMul BM2 BM2
    let Y ← emitHorner B z U
    let Z ← emitHorner BM z U
    let W ← dualAdd (← dualAdd i (← dualMul BM2 a)) (← dualMul B2M2 d)
    let t ← dualMul (← dualMul (← dualMul J (dualSwap Z)) W) Y
    let out ← dualAdd t (dualSwap t)
    return out.1).run {}

def invariantCircuit (N : ℕ) : Circuit :=
  let p := invariantProgram N
  ⟨p.2.code, p.1⟩

def constructionCost (N : ℕ) : ℕ := (invariantProgram N).2.cost

end UniformADProbes.Trace


