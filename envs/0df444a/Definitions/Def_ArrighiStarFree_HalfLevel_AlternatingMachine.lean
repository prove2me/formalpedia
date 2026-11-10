-- Prove2me | Definitions.Def_ArrighiStarFree_HalfLevel_AlternatingMachine
-- name    : ArrighiStarFree_HalfLevel_AlternatingMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:06:27.373857+00:00
-- url     : https://prove2.me/theorems/2a505588-37cd-4cd4-a86e-7f499aca26cd
-- title:
--   Uniform AC⁰ through concrete bounded-alternation logarithmic-time machines
-- statement:
--   A random-access alternating machine has fixed finite control, finite work alphabets, local work-tape heads and a binary address tape. One step reads the input bit at the address written on that tape; an out-of-range query returns an endmarker. Address bits themselves are changed only through a local tape head. Control states are existential, universal, accepting or rejecting. Acceptance combines the two successor values by OR at existential states and AND at universal states.
--
--   For a language $B$, the uniform AC⁰ predicate requires one such machine and constants $c>0,a$ such that every branch on every input $x$ terminates within $c\lfloor\log_2(|x|+2)\rfloor$ steps, changes existential/universal mode at most $a$ times, and the computation tree accepts exactly $B$. This is the bounded-alternation logarithmic-time formulation expressly used in §2, representing DLOGTIME-uniform AC⁰.
--
--   String maps use validity/data output bits. Put
--   $$P_d(n)=2^{d(\lfloor\log_2(n+2)\rfloor+1)}.$$
--   A map $f$ is uniform AC⁰-computable when some fixed $d$ bounds $|f(x)|$ by $P_d(|x|)$, and a single uniform AC⁰ language answers all output queries. The query contains a data/validity flag, self-delimiting binary encodings of $|x|$ and the position $j$, then $x$. A validity query accepts exactly when $j<|f(x)|$; a data query accepts exactly when the $j$th bit exists and equals one. Only positions below $P_d(|x|)$ are valid queries. All malformed queries reject.
--
--   The capacity has polynomial growth, and validity bits describe a prefix. No machine, advice, truth table or resource certificate varies with the input. This general definition supplies the weak reductions without weakening uniformity to logspace uniformity.
-- source:
--   Arrighi et al. (2021), supplied source.pdf (arXiv:2110.01279v1), §2, printed p. 23:3, PDF p. 3; Theorem 3 footnote 2, printed p. 23:6, PDF p. 6

import Definitions.Def_ArrighiStarFree_HalfLevel_SpaceMachine
import Mathlib.Data.Nat.Bits

namespace ArrighiStarFree.HalfLevel

inductive AlternationMode where
  | accept | reject | existsBranch | forallBranch
  deriving DecidableEq

def AlternationMode.terminal : AlternationMode → Bool
  | .accept | .reject => true
  | _ => false

def changesMode : AlternationMode → AlternationMode → Bool
  | .existsBranch, .forallBranch => true
  | .forallBranch, .existsBranch => true
  | _, _ => false

structure RandomAccessAction (q g k : ℕ) where
  next : Fin (q + 1)
  write : Fin (k + 1) → Fin (g + 1)
  workMove : Fin (k + 1) → HeadMove
  addressWrite : Bool
  addressMove : HeadMove

/-- Random-access alternating Turing machine. The input query reads the cell whose
binary address is on a dedicated tape. All writable tapes have local heads and finite
alphabets; there is no arithmetic instruction or nonlocal work-tape access. -/
structure AlternatingMachine where
  states : ℕ
  symbols : ℕ
  tapes : ℕ
  start : Fin (states + 1)
  mode : Fin (states + 1) → AlternationMode
  transition : Fin (states + 1) → Option Bool →
    (Fin (tapes + 1) → Fin (symbols + 1)) → Bool → Bool →
    RandomAccessAction states symbols tapes

structure RandomAccessConfig (M : AlternatingMachine) where
  state : Fin (M.states + 1)
  tape : Fin (M.tapes + 1) → ℕ → Fin (M.symbols + 1)
  head : Fin (M.tapes + 1) → ℕ
  addressTape : ℕ → Bool
  addressHead : ℕ
  addressVisited : ℕ

def AlternatingMachine.initial (M : AlternatingMachine) : RandomAccessConfig M where
  state := M.start
  tape := fun _ _ => 0
  head := fun _ => 0
  addressTape := fun _ => false
  addressHead := 0
  addressVisited := 1

/-- Little-endian address. All cells outside the visited prefix remain zero. -/
def RandomAccessConfig.address {M : AlternatingMachine} (s : RandomAccessConfig M) : ℕ :=
  ((List.range s.addressVisited).map s.addressTape).foldr
    (fun b n => (if b then 1 else 0) + 2 * n) 0

def AlternatingMachine.step (M : AlternatingMachine) (x : List Bool) (b : Bool)
    (s : RandomAccessConfig M) : RandomAccessConfig M :=
  if (M.mode s.state).terminal then s else
    let a := M.transition s.state x[s.address]? (fun i => s.tape i (s.head i))
      (s.addressTape s.addressHead) b
    { state := a.next
      tape := fun i j => if j = s.head i then a.write i else s.tape i j
      head := fun i => (a.workMove i).apply (s.head i)
      addressTape := fun j => if j = s.addressHead then a.addressWrite else s.addressTape j
      addressHead := a.addressMove.apply s.addressHead
      addressVisited := max s.addressVisited (a.addressMove.apply s.addressHead + 1) }

def AlternatingMachine.run (M : AlternatingMachine) (x : List Bool) (choices : ℕ → Bool) :
    ℕ → RandomAccessConfig M
  | 0 => M.initial
  | t + 1 => M.step x (choices t) (M.run x choices t)

/-- Acceptance of the finite computation tree, with OR/AND at existential/universal
states. Fuel is used only after checking terminal states, including at time zero. -/
def AlternatingMachine.evaluate (M : AlternatingMachine) (x : List Bool) :
    ℕ → RandomAccessConfig M → Bool
  | 0, s => decide (M.mode s.state = .accept)
  | t + 1, s =>
    match M.mode s.state with
    | .accept => true
    | .reject => false
    | .existsBranch => M.evaluate x t (M.step x false s) || M.evaluate x t (M.step x true s)
    | .forallBranch => M.evaluate x t (M.step x false s) && M.evaluate x t (M.step x true s)

def AlternatingMachine.alternations (M : AlternatingMachine) (x : List Bool)
    (choices : ℕ → Bool) (t : ℕ) : ℕ :=
  ((List.range t).filter (fun i => changesMode (M.mode (M.run x choices i).state)
    (M.mode (M.run x choices (i + 1)).state))).length

/-- The uniform AC⁰ model used in §2, PDF p. 3: one random-access finite machine,
logarithmic time on every branch, and a constant bound on alternations. -/
def InUniformAC0 (L : Set (List Bool)) : Prop :=
  ∃ (M : AlternatingMachine) (c a : ℕ), 0 < c ∧ ∀ x,
    let t := c * Nat.log2 (x.length + 2)
    (∀ choices, (M.mode (M.run x choices t).state).terminal = true ∧
      M.alternations x choices t ≤ a) ∧
    (M.evaluate x t M.initial = true ↔ x ∈ L)

/-- Prefix-free binary integer: a 1 before each bit, then a terminating 0. -/
def binaryCode (n : ℕ) : List Bool :=
  (Nat.bits n).flatMap (fun b => [true, b]) ++ [false]

/-- Index query header followed by the original string. False asks whether position j
is present; true asks whether its bit is one. Length is part of the header. -/
def outputQuery (x : List Bool) (j : ℕ) (data : Bool) : List Bool :=
  [data] ++ binaryCode x.length ++ binaryCode j ++ x

/-- A polynomial envelope with a power-of-two boundary: the index range can be
checked by its binary width without multiplying variable binary integers. -/
def outputCapacity (d n : ℕ) : ℕ := 2 ^ (d * (Nat.log2 (n + 2) + 1))

/-- Uniform AC⁰ transduction via its padded bit graph. The polynomial number of
positions each has a validity bit and a data bit. Malformed queries are NO instances.
The validity bits specify precisely a prefix, so decoding involves no selection oracle. -/
def UniformAC0Computable (f : List Bool → List Bool) : Prop :=
  ∃ d : ℕ, (∀ x, (f x).length ≤ outputCapacity d x.length) ∧
    InUniformAC0 {y | ∃ (x : List Bool) (j : ℕ) (data : Bool),
      y = outputQuery x j data ∧ j < outputCapacity d x.length ∧
      (if data then (f x)[j]? = some true else j < (f x).length)}

end ArrighiStarFree.HalfLevel


