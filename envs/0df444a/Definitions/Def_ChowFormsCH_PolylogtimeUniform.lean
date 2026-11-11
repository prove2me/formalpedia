-- Prove2me | Definitions.Def_ChowFormsCH_PolylogtimeUniform
-- name    : ChowFormsCH_PolylogtimeUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:22.726245+00:00
-- url     : https://prove2.me/theorems/8432e0c6-2df7-4601-8f21-78b11ce14a94
-- title:
--   Polylogtime-uniform families of threshold circuits (Definitions 2.7–2.9) and uniform TC$^0$
-- statement:
--   Let $\mathcal C=(C_\iota)$ be a family of threshold circuits indexed by tuples $\iota=(n_1,\dots,n_k)$, with sizes $s=s(\iota)$. Its **direct connection language** consists of the binary encodings of tuples $(k,n_1,\dots,n_k,a,p,b)$ such that $a$ is a gate of $C_\iota$ and either $p\neq\epsilon$ and $b$ is a predecessor of $a$, or $p=\epsilon$ and $b$ is the number of the type of $a$. The family is **polylogtime-uniform** if
--
--   1. its numbering is admissible (inputs, then outputs, numbered from $0$; every gate number has binary length at most $c\cdot\log s$, one $c$ for the family);
--   2. its direct connection language is decided by one deterministic machine in time polynomial in $\log s+\log k+\sum_i\log n_i$;
--   3. the numbers of inputs and outputs of $C_\iota$ and an upper bound on $s$ are computed from $\iota$ by one machine in time polynomial in the same quantity.
--
--   A **uniform TC$^0$ family** is polylogtime-uniform, of depth bounded by one constant, and of size polynomial in the number of input bits.
--
--   **Formalization Note** Machines are the published deterministic multitape machines `APSCounting893.Main.OracleMachine` with the empty oracle; "polynomial in $L$" is $c(L+1)^d$. Natural numbers are encoded in self-delimiting binary. Each logarithm is read as a binary length (`Nat.size`, plus one per index entry): read literally with $\lfloor\log_2\rfloor$, entries $n_i\in\{0,1\}$ contribute nothing and a sequential machine could not read the index in the allowed time. $c\log s$ is read as $c(\lfloor\log_2 s\rfloor+1)$. Families are defined on all index lists.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Definitions 2.7–2.9 and Remark 2.10, p.12

import Mathlib
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_ChowFormsCH_ThresholdCircuit

set_option autoImplicit false

namespace ChowFormsCH

open APSCounting893.Main

/-- Self-delimiting binary code of a natural number: each binary digit `b` (least significant
first) becomes `true, b`, and the code ends with `false, false` (Andrews–Garg–Oliveira–Schost,
*Some algebraic and geometric computations in CH via Chow forms*, arXiv:2611.05289, held version,
sha256 75e796c6…, Definition 2.8, p.12, "binary encodings of tuples"). Its length is
`2 · (number of binary digits) + 2`. -/
def encNat (k : ℕ) : Word := (Nat.bits k).flatMap (fun b => [true, b]) ++ [false, false]

/-- The code of a list of natural numbers: the concatenation of the codes of its entries. -/
def encNats (l : List ℕ) : Word := l.flatMap encNat

/-- The code of a circuit index `(n₁, …, n_k)`: the tuple `(k, n₁, …, n_k)` (Definition 2.8, p.12;
Remark 2.10: "the first index is a count of the remaining indices"). -/
def encodeIndex (ι : List ℕ) : Word := encNats (ι.length :: ι)

/-- The code of a direct-connection query `(k, n₁, …, n_k, a, p, b)`; `p = ε` is the flag `false`
(the query asks for the gate type), `p ≠ ε` is `true` (the query asks for a predecessor). -/
def encodeDCL (ι : List ℕ) (a : ℕ) (p : Bool) (b : ℕ) : Word :=
  encodeIndex ι ++ encNats [a, if p then 1 else 0, b]

/-- Membership of a query in the direct connection language of a threshold circuit
(Definition 2.8, p.12): `a` is a gate, and if `p ≠ ε` then `b` is some predecessor of `a`, while if
`p = ε` then `b` is the code of the type of `a`. -/
def InDCL (C : ThresholdCircuit) (a : ℕ) (p : Bool) (b : ℕ) : Prop :=
  a ∈ C.gates ∧ (if p then b ∈ C.preds a else b = (C.type a).code)

/-- The quantity `log(s) + log(k) + Σᵢ log(nᵢ)` of Definition 2.9 (p.12) for the circuit with index
`ι = (n₁, …, n_k)` and size `s`, with each logarithm read as a binary length: `Nat.size s`
(`⌊log₂ s⌋ + 1`, and `0` for `s = 0`), `Nat.size k`, and `Nat.size nᵢ + 1` for each index entry.

**Formalization Note** Read literally with `⌊log₂⌋`, an index entry `nᵢ ∈ {0, 1}` contributes `0`,
and a sequential machine could not even read an index `(n, m, 1, …, 1, h)` with many entries within
the allowed time. The binary-length reading makes the bound polynomial in the length of the
encoded query, which is the meaning of "polylogtime" for the sequential machines used here. -/
def polylogParam (F : List ℕ → ThresholdCircuit) (ι : List ℕ) : ℕ :=
  Nat.size (F ι).size + Nat.size ι.length + (ι.map fun x => Nat.size x + 1).sum

/-- The deterministic machine `M` (published machine model `APSCounting893.Main`, empty oracle)
halts on input `x` within `T` steps and its answer is `true` iff `P` holds. -/
def DecidesIn (M : OracleMachine) (x : Word) (P : Prop) (T : ℕ) : Prop :=
  ∃ answer : Bool, (machineRun M (fun _ => False) x [] T).answer = some answer ∧ (answer = true ↔ P)

/-- The deterministic machine `M` halts on input `x` within `T` steps with `y` on its output tape. -/
def ComputesIn (M : OracleMachine) (x y : Word) (T : ℕ) : Prop :=
  (machineRun M (fun _ => False) x [] T).answer.isSome ∧
    ((machineRun M (fun _ => False) x [] T).tapes M.outputTape).word = y

/-- An admissible encoding with constant `c` (Definition 2.7, p.12): the circuit is well formed
(items 1–2, inputs then outputs numbered from 0) and the binary representation of every gate number
has length at most `c · log(s)`.

**Formalization Note** `c · log(s)` is read as `c · (⌊log₂ s⌋ + 1)`, so that circuits of size `0`
or `1` are not excluded by `log 1 = 0`; for `s ≥ 2` this changes `c` by at most a factor 2. -/
def IsAdmissible (C : ThresholdCircuit) (c : ℕ) : Prop :=
  C.WellFormed ∧ ∀ a ∈ C.gates, Nat.size a ≤ c * (Nat.log 2 C.size + 1)

/-- A family `F` of threshold circuits, indexed by tuples `ι = (n₁, …, n_k)` of natural numbers, is
polylogtime-uniform (Definition 2.9, p.12):

0. its numbering is an admissible encoding with one constant `c` for the whole family
   (Definition 2.7);
1. its direct connection language is decided by one machine in time polynomial in
   `log(s) + log(k) + Σ log(nᵢ)`;
2. the numbers of inputs and outputs and an upper bound `S ι` on the size are computed from the
   encoded index by one machine in time polynomial in the same quantity.

**Formalization Note** Machines are the published deterministic multitape machines of
`APSCounting893.Main` with the empty oracle; "time polynomial in `L`" is `polyBound c d L =
c · (L + 1)^d`. Item 3 of Definition 2.9 concerns arithmetic circuits only. The family is defined on
all index lists; on lists that are not indices of the theorem at hand it may be anything, but the
uniformity conditions are required there too (a decider can recognize malformed indices). -/
def PolylogtimeUniform (F : List ℕ → ThresholdCircuit) : Prop :=
  (∃ c : ℕ, ∀ ι, IsAdmissible (F ι) c) ∧
  (∃ (M : OracleMachine) (c d : ℕ), ∀ (ι : List ℕ) (a : ℕ) (p : Bool) (b : ℕ),
      DecidesIn M (encodeDCL ι a p b) (InDCL (F ι) a p b) (polyBound c d (polylogParam F ι))) ∧
  (∃ (M : OracleMachine) (c d : ℕ) (S : List ℕ → ℕ), ∀ ι : List ℕ,
      (F ι).size ≤ S ι ∧
      ComputesIn M (encodeIndex ι) (encNats [(F ι).numIn, (F ι).numOut, S ι])
        (polyBound c d (polylogParam F ι)))

/-- Index-dependent layout parameters `g ι` (degree bounds and bit widths of outputs) are computed
from the encoded index by one machine in time polynomial in `log(s) + log(k) + Σ log(nᵢ)`, as the
numbers of inputs and outputs are in Definition 2.9 item 2 (p.12). -/
def PolyComputableIndexFn (F : List ℕ → ThresholdCircuit) (g : List ℕ → List ℕ) : Prop :=
  ∃ (M : OracleMachine) (c d : ℕ), ∀ ι : List ℕ,
    ComputesIn M (encodeIndex ι) (encNats (g ι)) (polyBound c d (polylogParam F ι))

/-- A polylogtime-uniform family of TC⁰ circuits (Lemmas 2.13 and 2.18, pp.15–18): polylogtime
uniform, of depth bounded by one constant, and of size polynomial in the number of input bits.

**Formalization Note** The paper does not define TC⁰; this is the standard notion (constant depth,
polynomial size, unbounded fan-in MAJORITY gates) with the paper's uniformity. -/
def IsUniformTC0 (F : List ℕ → ThresholdCircuit) : Prop :=
  PolylogtimeUniform F ∧ (∃ Δ : ℕ, ∀ ι, (F ι).HasDepthAtMost Δ) ∧
    ∃ c : ℕ, ∀ ι, (F ι).size ≤ c * ((F ι).numIn + 2) ^ c

end ChowFormsCH


