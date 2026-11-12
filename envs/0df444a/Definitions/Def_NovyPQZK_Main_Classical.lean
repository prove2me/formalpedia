-- Prove2me | Definitions.Def_NovyPQZK_Main_Classical
-- name    : NovyPQZK_Main_Classical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:34:25.930976+00:00
-- url     : https://prove2.me/theorems/2da51cb5-a28f-4b01-9547-1ddba3d01314
-- title:
--   Bit strings, polynomial time, classical probabilistic interactive parties and NP relations
-- statement:
--   **Strings.** Messages are bit strings. A list of strings $(x_1,\dots,x_k)$ is written with the self-delimiting encoding $\mathrm{pack}$ (each bit $b$ as $1b$, each string closed by $0$), parsed back by $\mathrm{unpack}$. Natural numbers are written in binary.
--
--   **Polynomial time.** $f$ is polynomial-time computable if one Turing machine (Mathlib's `TM2` model) computes it within a fixed polynomial of the input length.
--
--   **Parties.** A classical probabilistic interactive party draws all its coins at the start, the $i$-th uniformly from $\{0,\dots,m_i-1\}$ where the list $(m_i)$ is computed from its input, and computes each message deterministically from its **view** $\mathrm{pack}(\text{input},\text{coins},\text{messages received so far})$; after the last round the same function gives its output. It is **PPT** when the coin ranges and the next-message function are polynomial-time computable, every range is nonempty, and every message has length polynomial in the party's input whatever it receives (so polynomially many rounds take polynomial time in total).
--
--   Two parties $A$ and $B$ run $r$ rounds with $A$ speaking first in each round; the transcript is $(a_0,b_0,a_1,b_1,\dots)$ and $\Pr[A\text{ outputs }1]$ averages over both parties' coins.
--
--   **NP relations** (p. 43). $R(x,w)$ is decidable in polynomial time and every witness has length polynomial in $|x|$; $L_R = \{x : \exists w,\ R(x,w)\}$.
--
--   **Formalization Note** Drawing coins uniformly from $\{0,\dots,m-1\}$ is the sampling primitive; a fair-coin machine is the case $m = 2$. The output $1$ is the one-bit string `[true]`. Common input $(1^n, x)$ is `pack [1^n, x]`, the prover's input `pack [1^n, x, w]`.
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §3 p. 15 (PPT, negl), Definition 4 pp. 22–23 (PPT protocols), Definition 15 and NP relations p. 43

import Mathlib

namespace NovyPQZK.Main

/-!
Dupuis, Ligez, Medhioub, Salvail, Thibodeau, arXiv:2610.33185 (sha256 857d8563…3257f): the
classical layer of §3 (p. 15, Definition 4 on pp. 22–23) and §7 (Definition 15, p. 43).

* Bit strings, a self-delimiting encoding of lists of strings, binary numbers.
* Polynomial time: Mathlib's `Turing.TM2ComputableInPolyTime` on bit strings.
* A classical probabilistic interactive party (`Party`): it draws all its coins at the start,
  each uniformly from a range `{0, …, m − 1}` computed from its input, and computes each message
  deterministically from its view (input, coins, messages received). `Party.IsPPT` is uniform
  probabilistic polynomial time with exact uniform sampling.
* The run of two classical parties, the first speaking first in each round.
* NP relations (p. 43).
-/

/-- Classical bit strings. -/
abbrev Bits := List Bool

/-- `1^n`. -/
def unary (n : ℕ) : Bits := List.replicate n true

/-- The self-delimiting encoding of one string: `b ↦ 1b`, closed by a `0`. -/
def packOne (x : Bits) : Bits := x.flatMap (fun b => [true, b]) ++ [false]

/-- The injective encoding of a list of strings as one string. -/
def pack (l : List Bits) : Bits := l.flatMap packOne

/-- Parsing of `pack`; `cur` is the reversed current item. A truncated trailing item is dropped. -/
def unpackAux : Bits → Bits → List Bits
  | [], _ => []
  | false :: rest, cur => cur.reverse :: unpackAux rest []
  | true :: b :: rest, cur => unpackAux rest (b :: cur)
  | [true], _ => []

/-- The inverse of `pack` (total on all strings). -/
def unpack (x : Bits) : List Bits := unpackAux x []

/-- The first item of a packed string (`[]` if there is none): the decoding used whenever a
quantum party writes a string of arbitrary length into a fixed number of wires. -/
def decodeOne (x : Bits) : Bits := (unpack x).headD []

/-- A natural number in binary, least significant bit first, with no trailing zero. -/
def natToBits (k : ℕ) : Bits := Nat.bits k

/-- The number written in binary (least significant bit first) by a string. -/
def bitsToNat (b : Bits) : ℕ := b.foldr (fun x acc => 2 * acc + cond x 1 0) 0

/-- `f : Bits → Bits` is computable in polynomial time (one Turing machine, Mathlib's `TM2` model,
time polynomial in the input length). -/
def PolyTimeFn (f : Bits → Bits) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (id : Bits → Bits) (id : Bits → Bits) f)

/-- A number-valued function computable in polynomial time, its value written in unary (so it
is also polynomially bounded). -/
def PolyTimeNat (f : Bits → ℕ) : Prop := PolyTimeFn (fun s => unary (f s))

/-- The coins of a party drawing, for each entry `m` of `ms`, one uniform element of
`{0, …, m − 1}`. -/
abbrev CoinSpace (ms : List ℕ) := (i : Fin ms.length) → Fin (ms.get i)

/-- The encoding of drawn coins in the party's view. -/
def encCoins {ms : List ℕ} (c : CoinSpace ms) : Bits :=
  pack (List.ofFn fun i => natToBits (c i).val)

/-- The uniform average of `f` over a finite type (`0` on an empty type). -/
noncomputable def avgOver {M : Type*} [AddCommMonoid M] [Module ℝ M] (α : Type*) [Fintype α]
    (f : α → M) : M :=
  (Fintype.card α : ℝ)⁻¹ • ∑ a, f a

/-- A classical probabilistic interactive party. -/
structure Party where
  /-- The ranges of the uniform samples it draws, as a function of its input. -/
  coins : Bits → List ℕ
  /-- Its next message (and, at the end of the protocol, its output) as a function of its view
  `pack (input :: coins :: messages received so far)`. -/
  next : Bits → Bits

/-- The view of a party: input, coins and the messages received so far. -/
def Party.view (A : Party) (inp : Bits) (c : CoinSpace (A.coins inp)) (msgs : List Bits) : Bits :=
  pack (inp :: encCoins c :: msgs)

/-- The message a party sends, given its input, coins and the messages received so far. -/
def Party.msg (A : Party) (inp : Bits) (c : CoinSpace (A.coins inp)) (msgs : List Bits) : Bits :=
  A.next (A.view inp c msgs)

/-- Uniform probabilistic polynomial time with exact uniform sampling: the coin ranges and the
next-message function are polynomial-time computable, every range is nonempty, and every message
has length polynomial in the party's input, whatever it receives (so that polynomially many
rounds cost polynomial time in total). -/
def Party.IsPPT (A : Party) : Prop :=
  PolyTimeFn (fun s => pack ((A.coins s).map natToBits)) ∧ PolyTimeFn A.next ∧
    (∀ s, ∀ m ∈ A.coins s, 0 < m) ∧
    ∃ p : Polynomial ℕ, ∀ (inp : Bits) (c : CoinSpace (A.coins inp)) (msgs : List Bits),
      (A.msg inp c msgs).length ≤ p.eval inp.length

/-- The messages of `r` rounds between `A` (speaking first in each round) and `B`: the pair
(messages of `A`, messages of `B`). -/
def runMsgs (A B : Party) (inA inB : Bits) (cA : CoinSpace (A.coins inA))
    (cB : CoinSpace (B.coins inB)) : ℕ → List Bits × List Bits
  | 0 => ([], [])
  | r + 1 =>
      let p := runMsgs A B inA inB cA cB r
      let a := A.msg inA cA p.2
      let b := B.msg inB cB (p.1 ++ [a])
      (p.1 ++ [a], p.2 ++ [b])

/-- The public transcript `[a₀, b₀, a₁, b₁, …]` of a run. -/
def interleave : List Bits → List Bits → List Bits
  | a :: as, b :: bs => a :: b :: interleave as bs
  | as, [] => as
  | [], bs => bs

/-- The probability that `A` outputs `1` (the string `[true]`) after `r` rounds with `B`, over the
coins of both parties. -/
noncomputable def acceptProbCC (A B : Party) (inA inB : Bits) (r : ℕ) : ℝ :=
  avgOver (CoinSpace (A.coins inA) × CoinSpace (B.coins inB)) fun c =>
    if A.msg inA c.1 (runMsgs A B inA inB c.1 c.2 r).2 = [true] then 1 else 0

/-- p. 43: `R` is an NP relation: membership `(x, w) ∈ R` is decidable in polynomial time and
witnesses are polynomially bounded in `|x|`. -/
def IsNPRelation (R : Bits → Bits → Bool) : Prop :=
  PolyTimeFn (fun s => match unpack s with
    | [x, w] => [R x w]
    | _ => [false]) ∧
  ∃ p : Polynomial ℕ, ∀ x w, R x w = true → w.length ≤ p.eval x.length

/-- The common input `(1^n, x)` of an interactive protocol. -/
def commonInput (n : ℕ) (x : Bits) : Bits := pack [unary n, x]

/-- The prover's input `(1^n, x, w)`. -/
def proverInput (n : ℕ) (x w : Bits) : Bits := pack [unary n, x, w]

end NovyPQZK.Main


