-- Prove2me | Definitions.Def_DisjointPathsDAG_Machine
-- name    : DisjointPathsDAG_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:25.868236+00:00
-- url     : https://prove2.me/theorems/41903665-3b7b-4c11-bfa4-e4ff50ae119b
-- title:
--   The randomized word RAM with exact real additions and a finite-field bank
-- statement:
--   The model of computation of Section 2.1, as a machine. A **program** is a finite list of instructions acting on three banks of cells indexed by $\mathbb N$:
--
--   1. **words** of $w$ bits, with literals, $+,-,\times$, division, remainder, bitwise and, or, xor, shifts (all modulo $2^w$), indirect load and store, branches on $<$ and $=$, jumps and halt;
--   2. **reals**, with zero, $+$, $-$, indirect load and store addressed by words, and branches on $<$ and $=$; there is no real multiplication, division, floor or conversion to words;
--   3. **field cells** over a finite field $F$, with $0$, $1$, $+,-,\times$, inversion, indirect load and store, a branch on $=0$, the field element numbered by a word, and a fresh **uniform** field element.
--
--   The random tape has one independent uniform element of $F$ per time step, read by the sampling instruction executed at that step. Every executed instruction costs $1$; a run that halts after $t$ steps takes time $t+1$, and a run that never halts takes time $+\infty$. The **space** of a run is the largest number of cells whose content differs from the start. The input is placed in the first cells of the three banks; the output words follow the input words, preceded by their number, and field outputs follow the input field cells. A **generator** writes a straight-line program as output words and is constructed "in time linear in its length" if it halts within $C(\text{size}+1)$ steps on every tape.
--
--   Runs use $A\lceil\log_2(N+2)\rceil$-bit words for an input of size $N$, which is the paper's $\Theta(\log(m+n))$.
--
--   **Formalization Note** The absence of real multiplication and floor rules out packing data into reals. Lean's conventions $0^{-1}=0$ and division by the zero word give $0$; a program can test these cases first. A program counter past the end acts as halt.
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 2.1, p.6

import Mathlib
import Definitions.Def_DisjointPathsDAG_SLP

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DisjointPathsDAG

/-!
# The randomized word RAM with a real bank and a finite-field bank

Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 2.1, p.6: "Real edge weights are
handled by unit-cost exact additions, subtractions, and comparisons of weight values […]. All other
computation takes place on a word RAM with Θ(log(m + n))-bit words. Polynomial evaluations use a field
F2q with q = Θ(log(m + n)), whose elements fit in a constant number of words; field operations and
uniform sampling of field elements take unit time. The constant in q depends on the error exponent."

**Formalization Note** A deep-embedded machine, bundled in one module with its run, cost, space,
tape law, output conventions and the SLP-generation predicate, since they are mutually dependent.
* Parameters of a run: a word width `w` and a finite field `F`. A program is a list of instructions
  that mentions neither, so one program runs at every width and over every field.
* Three banks of cells indexed by `ℕ`: words `W : ℕ → BitVec w`, reals `Rl : ℕ → ℝ`, field cells
  `Fc : ℕ → F`. Word operations are those of `BitVec w`, i.e. modulo `2^w` (division and remainder by
  `0` give `0` and the dividend, Lean's `BitVec` convention). Addresses are word values.
* Reals: zero, `+`, `-`, indirect load/store, and branches on `<` and `=`. There is **no real
  multiplication, division, floor, or real-to-word conversion**: Section 2.1 allows exact addition,
  subtraction and comparison only, and this omission rules out packing data into reals.
* Field cells: `0`, `1`, `+`, `-`, `·`, inverse (Lean's `0⁻¹ = 0`, harmless since a program can test
  for `0` first), indirect load/store, branch on `= 0`, `fofword` (the field element numbered by a word
  value modulo `|F|`, through a fixed bijection `F ≃ Fin |F|`, so that a program can name distinct
  elements), and `funif`, which writes a fresh uniform field element. There is no field-to-word
  conversion.
* Randomness: the tape `ω : ℕ → Fin |F|` has independent uniform coordinates; `funif` executed at step
  `t` reads `ω t`, so distinct draws are independent by construction.
* Cost: every executed instruction costs `1`, input reads included; a run that halts after `t` steps
  has running time `t + 1` (the `halt` counted), and a run that never halts has running time `⊤`.
  A program counter past the end of the program acts as `halt`.
* Space: the largest number of cells (over all banks) whose content differs from the initial state, over
  all times of the run.
* Input: three lists, put in the cells `0, 1, …` of the three banks; every other cell is `0`. Word
  inputs are natural numbers, read modulo `2^w`; each statement chooses `w` so that its inputs fit.
* Output: the word cell at index `|input words|` holds the output length `L`, and the next `L` word
  cells hold the output words; field outputs are the field cells from index `|input field cells|` on.
-/

/-- An instruction. `W[·]`, `Rl[·]`, `Fc[·]` are the word, real and field cells.
* `wlit i c`: `W[i] := c mod 2^w`; `wadd … wshr i j k`: `W[i] := W[j] ∘ W[k]` (`shl`/`shr` shift by
  the value of `W[k]`); `wload i j`: `W[i] := W[W[j]]`; `wstore i j`: `W[W[i]] := W[j]`;
  `wblt i j l` / `wbeq i j l`: go to `l` if `W[i] < W[j]` / `W[i] = W[j]`; `jmp l`; `halt`.
* `rzero i`: `Rl[i] := 0`; `radd/rsub i j k`: `Rl[i] := Rl[j] ± Rl[k]`; `rload i j`: `Rl[i] := Rl[W[j]]`;
  `rstore i j`: `Rl[W[i]] := Rl[j]`; `rblt i j l` / `rbeq i j l`: go to `l` if `Rl[i] < Rl[j]` /
  `Rl[i] = Rl[j]`.
* `fzero i`, `fone i`; `fadd/fsub/fmul i j k`: `Fc[i] := Fc[j] ∘ Fc[k]`; `finv i j`: `Fc[i] := Fc[j]⁻¹`;
  `fload i j`: `Fc[i] := Fc[W[j]]`; `fstore i j`: `Fc[W[i]] := Fc[j]`; `fbz i l`: go to `l` if
  `Fc[i] = 0`; `fofword i j`: `Fc[i] :=` the field element numbered `W[j] mod |F|`; `funif i`:
  `Fc[i] :=` the fresh uniform element of the current step. -/
inductive Instr where
  | wlit (i c : ℕ)
  | wadd (i j k : ℕ)
  | wsub (i j k : ℕ)
  | wmul (i j k : ℕ)
  | wdiv (i j k : ℕ)
  | wmod (i j k : ℕ)
  | wand (i j k : ℕ)
  | wor (i j k : ℕ)
  | wxor (i j k : ℕ)
  | wshl (i j k : ℕ)
  | wshr (i j k : ℕ)
  | wload (i j : ℕ)
  | wstore (i j : ℕ)
  | wblt (i j l : ℕ)
  | wbeq (i j l : ℕ)
  | jmp (l : ℕ)
  | halt
  | rzero (i : ℕ)
  | radd (i j k : ℕ)
  | rsub (i j k : ℕ)
  | rload (i j : ℕ)
  | rstore (i j : ℕ)
  | rblt (i j l : ℕ)
  | rbeq (i j l : ℕ)
  | fzero (i : ℕ)
  | fone (i : ℕ)
  | fadd (i j k : ℕ)
  | fsub (i j k : ℕ)
  | fmul (i j k : ℕ)
  | finv (i j : ℕ)
  | fload (i j : ℕ)
  | fstore (i j : ℕ)
  | fbz (i l : ℕ)
  | fofword (i j : ℕ)
  | funif (i : ℕ)

/-- A program: a finite list of instructions, independent of the word width and of the field. -/
abbrev Program := List Instr

/-- A machine state: program counter and the three banks. -/
structure State (w : ℕ) (F : Type) where
  pc : ℕ
  W : ℕ → BitVec w
  Rl : ℕ → ℝ
  Fc : ℕ → F

/-- An input: the word, real and field-cell inputs. -/
structure Input (F : Type) where
  ws : List ℕ
  rs : List ℝ
  fs : List F

/-- The size of an input: the number of input cells plus the largest input word. -/
def Input.size {F : Type} (I : Input F) : ℕ :=
  I.ws.length + I.rs.length + I.fs.length + I.ws.foldr max 0

/-- The random tape: one uniform element of `Fin |F|` per time step. -/
abbrev Tape (F : Type) [Finite F] := ℕ → Fin (Nat.card F)

/-- The field element numbered `v mod |F|` (through the fixed bijection `Finite.equivFin`). -/
noncomputable def fieldOfWord (F : Type) [Field F] [Finite F] (v : ℕ) : F :=
  (Finite.equivFin F).symm ⟨v % Nat.card F, Nat.mod_lt _ Nat.card_pos⟩

/-- The constant table a program on the machine can realize at unit cost: index `0` is `0`, index `1`
is `1`, index `c + 2` is the field element numbered `c` (every element of `F` has such an index). -/
noncomputable def fieldTable (F : Type) [Field F] [Finite F] : ℕ → F
  | 0 => 0
  | 1 => 1
  | c + 2 => fieldOfWord F c

/-- The initial state on the input `I`. -/
noncomputable def initState (w : ℕ) (F : Type) [Zero F] (I : Input F) : State w F :=
  ⟨0, fun i => BitVec.ofNat w (I.ws.getD i 0), fun i => I.rs.getD i 0, fun i => I.fs.getD i 0⟩

open Classical in
/-- One step of `P` at time `t` on the tape `ω`. A halted state is unchanged. -/
noncomputable def step (w : ℕ) (F : Type) [Field F] [Finite F] (P : Program) (ω : Tape F) (t : ℕ)
    (s : State w F) : State w F :=
  let nx := s.pc + 1
  let setW : ℕ → BitVec w → State w F := fun i v => { s with pc := nx, W := Function.update s.W i v }
  let setR : ℕ → ℝ → State w F := fun i v => { s with pc := nx, Rl := Function.update s.Rl i v }
  let setF : ℕ → F → State w F := fun i v => { s with pc := nx, Fc := Function.update s.Fc i v }
  match P[s.pc]? with
  | none => s
  | some .halt => s
  | some (.wlit i c) => setW i (BitVec.ofNat w c)
  | some (.wadd i j k) => setW i (s.W j + s.W k)
  | some (.wsub i j k) => setW i (s.W j - s.W k)
  | some (.wmul i j k) => setW i (s.W j * s.W k)
  | some (.wdiv i j k) => setW i (s.W j / s.W k)
  | some (.wmod i j k) => setW i (s.W j % s.W k)
  | some (.wand i j k) => setW i (s.W j &&& s.W k)
  | some (.wor i j k) => setW i (s.W j ||| s.W k)
  | some (.wxor i j k) => setW i (s.W j ^^^ s.W k)
  | some (.wshl i j k) => setW i (s.W j <<< (s.W k).toNat)
  | some (.wshr i j k) => setW i (s.W j >>> (s.W k).toNat)
  | some (.wload i j) => setW i (s.W (s.W j).toNat)
  | some (.wstore i j) => { s with pc := nx, W := Function.update s.W (s.W i).toNat (s.W j) }
  | some (.wblt i j l) => { s with pc := if s.W i < s.W j then l else nx }
  | some (.wbeq i j l) => { s with pc := if s.W i = s.W j then l else nx }
  | some (.jmp l) => { s with pc := l }
  | some (.rzero i) => setR i 0
  | some (.radd i j k) => setR i (s.Rl j + s.Rl k)
  | some (.rsub i j k) => setR i (s.Rl j - s.Rl k)
  | some (.rload i j) => setR i (s.Rl (s.W j).toNat)
  | some (.rstore i j) => { s with pc := nx, Rl := Function.update s.Rl (s.W i).toNat (s.Rl j) }
  | some (.rblt i j l) => { s with pc := if s.Rl i < s.Rl j then l else nx }
  | some (.rbeq i j l) => { s with pc := if s.Rl i = s.Rl j then l else nx }
  | some (.fzero i) => setF i 0
  | some (.fone i) => setF i 1
  | some (.fadd i j k) => setF i (s.Fc j + s.Fc k)
  | some (.fsub i j k) => setF i (s.Fc j - s.Fc k)
  | some (.fmul i j k) => setF i (s.Fc j * s.Fc k)
  | some (.finv i j) => setF i (s.Fc j)⁻¹
  | some (.fload i j) => setF i (s.Fc (s.W j).toNat)
  | some (.fstore i j) => { s with pc := nx, Fc := Function.update s.Fc (s.W i).toNat (s.Fc j) }
  | some (.fbz i l) => { s with pc := if s.Fc i = 0 then l else nx }
  | some (.fofword i j) => setF i (fieldOfWord F (s.W j).toNat)
  | some (.funif i) => setF i ((Finite.equivFin F).symm (ω t))

/-- The state after `t` steps of `P` on the input `I` and the tape `ω`. -/
noncomputable def stateAt (w : ℕ) (F : Type) [Field F] [Finite F] (P : Program) (I : Input F)
    (ω : Tape F) : ℕ → State w F
  | 0 => initState w F I
  | t + 1 => step w F P ω t (stateAt w F P I ω t)

/-- The state `s` is halted under `P`: its instruction is `halt`, or the counter is past the end. -/
def IsHalted {w : ℕ} {F : Type} (P : Program) (s : State w F) : Prop :=
  P[s.pc]? = none ∨ P[s.pc]? = some Instr.halt

/-- The run halts at step `t`: `t` is the first time its state is halted. -/
def HaltsAt (w : ℕ) (F : Type) [Field F] [Finite F] (P : Program) (I : Input F) (ω : Tape F)
    (t : ℕ) : Prop :=
  IsHalted P (stateAt w F P I ω t) ∧ ∀ t' < t, ¬ IsHalted P (stateAt w F P I ω t')

/-- The running time: `t + 1` for a run halting at step `t` (the `t` executed instructions and the
final `halt`), and `⊤` for a run that never halts. -/
noncomputable def haltTime (w : ℕ) (F : Type) [Field F] [Finite F] (P : Program) (I : Input F)
    (ω : Tape F) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : IsHalted P (stateAt w F P I ω t)), ((t + 1 : ℕ) : ℕ∞)

/-- The space of the run: the supremum over all times of the number of cells, in all three banks,
whose content differs from the initial state. -/
noncomputable def spaceUsed (w : ℕ) (F : Type) [Field F] [Finite F] (P : Program) (I : Input F)
    (ω : Tape F) : ℕ∞ :=
  ⨆ t : ℕ,
    ({a : ℕ | (stateAt w F P I ω t).W a ≠ (initState w F I).W a}.encard +
      {a : ℕ | (stateAt w F P I ω t).Rl a ≠ (initState w F I).Rl a}.encard +
      {a : ℕ | (stateAt w F P I ω t).Fc a ≠ (initState w F I).Fc a}.encard)

/-- The output words of a state: `L := W[|I.ws|]` words from `W[|I.ws| + 1]` on, as naturals. -/
def outWords {w : ℕ} {F : Type} (I : Input F) (s : State w F) : List ℕ :=
  (List.range (s.W I.ws.length).toNat).map fun i => (s.W (I.ws.length + 1 + i)).toNat

/-- Field output number `i` of a state: the field cell `|I.fs| + i`. -/
def outField {w : ℕ} {F : Type} (I : Input F) (s : State w F) (i : ℕ) : F :=
  s.Fc (I.fs.length + i)

/-- The decision answer of a state: "yes" iff the first output word is `1`. -/
def answerYes {w : ℕ} {F : Type} (I : Input F) (s : State w F) : Prop :=
  (outWords I s).head? = some 1

/-- The law of the tape: independent coordinates, each uniform on `Fin |F|`. -/
noncomputable def tapeLaw (F : Type) [Field F] [Finite F] : Measure (Tape F) :=
  haveI : NeZero (Nat.card F) := ⟨Nat.card_pos.ne'⟩
  Measure.infinitePi fun _ => (PMF.uniformOfFintype (Fin (Nat.card F))).toMeasure

instance (F : Type) [Field F] [Finite F] : IsProbabilityMeasure (tapeLaw F) := by
  have : NeZero (Nat.card F) := ⟨Nat.card_pos.ne'⟩
  unfold tapeLaw
  infer_instance

/-- The word width of a run of a statement with constant `A` on an input of size `N`:
`A · ⌈log₂(N + 2)⌉`, i.e. `Θ(log N)` bits for fixed `A ≥ 1`. Every input word `≤ N` fits. -/
def wordWidth (A N : ℕ) : ℕ := A * Nat.clog 2 (N + 2)

/-- "Constructed in time linear in its length": the generator `Gen`, run on the word input `inp` with
width `wordWidth A |inp|` (the field bank, unused, is `ZMod 2`), halts on every tape at a step `t`
with `t + 1 ≤ C · (size + 1)`, where the output words decode (`SLP.decode`) to a program `P` with
property `spec`. -/
def GeneratesSLP (Gen : Program) (A : ℕ) (inp : List ℕ) (C : ℝ) (spec : SLP → Prop) : Prop :=
  ∀ ω : Tape (ZMod 2), ∃ t : ℕ,
    HaltsAt (wordWidth A (Input.size (⟨inp, [], []⟩ : Input (ZMod 2)))) (ZMod 2) Gen ⟨inp, [], []⟩ ω t ∧
    spec (SLP.decode (outWords (⟨inp, [], []⟩ : Input (ZMod 2))
      (stateAt (wordWidth A (Input.size (⟨inp, [], []⟩ : Input (ZMod 2)))) (ZMod 2) Gen
        ⟨inp, [], []⟩ ω t))) ∧
    ((t : ℝ) + 1 ≤ C * (((SLP.decode (outWords (⟨inp, [], []⟩ : Input (ZMod 2))
      (stateAt (wordWidth A (Input.size (⟨inp, [], []⟩ : Input (ZMod 2)))) (ZMod 2) Gen
        ⟨inp, [], []⟩ ω t))).size : ℝ) + 1))

end DisjointPathsDAG


