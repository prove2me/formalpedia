-- Prove2me | Definitions.Def_DynStrings_Supplement_DynOps
-- name    : DynStrings_Supplement_DynOps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:51:11.373741+00:00
-- url     : https://prove2.me/theorems/83918b46-3f14-41a7-83fe-aa231dd59a5c
-- title:
--   Persistent dynamic strings: operations, handles, oblivious admissible sequences, execution, time and space (§6.1–6.2)
-- statement:
--   The operations of §6.1 and their execution on the word RAM.
--
--   1. **Operations.** $\mathrm{Insert}(S)$, $\mathrm{Concat}(X,Y)$, $\mathrm{Split}(X,i)$, $\mathrm{Delete}(X)$, $\mathrm{Get}(X)$, $\mathrm{Equal}(X,Y)$, $\mathrm{Lcp}(X,Y)$ and $\mathrm{Ipm}(X,Y)$. An oblivious sequence is fixed in advance, so it names handles abstractly: output $j$ of operation $t$, or the constant empty handle. The strings of the handles are computed from the sequence alone. Insert returns $S$, Concat returns $XY$, and Split returns $X[1\,.\,.\,i]$ and $X(i\,.\,.\,|X|]$.
--   2. **The collection.** $\mathcal W$ just before operation $s$ holds one copy of the string of every live (created and not yet deleted) handle to a non-empty string.
--   3. **Well-formed and admissible sequences.** Arguments are live handles or the empty handle; $i\in[0\,.\,.\,|X|]$ for Split; $X,Y$ are non-empty with $|Y|<2|X|$ for Ipm. Every character and every string length is below $2^w$, every string has fewer than $2^w$ live handles, and fewer than $2^w$ distinct non-empty strings are live at any time.
--   4. **Data structures and execution.** A data structure consists of an initialization program, one program per operation, the word of the empty handle, and the random orders it parses with, as a function of its coins. Memory and registers persist between operations, and arguments are passed in registers $0,1$. Insert receives a read-only caller block holding $S$; Get returns a block holding $X$, which is handed to the caller. The **running time** of an operation is its number of steps, the **resident space** is the space between operations, and the **transient space** is the largest total, over the steps of the operation, of the blocks it allocates and frees before returning.
--   5. **Correct answers.** Handles of empty results are the empty handle. Get returns $|X|$ words holding $X$, Equal returns $[X=Y]$, and Lcp the length of the longest common prefix. Ipm returns $(f,d,c)$ with $c=|\mathrm{Occ}(X,Y)|$ and $\mathrm{Occ}(X,Y)=\{f+jd:j<c\}$, where $\mathrm{Occ}(X,Y)=\{i\in[0\,.\,.\,|Y|-|X|]:Y(i\,.\,.\,i+|X|]=X\}$.
--   6. **Bounds.** `timeBound` is the table of Theorem 6.1, and `unionSize` is the run-length straight-line program size of the union of the grammars of the strings of $\mathcal W$ under the declared orders.
--
--   These definitions turn every clause of Theorem 6.1 into a statement about one execution of one data structure.
--
--   **Formalization Note** Characters are natural numbers. The time, transient space and resident space of a failed execution (a fault or no halt) are $\infty$; correctness excludes failures.
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), §6.1, pp.27–28 (PDF pp.28–29); §6.2, p.28 (PDF p.29); p.29 (PDF p.30); Theorem 6.1, p.29 (PDF p.30)

import Mathlib
import Definitions.Def_DynStrings_Parse
import Definitions.Def_DynStrings_Supplement_CollParams
import Definitions.Def_DynStrings_Supplement_WordRAM

namespace DynStrings.Supplement

/-!
# Persistent dynamic strings: operations, handles, oblivious sequences, and their execution

Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript,
sha256 cfcb3de9…), §6.1, pp.27–28 (operations), §6.2, p.28 (admissible and oblivious operation
sequences), p.29 (space; collection parameters), Theorem 6.1, p.29.

**Formalization Note.**
* **Strings.** Characters are natural numbers (the input characters are words); strings are
  `List ℕ`.
* **Oblivious sequences.** An operation sequence `σ : List Op` is fixed before the coins. Handles
  are values chosen by the data structure, so the sequence names them abstractly: `HRef.out t j`
  is output `j` of operation `t` (`Insert` and `Concat` have one output, `Split` two), and
  `HRef.empty` is the distinguished constant handle of the empty string. `str σ r` is the string
  of `r`, computed from the sequence alone (`absOuts`).
* **Live handles and `W`.** A handle `out t j` is live before operation `s` if `t < s` and no
  `Delete` of it occurs before `s`; handles to the empty string are the empty handle and are never
  part of `W`. `coll σ s` is the multiset `W` just before operation `s` (`coll σ |σ|` after the last
  one): one copy of the string of every live handle to a non-empty string.
* **Well-formed sequences** (§6.1): every argument is the empty handle or a live handle (a handle
  of an empty result counts as the empty handle); `Split(X, i)` has `i ∈ [0 . . |X|]`;
  `Ipm(X, Y)` has non-empty `X, Y` with `|Y| < 2|X|`.
* **Admissible sequences** (§6.2): every input character and every string involved has length
  `< 2^w`, at every time every string has fewer than `2^w` live handles (its reference count
  fits in a word), and at every time fewer than `2^w` distinct non-empty strings are live. The
  last clause is the part of the paper's "every memory address fits in a word" that the sequence
  controls: on the paper's machine a handle is a word, and live handles to distinct strings must
  differ from each other and from the empty handle. Memory addresses are opaque pointers in this
  model (see `WordRAM`), so the condition on the data structure's own addresses is not stated.
* **Calling convention.** A data structure has an initialization program and one program per
  operation; registers and memory persist between operations. Arguments are placed in registers
  `0, 1`: handles as given, a cut `i` as a word, and `Insert(S)` receives a pointer to a read-only
  caller block holding `S` in register `0` and `|S|` in register `1`. Outputs are read from
  registers `0, 1, 2` at `halt`. `Get(X)` returns in register `0` a pointer to a block of `|X|`
  words holding `X`; that block is then handed to the caller. Caller blocks (input and returned
  arrays) are removed after the operation and are never counted as space.
* **Time and space.** The running time of an operation is its number of executed steps. The
  resident space at a time between operations is `Mem.space` (allocated words of the data
  structure plus one word per block). The transient space of an operation is the largest total
  (`size + 1`) of blocks that the operation allocates and frees before returning, over all steps
  of the operation. Each is `⊤` if the execution fails (a fault or no halt), which correctness
  excludes on every outcome.
* **The grammar union.** A data structure also declares the random orders it parses with, as a
  function `orders` of its coins; `unionSize` is the RLSLP size (base `StrSym.weight`) of the union
  of the base `grammar`s of the current strings under these orders.
-/

open DynStrings MeasureTheory

/-- An abstract handle: the empty handle, or output `j` of operation `t` of the sequence. -/
inductive HRef where
  | empty
  | out (t j : ℕ)
  deriving DecidableEq

/-- The operations of §6.1, with handle arguments named abstractly. -/
inductive Op where
  | insert (S : List ℕ)
  | concat (x y : HRef)
  | split (x : HRef) (i : ℕ)
  | delete (x : HRef)
  | get (x : HRef)
  | equal (x y : HRef)
  | lcp (x y : HRef)
  | ipm (x y : HRef)
  deriving DecidableEq

/-- The number of handles an operation returns. -/
def Op.numOuts : Op → ℕ
  | .insert _ => 1
  | .concat _ _ => 1
  | .split _ _ => 2
  | _ => 0

/-! ## Abstract semantics -/

/-- The string of a handle, given the strings returned by earlier operations. -/
def refStr (outs : List (List (List ℕ))) : HRef → List ℕ
  | .empty => []
  | .out t j => (outs.getD t []).getD j []

/-- The strings returned by an operation, given the strings returned by earlier operations:
`Insert(S)` returns `S`, `Concat(X, Y)` returns `XY`, `Split(X, i)` returns `X[1 . . i]` and
`X(i . . |X|]`. -/
def opAbsOut (outs : List (List (List ℕ))) : Op → List (List ℕ)
  | .insert S => [S]
  | .concat x y => [refStr outs x ++ refStr outs y]
  | .split x i => [(refStr outs x).take i, (refStr outs x).drop i]
  | _ => []

/-- The strings returned by all operations of the sequence, in order. -/
def absOuts (σ : List Op) : List (List (List ℕ)) :=
  σ.foldl (fun outs o => outs ++ [opAbsOut outs o]) []

/-- The string of an abstract handle in the sequence `σ`. -/
def str (σ : List Op) (r : HRef) : List ℕ := refStr (absOuts σ) r

/-- The handle `r` is deleted by one of the first `s` operations. -/
def DeletedBefore (σ : List Op) (s : ℕ) (r : HRef) : Prop :=
  ∃ u < s, σ[u]? = some (.delete r)

/-- `r` may be passed to operation `s`: the empty handle, a handle to an empty result (which is the
empty handle), or a live handle created by an earlier operation and not deleted before `s`. -/
def Usable (σ : List Op) (s : ℕ) : HRef → Prop
  | .empty => True
  | .out t j => t < s ∧ (∃ o, σ[t]? = some o ∧ j < o.numOuts) ∧
      (str σ (.out t j) = [] ∨ ¬ DeletedBefore σ s (.out t j))

/-- The well-formedness conditions of §6.1 on the arguments of operation `s`. -/
def OpWF (σ : List Op) (s : ℕ) : Op → Prop
  | .insert _ => True
  | .concat x y => Usable σ s x ∧ Usable σ s y
  | .split x i => Usable σ s x ∧ i ≤ (str σ x).length
  | .delete x => Usable σ s x
  | .get x => Usable σ s x
  | .equal x y => Usable σ s x ∧ Usable σ s y
  | .lcp x y => Usable σ s x ∧ Usable σ s y
  | .ipm x y => Usable σ s x ∧ Usable σ s y ∧ str σ x ≠ [] ∧ str σ y ≠ [] ∧
      (str σ y).length < 2 * (str σ x).length

/-- A well-formed operation sequence. -/
def WellFormed (σ : List Op) : Prop := ∀ s (o : Op), σ[s]? = some o → OpWF σ s o

open Classical in
/-- The live handles to non-empty strings just before operation `s`. -/
noncomputable def liveRefs (σ : List Op) (s : ℕ) : List HRef :=
  ((List.range s).flatMap fun t =>
      (List.range ((σ[t]?.map Op.numOuts).getD 0)).map fun j => HRef.out t j).filter
    fun r => decide (str σ r ≠ [] ∧ ¬ DeletedBefore σ s r)

/-- The collection `W` just before operation `s` (after the last operation for `s = |σ|`): one
copy of the string of every live handle to a non-empty string. -/
noncomputable def coll (σ : List Op) (s : ℕ) : Multiset (List ℕ) :=
  ((liveRefs σ s).map (str σ) : Multiset (List ℕ))

/-- Admissibility (§6.2) at word size `w`: every input character fits in a word, every string
involved has length `< 2^w`, at every time every string has fewer than `2^w` live handles, and at
every time fewer than `2^w` distinct non-empty strings are live (their handles fit in a word). -/
def Admissible (w : ℕ) (σ : List Op) : Prop :=
  (∀ (s : ℕ) (S : List ℕ), σ[s]? = some (Op.insert S) → ∀ a ∈ S, a < 2 ^ w) ∧
  (∀ outs ∈ absOuts σ, ∀ Z ∈ outs, Z.length < 2 ^ w) ∧
  (∀ s ≤ σ.length, ∀ Z, (coll σ s).count Z < 2 ^ w) ∧
  (∀ s ≤ σ.length, (coll σ s).toFinset.card < 2 ^ w)

/-- The length of the longest common prefix of two strings. -/
def lcpLen : List ℕ → List ℕ → ℕ
  | a :: as, b :: bs => if a = b then lcpLen as bs + 1 else 0
  | _, _ => 0

/-- `Occ(X, Y) = {i ∈ [0 . . |Y| − |X|] : Y(i . . i + |X|] = X}`. -/
def occ (X Y : List ℕ) : Finset ℕ :=
  (Finset.range (Y.length + 1 - X.length)).filter fun i => frag Y i (i + X.length) = X

/-! ## Data structures and their execution -/

/-- A data structure: an initialization program, one program per operation, the word value of the
empty handle, and the random orders it parses with, as a function of its coins. -/
structure DataStructure where
  init : Program
  insert : Program
  concat : Program
  split : Program
  delete : Program
  get : Program
  equal : Program
  lcp : Program
  ipm : Program
  emptyHandle : ℕ
  orders : Coins → ℕ → StrSym ℕ → StrSym ℕ → Prop

/-- The program run for an operation. -/
def DataStructure.prog (D : DataStructure) : Op → Program
  | .insert _ => D.insert
  | .concat _ _ => D.concat
  | .split _ _ => D.split
  | .delete _ => D.delete
  | .get _ => D.get
  | .equal _ _ => D.equal
  | .lcp _ _ => D.lcp
  | .ipm _ _ => D.ipm

/-- The state between operations: the memory and the handle values returned so far (one list per
operation). -/
structure HState (w : ℕ) where
  mem : Mem w
  handles : List (List (Val w))

/-- The record of one executed operation. -/
structure OpResult (w : ℕ) where
  /-- registers `0, 1, 2` at `halt` -/
  outs : List (Val w)
  /-- the block returned by `Get` (the block register `0` points to at `halt`) -/
  ret : Option (Block w)
  /-- the number of executed steps -/
  time : ℕ
  /-- the transient space -/
  transient : ℕ

/-- The word value of a handle argument. -/
def handleVal {w : ℕ} (D : DataStructure) (st : HState w) : HRef → Val w
  | .empty => .word (BitVec.ofNat w D.emptyHandle)
  | .out t j => (st.handles.getD t []).getD j (.word 0)

/-- The memory at the start of an operation: its arguments in registers `0, 1`; for `Insert(S)` a
new read-only caller block holding `S`. -/
def startMem {w : ℕ} (D : DataStructure) (st : HState w) : Op → Mem w
  | .insert S =>
    let m := st.mem
    ⟨Function.update (Function.update m.regs 0 (.ptr m.next)) 1
        (.word (BitVec.ofNat w S.length)),
      Function.update m.heap m.next
        (some ⟨S.length, fun o => .word (BitVec.ofNat w (S.getD o 0)), true⟩),
      m.next + 1, m.coin⟩
  | .concat x y => (st.mem.setReg 0 (handleVal D st x)).setReg 1 (handleVal D st y)
  | .split x i => (st.mem.setReg 0 (handleVal D st x)).setReg 1 (.word (BitVec.ofNat w i))
  | .delete x => st.mem.setReg 0 (handleVal D st x)
  | .get x => st.mem.setReg 0 (handleVal D st x)
  | .equal x y => (st.mem.setReg 0 (handleVal D st x)).setReg 1 (handleVal D st y)
  | .lcp x y => (st.mem.setReg 0 (handleVal D st x)).setReg 1 (handleVal D st y)
  | .ipm x y => (st.mem.setReg 0 (handleVal D st x)).setReg 1 (handleVal D st y)

/-- The block a value points to, if it is a pointer to a live block. -/
def pointee {w : ℕ} (m : Mem w) : Val w → Option (Block w)
  | .ptr b => m.heap b
  | .word _ => none

/-- Remove the caller blocks and, for `Get`, hand the returned block to the caller. -/
def cleanup {w : ℕ} (m : Mem w) (isGet : Bool) : Mem w :=
  { m with heap := fun b =>
      match m.heap b with
      | some B => if B.callerOwned || (isGet && decide (m.regs 0 = .ptr b)) then none else some B
      | none => none }

/-- The space at a configuration of the blocks numbered in `[lo, hi)` that are freed before the
operation returns (they are not live in the final memory `fin`). -/
def transientAt {w : ℕ} (lo : ℕ) (fin : Mem w) (m : Mem w) : ℕ :=
  ∑ b ∈ Finset.Ico lo fin.next,
    if fin.heap b = none then
      (match m.heap b with
        | some B => B.size + 1
        | none => 0)
    else 0

/-- `Get` operations. -/
def Op.isGet : Op → Bool
  | .get _ => true
  | _ => false

open Classical in
/-- Execute one operation from the state `st`: `none` if the program faults or does not halt. -/
noncomputable def doOp {w : ℕ} (D : DataStructure) (junk : ℕ → ℕ → BitVec w) (ω : Coins)
    (st : HState w) (o : Op) : Option (HState w × OpResult w) :=
  let P := D.prog o
  let c₀ : Config w := ⟨0, startMem D st o, .running⟩
  if Halts junk P ω c₀ then
    let T := haltTime junk P ω c₀
    let fin := (run junk P ω c₀ T).mem
    let outs := [fin.regs 0, fin.regs 1, fin.regs 2]
    let tr := (Finset.range (T + 1)).sup fun k =>
      transientAt st.mem.next fin (run junk P ω c₀ k).mem
    some (⟨cleanup fin o.isGet, st.handles ++ [outs.take o.numOuts]⟩,
      ⟨outs, if o.isGet then pointee fin (fin.regs 0) else none, T, tr⟩)
  else none

open Classical in
/-- The state after the initialization program, if it halts. -/
noncomputable def initState {w : ℕ} (D : DataStructure) (junk : ℕ → ℕ → BitVec w)
    (ω : Coins) : Option (HState w) :=
  let c₀ : Config w := ⟨0, ⟨fun _ => .word 0, fun _ => none, 0, 0⟩, .running⟩
  if Halts junk D.init ω c₀ then
    some ⟨(run junk D.init ω c₀ (haltTime junk D.init ω c₀)).mem, []⟩
  else none

/-- The state just before operation `s` (after initialization and operations `0, …, s − 1`). -/
noncomputable def stateBefore {w : ℕ} (D : DataStructure) (junk : ℕ → ℕ → BitVec w)
    (σ : List Op) (ω : Coins) : ℕ → Option (HState w)
  | 0 => initState D junk ω
  | s + 1 => (stateBefore D junk σ ω s).bind fun st =>
      σ[s]?.bind fun o => (doOp D junk ω st o).map Prod.fst

/-- The record of operation `s`. -/
noncomputable def opResult {w : ℕ} (D : DataStructure) (junk : ℕ → ℕ → BitVec w)
    (σ : List Op) (ω : Coins) (s : ℕ) : Option (OpResult w) :=
  (stateBefore D junk σ ω s).bind fun st =>
    σ[s]?.bind fun o => (doOp D junk ω st o).map Prod.snd

/-- The running time of operation `s` (`⊤` if the execution fails). -/
noncomputable def opTime {w : ℕ} (D : DataStructure) (junk : ℕ → ℕ → BitVec w)
    (σ : List Op) (ω : Coins) (s : ℕ) : ENNReal :=
  match opResult D junk σ ω s with
  | some r => r.time
  | none => ⊤

/-- The transient space of operation `s` (`⊤` if the execution fails). -/
noncomputable def opTransient {w : ℕ} (D : DataStructure) (junk : ℕ → ℕ → BitVec w)
    (σ : List Op) (ω : Coins) (s : ℕ) : ENNReal :=
  match opResult D junk σ ω s with
  | some r => r.transient
  | none => ⊤

/-- The resident space just before operation `s` (after the last operation for `s = |σ|`), in
words (`⊤` if the execution fails). -/
noncomputable def resident {w : ℕ} (D : DataStructure) (junk : ℕ → ℕ → BitVec w)
    (σ : List Op) (ω : Coins) (s : ℕ) : ENNReal :=
  match stateBefore D junk σ ω s with
  | some st => st.mem.space
  | none => ⊤

/-- The RLSLP size of the union of the grammars of the strings of `W` just before operation `s`,
under the orders the data structure draws with the coins `ω`. -/
noncomputable def unionSize (D : DataStructure) (σ : List Op) (s : ℕ) (ω : Coins) : ℕ :=
  ∑ A ∈ (coll σ s).toFinset.biUnion (fun Z => grammar (D.orders ω) Z), StrSym.weight A

/-- The answer of operation `s` is correct: the returned handle of an empty result is the empty
handle; `Get(X)` returns a block of `|X|` words holding `X`; `Equal`, `Lcp` return the right word;
`Ipm(X, Y)` returns `(first, offset, count)` whose progression is exactly `Occ(X, Y)`. -/
def AnswerOK {w : ℕ} (D : DataStructure) (σ : List Op) (r : OpResult w) : Op → Prop
  | .insert S => S = [] → r.outs.getD 0 (.ptr 0) = .word (BitVec.ofNat w D.emptyHandle)
  | .concat x y => str σ x ++ str σ y = [] →
      r.outs.getD 0 (.ptr 0) = .word (BitVec.ofNat w D.emptyHandle)
  | .split x i =>
      ((str σ x).take i = [] → r.outs.getD 0 (.ptr 0) = .word (BitVec.ofNat w D.emptyHandle)) ∧
      ((str σ x).drop i = [] → r.outs.getD 1 (.ptr 0) = .word (BitVec.ofNat w D.emptyHandle))
  | .delete _ => True
  | .get x => ∃ B, r.ret = some B ∧ B.size = (str σ x).length ∧
      ∀ o < (str σ x).length, B.data o = .word (BitVec.ofNat w ((str σ x).getD o 0))
  | .equal x y => r.outs.getD 0 (.ptr 0) = .word (if str σ x = str σ y then 1 else 0)
  | .lcp x y => r.outs.getD 0 (.ptr 0) = .word (BitVec.ofNat w (lcpLen (str σ x) (str σ y)))
  | .ipm x y => ∃ f d c : BitVec w,
      r.outs = [.word f, .word d, .word c] ∧ c.toNat = (occ (str σ x) (str σ y)).card ∧
      ∀ i, i ∈ occ (str σ x) (str σ y) ↔ ∃ j < c.toNat, i = f.toNat + j * d.toNat

/-- The time bound of Theorem 6.1 for operation `s` (without the hidden constant). -/
noncomputable def timeBound (σ : List Op) (s : ℕ) (η : ℝ) : Op → ℝ
  | .insert S => 1 + S.length * tau 1 η
  | .split x _ => tau (str σ x).length η
  | .concat x y => tau ((str σ x).length + (str σ y).length) η
  | .lcp x y => tau (max (str σ x).length (str σ y).length) η
  | .ipm x y => tau (max (str σ x).length (str σ y).length) η
  | .delete x => (1 + deltaRel (str σ x) (coll σ (s + 1))) * tau (str σ x).length η
  | .get x => 1 + (str σ x).length
  | .equal _ _ => 1

end DynStrings.Supplement


