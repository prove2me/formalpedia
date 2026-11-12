-- Prove2me | Definitions.Def_RTStringIndex_Main_Machine
-- name    : RTStringIndex_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:11.294241+00:00
-- url     : https://prove2.me/theorems/91353471-a932-4ef4-8aa3-043e48f879cf
-- title:
--   Online streams of appends and pattern queries on the randomized word RAM
-- statement:
--   The machine is the online randomized word RAM `DynConnWC_Program`. It has unit-cost arithmetic and bit operations on $W$-bit words, indirect memory access, an online input read one word at a time, output writes, and a random tape of independent uniform $W$-bit words.
--
--   A **stream** is a list of operations. The operation $\mathrm{append}(a)$ adds the letter $a$ at the right end of the text, and is the input words $0,a$. The operation $\mathrm{query}(P)$ asks for the occurrences of $P$, and is the words $1,|P|,P[1],\dots,P[|P|]$.
--
--   The **time** of an operation is the number of steps from the read of its first word to the read of the first word of the next operation, or of the end marker after the last one. Its **output** is the list of words written in that window. Space up to an operation is the set of memory cells touched from the start of the run to the end of that operation. The text after $t$ operations is the list of letters appended by them.
--
--   The law of the random tape is the product of uniform measures on $W$-bit words.
--
--   For Lemma 1, a program may also be started from a given memory content. A symbol is stored as a word: a letter $a$ as $a+1$, and $\$$ as $0$.
--
--   These definitions turn Theorem 1's real-time, query-time and space claims into statements about one run of one program.
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), Theorem 1, p. 2; Abstract, p. 1 (letters appended to T); §10, p. 24 (randomization only in the dictionaries); PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_RTStringIndex_Main_Strings

set_option autoImplicit false

namespace RTStringIndex.Main

/-! # Running a program on an online stream of appends and pattern queries

Kucherov, Nekrich, STOC 2027 submission #1543 (October 2026), Theorem 1, p.2: "Let T be a text
over an integer alphabet of arbitrary size that is given online, one letter at a time, and let n
denote the current length of T. On the word RAM, there is a data structure that uses O(n) words of
space and, for any constant c > 0, processes each new letter in O(1) worst-case time with
probability at least 1 − n^{−c}. At any moment, given a pattern P, it can report all occ
occurrences of P in the current text T in O(|P| + occ) worst-case time"; Abstract, p.1: "each new
letter appended to T".

**Formalization Note.** The machine is the online randomized word RAM `DynConnWC.Program`
(published definition `DynConnWC_Program`). A stream is a list of operations: `append a` adds the
letter `a` at the right end of the text, `query P` asks for the occurrences of `P`. An append is
the input words `0, a`; a query is `1, |P|` followed by the letters of `P`. Operation `t`
(`0`-based) starts with read number `firstRead σ t`; read number `firstRead σ |σ|` returns the
all-ones end marker. The **time** of operation `t` is the number of steps from the read of its
first word to the read of the first word of operation `t + 1` (or of the end marker); its
**output** is the list of words written in that window. Space is measured by the memory cells
touched from the start of the run to the end of the window of operation `t`. The random tape has
the law `tapeLaw W`: independent uniform `W`-bit words. `confFrom` runs a program from a given
memory content (used for Lemma 1); `symCode` stores a letter `a` as the word `a + 1` and `$` as
`0`. -/

open DynConnWC MeasureTheory

/-- An operation of the stream. -/
inductive Op where
  /-- append the letter `a` at the right end of the text -/
  | append (a : ℕ)
  /-- report the occurrences of the pattern `P` -/
  | query (P : List ℕ)

/-- The input words of one operation. -/
def Op.words : Op → List ℕ
  | .append a => [0, a]
  | .query P => [1, P.length] ++ P

/-- The input words of a stream. -/
def inputWords (σ : List Op) : List ℕ := σ.flatMap Op.words

/-- The number (counting from `1`) of the read that takes the first word of operation `t`; for
`t = |σ|`, the read that returns the end marker. -/
def firstRead (σ : List Op) (t : ℕ) : ℕ := ((σ.take t).flatMap Op.words).length + 1

/-- The letters appended by the first `t` operations: the text after them. -/
def textAfter (σ : List Op) (t : ℕ) : List ℕ :=
  (σ.take t).flatMap (fun o => match o with | .append a => [a] | .query _ => [])

/-- The number of appends in the stream. -/
def numAppends (σ : List Op) : ℕ := (textAfter σ σ.length).length

/-- Every letter and every pattern letter is below `2^W`, and so is every pattern length. -/
def WordsFit (W : ℕ) (σ : List Op) : Prop :=
  ∀ o ∈ σ, match o with
    | .append a => a < 2 ^ W
    | .query P => P.length < 2 ^ W ∧ ∀ x ∈ P, x < 2 ^ W

/-- The run reaches the read of the first word of every operation and the end-marker read. -/
def RunsThrough (W : ℕ) (Q : Program) (ω : ℕ → Fin (2 ^ W)) (σ : List Op) : Prop :=
  ∀ t, t ≤ σ.length → (readStep W Q (inputWords σ) ω (firstRead σ t)).isSome

/-- The step at which operation `t` starts (its first word is read). -/
noncomputable def startStep (W : ℕ) (Q : Program) (ω : ℕ → Fin (2 ^ W)) (σ : List Op)
    (t : ℕ) : ℕ :=
  (readStep W Q (inputWords σ) ω (firstRead σ t)).getD 0

/-- The time of operation `t`. -/
noncomputable def opTime (W : ℕ) (Q : Program) (ω : ℕ → Fin (2 ^ W)) (σ : List Op)
    (t : ℕ) : ℕ :=
  startStep W Q ω σ (t + 1) - startStep W Q ω σ t

/-- The words written during operation `t`. -/
noncomputable def opOutput (W : ℕ) (Q : Program) (ω : ℕ → Fin (2 ^ W)) (σ : List Op)
    (t : ℕ) : List ℕ :=
  outputBetween W Q (inputWords σ) ω (startStep W Q ω σ t) (startStep W Q ω σ (t + 1))

/-- The memory cells touched from the start of the run to the end of operation `t`. -/
noncomputable def addrsUpTo (W : ℕ) (Q : Program) (ω : ℕ → Fin (2 ^ W)) (σ : List Op)
    (t : ℕ) : Set ℕ :=
  touchedBetween W Q (inputWords σ) ω 0 (startStep W Q ω σ (t + 1))

/-- The law of the random tape: independent uniform `W`-bit words. -/
noncomputable def tapeLaw (W : ℕ) : Measure (ℕ → Fin (2 ^ W)) :=
  Measure.infinitePi (fun _ => (PMF.uniformOfFintype (Fin (2 ^ W))).toMeasure)

/-- The configuration after `t` steps of `P` started from memory `mem` (program counter `0`,
nothing read, drawn or written yet). -/
def confFrom (W : ℕ) (P : Program) (mem : ℕ → BitVec W) (inp : List ℕ) (ω : ℕ → Fin (2 ^ W))
    (t : ℕ) : Config W :=
  (step P inp ω)^[t] ⟨0, mem, 0, 0, []⟩

/-- The configuration `c` is halted: at `halt` or with the program counter outside `P`. -/
def Halted {W : ℕ} (P : Program) (c : Config W) : Prop :=
  P[c.pc]? = none ∨ P[c.pc]? = some Instr.halt

/-- The word storing a symbol of the suffix tree: a letter `a` is `a + 1`, the terminator `0`. -/
def symCode : Chr → ℕ
  | ⊤ => 0
  | (a : ℕ) => a + 1

end RTStringIndex.Main


