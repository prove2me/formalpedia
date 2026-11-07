-- Prove2me | Definitions.Def_DynConnWC_Run
-- name    : DynConnWC_Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:34:34.373204+00:00
-- url     : https://prove2.me/theorems/417faed7-307d-4173-9f4e-874f6758eb5b
-- title:
--   Running a program on operations: input words, time, answers, space, the law of the tape
-- statement:
--   The input of a run on $n$ vertices and operations $\sigma$ is the word $n$ followed by three words per operation: $0,u,v$ for an insertion, $1,u,v$ for a deletion, $2,u,v$ for a query. Operations are numbered $t=1,\dots,|\sigma|$; their words are the reads number $3t-1,3t,3t+1$, and read number $3|\sigma|+2$ returns the end marker.
--
--   The **initialization time** is the number of steps before the first word of operation $1$ is read. The **time of operation $t$** is the number of steps from the read of its first word to the read of the first word of operation $t+1$ (or of the end marker). The **answer** to operation $t$ is the first word written in that window; $1$ means connected and $0$ means not connected. **Space** is measured by the memory cells touched, over the whole run, during initialization, and during one operation. The tape's law consists of independent uniform $W$-bit words.
--
--   These definitions turn "worst-case time per operation" into a statement about one run.
--
--   **Formalization Note** `RunsThrough` says that every read up to the end marker is executed; without it, the windows are undefined and the default value $0$ of `getD` would make the time bounds empty. Theorem statements therefore always include `RunsThrough`. The tape's law is `Measure.infinitePi` of the uniform law on `Fin (2^W)`.
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Theorem 1, p.1 (PDF 2); §2, p.4 (PDF 5)

import Mathlib
import Definitions.Def_DynConnWC_Op
import Definitions.Def_DynConnWC_Program

set_option autoImplicit false

namespace DynConnWC

/-! # Running a program on a sequence of operations

King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027
submission, sha256 9d16c13e…), Theorem 1, p.1: "O(log³ n) worst-case update time,
O(log n/ log log n) worst-case query time, O(n log² n) words of space, and O(n log² n)
initialization time. These bounds always hold"; §2, p.4: "Time is measured in word operations and
space in words."

**Formalization Note.** The input of a run on `n` vertices and operations `σ` is the word `n`
followed by three words per operation: `0, u, v` for an insertion of `{u, v}`, `1, u, v` for a
deletion, `2, u, v` for a query. Operations are numbered `t = 1, …, |σ|`; the words of operation
`t` are read by the reads number `3t − 1, 3t, 3t + 1`, and read number `3|σ| + 2` returns the end
marker. Because the machine is online, the program sees operation `t + 1` only after it has
finished operation `t`. **Initialization time** is the number of steps before the first word of
operation 1 is read; the **time of operation `t`** is the number of steps from the read of its
first word to the read of the first word of operation `t + 1` (or of the end marker). The
**answer** to operation `t` is the first word written in that window (`none` if no word is written
or a read is never reached); `1` means "connected" and `0` "not connected". `RunsThrough` says that
every read up to the end marker is executed. **Space** is measured by the memory cells touched:
`addrs` are the cells touched before the end marker is read, `addrsInit` those touched during
initialization, `addrsDuring t` those touched during operation `t`. The random tape has the law
`tapeLaw W`: independent uniform `W`-bit words. -/

variable {n : ℕ}

/-- The three input words of an operation. -/
def Op.words : Op n → List ℕ
  | .ins u v => [0, u.val, v.val]
  | .del u v => [1, u.val, v.val]
  | .query u v => [2, u.val, v.val]

/-- The input words of a run: `n`, then three words per operation. -/
def inputWords (n : ℕ) (σ : List (Op n)) : List ℕ := n :: σ.flatMap Op.words

/-- Every read up to and including the end marker (read `3|σ| + 2`) is executed. -/
def RunsThrough (W : ℕ) (P : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)) : Prop :=
  ∀ k, 1 ≤ k → k ≤ 3 * σ.length + 2 → (readStep W P (inputWords n σ) ω k).isSome

/-- Initialization time: the steps executed before the first word of operation 1 is read. -/
noncomputable def initTime (W : ℕ) (P : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W))
    (σ : List (Op n)) : ℕ :=
  (readStep W P (inputWords n σ) ω 2).getD 0

/-- The time of operation `t` (`1 ≤ t ≤ |σ|`): the steps from the read of its first word to the
read of the next operation's first word (or of the end marker). -/
noncomputable def opTime (W : ℕ) (P : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n))
    (t : ℕ) : ℕ :=
  (readStep W P (inputWords n σ) ω (3 * t + 2)).getD 0 -
    (readStep W P (inputWords n σ) ω (3 * t - 1)).getD 0

/-- The answer word to operation `t` (`1 ≤ t ≤ |σ|`): the first word written during it. -/
noncomputable def answer (W : ℕ) (P : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n))
    (t : ℕ) : Option ℕ := do
  let a ← readStep W P (inputWords n σ) ω (3 * t - 1)
  let b ← readStep W P (inputWords n σ) ω (3 * t + 2)
  (outputBetween W P (inputWords n σ) ω a b).head?

/-- The memory cells touched before the end marker is read. -/
noncomputable def addrs (W : ℕ) (P : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)) :
    Set ℕ :=
  touchedBetween W P (inputWords n σ) ω 0
    ((readStep W P (inputWords n σ) ω (3 * σ.length + 2)).getD 0)

/-- The memory cells touched during initialization. -/
noncomputable def addrsInit (W : ℕ) (P : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W))
    (σ : List (Op n)) : Set ℕ :=
  touchedBetween W P (inputWords n σ) ω 0 ((readStep W P (inputWords n σ) ω 2).getD 0)

/-- The memory cells touched during operation `t` (`1 ≤ t ≤ |σ|`). -/
noncomputable def addrsDuring (W : ℕ) (P : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W))
    (σ : List (Op n)) (t : ℕ) : Set ℕ :=
  touchedBetween W P (inputWords n σ) ω
    ((readStep W P (inputWords n σ) ω (3 * t - 1)).getD 0)
    ((readStep W P (inputWords n σ) ω (3 * t + 2)).getD 0)

/-- Every query of `σ` is answered with the correct word: for the query `σ[t] = (u, v)` (the
operation number `t + 1`), the answer is `1` if `u` and `v` are connected in the graph after the
updates among `σ[0], …, σ[t-1]`, and `0` otherwise. -/
def AllCorrect (W : ℕ) (P : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)) : Prop :=
  ∀ (t : ℕ) (ht : t < σ.length) (u v : Fin n), σ[t] = .query u v →
    answer W P n ω σ (t + 1) = some (correctBit (graphAt σ t) u v)

open MeasureTheory in
/-- The law of the random tape: independent uniform `W`-bit words. -/
noncomputable def tapeLaw (W : ℕ) : Measure (ℕ → Fin (2 ^ W)) :=
  Measure.infinitePi (fun _ => (PMF.uniformOfFintype (Fin (2 ^ W))).toMeasure)

end DynConnWC


