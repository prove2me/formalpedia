-- Prove2me | Definitions.Def_MatroidSensOracle_WordRAM
-- name    : MatroidSensOracle_WordRAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:31.698195+00:00
-- url     : https://prove2.me/theorems/e69355b5-0f8a-4082-85c6-0e9d60b950b0
-- title:
--   The randomized word RAM and the semantics of a sensitivity oracle (preprocessing, stored bits, query)
-- statement:
--   The machine is a word RAM with words of $w$ bits and cells indexed by the integers. Its instructions are those of the published APSP word RAM — $[i]:=1$, $[i]:=[j]\pm[k]$, $[i]:=[j]\cdot[k]$ (all modulo $2^w$), indirect load $[i]:=[[j]]$ and store $[[i]]:=[j]$, and the branch "if $[i]<0$ go to $l$" — together with unsigned division and remainder ($x/0=0$, $x \bmod 0=x$), a coin instruction
--   $$[i] := \text{a uniform number in } \{0,1,\dots,[j]-1\}$$
--   (and $0$ when $[j]=0$), and $\mathrm{halt}$. Every instruction costs one step. Randomness is a sequence $\omega\in[0,1]^{\mathbb N}$ of independent uniform numbers; the $c$-th coin with bound $m$ returns $\min(\lfloor \omega_c m\rfloor, m-1)$.
--
--   A **sensitivity oracle** is a pair $(P,Q)$ of programs.
--   1. The preprocessing $P$ starts with the instance words in cells $0,1,2,\dots$. When it halts, cell $0$ holds a length $L$ and cells $1,\dots,\lceil L/w\rceil$ hold a bit string $S$ of $L$ bits (bits past $L$ are cleared). The **space** is $L$ bits.
--   2. The query $Q$ starts from a fresh memory containing only $L$, the words of $S$, and the query words after them, and draws fresh coins. So $Q$ sees the stored string and the query, and nothing else of the instance.
--   3. A time bound $T$ holds when the run halts within $T$ steps on every coin sequence (worst case). The error for a fixed query is the probability, over the independent coins of $P$ and $Q$, that the run does not end with a correct answer.
--
--   The paper works "in the Word-RAM model" with field arithmetic in constant time (p.13); unsigned division and remainder give arithmetic in $\mathbb F_p$, and the uniform-below coin makes worst-case time meaningful.
--
--   **Formalization Note** Programs are required to work for every word width above a threshold $b(\lfloor\log_2(\text{input size})\rfloor+1)$, so packing many values into one word does not help; space is counted in bits, not cells.
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), §2, p.13 (PDF p.16)

import Mathlib

open MeasureTheory

set_option autoImplicit false

namespace MatroidSensOracle

/-!
# The randomized word RAM and sensitivity-oracle semantics

Choudhary, Kumar, Saggi, *Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching
Problems with Applications*, arXiv:2609.01283 (held version, sha256 0de50841…), §2, p.13 (PDF p.16):
"We will be working with fields representable in O(log n) bits. This would support addition and
multiplication over F in constant time in the Word-RAM model." All oracles of the paper are
randomized (Monte Carlo).

**Formalization Note.**
* **Machine.** The instruction set of the published word RAM `TrulySubcubicAPSP.Instr` (`one`, `add`,
  `sub`, `mul` modulo `2^w`, indirect `load`/`store`, `bltz`), plus unsigned `udiv` and `umod`
  (`x / 0 = 0`, `x % 0 = x`, the `BitVec` conventions), plus one coin instruction
  `coin i j : [i] := a uniform number in {0, …, [j] − 1}` (`[j]` read unsigned; `0` when `[j] = 0`),
  plus `halt`. Fetching past the end of the program halts. Every executed instruction costs one step.
  Words are `BitVec w`; cells are indexed by `ℤ`, addresses are read signed.
* **Coins.** A run reads a coin sequence `ω : ℕ → [0,1]`; the `c`-th executed `coin` instruction
  with bound `m` returns `min ⌊ω_c · m⌋ (m − 1)`, which is uniform on `{0, …, m − 1}` when `ω_c`
  is uniform. The coin law is the product of uniform laws on `[0,1]`.
* **Oracle.** A sensitivity oracle is a pair `(P, Q)` of programs. `P` runs on the instance; when it
  halts, cell `0` holds a length `L` and cells `1, …, ⌈L/w⌉` hold the stored bit string `S` of `L`
  bits (bits past `L` are cleared). `Q` starts from a fresh memory holding only `L` in cell `0`, the
  words of `S` in cells `1, …, ⌈L/w⌉`, and the query encoding after them; so `Q` sees `S` and the
  query and nothing else. `Q` draws fresh coins. The space is `L`, in bits.
* **Time** is worst case: on every coin sequence of `P` (and of `Q`) the run halts within the bound.
-/

/-- `i j k` name cells, `l` a position in the program, `[i]` the word in cell `i`. -/
inductive Instr where
  | one (i : ℤ)             -- [i] := 1
  | add (i j k : ℤ)         -- [i] := [j] + [k]
  | sub (i j k : ℤ)         -- [i] := [j] - [k]
  | mul (i j k : ℤ)         -- [i] := [j] * [k]
  | udiv (i j k : ℤ)        -- [i] := [j] / [k], unsigned
  | umod (i j k : ℤ)        -- [i] := [j] mod [k], unsigned
  | load (i j : ℤ)          -- [i] := [[j]]
  | store (i j : ℤ)         -- [[i]] := [j]
  | bltz (i : ℤ) (l : ℕ)    -- if [i] < 0, go to position l
  | coin (i j : ℤ)          -- [i] := uniform in {0, …, [j] - 1}
  | halt

/-- A coin sequence: one uniform number in `[0,1]` per executed `coin` instruction. -/
abbrev Coins := ℕ → unitInterval

/-- The law of the coins: independent uniform numbers in `[0,1]`. -/
noncomputable def coinLaw : Measure Coins := Measure.infinitePi fun _ => volume

/-- The value of a coin `u` drawn below `m`: `min ⌊u·m⌋ (m − 1)`, uniform on `{0, …, m−1}`
for uniform `u` (and `0` when `m = 0`). -/
noncomputable def draw (u : unitInterval) (m : ℕ) : ℕ := min ⌊(u : ℝ) * m⌋₊ (m - 1)

/-- The final memory, if `P`, run from position `pc` with the next coin index `c` on memory `m`,
halts within `t` steps (the halting step counted). -/
noncomputable def exec {w : ℕ} (P : List Instr) (ω : Coins) :
    (t pc c : ℕ) → (m : ℤ → BitVec w) → Option (ℤ → BitVec w)
  | 0, _, _, _ => none
  | t + 1, pc, c, m =>
    let write (i : ℤ) (v : BitVec w) (c' : ℕ) :=
      exec P ω t (pc + 1) c' fun x => if x = i then v else m x
    match P.getD pc .halt with
    | .one i => write i 1 c
    | .add i j k => write i (m j + m k) c
    | .sub i j k => write i (m j - m k) c
    | .mul i j k => write i (m j * m k) c
    | .udiv i j k => write i (m j / m k) c
    | .umod i j k => write i (m j % m k) c
    | .load i j => write i (m (m j).toInt) c
    | .store i j => write (m i).toInt (m j) c
    | .bltz i l => exec P ω t (if (m i).toInt < 0 then l else pc + 1) c m
    | .coin i j => write i (BitVec.ofNat w (draw (ω c) (m j).toNat)) (c + 1)
    | .halt => some m

/-- The memory at the start: the words `ws` in cells `0, 1, 2, …` and `0` in every other cell. -/
def loadWords (w : ℕ) (ws : List ℤ) : ℤ → BitVec w :=
  fun a => if a < 0 then 0 else BitVec.ofInt w (ws.getD a.toNat 0)

/-- The length in bits of the string stored by a halted preprocessing run: the word in cell `0`. -/
def storedLength {w : ℕ} (mP : ℤ → BitVec w) : ℕ := (mP 0).toNat

/-- The number of words holding a stored string of `L` bits: `⌈L / w⌉`. -/
def storedWords (w L : ℕ) : ℕ := (L + w - 1) / w

/-- The memory at the start of a query: cell `0` holds `L`, cells `1, …, ⌈L/w⌉` hold the stored
bits (the bits of `P`'s final cells `1, …` with every bit past position `L` cleared), the query words
`q` follow, every other cell is `0`. Nothing else of the preprocessing run is visible. -/
def queryMemory (w : ℕ) (mP : ℤ → BitVec w) (q : List ℤ) : ℤ → BitVec w := fun a =>
  if a < 0 then 0
  else if a = 0 then mP 0
  else if a ≤ storedWords w (storedLength mP) then
    BitVec.ofNat w ((mP a).toNat % 2 ^ (storedLength mP - (a.toNat - 1) * w))
  else BitVec.ofInt w (q.getD (a.toNat - 1 - storedWords w (storedLength mP)) 0)

/-- A sensitivity oracle: a preprocessing program and a query program. -/
structure Oracle where
  prep : List Instr
  query : List Instr

/-- One run of an oracle: preprocessing on `inp` for at most `TP` steps with coins `ω₁`, then the
query on the stored string and `q` for at most `TQ` steps with fresh coins `ω₂`. The result holds both
final memories. -/
noncomputable def Oracle.run (O : Oracle) (w : ℕ) (inp q : List ℤ) (TP TQ : ℕ) (ω₁ ω₂ : Coins) :
    Option ((ℤ → BitVec w) × (ℤ → BitVec w)) :=
  match exec O.prep ω₁ TP 0 0 (loadWords w inp) with
  | none => none
  | some mP => (exec O.query ω₂ TQ 0 0 (queryMemory w mP q)).map fun mQ => (mP, mQ)

/-- Preprocessing bound: on every coin sequence the preprocessing run on `inp` halts within `TP`
steps and stores at most `space` bits. -/
def Oracle.PrepWithin (O : Oracle) (w : ℕ) (inp : List ℤ) (TP : ℕ) (space : ℝ) : Prop :=
  ∀ ω : Coins, ∃ mP, exec O.prep ω TP 0 0 (loadWords w inp) = some mP ∧
    (storedLength mP : ℝ) ≤ space

/-- Query bound: for every coin sequence of the preprocessing and of the query, the query on `q`
halts within `TQ` steps. -/
def Oracle.QueryWithin (O : Oracle) (w : ℕ) (inp q : List ℤ) (TP TQ : ℕ) : Prop :=
  ∀ ω₁ ω₂ : Coins, (O.run w inp q TP TQ ω₁ ω₂).isSome

/-- Error bound for one fixed query: over independent coins of preprocessing and query, the
probability that the run does not halt with a final query memory satisfying `ok` is at most `ε`. -/
def Oracle.ErrorAtMost (O : Oracle) (w : ℕ) (inp q : List ℤ) (TP TQ : ℕ)
    (ok : (ℤ → BitVec w) → Prop) (ε : ℝ) : Prop :=
  (coinLaw.prod coinLaw) {p : Coins × Coins |
      ¬ ∃ r, O.run w inp q TP TQ p.1 p.2 = some r ∧ ok r.2} ≤ ENNReal.ofReal ε

end MatroidSensOracle


