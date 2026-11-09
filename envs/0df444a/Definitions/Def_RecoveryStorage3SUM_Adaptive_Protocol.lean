-- Prove2me | Definitions.Def_RecoveryStorage3SUM_Adaptive_Protocol
-- name    : RecoveryStorage3SUM_Adaptive_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:59.83349+00:00
-- url     : https://prove2.me/theorems/f6e2347e-7235-46bc-9595-d4de0dd989c3
-- title:
--   The unknown-$C$ protocol for preprocessed 3SUM on the word RAM
-- statement:
--   A **data structure** for preprocessed 3SUM with unknown $C$ is a pair of programs of the published randomized word RAM: a preprocessing program, run with coins on the input words, and a query program.
--
--   1. The preprocessing starts on the words $n,A,B$, where $A$ and $B$ are sets of exactly $n$ integers listed in any order. It halts with a bit string in memory. Its length in bits is the **space**.
--   2. Each query starts from a fresh memory holding only that string and the words $|A'|,|B'|,|C'|,A',B',C'$. So a query sees nothing else of the preprocessing run, and cannot change what a later query sees.
--   3. A **legal query** has arbitrary, possibly empty, subsets $A'\subseteq A$, $B'\subseteq B$ and a set $C'$ of at most $qn$ integers. All integers are bounded by $H(n+2)^\kappa$ in absolute value, where $H,\kappa,q$ are fixed in advance.
--   4. On halting, cell $0$ holds the 3SUM decision (whether some $a\in A'$, $b\in B'$ have $a+b\in C'$) and cell $i+1$ holds the answer for the $i$-th target, as the number $1$ or $0$. A pair with $a=b$ counts when that value lies in both sets.
--
--   **Preprocessing succeeds** on coins $\omega$ when it halts within its budget and its stored string serves *every* legal query simultaneously. Since this quantifier sits inside the event on $\omega$, the guarantee covers queries chosen from the stored string and from earlier answers and running times.
--
--   Words have width $b(\lfloor\log_2(n+2)\rfloor+1)$, and $\widetilde O(n^\alpha)$ is the bound $C(n+2)^\alpha(\log(n+2))^e$.
--
--   **Formalization Note** Answers are read with `toNat`, so a positive answer requires nonzero word width, as ensured by the positive word-width multiplier in the resource theorems. The preprocessing receives only the instance encoding. The tradeoff exponent selects the programs in the existence theorem; no real-power oracle or precomputed tradeoff word is supplied. Bits and words differ by one logarithmic factor, absorbed in the displayed soft bounds.
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Section 1, p.2; Section 2, p.6; Section 3.3 and Algorithm 3, p.9

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

open MatroidSensOracle

/-!
# The unknown-C query protocol on the word RAM

Carmel, Kosoburd, Krauthgamer, *Recovery Beats Storage: Improved Space for Preprocessed 3SUM*,
STOC 2027 submission #561, §1, p.2 and §2, p.6: "We work in the word RAM with words of O(log n)
bits. All input integers are bounded in absolute value by a polynomial in n." "In the unknown-C
variant, only A and B are preprocessed, and the query specifies subsets A′ ⊆ A, B′ ⊆ B, and a set
C′ of O(n) integers".

**Formalization Note.** The machine is the published randomized word RAM `MatroidSensOracle.Instr`
with `exec`. A data structure is a pair of programs `MatroidSensOracle.Oracle`: the preprocessing
runs on the input words with coins and halts with a bit string in memory; the query starts from a
fresh memory holding only that string and the query words (`queryMemory`), so a query cannot change
what later queries see. Space is the length of the stored string, in bits.
-/

/-- The word width `b (⌊log₂ (n + 2)⌋ + 1)`: words of `O(log n)` bits, positive when `0 < b`. -/
def wordWidth (b n : ℕ) : ℕ := b * (Nat.log 2 (n + 2) + 1)

/-- The real bound `C (n + 2)^α (log (n + 2))^e` behind `Õ(n^α)`. -/
noncomputable def softBound (C α : ℝ) (e n : ℕ) : ℝ :=
  C * ((n : ℝ) + 2) ^ α * Real.log ((n : ℝ) + 2) ^ e

/-- The step budget `⌈C (n + 2)^α (log (n + 2))^e⌉`. -/
noncomputable def softSteps (C α : ℝ) (e n : ℕ) : ℕ := ⌈softBound C α e n⌉₊

/-- `|x| ≤ H (n + 2)^κ`: the fixed polynomial bound on every input integer. -/
def PolyBounded (H κ n : ℕ) (x : ℤ) : Prop := |x| ≤ (H : ℤ) * ((n : ℤ) + 2) ^ κ

/-- The input words of preprocessing: `n`, then `A`, then `B`, in the given order.
The tradeoff exponent is a parameter of the existence theorem, not an additional input or oracle. -/
def prepInput (as bs : List ℤ) : List ℤ :=
  (as.length : ℤ) :: (as ++ bs)

/-- The query words: the three lengths, then `A′`, `B′`, `C′`, each in the given order. -/
def queryInput (as' bs' cs : List ℤ) : List ℤ :=
  (as'.length : ℤ) :: (bs'.length : ℤ) :: (cs.length : ℤ) :: (as' ++ bs' ++ cs)

/-- A program that contains no coin instruction: its runs do not depend on the coins. -/
def CoinFree (P : List Instr) : Prop := ∀ i j : ℤ, Instr.coin i j ∉ P

/-- A legal input: `A` and `B` are sets of exactly `n` polynomially bounded integers, listed in
an arbitrary order without repetition. They may overlap and may contain `0` or negative numbers. -/
structure LegalInput (H κ n : ℕ) (as bs : List ℤ) : Prop where
  as_length : as.length = n
  bs_length : bs.length = n
  as_nodup : as.Nodup
  bs_nodup : bs.Nodup
  as_bounded : ∀ a ∈ as, PolyBounded H κ n a
  bs_bounded : ∀ b ∈ bs, PolyBounded H κ n b

/-- A legal query on the input `(as, bs)`: arbitrary, possibly empty, subsets `A′ ⊆ A`, `B′ ⊆ B`
and a set `C′` of at most `q n` polynomially bounded integers, unrelated to `A` and `B`. -/
structure LegalQuery (H κ q n : ℕ) (as bs as' bs' cs : List ℤ) : Prop where
  as'_nodup : as'.Nodup
  bs'_nodup : bs'.Nodup
  cs_nodup : cs.Nodup
  as'_subset : ∀ a ∈ as', a ∈ as
  bs'_subset : ∀ b ∈ bs', b ∈ bs
  cs_length : cs.length ≤ q * n
  cs_bounded : ∀ c ∈ cs, PolyBounded H κ n c

/-- The answer for one target: some `a ∈ A′`, `b ∈ B′` have `a + b = c`. A pair with `a = b` counts. -/
def TargetYes (as' bs' : List ℤ) (c : ℤ) : Prop := ∃ a ∈ as', ∃ b ∈ bs', a + b = c

/-- The 3SUM decision: some `a ∈ A′`, `b ∈ B′` have `a + b ∈ C′`. -/
def ThreeSumYes (as' bs' cs : List ℤ) : Prop := ∃ c ∈ cs, TargetYes as' bs' c

open Classical in
/-- Output convention of a halted query, with memory `mQ`: cell `0` holds the 3SUM decision and
cell `i + 1` the answer for the `i`-th target, each as the number `1` (yes) or `0` (no). A positive
answer requires nonzero word width; the resource theorems choose `0 < b`. -/
def AnswersCorrectly {w : ℕ} (mQ : ℤ → BitVec w) (as' bs' cs : List ℤ) : Prop :=
  (mQ 0).toNat = (if ThreeSumYes as' bs' cs then 1 else 0) ∧
    ∀ (i : ℕ) (c : ℤ), cs[i]? = some c →
      (mQ ((i : ℤ) + 1)).toNat = (if TargetYes as' bs' c then 1 else 0)

/-- The event of a preprocessing outcome `mP`: **every** legal query, on every coin sequence of the
query, halts within `TQ` steps from the fresh memory of `mP` and the query and answers correctly. -/
def AllQueriesGood (D : Oracle) (H κ q n w TQ : ℕ) (as bs : List ℤ) (mP : ℤ → BitVec w) : Prop :=
  ∀ as' bs' cs : List ℤ, LegalQuery H κ q n as bs as' bs' cs → ∀ ω : Coins,
    ∃ mQ, exec D.query ω TQ 0 0 (queryMemory w mP (queryInput as' bs' cs)) = some mQ ∧
      AnswersCorrectly mQ as' bs' cs

/-- The success event of preprocessing on the coins `ω`: the run halts within `TP` steps and its
stored string serves all legal queries simultaneously. The quantifier over queries is inside the
event, so the queries may depend on the stored string and on earlier answers and running times. -/
noncomputable def PreprocessingSucceeds (D : Oracle) (H κ q n w TP TQ : ℕ) (as bs : List ℤ)
    (ω : Coins) : Prop :=
  ∃ mP, exec D.prep ω TP 0 0 (loadWords w (prepInput as bs)) = some mP ∧
    AllQueriesGood D H κ q n w TQ as bs mP

end RecoveryStorage3SUM.Adaptive


