-- Prove2me | Definitions.Def_BoolCSPDel_inputWord
-- name    : BoolCSPDel_inputWord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:55:06.254567+00:00
-- url     : https://prove2.me/theorems/261f27ac-d735-48a1-bbab-7ed852636791
-- title:
--   Input and output words, $\mathrm{polylog}$, and the coin law
-- statement:
--   A constraint is coded as its relation's index in $\lceil\log_2|\Gamma|\rceil$ bits followed by each scope variable in $\lceil\log_2 n\rceil$ bits. The **input word** holds $n$, $\mu$, $M$, then each update as a sign bit and a constraint code. The **output word** is the answer bit, then each returned constraint preceded by a $1$, then a $0$. $\mathrm{polylog}(t)$ is a fixed power of $\log(t+2)$, and the coins are independent fair bits.
--
--   **Formalization Note** The index is from a fixed enumeration of $\Gamma$, which the program may know, as it is chosen after $\Gamma$. Failure probability $\delta$ is given as $1/M$.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), §3.1, p.17 (polylog); Theorem 1.1, p.6; Corollary 5.10, p.37

import Mathlib
import Definitions.Def_BoolCSPDel_Con
import Definitions.Def_BoolCSPDel_Program

open MeasureTheory

namespace BoolCSPDel

/-- `x` in exactly `w` bits, least significant first. -/
def fixedBits (w x : ℕ) : List Bool := List.ofFn fun i : Fin w => x.testBit i

/-- **Input and output words of the upper bound.** Bandekar, Sharma, Velusamy, STOC 2027 submission
(manuscript sha256 15f83519…), Theorem 1.1, p.6, Corollary 5.10, p.37.

A constraint as a bit block: the relation's index in `⌈log₂ |Γ|⌉` bits, then each scope variable in
`⌈log₂ n⌉` bits.

**Formalization Note.** The index comes from `Γ.equivFin`, a fixed enumeration of `Γ`. The program is
chosen after `Γ`, so it can know the enumeration and each relation's arity, and the block is parsed
without separators. -/
noncomputable def conBlock {k : ℕ} (Γ : Lang k) (n : ℕ) (C : Con Γ (Fin n)) : List Bool :=
  fixedBits (Nat.clog 2 Γ.card) (Γ.equivFin C.1) ++
    (List.ofFn C.2).flatMap fun v => fixedBits (Nat.clog 2 n) v

/-- The input word: `n`, `μ`, `M` (the failure bound is `δ = 1/M`), then the updates, each its sign
bit (`true` inserts) and its block. -/
noncomputable def inputWord {k : ℕ} (Γ : Lang k) (n μ M : ℕ) (s : List (Con Γ (Fin n) × Bool)) :
    List Bool :=
  encNat n ++ encNat μ ++ encNat M ++ s.flatMap fun u => u.2 :: conBlock Γ n u.1

/-- The output word: the answer bit (`true` = satisfiable), then each returned constraint preceded by
`true`, then `false`. -/
noncomputable def outWord {k : ℕ} (Γ : Lang k) (n : ℕ) (a : Bool) (S : List (Con Γ (Fin n))) :
    List Bool :=
  a :: (S.flatMap fun C => true :: conBlock Γ n C) ++ [false]

/-- p.17: "`polylog(t)` denotes a fixed power of `log(t + 2)`"; here the power is `K`. -/
noncomputable def polylog (K : ℕ) (t : ℝ) : ℝ := Real.log (t + 2) ^ K

/-- The law of the coin tape: independent fair bits. -/
noncomputable def coinMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

end BoolCSPDel


