-- Prove2me | Definitions.Def_TargetedSamplers_Supplement_SVN
-- name    : TargetedSamplers_Supplement_SVN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:12:09.600215+00:00
-- url     : https://prove2.me/theorems/13a72c6a-28fd-4982-86f2-343834ddf3d9
-- title:
--   SVN circuits, $\mathrm{DTIME}[2^n]$ and printable truth tables
-- statement:
--   A **single-valued nondeterministic (SVN) circuit** $C(x,w)$ on $n$ input bits and some number of witness bits has two output bits, $\mathrm{valid}$ and $\mathrm{value}$. It **computes** a language $L\subseteq\{0,1\}^*$ on inputs of length $n$ if for every $x\in\{0,1\}^n$
--
--   1. some witness $w$ gives $\mathrm{valid}=1$, and
--   2. every witness $w$ with $\mathrm{valid}=1$ gives $\mathrm{value}=L(x)$;
--
--   equivalently, the set of values output with $\mathrm{valid}=1$ is exactly $\{L(x)\}$. The **size** of $C$ is its number of fan-in-2 AND/OR and NOT gates. A language $L$ **cannot be computed by SVN circuits of size $s(n)$** if, for all sufficiently large $n$, no SVN circuit of size at most $s(n)$ computes $L$ on length $n$.
--
--   $L\in\mathrm{DTIME}[2^n]$ means that one deterministic program decides $L$ on every input $x$ within time $2^{|x|}$. The **truth table of $L$ on length $n$** is the $2^n$-bit string $(L(x))_{x\in\{0,1\}^n}$, and it **can be printed in time $t(n)$** if one program, on input $1^n$, prints it within time $t(n)$, for every $n$.
--
--   These notions state the hardness hypothesis of Theorem 4.22, overhead-free quantified derandomization from circuit lower bounds.
--
--   **Formalization Note** SVN circuits are the published multi-output nondeterministic circuits `MultAddExt.Multiplicative.MultiNondetCirc n 1` (last output = valid). The paper does not define SVN circuits; this is the standard notion of Chen–Tell [CT21b]. "Cannot be computed" is read almost everywhere: at $n=0$ a circuit without gates computes every language. Time is the base mission's `budget` (constant and polylogarithmic factors on the log-cost RAM). The truth table lists $x$ in the order of the numbers $0,\dots,2^n-1$ written in $n$ bits, least significant first.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorems 4.21–4.22, p.29 (pdf p.31)

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_NondetCircuit
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_encInput

namespace TargetedSamplers.Supplement

open Classical in
/-- An SVN (single-valued nondeterministic) circuit `C(x, w)` with `n` input bits computes the
language `L` on inputs of length `n` (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027
submission, manuscript sha256 599d0a59…, Theorems 4.21–4.22, p.29, "SVN circuits", the notion of
[CT21b]): `C` is the published multi-output nondeterministic circuit
`MultAddExt.Multiplicative.MultiNondetCirc n 1`, whose last output is the flag `valid` and whose
first output is `value`; for every `x ∈ {0,1}ⁿ` the set of values output with `valid = 1` is exactly
`{L(x)}`. That is: some witness `w` gives `valid = 1`, and every witness with `valid = 1` gives
`value = L(x)`.

**Formalization Note** The paper uses SVN circuits without defining them; this is the standard
notion of [CT21b]. The size of an SVN circuit is its number of fan-in-2 AND/OR and NOT gates
(`C.C.numGates`), see `SVNHardAE`. -/
def SVNComputes {n : ℕ} (C : MultAddExt.Multiplicative.MultiNondetCirc n 1) (L : Set (List Bool)) :
    Prop :=
  ∀ x : Fin n → Bool, C.acceptSet x = {fun _ => decide (List.ofFn x ∈ L)}

/-- `L` cannot be computed by SVN circuits of size `s(n)`, almost everywhere (Theorem 4.22, p.29,
"`L` cannot be computed by SVN circuits of size `2^{(1−α/4)n}`"): for all sufficiently large `n`, no
SVN circuit on `n` input bits with at most `s(n)` gates computes `L` on inputs of length `n`.

**Formalization Note** Size is the number of gates. "Cannot be computed" is read almost everywhere
(for all large `n`), as in [CT21b]: at `n = 0` a circuit without gates computes every language, so
the hypothesis read "for every `n`" could never hold. -/
def SVNHardAE (L : Set (List Bool)) (s : ℕ → ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ C : MultAddExt.Multiplicative.MultiNondetCirc n 1,
    (C.C.numGates : ℝ) ≤ s n → ¬ SVNComputes C L

/-- `L ∈ DTIME[2ⁿ]` (Theorem 4.22, p.29): one deterministic program decides `L`, outputting the bit
`[x ∈ L]` on every input `x` within time `2^{|x|}`.

**Formalization Note** Time is the base `budget` (constant and polylogarithmic factors), as for every
class of this development. -/
def InDTIMEExp (L : Set (List Bool)) : Prop :=
  ∃ (P : Program) (K k : ℕ), ∀ x : List Bool, ∃ b : Bool,
    P.RunsIn (Tapes.ofInput x) (budget K k (2 ^ x.length) x.length) (some [b]) ∧ (b = true ↔ x ∈ L)

open Classical in
/-- The truth table of `L` on inputs of length `n`: the `2ⁿ` bits `[x ∈ L]`, `x` running through
`{0,1}ⁿ` in the order of the numbers `0, …, 2ⁿ − 1` written in `n` bits, least significant bit
first (`bitsFixed`). -/
noncomputable def truthTable (L : Set (List Bool)) (n : ℕ) : List Bool :=
  (List.range (2 ^ n)).map fun i => decide (bitsFixed n i ∈ L)

/-- The truth table of `L` can be printed in time `t(n)` for every `n` (Theorem 4.22, p.29): one
deterministic program, on input `1ⁿ`, prints the truth table of `L` on length `n` within time
`t(n)` (`budget`). -/
def TruthTablePrintable (L : Set (List Bool)) (t : ℕ → ℕ) : Prop :=
  ∃ (P : Program) (K k : ℕ), ∀ n : ℕ,
    P.RunsIn (Tapes.ofInput (List.replicate n true)) (budget K k (t n) n) (some (truthTable L n))

end TargetedSamplers.Supplement


