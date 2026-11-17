-- Prove2me | Definitions.Def_ResultantVNP_Supplement_CountingClasses
-- name    : ResultantVNP_Supplement_CountingClasses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:53:50.625332+00:00
-- url     : https://prove2.me/theorems/b5951f49-a553-4967-889a-0e868712edc1
-- title:
--   The counting classes $\#\mathsf P$, $\oplus\mathsf P$, $\mathsf{PP}$, $\mathsf{FP}^A$ and $\mathsf{FP}^{\mathsf{PP}}$
-- statement:
--   All Boolean complexity classes of the supplement are built on one machine model: the published multi-tape oracle Turing machines with a sequential randomness (seed) tape, binary words, and polynomial clocks $c\,(N+1)^d$ in the input length $N$.
--
--   1. A function $f:\{0,1\}^*\to\mathbb N$ is in $\#\mathsf P$ if there is a machine $M$ with empty oracle and polynomials $t,q$ such that on every input $x$ and every seed $r\in\{0,1\}^{q(|x|)}$ the machine halts within $t(|x|)$ steps with a one-bit answer, and $f(x)$ is the number of seeds on which it answers $1$ (the accepting computation paths).
--   2. A language $L$ is in $\oplus\mathsf P$ if, for such a machine, $x\in L$ exactly when the number of accepting paths is odd.
--   3. $\mathsf{PP}$ is the published class $\mathsf{PP}^{\emptyset}$: $x\in L$ exactly when strictly more than half of the seeds accept.
--   4. For a language $A$, a function $f:\{0,1\}^*\to\{0,1\}^*$ is in $\mathsf{FP}^A$ if a machine with oracle $A$, started on $x$, halts within a polynomial clock with $f(x)$ on its output tape.
--   5. $\mathsf{FP}^{\mathsf{PP}}=\bigcup_{A\in\mathsf{PP}}\mathsf{FP}^A$.
--
--   These are the classes of Theorems 1.8, 1.11, 4.6 and E.1.
--
--   **Formalization Note** The nondeterministic choices are the seed; every path has the same polynomial length, the usual normal form of $\#\mathsf P$. $\mathsf{FP}^{\emptyset}$ is the published `FunctionInP`. The module defines the five classes together because they share one machine layer.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 4, p.18 (#P); Section 5, p.22 (⊕P); Theorem 4.6, p.21 (FP^PP)

import Mathlib
import Definitions.Def_ApproxPolySatCH_Main_Complexity

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

open ApproxPolySatCH.Main

/-- **The counting classes #P, ⊕P, PP, FP^A and FP^PP**, on the published machine layer
`ApproxPolySatCH.Main` (multi-tape oracle Turing machines `NKtLB.Machine`, words `List Bool`,
polynomial clocks `clock c d N = c·(N+1)^d`).

* `SharpP`: `f ∈ #P` iff `f x` is the number of accepting computation paths (seeds of the fixed
  polynomial length `clock a b |x|`) of a polynomial-time nondeterministic machine with oracle `∅`
  whose every path halts with a one-bit answer within `clock c d |x|` steps.
* `ParityP`: `L ∈ ⊕P` iff `x ∈ L` exactly when that number is odd.
* `PP`: `InOraclePP ∅` (strict majority of accepting seeds).
* `FunctionInOracleP A f`: `f ∈ FP^A`, i.e. a machine with oracle `A` halts within a polynomial
  clock with the bit string `f x` on its output tape.
* `FPPP`: `FP^PP = ⋃_{A ∈ PP} FP^A`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 4, p.18 ("a
function is in #P if it counts accepting paths of a polynomial-time nondeterministic Turing
machine"); Section 5, p.22 (⊕P); Theorem 4.6, p.21 (FP^PP).

**Formalization Note** The nondeterministic choices are the seed on the sequential randomness tape
of `NKtLB.Machine`; all paths have the same polynomial length, the standard normal form of #P.
`FunctionInOracleP ∅` is the published `FunctionInP`. -/
def SharpP : Set (Word → ℕ) :=
  {f | ∃ (M : NKtLB.Machine) (c d a b : ℕ), TotalClock M ∅ c d a b ∧
    ∀ x : Word, f x = acceptingSeeds M ∅ x (clock c d x.length) (clock a b x.length)}

/-- `L ∈ ⊕P`: some polynomial-time nondeterministic machine (every path halting within its clock)
has an odd number of accepting paths exactly on the words of `L` (p.22). -/
def ParityP : Set Language :=
  {L | ∃ (M : NKtLB.Machine) (c d a b : ℕ), TotalClock M ∅ c d a b ∧
    ∀ x : Word, x ∈ L ↔ Odd (acceptingSeeds M ∅ x (clock c d x.length) (clock a b x.length))}

/-- `PP = PP^∅` of the published layer (strict majority of the seeds accept). -/
def PP : Set Language := {L | InOraclePP ∅ L}

/-- `f ∈ FP^A`: a machine with oracle `A`, started with `x` on its input tape, halts within a
polynomial clock with the bit string `f x` on its output tape. -/
def FunctionInOracleP (A : Language) (f : Word → Word) : Prop :=
  ∃ (M : NKtLB.Machine) (c d : ℕ), ∀ x : Word,
    M.HaltsWith A ⟨x, [], [], []⟩ (clock c d x.length) (NKtLB.bitsSym (f x))

/-- `FP^PP`: the functions computable in polynomial time with an oracle for some `PP` language. -/
def FPPP : Set (Word → Word) := {f | ∃ A ∈ PP, FunctionInOracleP A f}

end Supplement

end ResultantVNP


