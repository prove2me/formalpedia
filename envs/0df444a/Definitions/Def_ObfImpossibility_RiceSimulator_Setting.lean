-- Prove2me | Definitions.Def_ObfImpossibility_RiceSimulator_Setting
-- name    : ObfImpossibility_RiceSimulator_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:27:29.193041+00:00
-- url     : https://prove2.me/theorems/70f1daa8-7888-4157-891f-2a1d7d792f71
-- title:
--   Machines, $[M]$, $\langle M\rangle(1^t,x)$, $|M|$, oracle runs $S^{\langle M\rangle}$, promise problems, $n$-compatibility and the sets $S_n$ (§2.1, App. A)
-- statement:
--   This file fixes the objects of Appendix A of Barak et al., *On the (Im)possibility of Obfuscating Programs*.
--
--   1. **Machines.** A machine $M$ is a program of a fixed universal programming language for the partial recursive functions; its canonical description is a natural number $\ulcorner M\urcorner$ (the paper identifies machines with their descriptions as strings).
--   2. **Computed function.** $[M]:\mathbb N\rightharpoonup\mathbb N$ is the (possibly partial) function computed by $M$. Two machines are *functionally equivalent*, $[M]\equiv[M']$, when these partial functions are equal (same domain, same values).
--   3. **Bounded run.** For a budget $t$ and an input $x$,
--   $$\langle M\rangle(1^t,x)=\begin{cases} y & \text{if } M(x) \text{ halts with output } y \text{ within budget } t,\\ \bot & \text{otherwise.}\end{cases}$$
--   4. **Size.** $|M|$ is the length of the binary description of $M$, i.e. the number of binary digits of $\ulcorner M\urcorner$. For every $s$ there are at most $2^s$ machines of size $s$.
--   5. **Oracle access to $\langle M\rangle$.** An oracle machine $S$ may query the total function $\langle M\rangle$: a query is a pair $(t,x)$ and the answer is $\langle M\rangle(1^t,x)$. We write $S^{\langle M\rangle}(z)$ for the (possibly divergent) output of $S$ on input $z$ with this oracle.
--   6. **Promise problems.** A promise problem $\Pi=(\Pi_Y,\Pi_N)$ is a pair of disjoint sets of machines. It is *closed under* $[\cdot]$ if for all $M,M'$ with $[M]\equiv[M']$ we have $M\in\Pi_Y\iff M'\in\Pi_Y$ and $M\in\Pi_N\iff M'\in\Pi_N$. A machine $T$ *decides* $\Pi$ if $T(\ulcorner M\urcorner)=1$ for every $M\in\Pi_Y$ and $T(\ulcorner M\urcorner)=0$ for every $M\in\Pi_N$; nothing is required of $T$ outside $\Pi_Y\cup\Pi_N$. $\Pi$ is *decidable* if some machine decides it.
--   7. **Compatibility.** A machine $N$ is *$n$-compatible* with $M$ if $\langle N\rangle(1^t,x)=\langle M\rangle(1^t,x)$ for all $x,t$ with $|x|\le n$ and $t\le n$.
--   8. **The sets $S_n$.** $S_n(M)$ is the set of machines of size $|M|$ that are $n$-compatible with $M$.
--   9. **Stage answers.** Stage $n$ of the paper's simulator *stops with answer* $\sigma$ when $T$, run for $n$ steps, halts on (the description of) every machine of $S_n(M)$ with output $\sigma$.
--
--   These are the objects every statement of the mission is written with: Theorem A.2 asserts that a decidable promise problem closed under $[\cdot]$ can be decided by a single oracle machine that sees only $\langle M\rangle$ and $1^{|M|}$, and the milestones are the steps of its proof.
--
--   **Formalization Note** Machines are Mathlib's `Nat.Partrec.Code`, descriptions are `Encodable.encode`, $[M]$ is `Code.eval`, and $\langle M\rangle(1^t,x)$ is `Code.evaln t M x : Option ℕ` (`none` is $\bot$). The budget of `evaln` is a fuel bound rather than a literal Turing-machine step count: it is monotone in $t$, converges to $[M]$, and is primitive recursive in $(t, M, x)$, which are the only properties the paper's argument uses; `evaln t M x = none` whenever $x \ge t$. Inputs are natural numbers and $|x|$ is `Nat.size x`. $|M|$ is `Nat.size (encode M)`. Oracle machines are the uniform oracle programs `FriedbergMuchnik.Program` with semantics `oracleEval` (imported); the oracle $\langle M\rangle$ is the total function sending `Nat.pair t x` to `0` for $\bot$ and to `y+1` for output $y$. Disjointness of $\Pi_Y,\Pi_N$ is a field of `PromiseProblem`, as in the paper's definition (p. A:32); the theorems do not use it.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:7 (Section 2.1: [M], ⟨M⟩(1^t,x)), p. A:32 (promise problems), pp. A:40–A:41 (Appendix A: decides, closed under [·], n-compatible, the sets S_n)

import Mathlib
import Definitions.Def_FriedbergMuchnik_Priority

namespace ObfImpossibility.RiceSimulator

/-- Machines (§2.1, p. A:7). A machine is a program of Mathlib's partial recursive
programming language `Nat.Partrec.Code`; its canonical description is the natural
number `Encodable.encode M`. -/
abbrev Machine := Nat.Partrec.Code

/-- `[M]` (§2.1, p. A:7): the (possibly partial) function computed by `M`. -/
def fn (M : Machine) : ℕ →. ℕ := M.eval

/-- `⟨M⟩(1^t, x)` (§2.1, p. A:7): the result of running `M` on `x` with budget `t`;
`some y` if the run halts with output `y` within budget `t`, `none` (= ⊥) otherwise.
The budget is Mathlib's fuel `Code.evaln`, which is monotone in `t` and converges to `[M]`. -/
def bounded (M : Machine) (t x : ℕ) : Option ℕ := M.evaln t x

/-- `|M|` : the length of the binary description of `M`. -/
def size (M : Machine) : ℕ := Nat.size (Encodable.encode M)

/-- The oracle `⟨M⟩` as a total function on query codes: the query `(1^t, x)` is the number
`Nat.pair t x`; the answer `⊥` is encoded as `0` and the answer `y` as `y + 1`. -/
def oracle (M : Machine) (q : ℕ) : ℕ :=
  match bounded M q.unpair.1 q.unpair.2 with
  | none => 0
  | some y => y + 1

/-- `S^{⟨M⟩}(x)`: the run of the oracle machine `S` on input `x` with oracle access to `⟨M⟩`.
Oracle machines are the uniform oracle programs `FriedbergMuchnik.Program`. -/
def simRun (S : FriedbergMuchnik.Program) (M : Machine) (x : ℕ) : Part ℕ :=
  FriedbergMuchnik.oracleEval (PFun.lift (oracle M)) S x

/-- A promise problem (p. A:32): a pair `(Π_Y, Π_N)` of disjoint sets of machines. -/
structure PromiseProblem where
  yes : Set Machine
  no : Set Machine
  disjoint : Disjoint yes no

/-- `Π` is closed under `[·]` (p. A:41): functionally equivalent machines lie in the same
parts of `Π`. -/
def PromiseProblem.ClosedUnderFn (P : PromiseProblem) : Prop :=
  ∀ M M' : Machine, fn M = fn M' → (M ∈ P.yes ↔ M' ∈ P.yes) ∧ (M ∈ P.no ↔ M' ∈ P.no)

/-- The machine `T`, run on descriptions of machines, decides `Π` (pp. A:40–A:41):
it outputs `1` on every yes-instance and `0` on every no-instance; off the promise it is
unconstrained (it may diverge). -/
def Decides (T : Machine) (P : PromiseProblem) : Prop :=
  (∀ M ∈ P.yes, T.eval (Encodable.encode M) = Part.some 1) ∧
  (∀ M ∈ P.no, T.eval (Encodable.encode M) = Part.some 0)

/-- `Π` is decidable (p. A:41): some machine decides it. -/
def PromiseProblem.IsDecidable (P : PromiseProblem) : Prop :=
  ∃ T : Machine, Decides T P

/-- `N` is `n`-compatible with `M` (p. A:41): `⟨N⟩(1^t, x) = ⟨M⟩(1^t, x)` for all `x, t` with
`|x| ≤ n` and `t ≤ n`, where `|x|` is the binary length `Nat.size x`. -/
def Compatible (n : ℕ) (N M : Machine) : Prop :=
  ∀ t x : ℕ, t ≤ n → Nat.size x ≤ n → bounded N t x = bounded M t x

/-- `S_n` (p. A:41): the machines of size `|M|` that are `n`-compatible with `M`. -/
def survivors (n : ℕ) (M : Machine) : Set Machine :=
  {N | size N = size M ∧ Compatible n N M}

/-- Stage `n` of the paper's simulator stops with answer `σ` (p. A:41, step (2)): `T`, run
for `n` steps (`Code.evaln n`), halts on every machine of `S_n` with the same answer `σ`. -/
def StageAnswer (T : Machine) (M : Machine) (n σ : ℕ) : Prop :=
  ∀ N ∈ survivors n M, T.evaln n (Encodable.encode N) = some σ

end ObfImpossibility.RiceSimulator


