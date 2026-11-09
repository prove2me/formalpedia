-- Prove2me | Definitions.Def_KColoringFaster_ListBootstrap_Algorithms
-- name    : KColoringFaster_ListBootstrap_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:13.23805+00:00
-- url     : https://prove2.me/theorems/094c352d-8799-4c7a-bdca-d2912736800c
-- title:
--   §3 — randomized and deterministic algorithms running in $O^*(T)$ time on the integer RAM
-- statement:
--   The paper states its results as running times $O^*(T)$, where $O^*$ suppresses factors polynomial in the input size, and allows "all algorithms to have an exponentially small error-probability", remarking that errors can be assumed one-sided (§3, p. 7). This definition fixes the meaning of these claims on the published integer RAM `CongruencyTU_Machine` (unit-cost arithmetic, a coin instruction, every register kept within a polynomial number of bits of the input size).
--
--   Let $\sigma(x)$ be the bit size of an input word list $x$. A program $P$ and polynomials $p,q$ with natural coefficients **decide** a property $\mathrm{Yes}$ on a class $\mathrm{Dom}$ in time $O^*(T)$ with errors $\eta_Y,\eta_N$ if, for every input $a\in\mathrm{Dom}$ with encoding $x$ and with budget
--   $$B=\big\lceil p(\sigma(x))\cdot T(a)\big\rceil,$$
--   1. every coin string $c\in\{0,1\}^B$ gives a run that halts with cost at most $B$ and keeps all registers within $q(\sigma(x))$ bits;
--   2. if $a$ is a yes-instance, at least a $1-\eta_Y(n)$ fraction of the coin strings give the output $[1]$;
--   3. if $a$ is a no-instance, at least a $1-\eta_N(n)$ fraction give the output $[0]$.
--
--   Here $n$ is the number of vertices of $a$. **One-sided error** is $\eta_N=0$: every coin string rejects a no-instance. $\mathrm{RandDecides}$ asserts that such $P,p,q$ exist; they are fixed before the input. A **search** algorithm ($\mathrm{RandFinds}$) has the same running-time clause and outputs a solution with probability at least $1-\eta(n)$ whenever one exists. A **deterministic polynomial-time** algorithm runs without coins, within cost $p(\sigma(x))$, and its output is always correct. The error bound $e^{-cn}$ is written $\mathrm{expErr}\,c$.
--
--   **Formalization Note** The time is worst case over coin strings, not expected time. The register bit-length bound keeps unit-cost arithmetic within a polynomial factor of bit cost, which $O^*$ absorbs; it rules out packing $2^n$ bits into one register. Programs have no oracle. Space is not bounded separately: a run of cost $B$ touches at most $B$ memory cells.
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 7, §3 (standing conventions on O*, error probabilities); p. 8, §3.2

import Mathlib
import Definitions.Def_CongruencyTU_Machine

open Classical

namespace KColoringFaster.ListBootstrap

open CongruencyTU

/-! # Randomized and deterministic algorithms with an `O*(T)` running time

Zamir, arXiv:2607.25973 (revision of 9 Sep 2026), §3, p. 7: "The notation O∗(·) suppresses factors
polynomial in the input size. … We allow all algorithms to have an exponentially small
error-probability. We remark that as the output of coloring algorithms is verifiable, all errors can
be assumed to be one-sided."

The machine is the published integer RAM `CongruencyTU` (unit-cost arithmetic, coins, register bit
lengths bounded by a polynomial in the input bit size). Only its primitives `Program`, `RunBounded`,
`outputAfter`, `extendCoins`, `noOracle`, `noCoins`, `bitSize` are used.

**Formalization Note.**
* "Solved in `O*(T)` time" means: one program `P` and polynomials `p q`, fixed before the input; on
  input `x` the budget is `B = ⌈p(σ(x)) · T⌉` with `σ(x)` the bit size of the input; **every** coin
  string `c ∈ {0,1}^B` gives a run that halts with cost at most `B` and keeps every register within
  `q(σ(x))` bits. Worst case over coins, not expected time. No oracle.
* Probabilities are fractions of the `2^B` coin strings.
* `RandDecides … ηY ηN`: on a yes-instance the output is `[1]` with probability at least
  `1 - ηY(n)`; on a no-instance it is `[0]` with probability at least `1 - ηN(n)`. One-sided error
  is `ηN = 0`, i.e. every coin string rejects a no-instance. -/

/-- The running-time budget `⌈p(σ(x)) · T⌉` on input `x`. -/
noncomputable def budget (p : Polynomial ℕ) (x : List ℤ) (T : ℝ) : ℕ :=
  ⌈((p.eval (bitSize x) : ℕ) : ℝ) * T⌉₊

/-- Every run on input `x` with a coin string of length `B` halts with cost at most `B`, and its
registers stay within `q(σ(x))` bits. -/
def AllRunsBounded (P : Program) (q : Polynomial ℕ) (x : List ℤ) (B : ℕ) : Prop :=
  ∀ c : Fin B → Bool, RunBounded P noOracle (extendCoins c) x B q 0

/-- The fraction of coin strings of length `B` on which the output after `B` steps satisfies
`Good`. -/
noncomputable def coinFrac (P : Program) (x : List ℤ) (B : ℕ) (Good : List ℤ → Prop) : ℝ :=
  ((Finset.univ.filter fun c : Fin B → Bool =>
      Good (outputAfter P noOracle (extendCoins c) x B)).card : ℝ) / 2 ^ B

/-- The error bound `e^{-c n}`. -/
noncomputable def expErr (c : ℝ) : ℕ → ℝ := fun n => Real.exp (-(c * n))

/-- No error. -/
def zeroErr : ℕ → ℝ := fun _ => 0

/-- The fixed program `P` with polynomials `p, q` decides `Yes` on the domain `Dom` in time
`O*(T)`, with error at most `ηY(n)` on yes-instances and `ηN(n)` on no-instances, where `n = nv a`
is the number of vertices. -/
def RandDecidesBy {α : Type*} (P : Program) (p q : Polynomial ℕ) (enc : α → List ℤ)
    (nv : α → ℕ) (Dom Yes : α → Prop) (T : α → ℝ) (ηY ηN : ℕ → ℝ) : Prop :=
  ∀ a, Dom a →
    AllRunsBounded P q (enc a) (budget p (enc a) (T a)) ∧
    (Yes a → 1 - ηY (nv a) ≤ coinFrac P (enc a) (budget p (enc a) (T a)) (· = [1])) ∧
    (¬ Yes a → 1 - ηN (nv a) ≤ coinFrac P (enc a) (budget p (enc a) (T a)) (· = [0]))

/-- `Yes` can be decided on `Dom` by a randomized algorithm in `O*(T)` time with errors `ηY, ηN`. -/
def RandDecides {α : Type*} (enc : α → List ℤ) (nv : α → ℕ) (Dom Yes : α → Prop)
    (T : α → ℝ) (ηY ηN : ℕ → ℝ) : Prop :=
  ∃ (P : Program) (p q : Polynomial ℕ), RandDecidesBy P p q enc nv Dom Yes T ηY ηN

/-- Search (§3.2, p. 8): on every input of `Dom` all runs are within `O*(T)`, and whenever a
solution exists (`∃ y, Sol a y`), the output is a solution with probability at least `1 - η(n)`. -/
def RandFinds {α : Type*} (enc : α → List ℤ) (nv : α → ℕ) (Dom : α → Prop)
    (Sol : α → List ℤ → Prop) (T : α → ℝ) (η : ℕ → ℝ) : Prop :=
  ∃ (P : Program) (p q : Polynomial ℕ), ∀ a, Dom a →
    AllRunsBounded P q (enc a) (budget p (enc a) (T a)) ∧
    ((∃ y, Sol a y) → 1 - η (nv a) ≤ coinFrac P (enc a) (budget p (enc a) (T a)) (Sol a))

/-- A deterministic polynomial-time computation: one program `P` and polynomials `p q` such that on
every input of `Dom` the run without coins halts within cost `p(σ(enc a))`, keeps its registers
within `q(σ(enc a))` bits, and its output satisfies `Good a`. -/
def DetPolyComputes {α : Type*} (enc : α → List ℤ) (Dom : α → Prop)
    (Good : α → List ℤ → Prop) : Prop :=
  ∃ (P : Program) (p q : Polynomial ℕ), ∀ a, Dom a →
    RunBounded P noOracle noCoins (enc a) (p.eval (bitSize (enc a))) q 0 ∧
    Good a (outputAfter P noOracle noCoins (enc a) (p.eval (bitSize (enc a))))

/-- Deterministic polynomial-time decision: the output is `[1]` on yes-instances and `[0]` on
no-instances, with no error. -/
def DetPolyDecides {α : Type*} (enc : α → List ℤ) (Dom Yes : α → Prop) : Prop :=
  DetPolyComputes enc Dom fun a out => out = if Yes a then [1] else [0]

end KColoringFaster.ListBootstrap


