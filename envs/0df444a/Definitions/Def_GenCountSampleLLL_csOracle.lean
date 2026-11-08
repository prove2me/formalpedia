-- Prove2me | Definitions.Def_GenCountSampleLLL_csOracle
-- name    : GenCountSampleLLL_csOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:49:36.068093+00:00
-- url     : https://prove2.me/theorems/481cedf8-0b8c-46d9-acb6-98c5b5d2b5a2
-- title:
--   The computational model: the CSP oracle, the encodings $\mathrm{encInst}$, size $I$, admissible programs, expected cost
-- statement:
--   Remark 1.2 assumes "access to oracles for testing constraints and drawing independent samples from the coordinate distributions", with "the domains, the sets $\mathrm{vbl}(a)$, and their incidence lists" given explicitly and $I$ the encoded instance size.
--
--   Programs run on the published randomized log-cost oracle RAM (`PDSEquiv.Machine`). A program is **admissible** if it never uses the machine's exact Bernoulli instruction, so its randomness comes from fair bits. The **CSP oracle** answers a query $[0,v]$ with a fresh draw from $\nu_v$, a query $1::a::\mathit{vals}$ with whether the values $\mathit{vals}$ (one per variable of $\mathrm{vbl}(a)$, in increasing order) form a forbidden assignment of $a$, and $[2]$ with a fair bit; every other query gets the empty reply. The input `encInst` lists $n$, $m$, the domain sizes $q_v$, each $\mathrm{vbl}(a)$ and each incidence list; the size $I$ is its length plus $\sum_v q_v$. Assignments, families of constraints and integer outputs have fixed encodings. The **expected cost** of a run is $\sup_t\mathbb E[\text{cost after }t\text{ steps}]$ in $[0,\infty]$; a program **halts almost surely** when its output masses sum to $1$.
--
--   These notions make "FPRAS", "polynomial expected time" and "estimator" statements about programs.
--
--   **Formalization Note** The program sees neither $\nu$, nor the forbidden sets, nor $x$, except through the oracle. Every query and reply is charged by the bit lengths of its cells, so oracle costs are polynomial in $I$.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Remark 1.2, p.2

import Mathlib
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_GenCountSampleLLL_Inst

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace GenCountSampleLLL

noncomputable section

open Classical

/-!
# The computational model: the CSP oracle, the encodings, and the cost notions

Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671
(held file sha256 cd449f83…), Remark 1.2, p.2: "We use the same basic computational assumptions
as in the Moser–Tardos algorithm [10]. The domains, the sets vbl(a), and their incidence lists are
given explicitly. Write I for the encoded instance size. We assume access to oracles for testing
constraints and drawing independent samples from the coordinate distributions, each with
polynomial cost in I."

**Formalization Note.** Programs run on the published randomized log-cost oracle RAM
`PDSEquiv.Machine` (every instruction, oracle query and reply charged by the bit lengths of the
cells involved). `Admissible` programs do not use its exact rational Bernoulli instruction `ber`;
their randomness is the fair bits of the oracle. The single oracle `csOracle` answers three kinds
of query: `[0, v]` (a fresh draw from `ν_v`), `1 :: a :: vals` (whether the values `vals`, listed
for the variables of `vbl(a)` in increasing order, form a forbidden assignment of `a`), and `[2]`
(a fair bit); every other query gets `[]`. The program sees neither `ν`, nor the forbidden sets,
nor `x`. The input `encInst` lists `n`, `m`, the domain sizes, each `vbl(a)`, and each incidence
list; `size` is its length plus `Σ_v q_v`, since the domains are given explicitly. Expected
cost `expCost` is in `ℝ≥0∞` and charges non-halting branches.
-/

namespace Inst

variable (I : Inst)

/-- The encoded instance: `[n, m]`, the domain sizes `q_0, …, q_{n−1}`, then for each constraint
`a` the number `|vbl(a)|` followed by its variables in increasing order, then for each variable
`v` the number of constraints containing `v` followed by those constraints in increasing order
(the incidence lists). -/
def encInst : List ℕ :=
  [I.n, I.m] ++ List.ofFn (fun v => I.q v) ++
    (List.ofFn fun a => (I.vbl a).card :: ((I.vbl a).sort (· ≤ ·)).map fun v => (v : ℕ)).flatten ++
    (List.ofFn fun v =>
      ((Finset.univ.filter fun a => v ∈ I.vbl a).card ::
        ((Finset.univ.filter fun a => v ∈ I.vbl a).sort (· ≤ ·)).map fun a => (a : ℕ))).flatten

/-- The encoded instance size `I` of Remark 1.2: the length of `encInst` plus the total domain
size `Σ_v q_v`. -/
def size : ℕ := I.encInst.length + ∑ v, I.q v

/-- The encoding of an assignment: its values `σ_0, …, σ_{n−1}`. -/
def encAssign (σ : I.Assign) : List ℕ := List.ofFn fun v => ((σ v : Fin (I.q v)) : ℕ)

/-- The encoding of a family `D ⊆ C`: `|D|` followed by its members in increasing order. -/
def encFamily (D : Finset (Fin I.m)) : List ℕ := D.card :: (D.sort (· ≤ ·)).map fun a => (a : ℕ)

/-- The position of the variable `v` in the increasing listing of `vbl(a)`. -/
def idx (a : Fin I.m) (v : Fin I.n) : ℕ := ((I.vbl a).filter (· < v)).card

/-- The answer to a constraint test: `some true` if `vals` (one value per variable of `vbl(a)`,
in increasing variable order, each in range) is a forbidden assignment of `a`, `some false` if it
is an allowed one, `none` if `vals` is malformed. -/
def testQuery (a : Fin I.m) (vals : List ℕ) : Option Bool :=
  if h : vals.length = (I.vbl a).card ∧ ∀ v ∈ I.vbl a, vals.getD (I.idx a v) 0 < I.q v then
    some (decide ((fun v : {v // v ∈ I.vbl a} =>
      (⟨vals.getD (I.idx a v.1) 0, h.2 v.1 v.2⟩ : Fin (I.q v.1))) ∈ I.forb a))
  else none

/-- The CSP oracle of Remark 1.2: `[0, v]` with `v < n` returns `[x]` with `x ∼ ν_v` (a fresh
draw); `1 :: a :: vals` with `a < m` and `vals` well formed returns `[1]` if `vals` is forbidden
by `a` and `[0]` otherwise; `[2]` returns a fair bit `[0]` or `[1]`; every other query returns
`[]`. -/
def csOracle : PDSEquiv.Oracle := fun qry =>
  match qry with
  | [0, v] => if h : v < I.n then (I.ν ⟨v, h⟩).map fun x => [(x : ℕ)] else PMF.pure []
  | 1 :: a :: vals =>
    if h : a < I.m then
      match I.testQuery ⟨a, h⟩ vals with
      | some b => PMF.pure [if b then 1 else 0]
      | none => PMF.pure []
    else PMF.pure []
  | [2] => (PMF.uniformOfFintype Bool).map fun b => [if b then 1 else 0]
  | _ => PMF.pure []

/-- The law of the decoded output assignment: the probability that the program halts with
output `encAssign σ`. -/
def outLaw (P : PDSEquiv.Program) (input : List ℕ) (σ : I.Assign) : ℝ :=
  PDSEquiv.outMass P I.csOracle input (I.encAssign σ)

end Inst

/-- A program that never uses the exact Bernoulli instruction `ber`; its randomness is the
oracle's fair bits. -/
def Admissible (P : PDSEquiv.Program) : Prop := ∀ i ∈ P, ∀ d a b, i ≠ PDSEquiv.Instr.ber d a b

/-- The expected log-cost of a run, `sup_t E[cost after t steps]`, in `ℝ≥0∞`. The cost is
nondecreasing along every run (a halted machine stutters at no cost), so this is the expected
total cost; branches that never halt are charged their unbounded cost. -/
def expCost (P : PDSEquiv.Program) (Q : PDSEquiv.Oracle) (input : List ℕ) : ℝ≥0∞ :=
  ⨆ t, ∑' s, PDSEquiv.runLaw P Q input t s * (s.cost : ℝ≥0∞)

/-- The program halts almost surely: its output masses sum to `1`. -/
def HaltsAS (P : PDSEquiv.Program) (Q : PDSEquiv.Oracle) (input : List ℕ) : Prop :=
  ∑' o, PDSEquiv.outMass P Q input o = 1

/-- An integer output: `[0, k]` stands for `k` and `[1, k]` for `−k`. -/
def IsIntOut (o : List ℕ) : Prop := ∃ k : ℕ, o = [0, k] ∨ o = [1, k]

/-- The value of an integer output. -/
def intOut : List ℕ → ℝ
  | [0, k] => k
  | [1, k] => -(k : ℝ)
  | _ => 0

end

end GenCountSampleLLL


