-- Prove2me | Definitions.Def_AcceptSubcube_Supplement_CompleteSigned
-- name    : AcceptSubcube_Supplement_CompleteSigned
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:48:39.486693+00:00
-- url     : https://prove2.me/theorems/5a9b32d4-459c-4fdb-af03-06df473761fe
-- title:
--   Signed threshold and NAE predicates, complement invariance, the all-positive clause, and Boolean Turán networks
-- statement:
--   All instances are lists of constraints on the variables $0,\dots,n-1$, each a scope (a list of distinct variables) with the truth table of its predicate.
--
--   1. **Threshold predicate.** $\mathrm{THR}_{k,s}(u)=1$ iff at least $s$ of the $k$ bits of $u$ equal $1$. $\mathrm{THR}_{k,1}$ is the $k$-clause.
--   2. **Not-all-equal.** $\mathrm{NAE}_k(u)=1$ iff $u$ is not constant.
--   3. **Signed predicate.** A constraint on scope $E$ *carries the signed predicate* $P$ if there is a sign vector $\sigma\in\{0,1\}^E$ with $P_E(y)=P(y\oplus\sigma)$ for every local pattern $y$, i.e. $P$ is applied to the literals $x_v$ ($\sigma_v=0$) and $\neg x_v$ ($\sigma_v=1$). The signs are chosen per constraint.
--   4. **Complete signed $P$.** A complete $k$-CSP (one unweighted constraint on every $k$-subset of $[n]$) in which every constraint carries the signed predicate $P$. Complete Min-$k$-SAT is complete signed $\mathrm{THR}_{k,1}$.
--   5. **Complement invariance.** A constraint is complement-invariant if $P_E(y)=P_E(\bar y)$ for every pattern $y$. The class $\mathcal{CI}_k$ consists of the complete $k$-CSPs whose predicates are all nontrivial and complement-invariant; it contains complete signed $\mathrm{NAE}_k$.
--   6. **All-positive clause.** A constraint is the all-positive clause if it rejects exactly the all-zero pattern; $\#\{E : P_E\text{ is not the all-positive clause}\}$ counts the others.
--   7. **Boolean Turán network** with parameters $(k,q)$ (Definition 6.1): a simple $k$-uniform hypergraph $H$ on $[n]$ such that every $q$-set of variables contains a scope of $H$, with one unweighted nontrivial predicate on every $E\in H$. Absent scopes carry no constraint.
--
--   These are the instance families of the hardness theorems (Theorems 1.2, 4.11, 5.7, 7.9) and of the Turán application (Theorem 1.4).
--
--   **Formalization Note** A local pattern is a list of $|E|$ bits read in the scope's order; the table entry of $y$ is at index $\sum_i 2^iy_i$, as in the published `GInst`. Completeness is the published `GInst.IsComplete`. For $n<q$ the Turán coverage condition is vacuous, as in the paper.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), p.4 (THR_{k,s}, NAE_k); §7, p.34 (signed predicates); Theorem 5.7, p.28 (complement invariance); (34), p.40; Definition 6.1, p.30

import Mathlib
import Definitions.Def_AcceptSubcube_GInst

namespace AcceptSubcube.Supplement

open AcceptSubcube

/-- **The threshold predicate** `THR_{k,s}`: a pattern `u` (a list of `k` bits) is accepted iff at
least `s` of its entries are `1`.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), p.4: "signed threshold predicates THR_{k,s},
which require at least s true literals"; §7.3, p.36. The arity `k` is the length of the pattern;
`THR_{k,1}` is the `k`-clause. -/
def thr (s : ℕ) (u : List Bool) : Bool := decide (s ≤ u.count true)

/-- **The predicate** `NAE_k`: it rejects exactly the two constant patterns (p.4: "The predicate
NAE_k, which rejects exactly the two constant patterns"). `INT_{k,1} = NAE_k` (§7.4, p.38). -/
def nae (u : List Bool) : Bool := u.any id && u.any not

/-- **A constraint carries the signed predicate `P`**: there is a sign vector `σ` on its scope such
that the table at every local pattern `y` is `P(y ⊕ σ)`, i.e. `P` applied to the literals
`x_v` (`σ_v = 0`) and `¬x_v` (`σ_v = 1`).

Cai, Jiang, Liu, STOC 2027 submission (manuscript sha256 66626baf…), §7, p.34: "a scope carries a
signed predicate on given literals when the predicate is applied to those literals".

**Formalization Note.** The sign vector is chosen per constraint. Local patterns are lists of
`|scope|` bits, read in the scope's order, the table entry of `y` being at index `Σ_i 2^i y_i`
(`patIdx`, as in the published `GInst`). -/
def IsSignedOf (P : List Bool → Bool) (c : List ℕ × List Bool) : Prop :=
  ∃ σ : List Bool, σ.length = c.1.length ∧
    ∀ y : List Bool, y.length = c.1.length → c.2.getD (patIdx y) false = P (List.zipWith xor y σ)

/-- **Complete signed `P` instance** of arity `k`: a complete `k`-CSP (one unweighted constraint on
every `k`-subset of `[n]`, published `GInst.IsComplete`) in which every constraint carries the
signed predicate `P` (Theorem 1.2, p.4: "complete signed THR_{k,k−2}"; Theorem 5.7, p.28:
"complete signed NAE_k"). Complete Min-`k`-SAT is `CompleteSigned (thr 1) k`. -/
def CompleteSigned (P : List Bool → Bool) (k : ℕ) (I : GInst) : Prop :=
  I.IsComplete k ∧ ∀ c ∈ I.cons, IsSignedOf P c

/-- **A complement-invariant constraint**: its predicate is unchanged when all inputs are
complemented, `P(y) = P(¬y)` for every local pattern `y` (Theorem 5.7, p.28: "every nontrivial
predicate invariant under complementing all inputs"). -/
def ComplInv (c : List ℕ × List Bool) : Prop :=
  ∀ y : List Bool, y.length = c.1.length →
    c.2.getD (patIdx y) false = c.2.getD (patIdx (y.map not)) false

/-- **The class of the upper bounds of Theorem 5.7**: complete `k`-CSPs whose every predicate is
nontrivial and complement-invariant (predicates may differ between scopes). It contains every
complete signed `NAE_k` instance. -/
def CompleteComplInv (k : ℕ) (I : GInst) : Prop :=
  I.IsComplete k ∧ I.Nontrivial ∧ ∀ c ∈ I.cons, ComplInv c

/-- The constraint is **the all-positive clause** on its scope: it rejects exactly the all-zero
local pattern (the pattern of index `0`). Theorem 7.9, (34), p.40. -/
def isAllPos (c : List ℕ × List Bool) : Bool :=
  c.2 == (List.range (2 ^ c.1.length)).map (fun j => j != 0)

/-- The number of constraints that are not the all-positive clause
(`|{E : P_E is not the all-positive clause}|`, (34), p.40). -/
def numNotAllPos (I : GInst) : ℕ := I.cons.countP (fun c => !isAllPos c)

/-- **Boolean Turán Min-CSP with parameters `(k, q)`** (Definition 6.1, p.30): "Fix integers
q ≥ k ≥ 2. An instance … consists of a simple k-uniform hypergraph H on [n] with α(H) < q, i.e.,
every q-set of variables contains a scope of H, (26) and, for every E ∈ H, one unweighted nontrivial
predicate P_E : {0,1}^E → {0,1}."

Well formed, `k`-uniform, at most one constraint per scope (the scopes form a simple hypergraph),
every predicate nontrivial, and every `q`-subset `W` of `[n]` contains the scope of a constraint.

**Formalization Note.** Cost and optimum are the published `cost`/`OPT` (absent scopes carry no
constraint). For `n < q` the coverage condition (26) is vacuous, as in the paper (p.33: "If n < q,
solve the instance by exhaustive search"). The parameters `q ≥ k ≥ 2` are hypotheses of the
theorems that use this class. -/
def TuranNet (k q : ℕ) (I : GInst) : Prop :=
  I.WellFormed ∧ I.Uniform k ∧ I.ScopeUnique ∧ I.Nontrivial ∧
    ∀ W : Finset ℕ, W ⊆ Finset.range I.n → W.card = q → ∃ c ∈ I.cons, c.1.toFinset ⊆ W

end AcceptSubcube.Supplement


