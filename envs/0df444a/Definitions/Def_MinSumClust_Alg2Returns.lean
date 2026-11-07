-- Prove2me | Definitions.Def_MinSumClust_Alg2Returns
-- name    : MinSumClust_Alg2Returns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:49.97794+00:00
-- url     : https://prove2.me/theorems/87431cd8-3ad6-458f-b6a2-eab1eabd66c4
-- title:
--   Algorithm 2: obtaining an approximately openable set
-- statement:
--   Algorithm 2 (p.23), called on a state of Algorithm 3, may return a set $S$ of clients as follows.
--
--   1. **Singletons.** If some active client $i$ has $\alpha_i\ge f$, it returns $\{i\}$.
--   2. **Enumeration.** Otherwise, for a size $s\in\{1,\dots,n\}$ and a center $c$: a tree whose root $\upsilon$ has $S_V(\upsilon)\ne\bot$ and $|S_V(\upsilon)|<r_S\cdot s$ is ignored, and $D_{\mathrm{ignore}}$ is the set of clients of ignored trees. Among the available sets $T\subseteq D\setminus D_{\mathrm{ignore}}$ with $|T|\le s$, a maximizer $S_0$ of $\sum_{j\in T}(\alpha_j-s\cdot 4\gamma_{DC}\cdot d(j,c))$ is taken; if its value is at least $f$, the enumeration ends with $S_0$.
--   3. **Cleaning.** Step III.1 repeats: with $\gamma'=(\sum_{j\in S}\alpha_j-f)/\mathrm{cost}(S)$, if $\sum_{j\in S\setminus A}\alpha_j<\gamma'\sum_{j\in S\setminus A}d(j,S)$ then $S\leftarrow A\cap S$; otherwise one $j\in S\cap A$ with $\alpha_j<2\gamma' d(j,S)$ is removed; the loop stops when nothing is removed. Step III.2 repeats while some $i\in S$ has $\alpha_i<\gamma_{DC}d(i,S)$: it removes every $j\in S$ with $j\preceq i$. The cleaned set is returned.
--
--   **Formalization Note** The paper does not fix the enumeration order of $(s,c)$, which maximizer the dynamic program finds, or which client a cleaning round removes. The relation allows every such choice (any $(s,c)$ whose maximum reaches $f$ is first in some enumeration order), so the milestones about Algorithm 3 hold for all of them. The division by $\mathrm{cost}(S)$ is kept literally (the paper shows $|S|\ge 2$ there).
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Algorithm 2, p.23 (PDF p.25); Lemma 14, p.22

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_Alg3State

namespace MinSumClust

/-- Client `i` lies in an ignored tree for the size `s` (Algorithm 2, step II, p.23): the root `υ`
of its tree has `S_V(υ) ≠ ⊥` and `|S_V(υ)| < r_S · s`. The set of such clients is `D_ignore`.

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Algorithm 2, p.23 (PDF p.25). -/
def Ignored {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) (s : ℕ) (i : Fin n) : Prop :=
  ∃ r S, IsRootOf σ r i ∧ nodeSV σ.hist r = some S ∧ (S.card : ℝ) < P.rS * s

/-- The objective of step II: `∑_{j ∈ T} (α_j − s · 4γ_DC · d(j, c))`. -/
def dpObj {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) (s : ℕ) (c : Fin n)
    (T : Finset (Fin n)) : ℝ :=
  ∑ j ∈ T, (σ.α j - s * (4 * P.γDC) * P.d j c)

/-- A candidate set of step II for the size `s`: `T ⊆ D \ D_ignore`, `T` available, `|T| ≤ s`. -/
def IsDPCand {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) (s : ℕ) (T : Finset (Fin n)) : Prop :=
  (∀ i ∈ T, ¬ Ignored P σ s i) ∧ Available σ T ∧ T.card ≤ s

/-- `T` is a maximizer of the step II objective for `(s, c)` among the candidate sets (the set the
dynamic program finds). -/
def IsDPMax {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) (s : ℕ) (c : Fin n)
    (T : Finset (Fin n)) : Prop :=
  IsDPCand P σ s T ∧ ∀ T', IsDPCand P σ s T' → dpObj P σ s c T' ≤ dpObj P σ s c T

/-- `γ′ = (∑_{j ∈ S} α_j − f) / cost(S)` of cleaning step III.1. -/
noncomputable def gammaPrime {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) (S : Finset (Fin n)) : ℝ :=
  (∑ j ∈ S, σ.α j - P.f) / cost P.d S

/-- The first test of step III.1: `∑_{j ∈ S \ A} α_j < γ′ · ∑_{j ∈ S \ A} d(j, S)`. -/
def Clean1Test {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) (S : Finset (Fin n)) : Prop :=
  ∑ j ∈ S \ σ.A, σ.α j < gammaPrime P σ S * ∑ j ∈ S \ σ.A, dist1 P.d j S

/-- One round of cleaning step III.1: if the first test holds, `S ← A ∩ S`; otherwise remove one
`j ∈ S ∩ A` with `α_j < 2γ′ d(j, S)`. -/
def Clean1Step {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) (S S' : Finset (Fin n)) : Prop :=
  (Clean1Test P σ S ∧ S' = σ.A ∩ S) ∨
    (¬ Clean1Test P σ S ∧ ∃ j ∈ S ∩ σ.A,
      σ.α j < 2 * gammaPrime P σ S * dist1 P.d j S ∧ S' = S.erase j)

/-- Step III.1 breaks its loop at `S`: no client is removed. -/
def Clean1Stops {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) (S : Finset (Fin n)) : Prop :=
  ¬ Clean1Test P σ S ∧ ∀ j ∈ S ∩ σ.A, ¬ σ.α j < 2 * gammaPrime P σ S * dist1 P.d j S

/-- One round of cleaning step III.2: for a client `i ∈ S` with `α_i < γ_DC d(i, S)`, remove every
`j ∈ S` with `j ⪯ i`. -/
noncomputable def Clean2Step {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) (S S' : Finset (Fin n)) :
    Prop :=
  open Classical in
  ∃ i ∈ S, σ.α i < P.γDC * dist1 P.d i S ∧ S' = S.filter fun j => ¬ Prec σ j i

/-- Step III.2 stops at `S`: no `i ∈ S` has `α_i < γ_DC d(i, S)`. -/
def Clean2Stops {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ¬ σ.α i < P.γDC * dist1 P.d i S

/-- **Algorithm 2 (Obtain an approximately openable set)**, p.23 (PDF p.25), as the relation
"Algorithm 2, called on the state `σ`, can return the set `S`".

* Step I: some `i ∈ A` has `α_i ≥ f`, and `S = {i}`.
* Otherwise (every active `α_i < f`), step II: for some size `s ∈ [n]` and center `c`, a maximizer
  `S₀` of `∑_{j ∈ T}(α_j − s·4γ_DC·d(j, c))` over the available `T ⊆ D \ D_ignore` with `|T| ≤ s`
  has objective `≥ f`; and `S` is a result of the cleaning III.1 followed by III.2 started at `S₀`.

**Formalization Note.** The paper leaves open the enumeration order of `(s, c)`, which maximizer
the dynamic program returns, and which client a cleaning round removes. The relation admits every
such choice (any `(s, c)` whose maximum reaches `f` comes first in some enumeration order), so
every statement about Algorithm 3 holds for all of them. `γ′` divides by `cost(S)`, literally as
printed (Lean's `x / 0 = 0`; the paper shows `|S| ≥ 2` there, Lemma 14). -/
def Alg2Returns {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) (S : Finset (Fin n)) : Prop :=
  (∃ i ∈ σ.A, P.f ≤ σ.α i ∧ S = {i}) ∨
    ((∀ i ∈ σ.A, σ.α i < P.f) ∧
      ∃ s : ℕ, 1 ≤ s ∧ s ≤ n ∧ ∃ c : Fin n, ∃ S₀ : Finset (Fin n),
        IsDPMax P σ s c S₀ ∧ P.f ≤ dpObj P σ s c S₀ ∧
        ∃ S₁, Relation.ReflTransGen (Clean1Step P σ) S₀ S₁ ∧ Clean1Stops P σ S₁ ∧
          Relation.ReflTransGen (Clean2Step P σ) S₁ S ∧ Clean2Stops P σ S)

end MinSumClust


