-- Prove2me | Definitions.Def_CNFLearnMQ_Supplement_randomCNF
-- name    : CNFLearnMQ_Supplement_randomCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:01:48.379566+00:00
-- url     : https://prove2.me/theorems/34896ffd-9c5c-4489-a6a9-bb82f2a2c96d
-- title:
--   The random $k$-CNF model $\Phi(k,n,m)$, the exponent $\eta_k$ and the density bound
-- statement:
--   Let $V=\{v_1,\dots,v_n\}$ and consider the $2n$ literals $v_1,\dots,v_n,\neg v_1,\dots,\neg v_n$. The **random $k$-CNF formula** $\Phi=\Phi(k,n,m)$ is generated as follows: each of the $m$ clauses is generated independently by drawing $k$ literals uniformly with replacement from the $2n$ literals. Tautological clauses (containing both a variable and its negation) are deleted, and repeated copies of a literal within a clause are merged. The resulting formula $\Phi=(V,\mathcal C)$ has the same solution set as the generated one; its clauses may have width less than $k$. In §6 the number of clauses is $m=\lfloor\alpha n\rfloor$ for a constant density $\alpha>0$.
--
--   The module also fixes the two constants of §6:
--   $$\eta_k = 4096\,k^{6/5}\cdot 2^{-k^{4/5}},\qquad \alpha_{\max}(k)=\frac{2^{\,k-30k^{4/5}\log k}}{2^{10}e^2k^8},$$
--   where $\log$ is the base-2 logarithm. The density regime of Theorems 6.1 and 6.3 is $k\ge 10^5$ and $0<\alpha\le\alpha_{\max}(k)$; $\eta_k=o_k(1)$ is the excess exponent of the running time.
--
--   **Formalization Note** The model is the law of the formula obtained from a uniform element of $(\mathrm{Fin}\,m\to\mathrm{Fin}\,k\to\mathrm{Fin}\,n\times\mathrm{Bool})$, a literal $(v,b)$ being satisfied when $x_v=b$. A formula is a finite set of clauses in the published clause type (the stored value is the satisfying one), so two generated clauses with the same literal set are kept once; the solution set is unchanged. For $n=0$ (no literals) the law is the point mass on the empty formula.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), §6, pp.36–37; Theorem 6.1, p.37

import Mathlib
import Definitions.Def_CNFLearning873_Valiant_Thresholds

set_option autoImplicit false

namespace CNFLearnMQ.Supplement

open CNFLearning873.Valiant

/-- The exponent `η_k = 4096·k^{6/5}·2^{−k^{4/5}}` (Feng, Yu, Zhang, *Learning CNF Formulas with
Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256
519ee6d4…), Theorem 6.1, p.37). A real number, used as a real exponent (`Real.rpow`). -/
noncomputable def etaK (k : ℕ) : ℝ :=
  4096 * (k : ℝ) ^ ((6 : ℝ) / 5) * (2 : ℝ) ^ (-((k : ℝ) ^ ((4 : ℝ) / 5)))

/-- The density bound of §6, `2^{k − 30k^{4/5} log k}/(2^{10} e² k⁸)` (Theorem 6.1 and Lemma 6.2,
p.37), with `log` the base-2 logarithm (p.13). -/
noncomputable def densityBound (k : ℕ) : ℝ :=
  (2 : ℝ) ^ ((k : ℝ) - 30 * (k : ℝ) ^ ((4 : ℝ) / 5) * log₂ k) /
    ((2 : ℝ) ^ 10 * Real.exp 2 * (k : ℝ) ^ 8)

/-- A literal on `n` variables: a variable `v` and the Boolean value `b` that satisfies the literal
(`(v, true)` is `v`, `(v, false)` is `¬v`). There are `2n` literals. -/
abbrev Literal (n : ℕ) := Fin n × Bool

/-- A drawn clause (a `k`-tuple of literals) is tautological if it contains a variable and its
negation. -/
def IsTautology {n k : ℕ} (w : Fin k → Literal n) : Prop :=
  ∃ v : Fin n, (∃ i, w i = (v, true)) ∧ ∃ j, w j = (v, false)

/-- The clause whose literal set is the set of drawn literals (repeated copies merged), in the
published clause convention: `c v = some b` stores the satisfying value `b`. On a non-tautological
tuple at most one of `(v, true)`, `(v, false)` occurs. -/
noncomputable def drawnClause {n k : ℕ} (w : Fin k → Literal n) : Clause n := by
  classical
  exact fun v => if ∃ i, w i = (v, true) then some true
    else if ∃ i, w i = (v, false) then some false else none

/-- The formula generated from `m` drawn `k`-tuples of literals: tautological clauses deleted,
repeated literals merged, and each surviving clause kept (as an element of a `Finset`). -/
noncomputable def formulaOf {n k m : ℕ} (W : Fin m → Fin k → Literal n) : CNF n := by
  classical
  exact (Finset.univ.filter fun j => ¬ IsTautology (W j)).image fun j => drawnClause (W j)

/-- The random `k`-CNF model `Φ(k, n, m)` of §6 (pp.36–37): each of the `m` clauses is generated
independently by drawing `k` literals uniformly with replacement from the `2n` literals on `V`;
tautological clauses are deleted and repeated copies of a literal within a clause are merged. This
is the law of `formulaOf W` for `W` uniform on `(Fin m → Fin k → Literal n)`.

**Formalization Note** `n ≥ 1` is needed for literals to exist; for `n = 0` the uniform law on the
(empty, when `m, k ≥ 1`) type of draws does not exist, and we return the empty formula. A formula is a
`Finset` of clauses, so two generated clauses with the same literal set are kept once; this leaves
the solution set (and cores) unchanged. -/
noncomputable def randomCNF (k n m : ℕ) : PMF (CNF n) := by
  classical
  exact if h : Nonempty (Fin m → Fin k → Literal n) then
    haveI := h
    (PMF.uniformOfFintype (Fin m → Fin k → Literal n)).map formulaOf
  else PMF.pure ∅

end CNFLearnMQ.Supplement


