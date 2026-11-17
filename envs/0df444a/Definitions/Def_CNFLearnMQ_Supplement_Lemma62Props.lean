-- Prove2me | Definitions.Def_CNFLearnMQ_Supplement_Lemma62Props
-- name    : CNFLearnMQ_Supplement_Lemma62Props
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:02:20.35054+00:00
-- url     : https://prove2.me/theorems/4597973c-1a31-434f-807d-d1a35395a793
-- title:
--   Properties (i)–(vi) of Lemma 6.2 of a random formula
-- statement:
--   Two distinct clauses are **neighbors** if they share a variable; the **clause line graph** has one vertex per clause and an edge between neighbors; a clause family $\mathcal Q\subseteq\mathcal C$ is **connected** if it induces a connected subgraph; a variable of $c\in\mathcal Q$ is **private** to $c$ within $\mathcal Q$ if it occurs in no other clause of $\mathcal Q$. For a formula $\Phi=(V,\mathcal C)$ on $n$ variables, parameters $k,\alpha$ and $m=\lfloor\alpha n\rfloor$, the properties are:
--
--   1. every clause has between $k-2$ and $k$ variables, and two distinct clauses share at most three variables;
--   2. every variable occurs in at most $10\log n$ clauses;
--   3. there are $\widetilde V_{\mathrm{bad}}\subseteq V$ and $\widetilde{\mathcal C}_{\mathrm{bad}}\subseteq\mathcal C$ such that every clause of $\widetilde{\mathcal C}_{\mathrm{bad}}$ has all its variables in $\widetilde V_{\mathrm{bad}}$, every variable outside $\widetilde V_{\mathrm{bad}}$ has degree at most $12k^7\alpha$, every clause outside $\widetilde{\mathcal C}_{\mathrm{bad}}$ has at least $k-k^{4/5}-2$ variables outside $\widetilde V_{\mathrm{bad}}$, and, if $\alpha>k^{-3}$, every connected family $\mathcal Q$ with $|\mathcal Q|\ge\log n$ satisfies $|\mathcal Q\cap\widetilde{\mathcal C}_{\mathrm{bad}}|\le \frac{k^{-1/5}}{16}|\mathcal Q|$;
--   4. for every clause $c$ and integer $\ell\ge1$, the number of connected $\ell$-clause families containing $c$ is at most $n^3(ek^2\alpha)^\ell$;
--   5. for $B\in\{k-2,\,k-8k^{4/5}\}$, every nonempty family $\mathcal Q$ with $|\mathcal Q|\le m/2^k$ and every choice of sets $T_c\subseteq\mathrm{vbl}(c)$ of size at least $B$ satisfy $\bigl|\bigcup_{c\in\mathcal Q}T_c\bigr|>(1-k^{-2/5})B|\mathcal Q|$;
--   6. every family $\mathcal Q\subseteq\mathcal C$ with $2\le|\mathcal Q|\le1024k^{6/5}\ln n$ contains two distinct clauses, each having at least $k-k^{4/5}$ variables private to it within $\mathcal Q$.
--
--   Lemma 6.2 asserts that a random formula is satisfiable and has these properties with probability $1-o(1/n)$; from §6.2 on the paper fixes a formula with them. They are the hypotheses of Theorem 6.3.
--
--   **Formalization Note** $\log$ is base 2 and $\ln$ natural (p.13); every real-valued threshold is compared as a real number. A connected family is nonempty. Satisfiability is a separate hypothesis wherever the properties are used.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 6.2, pp.37–38, and the terminology of §6.1, p.37

import Mathlib
import Definitions.Def_CNFLearnMQ_Supplement_randomCNF

set_option autoImplicit false

namespace CNFLearnMQ.Supplement

open CNFLearning873.Valiant

variable {n : ℕ}

/-- The degree of the variable `v` in the clause family `Q`: the number of clauses of `Q` that
contain `v`. -/
def varDegree (Q : CNF n) (v : Fin n) : ℕ := (Q.filter fun c => v ∈ support c).card

/-- The clause line graph induced on a clause family `Q` (Feng, Yu, Zhang, STOC 2027 submission
(manuscript sha256 519ee6d4…), §6.1, p.37): one vertex per clause of `Q`, and an edge between two
distinct clauses that share at least one variable (neighbors). -/
def lineGraphOn (Q : CNF n) : SimpleGraph Q :=
  SimpleGraph.fromRel fun a b => (support a.1 ∩ support b.1).Nonempty

/-- A clause family is connected if it induces a connected subgraph of the clause line graph
(p.37). A connected family is nonempty (`SimpleGraph.Connected` includes nonemptiness). -/
def IsConnectedFamily (Q : CNF n) : Prop := (lineGraphOn Q).Connected

/-- The variables of `c` private to `c` within `Q`: those occurring in no other clause of `Q`
(p.37). -/
def privateVars (Q : CNF n) (c : Clause n) : Finset (Fin n) := by
  classical
  exact (support c).filter fun v => ∀ c' ∈ Q, c' ≠ c → v ∉ support c'

open Classical in
/-- Properties (i)–(vi) of Lemma 6.2 (pp.37–38) for a formula `Φ` on `n` variables, with clause
parameters `k`, density `α` and `m = ⌊αn⌋`:
1. every clause has between `k − 2` and `k` variables, and two distinct clauses share at most three;
2. every variable occurs in at most `10 log n` clauses;
3. there are `Ṽ_bad ⊆ V`, `C̃_bad ⊆ C` with every clause of `C̃_bad` inside `Ṽ_bad`, every variable
   outside `Ṽ_bad` of degree at most `12k⁷α`, every clause outside `C̃_bad` with at least
   `k − k^{4/5} − 2` variables outside `Ṽ_bad`, and, if `α > k^{−3}`, every connected family `Q`
   with `|Q| ≥ log n` has `|Q ∩ C̃_bad| ≤ (k^{−1/5}/16)|Q|`;
4. for every clause `c` and `ℓ ≥ 1`, at most `n³(ek²α)^ℓ` connected `ℓ`-clause families contain `c`;
5. for `B ∈ {k − 2, k − 8k^{4/5}}`, every nonempty `Q` with `|Q| ≤ m/2^k` and every choice of
   `T_c ⊆ vbl(c)` with `|T_c| ≥ B` satisfy `|⋃_{c∈Q} T_c| > (1 − k^{−2/5}) B |Q|`;
6. every `Q ⊆ C` with `2 ≤ |Q| ≤ 1024k^{6/5} ln n` contains two distinct clauses each with at least
   `k − k^{4/5}` variables private to it within `Q`.

**Formalization Note** `log` is base 2 and `ln` natural (p.13). Real-valued thresholds are compared
as reals. Clause families are subsets of the formula's `Finset` of clauses. Satisfiability, the
other conclusion of Lemma 6.2, is a separate hypothesis wherever these properties are assumed. -/
def Lemma62Props (k : ℕ) (α : ℝ) (n : ℕ) (Φ : CNF n) : Prop :=
  -- (i)
  ((∀ c ∈ Φ, k - 2 ≤ width c ∧ width c ≤ k) ∧
    ∀ c ∈ Φ, ∀ c' ∈ Φ, c ≠ c' → (support c ∩ support c').card ≤ 3) ∧
  -- (ii)
  (∀ v : Fin n, (varDegree Φ v : ℝ) ≤ 10 * log₂ n) ∧
  -- (iii)
  (∃ Vbad : Finset (Fin n), ∃ Cbad : CNF n, Cbad ⊆ Φ ∧
    (∀ c ∈ Cbad, support c ⊆ Vbad) ∧
    (∀ v : Fin n, v ∉ Vbad → (varDegree Φ v : ℝ) ≤ 12 * (k : ℝ) ^ 7 * α) ∧
    (∀ c ∈ Φ, c ∉ Cbad →
      (k : ℝ) - (k : ℝ) ^ ((4 : ℝ) / 5) - 2 ≤ ((support c \ Vbad).card : ℝ)) ∧
    ((k : ℝ) ^ (-3 : ℝ) < α → ∀ Q : CNF n, Q ⊆ Φ → IsConnectedFamily Q → log₂ n ≤ (Q.card : ℝ) →
      ((Q ∩ Cbad).card : ℝ) ≤ (k : ℝ) ^ (-(1 : ℝ) / 5) / 16 * Q.card)) ∧
  -- (iv)
  (∀ c ∈ Φ, ∀ ℓ : ℕ, 1 ≤ ℓ →
    (((Φ.powerset.filter fun Q : CNF n => c ∈ Q ∧ Q.card = ℓ ∧ IsConnectedFamily Q).card : ℕ) : ℝ) ≤
      (n : ℝ) ^ 3 * (Real.exp 1 * (k : ℝ) ^ 2 * α) ^ ℓ) ∧
  -- (v)
  (∀ B : ℝ, (B = (k : ℝ) - 2 ∨ B = (k : ℝ) - 8 * (k : ℝ) ^ ((4 : ℝ) / 5)) →
    ∀ Q : CNF n, Q ⊆ Φ → Q.Nonempty → (Q.card : ℝ) ≤ (⌊α * n⌋₊ : ℝ) / 2 ^ k →
    ∀ T : Clause n → Finset (Fin n), (∀ c ∈ Q, T c ⊆ support c ∧ B ≤ ((T c).card : ℝ)) →
      (1 - (k : ℝ) ^ (-(2 : ℝ) / 5)) * B * Q.card < ((Q.biUnion T).card : ℝ)) ∧
  -- (vi)
  (∀ Q : CNF n, Q ⊆ Φ → 2 ≤ Q.card → (Q.card : ℝ) ≤ 1024 * (k : ℝ) ^ ((6 : ℝ) / 5) * Real.log n →
    ∃ c₁ ∈ Q, ∃ c₂ ∈ Q, c₁ ≠ c₂ ∧
      (k : ℝ) - (k : ℝ) ^ ((4 : ℝ) / 5) ≤ ((privateVars Q c₁).card : ℝ) ∧
      (k : ℝ) - (k : ℝ) ^ ((4 : ℝ) / 5) ≤ ((privateVars Q c₂).card : ℝ))

end CNFLearnMQ.Supplement


