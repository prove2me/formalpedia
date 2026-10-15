-- Prove2me | Definitions.Def_HiringLP_ProbeTopK_Model
-- name    : HiringLP_ProbeTopK_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:38.169995+00:00
-- url     : https://prove2.me/theorems/edc75db0-ec5d-40af-af51-5fc617c50fff
-- title:
--   §3.1, §4.1–4.3, pp. 11–17 — ProbeTop-k instances, LPptk, basic feasible solutions, DR, ALGptk and its expected reward
-- statement:
--   **Instances (§3.1).** A firm must fill $k$ positions from $n$ applicants and may conduct at most $T$ interviews. Applicant $i$ has a random non-negative value $V_i$ supported on $\{r_1, \dots, r_J\}$, with $q_{ij} = \Pr(V_i = r_j)$; the values are independent across applicants. An instance $I = (k, T, n, (r_j), (q_{ij}))$ is **valid** when
--
--   $$
--   1 \le k \le T \le n, \qquad r_j \ge 0, \qquad q_{ij} \ge 0, \qquad \sum_{j} q_{ij} = 1 .
--   $$
--
--   **The linear program (§4.1).** $\mathrm{LP}_{ptk}(I)$ maximises $\sum_{i}\sum_{j} r_j x_{ij}$ subject to
--
--   $$
--   x_{ij} \le y_i q_{ij}, \quad \sum_i y_i \le T, \quad \sum_i \sum_j x_{ij} \le k, \quad x_{ij} \ge 0, \quad 0 \le y_i \le 1 .
--   $$
--
--   An optimal solution is a feasible $(x, y)$ whose objective is at least that of every feasible point. The feasible set is a polytope in $(x,y)$-space; its extreme points are its basic feasible solutions.
--
--   **Derived quantities (4).** For a solution $(x,y)$,
--
--   $$
--   p_i = \frac{\sum_j x_{ij}}{y_i}, \qquad v_i = \frac{\sum_j r_j x_{ij}}{\sum_j x_{ij}},
--   $$
--
--   each defined as $0$ when its denominator is $0$ (footnote 2), and the hiring probability of an interviewed applicant $i$ with value $r_j$ is $x_{ij}/(y_i q_{ij})$ (again $0$ when $y_i q_{ij} = 0$).
--
--   **Dependent rounding DR (§4.2).** Let $B = \{i : y_i = 1\}$ and $F = \{i : 0 < y_i < 1\}$. DR outputs a random interview set $S$ with $B \subseteq S \subseteq B \cup F$: if $F = \emptyset$ then $S = B$; if $F = \{a\}$ then $a \in S$ with probability $y_a$; if $F = \{a, b\}$ then $S = B \cup \{a\}$ with probability $y_a$ and $S = B \cup \{b\}$ with probability $y_b$.
--
--   **ALGptk and its expected reward (§4.3).** Given an LP solution $(x,y)$ and an interview order (in the paper, decreasing in $v_i$), ALGptk draws $S$ from DR, interviews the applicants of $S$ in that order, and on observing value $r_j$ for applicant $i$ hires $i$ with probability $x_{ij}/(y_i q_{ij})$, provided a position is still open. Its expected reward $R_{ALG_{ptk}}(I)$ is the expected sum of the realised values $V_i$ of the hired applicants, where $S$, the values, and the hiring coins are independent, and the coins are independent across applicants given the values.
--
--   Finally, the quantity $\sum_i v_i\, \mathbb{E}(\mathbf 1\{N_{i-1} < k\} Z_i)$ of §4.4 is defined for an arbitrary law of the interview set: $Y_i = \mathbf 1\{i \in S\}$, independent Bernoulli($p_i$) indicators $P_i$ independent of $S$, $Z_i = Y_i P_i$, and $N_{i-1}$ the number of $\ell$ before $i$ in the order with $Z_\ell = 1$.
--
--   **Formalization Note.** Applicants are `Fin n`, support points `Fin J`. Probabilities are explicit finite sums over the interview set, the value vector $V \in [J]^n$ (weight $\prod_i q_{i V_i}$) and the coin set (weight $\prod_i$ of the coin probability or its complement). Hiring is committed: applicant $i$ is hired iff $i \in S$, its coin is heads, and fewer than $k$ earlier applicants of $S$ had heads; the collected value is the realised $r_{V_i}$, not $v_i$. The interview order is a permutation `ord` (the $t$-th interview is `ord t`); "decreasing in $v$" is the predicate `SortedBy ord v`, which allows any order among ties. The formula for DR is used only at extreme points, which have at most two fractional coordinates; on vectors with three or more fractional coordinates it is independent rounding of those coordinates, a case the paper never needs.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, pp. 11–17, §3.1 and §4.1–4.3, equations (1)–(4) and footnote 2

import Mathlib

namespace HiringLP.ProbeTopK

open Finset

/-- §3.1, p. 11: a ProbeTop-k instance with `n` applicants and value support `{r j}_{j ∈ Fin J}`;
`q i j = P(V i = r j)`. -/
structure Instance (n J : ℕ) where
  k : ℕ
  T : ℕ
  r : Fin J → ℝ
  q : Fin n → Fin J → ℝ

/-- §3.1, p. 11: `1 ≤ k ≤ T ≤ n`, non-negative support values, each `q i` a probability vector. -/
def Instance.Valid {n J : ℕ} (I : Instance n J) : Prop :=
  1 ≤ I.k ∧ I.k ≤ I.T ∧ I.T ≤ n ∧ (∀ j, 0 ≤ I.r j) ∧ (∀ i j, 0 ≤ I.q i j) ∧ ∀ i, ∑ j, I.q i j = 1

/-- p. 16: the constraints (1)–(3) and the bounds of LPptk. -/
def LPFeasible {n J : ℕ} (I : Instance n J) (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) : Prop :=
  (∀ i j, x i j ≤ y i * I.q i j) ∧ (∑ i, y i ≤ (I.T : ℝ)) ∧ (∑ i, ∑ j, x i j ≤ (I.k : ℝ)) ∧
    (∀ i j, 0 ≤ x i j) ∧ ∀ i, 0 ≤ y i ∧ y i ≤ 1

/-- p. 16: the objective of LPptk. -/
def LPobj {n J : ℕ} (I : Instance n J) (x : Fin n → Fin J → ℝ) (_y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, I.r j * x i j

/-- An optimal solution of LPptk; its objective value is `LPptk(I)`. -/
def IsLPOpt {n J : ℕ} (I : Instance n J) (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) : Prop :=
  LPFeasible I x y ∧ ∀ x' y', LPFeasible I x' y' → LPobj I x' y' ≤ LPobj I x y

/-- The feasible polytope of LPptk in `(x, y)`-space; its extreme points are the basic feasible solutions. -/
def feasibleSet {n J : ℕ} (I : Instance n J) : Set ((Fin n → Fin J → ℝ) × (Fin n → ℝ)) :=
  {z | LPFeasible I z.1 z.2}

/-- (4), p. 17: `p_i = (Σ_j x_ij) / y_i`, with footnote 2's convention `0` when `y_i = 0`. -/
noncomputable def pbar {n J : ℕ} (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  if y i = 0 then 0 else (∑ j, x i j) / y i

/-- (4), p. 17: `v_i = (Σ_j r_j x_ij) / (Σ_j x_ij)`, with footnote 2's convention `0` when the
denominator is `0`. -/
noncomputable def vbar {n J : ℕ} (I : Instance n J) (x : Fin n → Fin J → ℝ) (i : Fin n) : ℝ :=
  if ∑ j, x i j = 0 then 0 else (∑ j, I.r j * x i j) / ∑ j, x i j

/-- p. 17: the probability `x_ij / (y_i q_ij)` with which ALGptk hires an interviewed applicant `i`
whose value is `r_j` (`0` when `y_i q_ij = 0`). -/
noncomputable def coin {n J : ℕ} (I : Instance n J) (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (i : Fin n) (j : Fin J) : ℝ :=
  if y i * I.q i j = 0 then 0 else x i j / (y i * I.q i j)

/-- The applicants with `y_i = 1`. -/
noncomputable def onesSet {n : ℕ} (y : Fin n → ℝ) : Finset (Fin n) :=
  univ.filter (fun i => y i = 1)

/-- The applicants with fractional `y_i`, `0 < y_i < 1`. -/
noncomputable def fracSet {n : ℕ} (y : Fin n → ℝ) : Finset (Fin n) :=
  univ.filter (fun i => 0 < y i ∧ y i < 1)

/-- §4.2, pp. 16–17: the law of the interview set `S = {i : Y_i = 1}` produced by the dependent rounding
DR. Every outcome contains all `i` with `y_i = 1` and only applicants with `y_i > 0`. With no fractional
entry `S = {i : y_i = 1}`; with one fractional entry `a`, `a ∈ S` with probability `y_a`; with two
fractional entries `a, b`, exactly one of them is in `S`, `a` with probability `y_a` and `b` with
probability `y_b`. ALGptk applies DR to a basic feasible solution, which has at most two fractional
entries (Lemma 2); for vectors with three or more fractional entries this formula is independent rounding
of the fractional entries, a case the paper never uses. -/
noncomputable def DR {n : ℕ} (y : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  if onesSet y ⊆ S ∧ S ⊆ onesSet y ∪ fracSet y then
    (if (fracSet y).card = 2 then
      (if (S \ onesSet y).card = 1 then ∑ i ∈ S \ onesSet y, y i else 0)
    else ∏ i ∈ fracSet y, (if i ∈ S then y i else 1 - y i))
  else 0

/-- The interview order: the `t`-th interview (if scheduled) is applicant `ord t`; `l` comes before `i`. -/
abbrev before {n : ℕ} (ord : Equiv.Perm (Fin n)) (l i : Fin n) : Prop :=
  ord.symm l < ord.symm i

/-- p. 17: the order interviews applicants in decreasing order of `v` (ties in any order). -/
def SortedBy {n : ℕ} (ord : Equiv.Perm (Fin n)) (v : Fin n → ℝ) : Prop :=
  ∀ l i, before ord l i → v i ≤ v l

/-- §4.3, p. 17: the expected reward `R_{ALG_ptk}(I)` of ALGptk run on the LP solution `(x, y)` with
interview order `ord`. The interview set `S` has law `DR y`; independently, the values `V i` are
independent with `P(V i = r j) = q i j`; independently given the values, each applicant `i` has a coin
`i ∈ C` that is heads with probability `coin i (V i)`, independently across applicants. Interviewed
applicants are processed in the order `ord`; applicant `i` is hired iff `i ∈ S`, its coin is heads, and
fewer than `k` applicants were hired before it (committed hiring: an earlier applicant in `S` with heads
was hired whenever a position remained, so the hires before `i` are `min(k, #{l ∈ S ∩ C before i})`).
A hired applicant contributes its realised value `r (V i)`. -/
noncomputable def algReward {n J : ℕ} (I : Instance n J) (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (ord : Equiv.Perm (Fin n)) : ℝ :=
  ∑ S : Finset (Fin n), DR y S * ∑ V : Fin n → Fin J, (∏ i, I.q i (V i)) *
    ∑ C : Finset (Fin n), (∏ i, if i ∈ C then coin I x y i (V i) else 1 - coin I x y i (V i)) *
      ∑ i, if i ∈ S ∧ i ∈ C ∧ (univ.filter fun l => l ∈ S ∧ l ∈ C ∧ before ord l i).card < I.k
        then I.r (V i) else 0

/-- p. 18: `Σ_i v_i E(1{N_{i−1} < k} Z_i)` where the interview set `S = {i : Y_i = 1}` has law `μ`,
independently the `P_i` are independent Bernoulli(`p_i`) (`P = {i : P_i = 1}`), `Z_i = Y_i P_i` and
`N_{i−1}` counts the `l` before `i` in the order with `Z_l = 1`. -/
noncomputable def cutValue {n J : ℕ} (I : Instance n J) (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (ord : Equiv.Perm (Fin n)) (μ : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), μ S * ∑ P : Finset (Fin n),
    (∏ i, if i ∈ P then pbar x y i else 1 - pbar x y i) *
      ∑ i, if i ∈ S ∧ i ∈ P ∧ (univ.filter fun l => l ∈ S ∧ l ∈ P ∧ before ord l i).card < I.k
        then vbar I x i else 0

end HiringLP.ProbeTopK


