-- Prove2me | Definitions.Def_ClassicalSchurBasic
-- name    : ClassicalSchurBasic
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-26T21:17:35.540303+00:00
-- url     : https://prove2.me/theorems/e1d4bc2b-38ad-4d2a-8070-47bf8eea97f6
-- title:
--   Sumfree sets, the Schur degree $\operatorname{sdeg}$, block sums $\hat A$ and the number $L(n)$ of Eliahou–Revuelta
-- statement:
--   This bundle fixes the objects of Eliahou and Revuelta's study of the Schur degree of block-sum sets. It was written for the formalization of $L(4) = 16$ cited in the source field, whose main theorems use all of its definitions. Other theorems can use only some of them, for example only the sumfree sets and covers of items 1 and 2.
--
--   Throughout, $\mathbb{N} = \{0, 1, 2, \dots\}$ and $\mathbb{N}^{+} = \{1, 2, 3, \dots\}$, and a *sequence* is a finite list $A = (a_1, \dots, a_N)$ of natural numbers, of length $|A| = N$.
--
--   1. A set $S \subseteq \mathbb{N}$ is **sumfree** (Lean `SumFree`) if $x + y \notin S$ for all $x, y \in S$. The case $x = y$ is included, so the condition is $(S + S) \cap S = \emptyset$.
--   2. A set $X \subseteq \mathbb{N}$ is **covered by $n$ sumfree sets** (Lean `CoveredBySumFree X n`) if there are sumfree sets $C_1, \dots, C_n \subseteq \mathbb{N}$ with $X \subseteq C_1 \cup \dots \cup C_n$. The sets $C_i$ need not be disjoint and need not lie in $X$.
--   3. The **Schur degree** $\operatorname{sdeg}(X)$ of $X \subseteq \mathbb{N}$ (Lean `sdeg`) is the least $n \ge 1$ such that $X$ is covered by $n$ sumfree sets, and $\infty$ if there is no such $n$.
--   4. A **block** of $A$ is a nonempty run $(a_i, a_{i+1}, \dots, a_j)$ of consecutive entries, $1 \le i \le j \le N$. The set of **block sums** of $A$ (Lean `blockSums A`) is $\hat A = \{\, a_i + a_{i+1} + \dots + a_j : 1 \le i \le j \le N \,\}$.
--   5. The **average** of $A$ (Lean `average A`) is the rational number $\mu(A) = (a_1 + \dots + a_N)/N$.
--   6. For $n, L \in \mathbb{N}$, the **property $P_n(L)$** (Lean `ERProperty n L`) states: every sequence $A$ of positive integers with $|A| = L$ and $\mu(A) \le n$ satisfies $\operatorname{sdeg}(\hat A) \ge n$.
--   7. The number **$L(n)$** (Lean `erL n`) is the least positive integer $L$ such that $P_n(L)$ holds.
--
--   In display form, the two central quantities are
--
--   $$
--   \operatorname{sdeg}(X) = \min\{\, n \ge 1 : X \subseteq C_1 \cup \dots \cup C_n \text{ for some sumfree } C_1, \dots, C_n \subseteq \mathbb{N} \,\} \in \mathbb{N} \cup \{\infty\},
--   $$
--
--   with $\min \emptyset = \infty$, and
--
--   $$
--   L(n) = \min\{\, L \ge 1 : \text{every } A \in (\mathbb{N}^{+})^{L} \text{ with } \mu(A) \le n \text{ has } \operatorname{sdeg}(\hat A) \ge n \,\}.
--   $$
--
--   Eliahou and Revuelta prove $S(n-1) + 1 \le L(n) \le R_{n-1}(3) - 1$ for $n \ge 2$ (Proposition 5.3), where $S(n)$ is the Schur number, the largest $N$ such that $\{1, \dots, N\}$ can be partitioned into $n$ sumfree sets, and $R_n(3)$ is the multicolour Ramsey number of triangles, and they conjecture $L(n) = S(n-1) + 1$ (Conjecture 5.6).
--
--   **Formalization Note** (1) The ambient set is $\mathbb{N}$, while the paper works in an abelian group $G$ (for $L(n)$, in the integers). For $X \subseteq \mathbb{N}$ the least number of sumfree sets that cover $X$ does not depend on this choice: a sumfree subset of $\mathbb{Z}$ meets $\mathbb{N}$ in a sumfree set, and a sumfree subset of $\mathbb{N}$ is sumfree in $\mathbb{Z}$. (2) $\operatorname{sdeg}$ takes values in the extended naturals `ℕ∞`, where $\infty$ is `⊤`; it is the infimum of the set of admissible $n \ge 1$, and the infimum of the empty set is `⊤`. (3) Sequences are lists of natural numbers, and blocks are nonempty contiguous sublists (`List.IsInfix`); positivity of the entries is a hypothesis of $P_n(L)$, not part of the definition of $\hat A$. (4) The average is computed in $\mathbb{Q}$, and the empty sequence has average $0$ by Lean's convention for division by zero; the paper does not define $\mu$ of the empty sequence, and $L(n)$ only uses lengths $L \ge 1$. (5) $L(n)$ is defined for every $n \in \mathbb{N}$ as an infimum in $\mathbb{N}$, where the empty infimum would be $0$. For every $n \ge 1$ the set is nonempty (by the form of Theorem 4.1 of the paper proved in the formalization of $L(4) = 16$ cited in the source field), so $L(n)$ is its least element, and for $n \ge 2$ it is the $L(n)$ of the paper, which the paper defines only for $n \ge 2$.
-- source:
--   S. Eliahou and M. P. Revuelta, "The Schur degree of additive sets", Discrete Math. 344(5) (2021) 112332, https://doi.org/10.1016/j.disc.2021.112332 (preprint arXiv:2006.01502), §1 and §2.3 (sumfree sets; (X + X) ∩ X = ∅), Definition 2.1 (cover by n sumfree subsets; the Schur degree sdeg), §2.1 and Notation 2.2 (blocks and the block-sum set Â), Definition 5.1 (the average μ(A) and the number L(n)). A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §2. Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Basic.lean#L29-L59 (release v1.0.1, doi:10.5281/zenodo.22987688).

-- Generated from lean/ClassicalSchur/Basic.lean by skeleton
-- subtraction: every declaration except the def-material below is deleted,
-- and project imports are rewritten to their platform Definitions bundles.
import Mathlib

namespace ClassicalSchur



/-- A set of naturals is sumfree when it has no `x, y, z` with `x + y = z`;
`x = y` is allowed (ER §2.3: `(S + S) ∩ S = ∅`). -/
def SumFree (S : Set ℕ) : Prop := ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S

/-- `X` is covered by `n` sumfree sets (ER Definition 2.1). -/
def CoveredBySumFree (X : Set ℕ) (n : ℕ) : Prop :=
  ∃ C : Fin n → Set ℕ, (∀ i, SumFree (C i)) ∧ X ⊆ ⋃ i, C i

/-- The Schur degree (ER Definition 2.1): the least `n ≥ 1` such that `X` is
covered by `n` sumfree sets, and `⊤` when there is no such `n`. -/
noncomputable def sdeg (X : Set ℕ) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) '' {n | 1 ≤ n ∧ CoveredBySumFree X n})

/-- The block sums `Â` of a sequence `A` (ER Notation 2.2): the sums of the
nonempty runs of consecutive entries of `A`. -/
def blockSums (A : List ℕ) : Set ℕ :=
  {s | ∃ B : List ℕ, B <:+: A ∧ B ≠ [] ∧ B.sum = s}

/-- The average `μ(A)` of a sequence. -/
def average (A : List ℕ) : ℚ := (A.sum : ℚ) / A.length

/-- The property of ER Definition 5.1 at length `L`: every sequence of
positive integers of length `L` and average at most `n` has
`sdeg(Â) ≥ n`. -/
def ERProperty (n L : ℕ) : Prop :=
  ∀ A : List ℕ, A.length = L → (∀ a ∈ A, 0 < a) → average A ≤ n →
    (n : ℕ∞) ≤ sdeg (blockSums A)

/-- `L(n)` of ER Definition 5.1: the least positive integer `L` with
`ERProperty n L`. -/
noncomputable def erL (n : ℕ) : ℕ := sInf {L | 0 < L ∧ ERProperty n L}

end ClassicalSchur


