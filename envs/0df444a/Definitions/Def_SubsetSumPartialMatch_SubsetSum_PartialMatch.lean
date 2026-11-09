-- Prove2me | Definitions.Def_SubsetSumPartialMatch_SubsetSum_PartialMatch
-- name    : SubsetSumPartialMatch_SubsetSum_PartialMatch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:24.440722+00:00
-- url     : https://prove2.me/theorems/5fb6dcda-16a1-4c2f-bfe3-e64c1174665d
-- title:
--   Half-stars partial match and admissible exponent pairs
-- statement:
--   Binary strings are the elements of $\{0,1\}^n$ and query strings the elements of $\{0,1,*\}^n$, where $*$ is a wildcard. For a query $y$, $S(y)=\{i:y_i\ne *\}$ is the set of specified positions. The **partial match matrix** is
--   $$P_1=\begin{pmatrix}1&0&1\\0&1&1\end{pmatrix},$$
--   with rows indexed by $0,1$ and columns by $0,1,*$, so that $(P_1^{\otimes n})_{x,y}=\prod_i (P_1)_{x_i,y_i}$ equals $1$ exactly when $x$ agrees with $y$ on $S(y)$; in that case $x$ **matches** $y$. For $s\in\mathbb R$, $P_{n,s}$ retains all rows of $P_1^{\otimes n}$ and the columns $y$ with $|S(y)|=\lfloor sn\rfloor$.
--
--   In **half-stars partial match** one is given an even integer $n$, a set $A\subseteq\{0,1\}^n$ and a set $B$ of queries with $|S(y)|=n/2$, and must decide whether some $x\in A$ matches some $y\in B$.
--
--   A pair $(l,r)$ with $l,r\ge 0$ is an **admissible exponent pair** if for every $\varepsilon>0$ there is one deterministic algorithm that solves half-stars partial match for all even $n$ and all $A,B$ in time
--   $$O\bigl(2^{(l+\varepsilon)n}|A|+2^{(r+\varepsilon)n}|B|\bigr).$$
--
--   **Formalization Note** The sets $A,B$ are presented to the machine as duplicate-free lists in arbitrary order, each string as one word per position, and the algorithm must work for every such presentation. The time bound is written $C(1+2^{(l+\varepsilon)n}|A|+2^{(r+\varepsilon)n}|B|)$ for $n\ge N$: the $1$ is the constant input/output overhead of a run, which the source's input-sensitive formula leaves implicit and which matters only when $A$ and $B$ are both empty. Correctness is required for every even $n$, including $n=0$, with no nonemptiness assumption on $A$ or $B$.
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, pp. 9–10, §2.1, matrix $P_1$ and Definition 2.1; p. 16, definition of $P_{n,s}$

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_RAM

namespace SubsetSumPartialMatch.SubsetSum

/-- Binary strings `{0,1}^n`. -/
abbrev BinStr (n : ℕ) := Fin n → Bool

/-- Query strings `{0,1,*}^n`; `none` is the wildcard `*`. -/
abbrev QueryStr (n : ℕ) := Fin n → Option Bool

/-- The specified positions `S(y) = {i : y_i ≠ *}`. -/
def specified {n : ℕ} (y : QueryStr n) : Finset (Fin n) :=
  Finset.univ.filter fun i => y i ≠ none

/-- The partial match matrix `P_1`, rows `0, 1`, columns `0, 1, *`. -/
def P1 : Matrix Bool (Option Bool) ℤ := fun x y =>
  match y with
  | none => 1
  | some b => if x = b then 1 else 0

/-- The entry `(P_1^{⊗n})_{x,y} = ∏_i (P_1)_{x_i,y_i}`. -/
def pmEntry {n : ℕ} (x : BinStr n) (y : QueryStr n) : ℤ := ∏ i, P1 (x i) (y i)

/-- `x` matches `y`: they agree on every specified position of `y`. -/
def Matches {n : ℕ} (x : BinStr n) (y : QueryStr n) : Prop :=
  ∀ i ∈ specified y, y i = some (x i)

/-- The columns of `P_{n,s}`: the queries with `|S(y)| = ⌊s n⌋`. -/
abbrev PMCol (n : ℕ) (s : ℝ) := {y : QueryStr n // (specified y).card = ⌊s * n⌋₊}

/-- `P_{n,s}`: all rows of `P_1^{⊗n}` and the columns with `|S(y)| = ⌊s n⌋`. -/
def pm (n : ℕ) (s : ℝ) : Matrix (BinStr n) (PMCol n s) ℤ := fun x y => pmEntry x y.1

/-- The machine words of a binary string: one word `0` or `1` per position. -/
def binWords {n : ℕ} (x : BinStr n) : List ℤ := List.ofFn fun i => if x i then 1 else 0

/-- The machine words of a query: one word per position, `0`, `1`, or `2` for `*`. -/
def queryWords {n : ℕ} (y : QueryStr n) : List ℤ :=
  List.ofFn fun i =>
    match y i with
    | some true => 1
    | some false => 0
    | none => 2

/-- The input of half-stars partial match: `n`, `|A|`, `|B|`, then the strings of `A` and `B`. -/
def pmWords {n : ℕ} (A : List (BinStr n)) (B : List (QueryStr n)) : List ℤ :=
  (n : ℤ) :: (A.length : ℤ) :: (B.length : ℤ) ::
    (A.flatMap binWords ++ B.flatMap queryWords)

open Classical in
/-- The output of a decision procedure: `[1]` for yes and `[0]` for no. -/
noncomputable def decisionWords (p : Prop) : List ℤ := [if p then 1 else 0]

/-- `(l, r)` is an admissible exponent pair (Definition 2.1): `l, r ≥ 0` and for every `ε > 0` one
deterministic program decides half-stars partial match on all even `n` and all sets `A`, `B`
(presented as duplicate-free lists, in any order), in time
`O(1 + 2^{(l+ε)n} |A| + 2^{(r+ε)n} |B|)`. -/
def AdmissiblePair (l r : ℝ) : Prop :=
  0 ≤ l ∧ 0 ≤ r ∧ ∀ ε : ℝ, 0 < ε → ∃ P : Program, Deterministic P ∧
    ∃ (C : ℝ) (N : ℕ), 0 < C ∧
      ∀ (n : ℕ), Even n → ∀ (A : List (BinStr n)) (B : List (QueryStr n)),
        A.Nodup → B.Nodup → (∀ y ∈ B, 2 * (specified y).card = n) →
        Outputs P blankTape (pmWords A B) (decisionWords (∃ x ∈ A, ∃ y ∈ B, Matches x y)) ∧
        (N ≤ n → CostWithin P blankTape (pmWords A B)
          (C * (1 + (2 : ℝ) ^ ((l + ε) * n) * A.length + (2 : ℝ) ^ ((r + ε) * n) * B.length)))

end SubsetSumPartialMatch.SubsetSum


