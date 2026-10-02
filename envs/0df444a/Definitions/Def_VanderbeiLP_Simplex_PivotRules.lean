-- Prove2me | Definitions.Def_VanderbeiLP_Simplex_PivotRules
-- name    : VanderbeiLP_Simplex_PivotRules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T16:45:11.363538+00:00
-- url     : https://prove2.me/theorems/3315db9b-9581-41ce-a2bd-5ce53aa5e0bc
-- title:
--   Simplex pivots, Bland's rule and the lexicographic rule
-- statement:
--   Let $D$ be a dictionary with basic set $\mathcal B$, nonbasic set $\mathcal N$ and coefficients $\bar b, \bar a, \bar c$.
--
--   1. An **entering candidate** is an index $k \in \mathcal N$ with $\bar c_k > 0$. If there is none, the dictionary is optimal.
--   2. For an entering variable $x_k$, a **leaving candidate** is an index $l \in \mathcal B$ with $\bar a_{lk} > 0$ whose ratio $\bar b_l/\bar a_{lk}$ is minimal among all $i \in \mathcal B$ with $\bar a_{ik} > 0$. If no $\bar a_{ik}$ is positive, the problem is unbounded.
--   3. A **simplex pivot** from $D$ to $D'$ picks an entering candidate $x_k$ and a leaving candidate $x_l$ for it; the basic set of $D'$ is $(\mathcal B \setminus \{l\}) \cup \{k\}$.
--   4. **Bland's rule** chooses both the entering and the leaving variable from their respective sets of candidates as the variable with the smallest index. A dictionary is **terminal** for this rule when there is no entering candidate, or the entering variable $x_k$ chosen by Bland's rule has $\bar a_{ik} \le 0$ for all $i \in \mathcal B$.
--   5. The **lexicographic rule** for a run started at the dictionary $D_0$ adds symbolic parameters $0 < \epsilon_m \ll \dots \ll \epsilon_1 \ll$ all data to the right-hand sides of $D_0$, one to each row. In a later dictionary $D$ the right-hand side of the row of $x_i$ becomes $\bar b_i + r_{i1}\epsilon_1 + \dots + r_{im}\epsilon_m$, and for the entering variable $x_k$ the rule chooses the leaving variable $x_l$, $\bar a_{lk} > 0$, whose perturbed ratio
--   $$
--   \frac{\bar b_l + r_{l1}\epsilon_1 + \dots + r_{lm}\epsilon_m}{\bar a_{lk}}
--   $$
--   is minimal among the rows with $\bar a_{ik} > 0$. Because of the separation of scales, this comparison is the lexicographic comparison of the vectors $(\bar b_i, r_{i1}, \dots, r_{im})/\bar a_{ik}$. The entering variable is any entering candidate.
--
--   These are the pivoting rules whose termination is the subject of the mission.
--
--   **Formalization Note** The indices $1,\dots,n+m$ are ordered as `Fin (n + m)`: decision variables $x_1,\dots,x_n$ before slacks $w_1,\dots,w_m$, which is the order Bland's rule compares. For the lexicographic rule, $\epsilon_{p}$ is attached in $D_0$ to the row of its $p$-th basic variable in increasing index order (for the initial dictionary, $\epsilon_i$ is added to the $i$-th constraint, as on p. 29). The coefficient $r_{ip}$ in the dictionary $D$ equals $\bar a_{i,\beta_p}$, where $\beta_p$ is that $p$-th basic variable of $D_0$; the vectors are compared with Mathlib's lexicographic order `toLex` on `Fin (m + 1) → ℝ`.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 15 (PDF 33), entering and leaving variable; pp. 18–19 (PDF 36–37), unboundedness; pp. 28–30 (PDF 45–47), §3.3 perturbation/lexicographic method; p. 31 (PDF 48), §3.4 Bland's rule

import Mathlib
import Definitions.Def_VanderbeiLP_Simplex_Dictionary

namespace VanderbeiLP.Simplex

variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}

namespace Dictionary

/-- `x_k` is an **entering-variable candidate** of the dictionary `D` (Vanderbei, p. 15):
`k ∈ N` and `c̄_k > 0`. -/
def IsEnteringCandidate (D : Dictionary A) (c : Fin n → ℝ) (k : Fin (n + m)) : Prop :=
  k ∉ D.B ∧ 0 < D.cbar c k

/-- `x_l` is a **leaving-variable candidate** for the entering variable `x_k` (p. 15): `l ∈ B`,
`ā_{lk} > 0`, and the ratio `b̄_l / ā_{lk}` is minimal among all `i ∈ B` with `ā_{ik} > 0`. -/
def IsLeavingCandidate (D : Dictionary A) (b : Fin m → ℝ) (k l : Fin (n + m)) : Prop :=
  l ∈ D.B ∧ 0 < D.abar l k ∧
    ∀ i ∈ D.B, 0 < D.abar i k → D.bbar b l / D.abar l k ≤ D.bbar b i / D.abar i k

/-- One **pivot of the simplex method** (p. 15) takes `D` to `D'`: some entering candidate
`x_k` becomes basic and some leaving candidate `x_l` for it becomes nonbasic. -/
def IsSimplexPivot (b : Fin m → ℝ) (c : Fin n → ℝ) (D D' : Dictionary A) : Prop :=
  ∃ k l, D.IsEnteringCandidate c k ∧ D.IsLeavingCandidate b k l ∧
    D'.B = insert k (D.B.erase l)

/-- **Bland's rule** for the entering variable (p. 31): `x_k` is the entering candidate with
the smallest index `k`. -/
def IsBlandEntering (D : Dictionary A) (c : Fin n → ℝ) (k : Fin (n + m)) : Prop :=
  D.IsEnteringCandidate c k ∧ ∀ j, D.IsEnteringCandidate c j → k ≤ j

/-- **Bland's rule** for the leaving variable (p. 31): `x_l` is the leaving candidate for
`x_k` with the smallest index `l`. -/
def IsBlandLeaving (D : Dictionary A) (b : Fin m → ℝ) (k l : Fin (n + m)) : Prop :=
  D.IsLeavingCandidate b k l ∧ ∀ i, D.IsLeavingCandidate b k i → l ≤ i

/-- A pivot from `D` to `D'` in which both the entering and the leaving variable are chosen by
Bland's rule. -/
def IsBlandPivot (b : Fin m → ℝ) (c : Fin n → ℝ) (D D' : Dictionary A) : Prop :=
  ∃ k l, D.IsBlandEntering c k ∧ D.IsBlandLeaving b k l ∧ D'.B = insert k (D.B.erase l)

/-- The two ways the simplex method under Bland's rule stops at `D` (pp. 15, 18–19): no
variable has `c̄_j > 0` (the dictionary is optimal), or the entering variable chosen by Bland's
rule has `ā_{ik} ≤ 0` for every `i ∈ B` (the problem is unbounded). -/
def IsBlandTerminal (D : Dictionary A) (c : Fin n → ℝ) : Prop :=
  (∀ j, ¬ D.IsEnteringCandidate c j) ∨
    ∃ k, D.IsBlandEntering c k ∧ ∀ i ∈ D.B, D.abar i k ≤ 0

/-- The variable whose row receives the symbolic perturbation `ε_{p+1}` in the first
dictionary `D₀` of a run of the lexicographic method (p. 29): the basic variables of `D₀`
listed in increasing order of index. When `D₀` is the initial dictionary, `ε_{p+1}` is added
to the `(p+1)`-st constraint. -/
noncomputable def epsVar (D₀ : Dictionary A) (p : Fin m) : Fin (n + m) :=
  D₀.B.orderEmbOfFin D₀.card_B p

/-- The perturbed right-hand side of the row of `x_i` in the dictionary `D` of the
lexicographic method started at `D₀` (p. 30), as the coefficient vector
`(b̄_i, r_{i1}, …, r_{im})` of `b̄_i + r_{i1} ε_1 + ⋯ + r_{im} ε_m`. -/
noncomputable def lexRow (D₀ D : Dictionary A) (b : Fin m → ℝ) (i : Fin (n + m)) :
    Fin (m + 1) → ℝ :=
  Fin.cons (D.bbar b i) (fun p => D.abar i (D₀.epsVar p))

/-- The **lexicographic rule** for the leaving variable (pp. 29–30), for the entering variable
`x_k`: `l ∈ B`, `ā_{lk} > 0`, and the perturbed ratio `(b̄_l + ∑_p r_{lp} ε_p)/ā_{lk}` is
minimal among all `i ∈ B` with `ā_{ik} > 0`, where the symbols satisfy
`0 < ε_m ≪ ⋯ ≪ ε_1 ≪` all data, i.e. the coefficient vectors are compared lexicographically. -/
def IsLexLeaving (D₀ D : Dictionary A) (b : Fin m → ℝ) (k l : Fin (n + m)) : Prop :=
  l ∈ D.B ∧ 0 < D.abar l k ∧
    ∀ i ∈ D.B, 0 < D.abar i k →
      toLex ((D.abar l k)⁻¹ • lexRow D₀ D b l) ≤ toLex ((D.abar i k)⁻¹ • lexRow D₀ D b i)

/-- A pivot from `D` to `D'` of the lexicographic method started at `D₀`: any entering
candidate `x_k`, and the leaving variable chosen by the lexicographic rule. -/
def IsLexPivot (D₀ : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ) (D D' : Dictionary A) :
    Prop :=
  ∃ k l, D.IsEnteringCandidate c k ∧ IsLexLeaving D₀ D b k l ∧ D'.B = insert k (D.B.erase l)

end Dictionary

end VanderbeiLP.Simplex


