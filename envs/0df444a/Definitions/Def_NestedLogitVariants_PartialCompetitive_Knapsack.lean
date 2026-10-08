-- Prove2me | Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack
-- name    : NestedLogitVariants_PartialCompetitive_Knapsack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:46:00.368433+00:00
-- url     : https://prove2.me/theorems/e10d8485-eb67-47bd-ae48-2a3c13495a49
-- title:
--   §5, pp. 22–24 — the knapsack value K_i (9), problem (10), the continuous knapsack (11), its greedy solution ẑ_i, Ŝ_i and the candidate collection
-- statement:
--   Fix a nest $i$ of the nested logit instance and a capacity $\epsilon_i \ge 0$. The **knapsack value** of display (9) is
--
--   $$K_i(\epsilon_i) = \max\Big\{ \sum_{j \in N} r_{ij} v_{ij} z_{ij} \;:\; \sum_{j\in N} v_{ij} z_{ij} \le \epsilon_i,\ z_i \in \{0,1\}^n \Big\},$$
--
--   the largest value $\sum_{j \in S} r_{ij} v_{ij}$ over assortments $S \subseteq N$ whose total preference weight fits into $\epsilon_i$. **Problem (10)** is
--
--   $$\min\ x \quad \text{s.t.}\quad v_0\, x \ge \sum_{i\in M} y_i, \qquad y_i \ge \max_{\epsilon_i \ge 0} \Big\{ (v_{i0} + \epsilon_i)^{\gamma_i} \Big[ \frac{K_i(\epsilon_i)}{v_{i0} + \epsilon_i} - x \Big] \Big\} \quad \forall i \in M;$$
--
--   a pair $(x, y)$ is feasible when $y_i$ bounds the bracket for every $\epsilon_i \ge 0$, and optimal when it is feasible with the least $x$. An optimal solution of (3) is defined the same way.
--
--   The **continuous knapsack problem (11)** relaxes (9):
--
--   $$\hat K_i(\epsilon_i) = \max\Big\{ \sum_{j \in N} r_{ij} v_{ij} z_{ij} \;:\; \sum_{j \in N} v_{ij} z_{ij} \le \epsilon_i,\ 0 \le z_{ij} \le \mathbf 1(v_{ij} \le \epsilon_i)\ \forall j \in N \Big\},$$
--
--   so a product heavier than $\epsilon_i$ cannot be taken even fractionally. Its **greedy solution** $\hat z_i(\epsilon_i)$ goes through the eligible products ($v_{ij} \le \epsilon_i$) in revenue order $r_{i1} \ge r_{i2} \ge \dots$, takes each one fully while it fits, takes the next one fractionally to fill the remaining capacity, and sets every other component to $0$. Explicitly, with $L_{ij}(\epsilon_i) = \sum_{k < j,\ v_{ik} \le \epsilon_i} v_{ik}$ the capacity used before product $j$,
--
--   $$\hat z_{ij}(\epsilon_i) = \begin{cases} \max\{0, \min\{1, (\epsilon_i - L_{ij}(\epsilon_i))/v_{ij}\}\} & v_{ij} \le \epsilon_i, \\ 0 & \text{otherwise.}\end{cases}$$
--
--   The assortment $\hat S_i(\epsilon_i) = \{ j \in N : \hat z_{ij}(\epsilon_i) = 1\}$ collects the products taken fully, and the **candidate collection** of nest $i$ is
--
--   $$\{\hat S_i(\epsilon_i) : \epsilon_i \in [0, \infty]\} \cup \{\{j\} : j \in N\}.$$
--
--   These objects carry the knapsack reformulation of §5: Lemma 9 replaces the exponentially many constraints of (3) by problem (10), and Theorem 10 shows that problem (4) over the candidate collection loses at most a factor of two.
--
--   **Formalization Note** A vector $z_i \in \{0,1\}^n$ is encoded by its support. $K_i(\epsilon)$ is defined only for $\epsilon \ge 0$, where the empty assortment is feasible and the maximum over the finite feasible family exists; the value $0$ returned for $\epsilon < 0$ is a placeholder that no statement uses, since (10) and every statement quantify over $\epsilon \ge 0$ only. The constraint of (10) is written in constraint form (no supremum is taken). Ties in revenue are broken by product index, as the products are indexed in revenue order. The value $\epsilon_i = \infty$ adds nothing to the candidate collection: for $\epsilon_i \ge \sum_j v_{ij}$ every product is eligible and fits, so $\hat S_i(\epsilon_i) = N$ already; the collection is therefore taken over real $\epsilon_i \ge 0$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 22–24, §5, displays (9), (10), (11), the definitions of ẑ_i(ϵ_i) and Ŝ_i(ϵ_i), and the candidate collection

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model

namespace NestedLogitVariants.PartialCompetitive

variable {ι : Type*} {n : ℕ}

/-- The feasible family of the knapsack problem (9) (p. 22) in nest `i` with capacity `ε`: a vector
`z_i ∈ {0, 1}^n` is encoded by its support `S`, and it is feasible when `∑_{j ∈ S} v_{ij} ≤ ε`. -/
noncomputable def knapFeasible (I : Instance ι n) (i : ι) (ε : ℝ) : Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter (fun S => ∑ j ∈ S, I.v i j ≤ ε)

/-- The knapsack value (9), p. 22:
`K_i(ε) = max { ∑_j r_{ij} v_{ij} z_{ij} : ∑_j v_{ij} z_{ij} ≤ ε, z_i ∈ {0, 1}^n }`.
For `ε ≥ 0` the empty set is feasible, so the maximum over the finite feasible family exists.
The value `0` for `ε < 0` is a junk value that no statement uses: problem (10) and every
statement of this mission quantify over `ε ≥ 0` only. -/
noncomputable def Kval (I : Instance ι n) (i : ι) (ε : ℝ) : ℝ :=
  if h : 0 ≤ ε then
    (knapFeasible I i ε).sup' ⟨∅, by simp [knapFeasible, h]⟩
      (fun S => ∑ j ∈ S, I.r i j * I.v i j)
  else 0

/-- `(x, y)` is feasible for problem (10), p. 22: `v_0 x ≥ ∑_i y_i` and, for every nest `i`,
`y_i ≥ max_{ε ≥ 0} (v_{i0} + ε)^{γ_i} [K_i(ε) / (v_{i0} + ε) − x]`, written in constraint form:
`y_i` bounds the bracket for every `ε ≥ 0`. -/
def LP10Feasible [Fintype ι] (I : Instance ι n) (x : ℝ) (y : ι → ℝ) : Prop :=
  (∑ i, y i) ≤ I.v0 * x ∧
    ∀ i, ∀ ε : ℝ, 0 ≤ ε → (I.vnp i + ε) ^ I.γ i * (Kval I i ε / (I.vnp i + ε) - x) ≤ y i

/-- `(x, y)` is an optimal solution of (10): feasible, and `x` is minimal among feasible points. -/
def LP10Optimal [Fintype ι] (I : Instance ι n) (x : ℝ) (y : ι → ℝ) : Prop :=
  LP10Feasible I x y ∧ ∀ x' y', LP10Feasible I x' y' → x ≤ x'

/-- `(x, y)` is an optimal solution of (3): feasible, and `x` is minimal among feasible points. -/
def LP3Optimal [Fintype ι] (I : Instance ι n) (x : ℝ) (y : ι → ℝ) : Prop :=
  LP3Feasible I x y ∧ ∀ x' y', LP3Feasible I x' y' → x ≤ x'

/-- `z` is feasible for the continuous knapsack problem (11), p. 23:
`∑_j v_{ij} z_j ≤ ε` and `0 ≤ z_j ≤ 1(v_{ij} ≤ ε)` for every product `j`; a product heavier than
`ε` is excluded even fractionally. -/
def feas11 (I : Instance ι n) (i : ι) (ε : ℝ) (z : Fin n → ℝ) : Prop :=
  (∑ j, I.v i j * z j ≤ ε) ∧ ∀ j, 0 ≤ z j ∧ z j ≤ (if I.v i j ≤ ε then 1 else 0)

/-- The capacity used by the eligible products (weight `≤ ε`) that precede product `j` in index
order, which is revenue order since `r_{i1} ≥ … ≥ r_{in}`. -/
noncomputable def prefixLoad (I : Instance ι n) (i : ι) (ε : ℝ) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => k < j ∧ I.v i k ≤ ε), I.v i k

/-- The greedy solution `ẑ_i(ε)` of (11), pp. 23–24: fill the knapsack of capacity `ε` with the
eligible products (`v_{ij} ≤ ε`) in revenue order (ties broken by index), taking each product
fully while it fits and the next one fractionally; ineligible products get `0`. -/
noncomputable def zhat (I : Instance ι n) (i : ι) (ε : ℝ) (j : Fin n) : ℝ :=
  if I.v i j ≤ ε then max 0 (min 1 ((ε - prefixLoad I i ε j) / I.v i j)) else 0

/-- `Ŝ_i(ε) = {j ∈ N : ẑ_{ij}(ε) = 1}`, p. 24. -/
noncomputable def Shat (I : Instance ι n) (i : ι) (ε : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => zhat I i ε j = 1)

/-- The candidate collection of nest `i`, p. 24:
`{Ŝ_i(ε) : ε ∈ [0, ∞]} ∪ {{j} : j ∈ N}`. The value `ε = ∞` adds nothing: for
`ε ≥ ∑_j v_{ij}` every product is eligible and fits, so `Ŝ_i(ε) = N` already. -/
def candidates (I : Instance ι n) (i : ι) : Set (Finset (Fin n)) :=
  {S | (∃ ε : ℝ, 0 ≤ ε ∧ S = Shat I i ε) ∨ ∃ j, S = {j}}

end NestedLogitVariants.PartialCompetitive


