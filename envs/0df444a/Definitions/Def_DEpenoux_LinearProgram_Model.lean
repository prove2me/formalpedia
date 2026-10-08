-- Prove2me | Definitions.Def_DEpenoux_LinearProgram_Model
-- name    : DEpenoux_LinearProgram_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:00:26.873146+00:00
-- url     : https://prove2.me/theorems/af19c246-b33f-4dd6-901d-440673433415
-- title:
--   d'Epenoux's production–inventory model: admissible potentials, strategies, $P_J$, $U_{ij}$ of (9), the sets $A$ and $B$, and the program $(P_2)$
-- statement:
--   This file sets up the discounted production and inventory model of d'Epenoux (1963), Sections 1, 2 and 5.
--
--   **States and decisions.** The stock at the beginning of a period is $i \in \{0, 1, \dots, \sigma\}$, where $\sigma$ is the stock capacity. The decision is the *potential* $j = h + i$ (output plus initial stock), which is admissible when $i \le j \le \sigma$. Write $U(i) = \{ j : i \le j \le \sigma\}$; it always contains $j = i$.
--
--   **Data.** For each potential $j$, $p_{js}$ is the probability that the stock at the end of the period is $s$; every row $(p_{js})_s$ is a probability vector. The expected one-period cost of stock $i$ and potential $j$ is a real number $d_{ij}$, with no sign or structure assumed. The discount factor is $\lambda$, $0 < \lambda < 1$ (stated as a hypothesis wherever it is used).
--
--   **The decision model.** These data form an instance of the finite discounted model `BertsekasSSPModel` (states $0,\dots,\sigma$, controls $j$, admissible sets $U(i)$, transition probabilities $p_{js}$ independent of $i$, stage costs $d_{ij}$). Its Bellman operator is
--   $$ (Tu)_i = \min_{j \ge i} \Big( d_{ij} + \lambda \sum_{s=0}^{\sigma} p_{js} u_s \Big), $$
--   so the paper's fundamental equation (7), $u^* = \min_J (d_J + \lambda P_J u^*)$, reads $T u^* = u^*$.
--
--   **Strategies.** A strategy is a map $J : \{0,\dots,\sigma\} \to \{0,\dots,\sigma\}$ with $i \le J(i)$ for every $i$. Its transition matrix is $(P_J)_{is} = p_{J(i)s}$.
--
--   **The constraint set and the program.** For a vector $u = (u_0,\dots,u_\sigma)$ put
--   $$ U_{ij} = u_i - \lambda \sum_{s} p_{js} u_s - d_{ij}. $$
--   The set $A$ consists of the $u$ with $U_{ij} \le 0$ for every $i$ and every admissible $j \ge i$ (conditions (A), equivalently the constraints (9)); the set $B$ consists of the $u$ with $\prod_{j \ge i} U_{ij} = 0$ for every $i$ (condition (B)). For weights $c_i$, a vector $u$ is an optimal solution of $(P_2)$ when $u \in A$ and
--   $$ (1-\lambda) \sum_i c_i v_i \le (1-\lambda) \sum_i c_i u_i \quad \text{for every } v \in A. $$
--
--   These are the objects of Section 5, where the dynamic program (7) is turned into the linear program $(P_2)$.
--
--   **Formalization Note** Stock levels and potentials are `Fin (σ + 1)`, $0$-based as in the paper. The discount is called `lam` because `λ` is a Lean keyword. The paper's demand-driven kernel ($p_{j0} = \sum_{n \ge j} p_n$, $p_{js} = p_{j-s}$ for $0 < s \le j$, $p_{js} = 0$ for $s > j$) and the cost decomposition $d_{ij} = d'(j-i) + \sum_n p_n d''(i,j,n)$ are not built in: the kernel is an arbitrary stochastic kernel indexed by the potential and the costs are arbitrary reals, since the arguments of Sections 2–5 use only that each $P_J$ is stochastic (the paper notes on p. 101 that its methods apply well beyond the inventory problem). Only admissible pairs $i \le j$ enter $A$, $B$, the minimum in (7) and strategies; the values $d_{ij}$ for $j < i$ are never used.
-- source:
--   d'Epenoux, A Probabilistic Production and Inventory Problem, Management Sci. 10 (1963), pp. 98–99 (Section 1, Notation and Terminology), pp. 100–101 (Section 2, P_J, d_J), p. 102 (Eq. (7)), p. 104 (Section 5, U_ij, (A), (B)), p. 105 (Eq. (9), (P2))

import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace DEpenoux.LinearProgram

open Finset

/-- d'Epenoux 1963, §1, pp. 98–99: the admissible potentials at initial stock `i`, namely the
potentials `j` with `i ≤ j ≤ σ` (stock levels and potentials are `0, 1, …, σ`). -/
def admissible (σ : ℕ) (i : Fin (σ + 1)) : Finset (Fin (σ + 1)) :=
  univ.filter (fun j => i ≤ j)

/-- d'Epenoux 1963, §1, p. 99: the production–inventory model as a finite discounted decision
model, an instance of the published `BertsekasSSPModel`. States are the stock levels
`i = 0, …, σ`, controls are the potentials `j`, admissible when `i ≤ j`; the transition
probability from stock `i` under potential `j` to end stock `s` is `p j s` (it depends on the
potential only); the one-period expected cost is `d i j`. The hypotheses say that every row
`p j ·` is a probability vector. -/
def model (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1) :
    BertsekasSSPModel (σ + 1) (Fin (σ + 1)) where
  U i := admissible σ i
  hU i := ⟨i, by simp [admissible]⟩
  p _ j s := p j s
  g i j := d i j
  hp_nonneg _ j s := hp0 j s
  hp_sum _ j _ := le_of_eq (hp1 j)

/-- d'Epenoux 1963, §1, p. 99: a strategy `J` fixes the potential `J i` from the initial stock
`i` only, and must be admissible: `i ≤ J i`. -/
def IsStrategy {σ : ℕ} (J : Fin (σ + 1) → Fin (σ + 1)) : Prop :=
  ∀ i, i ≤ J i

/-- d'Epenoux 1963, §2, pp. 100–101: the transition matrix `P_J` of a strategy `J`,
`(P_J)_{is} = p_{J(i) s}`. -/
def stratMatrix {σ : ℕ} (p : Fin (σ + 1) → Fin (σ + 1) → ℝ) (J : Fin (σ + 1) → Fin (σ + 1)) :
    Matrix (Fin (σ + 1)) (Fin (σ + 1)) ℝ :=
  fun i s => p (J i) s

/-- d'Epenoux 1963, §5, p. 104, and (9), p. 105:
`U_ij = u_i − λ ∑_s p_js u_s − d_ij`. -/
def Uij {σ : ℕ} (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ) (lam : ℝ) (u : Fin (σ + 1) → ℝ)
    (i j : Fin (σ + 1)) : ℝ :=
  u i - lam * ∑ s, p j s * u s - d i j

/-- d'Epenoux 1963, §5, p. 104, condition (A), i.e. the constraints (9) of p. 105:
`U_ij ≤ 0` for every stock level `i` and every admissible potential `j ≥ i`. -/
def setA {σ : ℕ} (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ) (lam : ℝ) : Set (Fin (σ + 1) → ℝ) :=
  {u | ∀ i j, i ≤ j → Uij p d lam u i j ≤ 0}

/-- d'Epenoux 1963, §5, p. 104, condition (B): `∏_j U_ij = 0` for every `i`, the product over
the admissible potentials `j ≥ i`. -/
def setB {σ : ℕ} (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ) (lam : ℝ) : Set (Fin (σ + 1) → ℝ) :=
  {u | ∀ i, ∏ j ∈ admissible σ i, Uij p d lam u i j = 0}

/-- d'Epenoux 1963, §5, p. 105, program (P₂): `u` is an optimal solution of
"maximize `(1 − λ) ∑_i c_i u_i` under the constraints (9)". -/
def IsP2Optimal {σ : ℕ} (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ) (lam : ℝ)
    (c : Fin (σ + 1) → ℝ) (u : Fin (σ + 1) → ℝ) : Prop :=
  u ∈ setA p d lam ∧
    ∀ v ∈ setA p d lam, (1 - lam) * ∑ i, c i * v i ≤ (1 - lam) * ∑ i, c i * u i

end DEpenoux.LinearProgram


