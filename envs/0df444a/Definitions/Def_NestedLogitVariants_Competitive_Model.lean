-- Prove2me | Definitions.Def_NestedLogitVariants_Competitive_Model
-- name    : NestedLogitVariants_Competitive_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:02:45.042734+00:00
-- url     : https://prove2.me/theorems/461f8328-d680-4718-9183-b520f8b65f63
-- title:
--   §1–§2, pp. 6–12 — the nested logit instance, V_i, R_i, V_i^γ_i, Π, problem (2), N_ij and the linear programs (3), (4)
-- statement:
--   There are $m$ nests $M$ and $n$ products $N = \{1, \dots, n\}$ in each nest. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}$; nest $i$ has a no-purchase weight $v_{i0}$ and a dissimilarity parameter $\gamma_i$, and $v_0$ is the weight of choosing no nest at all. For an assortment $S_i \subseteq N$ offered in nest $i$,
--
--   $$V_i(S_i) = v_{i0} + \sum_{j \in S_i} v_{ij}, \qquad R_i(S_i) = \frac{\sum_{j \in S_i} r_{ij} v_{ij}}{V_i(S_i)},$$
--
--   with $R_i(\emptyset) = 0$. A customer picks nest $i$ with probability $Q_i(S_1, \dots, S_m) = V_i(S_i)^{\gamma_i} / (v_0 + \sum_{l \in M} V_l(S_l)^{\gamma_l})$ (display (1)), and the expected revenue of $(S_1, \dots, S_m)$ is
--
--   $$\Pi(S_1, \dots, S_m) = \sum_{i \in M} Q_i(S_1, \dots, S_m)\, R_i(S_i) = \frac{\sum_{i\in M} V_i(S_i)^{\gamma_i} R_i(S_i)}{v_0 + \sum_{i \in M} V_i(S_i)^{\gamma_i}}.$$
--
--   An assortment is optimal for problem (2), $Z^* = \max \Pi(S_1, \dots, S_m)$, when no other assortment earns more. The nested-by-revenue assortment $N_{ij} = \{1, \dots, j\}$ collects the $j$ highest-revenue products.
--
--   A pair $(x, y)$ with $y = (y_1, \dots, y_m)$ is feasible for the linear program (3) when
--   $$v_0\, x \ge \sum_{i \in M} y_i, \qquad y_i \ge V_i(S_i)^{\gamma_i}\,(R_i(S_i) - x) \quad \forall S_i \subseteq N,\ i \in M,$$
--   and feasible for (4), given candidate collections $\{A_{it} : t \in \mathcal T_i\}$ of assortments for each nest, when the second family of constraints is imposed only for $S_i$ in the collection of nest $i$. An optimal solution of (4) is a feasible pair whose $x$ is no larger than that of any feasible pair.
--
--   These are the objects of every statement of this mission: (3) is the linear-programming form of the assortment problem (2), and (4) is its restriction to candidate assortments.
--
--   **Formalization Note** Products are indexed $0, \dots, n-1$ (`Fin n`), so $N_{ij}$ is `nbr n j` $= \{k : k < j\}$. Powers are real powers (`Real.rpow`), and $x/0 = 0$ in Lean, which gives $R_i(\emptyset) = 0$ and $\Pi = 0$ when the denominator vanishes. A candidate collection is a set of finite sets of products. The standing assumptions are those of §1: $v_0 \ge 0$, $v_{i0} \ge 0$, revenues ordered $r_{i1} \ge \dots \ge r_{in}$, together with the disclosed pins $v_{ij} > 0$ (the page allows zero-weight padding products, under which Proposition 2 of the paper fails), $r_{ij} \ge 0$ (revenues are prices) and $\gamma_i > 0$ (the page has $\gamma_i \ge 0$; its convention $V_i(\emptyset)^{\gamma_i} = 0$ when $v_{i0} = 0$ fails at $\gamma_i = 0$).
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 6–12, §1 and §2, displays (1)–(4); N_ij from §3, pp. 13–14

import Mathlib

namespace NestedLogitVariants.Competitive

/-- An instance of the assortment problem of §1 (pp. 6–8): nests `ι` (the paper's `M`), products
`Fin n` (the paper's `N = {1, …, n}`, here `0, …, n-1`), the no-nest weight `v0` (`v_0`), the
within-nest no-purchase weights `vnp i` (`v_{i0}`), the preference weights `v i j` (`v_{ij}`), the
revenues `r i j` (`r_{ij}`) and the dissimilarity parameters `γ i` (`γ_i`). -/
structure Instance (ι : Type*) (n : ℕ) where
  v0 : ℝ
  vnp : ι → ℝ
  v : ι → Fin n → ℝ
  r : ι → Fin n → ℝ
  γ : ι → ℝ

/-- The standing assumptions of §1 (pp. 6–7): nonnegative no-purchase weights `v_0, v_{i0} ≥ 0`,
revenues ordered `r_{i1} ≥ … ≥ r_{in}` within each nest, together with the disclosed pins
`v_{ij} > 0`, `r_{ij} ≥ 0` and `γ_i > 0` (the page has `γ_i ≥ 0`). -/
structure Instance.Standing {ι : Type*} {n : ℕ} (I : Instance ι n) : Prop where
  v0_nonneg : 0 ≤ I.v0
  vnp_nonneg : ∀ i, 0 ≤ I.vnp i
  v_pos : ∀ i j, 0 < I.v i j
  r_nonneg : ∀ i j, 0 ≤ I.r i j
  γ_pos : ∀ i, 0 < I.γ i
  r_antitone : ∀ i, Antitone (I.r i)

variable {ι : Type*} {n : ℕ}

/-- `V_i(S) = v_{i0} + ∑_{j ∈ S} v_{ij}`, the total preference weight in nest `i` when `S` is
offered there. -/
def V (I : Instance ι n) (i : ι) (S : Finset (Fin n)) : ℝ := I.vnp i + ∑ j ∈ S, I.v i j

/-- `R_i(S) = ∑_{j ∈ S} r_{ij} v_{ij} / V_i(S)`, the expected revenue from nest `i` given that the
customer chose it; `R_i(∅) = 0` because the numerator is `0` (and `x / 0 = 0`). -/
noncomputable def R (I : Instance ι n) (i : ι) (S : Finset (Fin n)) : ℝ :=
  (∑ j ∈ S, I.r i j * I.v i j) / V I i S

/-- `V_i(S)^{γ_i}` (`Real.rpow`), the attractiveness of nest `i`. -/
noncomputable def nestWeight (I : Instance ι n) (i : ι) (S : Finset (Fin n)) : ℝ := V I i S ^ I.γ i

/-- `Π(S_1, …, S_m) = ∑_i Q_i(S_1, …, S_m) R_i(S_i)` with `Q_i` from (1):
`Q_i = V_i(S_i)^{γ_i} / (v_0 + ∑_l V_l(S_l)^{γ_l})`. -/
noncomputable def revenue [Fintype ι] (I : Instance ι n) (S : ι → Finset (Fin n)) : ℝ :=
  (∑ i, nestWeight I i (S i) * R I i (S i)) / (I.v0 + ∑ i, nestWeight I i (S i))

/-- `S` is an optimal solution of problem (2): `Π(S) ≥ Π(S')` for every assortment `S'`. -/
def IsOptimal [Fintype ι] (I : Instance ι n) (S : ι → Finset (Fin n)) : Prop :=
  ∀ S' : ι → Finset (Fin n), revenue I S' ≤ revenue I S

/-- The nested-by-revenue assortment `N_ij = {1, …, j}` (`N_i0 = ∅`), here `{k | k < j}`; it does not
depend on the nest. -/
def nbr (n j : ℕ) : Finset (Fin n) := Finset.univ.filter (fun k => k.val < j)

/-- `(x, y)` is feasible for the linear program (3):
`v_0 x ≥ ∑_i y_i` and `y_i ≥ V_i(S)^{γ_i} (R_i(S) − x)` for every `S ⊂ N` and every nest `i`. -/
def LP3Feasible [Fintype ι] (I : Instance ι n) (x : ℝ) (y : ι → ℝ) : Prop :=
  (∑ i, y i) ≤ I.v0 * x ∧ ∀ i (S : Finset (Fin n)), nestWeight I i S * (R I i S - x) ≤ y i

/-- `(x, y)` is feasible for the linear program (4) with candidate collections `A i`
(the paper's `{A_it : t ∈ T_i}`): the second constraint of (3) only for `S ∈ A i`. -/
def LP4Feasible [Fintype ι] (I : Instance ι n) (A : ι → Set (Finset (Fin n))) (x : ℝ) (y : ι → ℝ) :
    Prop :=
  (∑ i, y i) ≤ I.v0 * x ∧ ∀ i, ∀ S ∈ A i, nestWeight I i S * (R I i S - x) ≤ y i

/-- `(x, y)` is an optimal solution of (4): feasible, and `x` is minimal among feasible points. -/
def LP4Optimal [Fintype ι] (I : Instance ι n) (A : ι → Set (Finset (Fin n))) (x : ℝ) (y : ι → ℝ) :
    Prop :=
  LP4Feasible I A x y ∧ ∀ x' y', LP4Feasible I A x' y' → x ≤ x'

end NestedLogitVariants.Competitive


