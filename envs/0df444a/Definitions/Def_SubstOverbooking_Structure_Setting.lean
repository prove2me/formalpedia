-- Prove2me | Definitions.Def_SubstOverbooking_Structure_Setting
-- name    : SubstOverbooking_Structure_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:08:56.883856+00:00
-- url     : https://prove2.me/theorems/0561db23-28ce-44a7-9f88-2a0d57255723
-- title:
--   §2–§2.2 and Definition 1, pp. 85–87 — TP value V₀(z, c), DTP, semigroup survival laws, G(u) of (2), decreasing differences
-- statement:
--   This file sets up the single-period overbooking model with substitutable inventory classes of Karaesmen and van Ryzin.
--
--   **Classes and data.** There are $n$ reservation classes $i$ and $m + 1$ inventory classes $j = 0, 1, \dots, m$, where class $0$ is a virtual class: assigning a customer to it means the customer is denied service. The data are revenues $r_i$, refunds $q_i$, reservations on hand $x_i$, net benefits $a_{ij}$ (of any sign) of serving a class-$i$ customer from inventory class $j$, and capacities $c_j$.
--
--   **Transportation problem (TP).** Given the numbers $z = (z_1, \dots, z_n)$ of surviving customers, an assignment $y = (y_{ij})$ is feasible if
--
--   $$y_{ij} \ge 0, \qquad \sum_{j=0}^m y_{ij} = z_i \ (i = 1, \dots, n), \qquad \sum_{i=1}^n y_{ij} \le c_j \ (j = 1, \dots, m),$$
--
--   and the service-period value is
--
--   $$V_0(z, c) = \sup\Big\{ \sum_{i=1}^n \sum_{j=0}^m a_{ij} y_{ij} \;:\; y \text{ feasible} \Big\}.$$
--
--   **Dual (DTP).** A pair $(\mu, \lambda) \in \mathbb R^n \times \mathbb R^{m+1}$ is dual feasible if $\lambda_j \ge 0$ for all $j$, $\lambda_0 = 0$, and $\mu_i + \lambda_j \ge a_{ij}$ for all $i, j$; its objective is $\sum_i z_i \mu_i + \sum_j c_j \lambda_j$.
--
--   **Decreasing differences (Definition 1).** A function $f$ on $S \subseteq \mathbb R^n$ has decreasing differences on $S$ if for every $s \in S$, all distinct coordinates $i \ne j$, and all $s'_i \ge s_i$, $s'_j \ge s_j$ (with the modified vectors in $S$),
--
--   $$f(s_{-ij}, s'_i, s'_j) - f(s_{-ij}, s'_i, s_j) \le f(s_{-ij}, s_i, s'_j) - f(s_{-ij}, s_i, s_j).$$
--
--   **Survivals.** For each class $i$, $u \mapsto L_i(u)$ is the law of the number $Z_i(u)$ of class-$i$ customers who survive to the service period when $u$ reservations are held. Levels range over a **parameter set** $P \subseteq [0, \infty)$ containing $0$ and closed under addition and under nonnegative differences ($P = \mathbb N$ for the binomial model, $P = [0, \infty)$ for the Poisson model). The family has the **semigroup property** on $P$ if, whenever $Y_1, Y_2$ are independent with laws $L_i(u), L_i(s)$, $u, s \in P$, the sum $Y_1 + Y_2$ has law $L_i(u + s)$; each law is also required to have a finite mean. The survival vector $Z(u) = (Z_1(u_1), \dots, Z_n(u_n))$ has independent coordinates.
--
--   **Expected net revenue (2).**
--
--   $$G(u) = \sum_{i=1}^n r_i (u_i - x_i) - \mathbb E\Big[\sum_{i=1}^n q_i\big(u_i - Z_i(u_i)\big)\Big] + \mathbb E\big[V_0(Z(u), c)\big].$$
--
--   These objects are the vocabulary of the structural results of §3: submodularity and concavity of $V_0$, and componentwise concavity and submodularity of $G$.
--
--   **Formalization Note.** Reservation classes are `Fin n` (0-based) and inventory classes `Fin (m + 1)` with `0` the virtual class. The page gives class 0 "finite but very high capacity"; here it is uncapacitated (constraint (4) only for $j \ne 0$, $c_0$ unused), which is what makes TP feasible for every $z \ge 0$, and correspondingly $\lambda_0 = 0$ in DTP. $V_0$ is a supremum of reals and is the junk value $0$ when the feasible set is empty (some $z_i < 0$); all statements assume $z \ge 0$. Survival laws are probability mass functions on $\mathbb N$ (survivals count customers); the semigroup property is stated as an identity of laws (law of the sum of independent copies = image of the product law under addition), and mutual independence as the product law `Measure.pi`. The finite-mean requirement keeps the Bochner integrals in $G$ meaningful. On ℕ-valued $z$, $V_0$ coincides with `RevenueManagement.serviceValue` of the platform definition `RevenueManagement_overbooking`.
-- source:
--   Karaesmen & van Ryzin, Overbooking with Substitutable Inventory Classes, Operations Research 52(1):83–104 (2004), pp. 85–87, §2 (1)–(2), §2.1, §2.2 (TP), (3)–(5), (DTP), Definition 1

import Mathlib

namespace SubstOverbooking.Structure

open MeasureTheory

/-- (TP), p. 86: a matrix `y` (customers of reservation class `i` assigned to inventory class `j`)
is feasible for the transportation problem with demands `z` and capacities `c` if it is
nonnegative, routes every survivor (constraint (3)), and respects the capacity of every real
inventory class `j ≠ 0` (constraint (4)). Inventory class `0` is the virtual denied-service class,
taken uncapacitated, so `c 0` is not used. -/
def IsTPFeasible {n m : ℕ} (c : Fin (m + 1) → ℝ) (z : Fin n → ℝ)
    (y : Fin n → Fin (m + 1) → ℝ) : Prop :=
  (∀ i j, 0 ≤ y i j) ∧ (∀ i, ∑ j, y i j = z i) ∧ (∀ j, j ≠ 0 → ∑ i, y i j ≤ c j)

/-- (TP), p. 86: the objective `∑ᵢ ∑ⱼ a_ij y_ij`. -/
def tpObjective {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) (y : Fin n → Fin (m + 1) → ℝ) : ℝ :=
  ∑ i, ∑ j, a i j * y i j

/-- (TP), p. 86: the service-period value `V₀(z, c)`, the supremum of the TP objective over the
TP-feasible assignments. (For `z` with a negative coordinate the feasible set is empty and the
value is the junk `0`; every statement about `V0` assumes `z ≥ 0`.) -/
noncomputable def V0 {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) (c : Fin (m + 1) → ℝ)
    (z : Fin n → ℝ) : ℝ :=
  sSup (tpObjective a '' {y | IsTPFeasible c z y})

/-- (DTP), p. 86: `(μ, λ)` is feasible for the dual transportation problem if `λ ≥ 0` and
`μ_i + λ_j ≥ a_ij` for all `i, j` (constraint (5)). Because inventory class `0` is uncapacitated
in this formalization, its dual variable is fixed to `λ_0 = 0`. -/
def IsDTPFeasible {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) (μ : Fin n → ℝ)
    (lam : Fin (m + 1) → ℝ) : Prop :=
  lam 0 = 0 ∧ (∀ j, 0 ≤ lam j) ∧ ∀ i j, a i j ≤ μ i + lam j

/-- (DTP), p. 86: the dual objective `∑ᵢ z_i μ_i + ∑ⱼ c_j λ_j`. -/
def dtpObjective {n m : ℕ} (c : Fin (m + 1) → ℝ) (z : Fin n → ℝ) (μ : Fin n → ℝ)
    (lam : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i, z i * μ i + ∑ j, c j * lam j

/-- Definition 1, p. 87 (decreasing differences). `f` has decreasing differences on `S` if for
every `s ∈ S`, all distinct coordinates `i ≠ j` and all `s'_i ≥ s_i`, `s'_j ≥ s_j` for which the
modified vectors lie in `S`,
`f(s_{-ij}, s'_i, s'_j) − f(s_{-ij}, s'_i, s_j) ≤ f(s_{-ij}, s_i, s'_j) − f(s_{-ij}, s_i, s_j)`. -/
def DecreasingDifferencesOn {n : ℕ} (f : (Fin n → ℝ) → ℝ) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ s ∈ S, ∀ i j : Fin n, i ≠ j → ∀ si sj : ℝ, s i ≤ si → s j ≤ sj →
    Function.update s i si ∈ S → Function.update s j sj ∈ S →
    Function.update (Function.update s i si) j sj ∈ S →
    f (Function.update (Function.update s i si) j sj) - f (Function.update s i si) ≤
      f (Function.update s j sj) - f s

/-- The set of admissible overbooking levels of one class: it contains `0`, is closed under
addition and under nonnegative differences, and consists of nonnegative reals. Both
`Set.range (Nat.cast : ℕ → ℝ)` (binomial model) and `Set.Ici 0` (Poisson model) qualify. -/
def IsParamSet (P : Set ℝ) : Prop :=
  0 ∈ P ∧ (∀ u ∈ P, ∀ s ∈ P, u + s ∈ P) ∧ (∀ u ∈ P, ∀ s ∈ P, u ≤ s → s - u ∈ P) ∧
    P ⊆ Set.Ici 0

/-- §2.1, p. 85: the family of survival laws `u ↦ L u` (law of `Z_i(u)`, a count of customers)
has the semigroup property on the parameter set `P`: if `Y₁, Y₂` are independent with laws
`L u`, `L s`, then `Y₁ + Y₂` has law `L (u + s)`. Each law also has a finite mean. -/
def IsSemigroupFamily (P : Set ℝ) (L : ℝ → PMF ℕ) : Prop :=
  (∀ u ∈ P, ∀ s ∈ P,
    (L (u + s)).toMeasure = ((L u).toMeasure.prod (L s).toMeasure).map (fun p => p.1 + p.2)) ∧
  ∀ u ∈ P, Integrable (fun k : ℕ => (k : ℝ)) (L u).toMeasure

/-- §2.1, p. 85: the joint law of the survival vector `Z(u) = (Z_1(u_1), …, Z_n(u_n))`, with
mutually independent coordinates. -/
noncomputable def survivalLaw {n : ℕ} (L : Fin n → ℝ → PMF ℕ) (u : Fin n → ℝ) :
    Measure (Fin n → ℕ) :=
  Measure.pi (fun i => (L i (u i)).toMeasure)

/-- (2), p. 85: the expected net revenue
`G(u) = ∑ᵢ r_i (u_i − x_i) − E[∑ᵢ q_i (u_i − Z_i(u_i))] + E[V₀(Z(u), c)]`. -/
noncomputable def G {n m : ℕ} (r q x : Fin n → ℝ) (a : Fin n → Fin (m + 1) → ℝ)
    (c : Fin (m + 1) → ℝ) (L : Fin n → ℝ → PMF ℕ) (u : Fin n → ℝ) : ℝ :=
  ∑ i, r i * (u i - x i) - ∫ z, (∑ i, q i * (u i - (z i : ℝ))) ∂(survivalLaw L u) +
    ∫ z, V0 a c (fun i => (z i : ℝ)) ∂(survivalLaw L u)

end SubstOverbooking.Structure


