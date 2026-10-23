-- Prove2me | Definitions.Def_PriorityAlloc_DAFlex_Model
-- name    : PriorityAlloc_DAFlex_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:29.564012+00:00
-- url     : https://prove2.me/theorems/1a90528a-511a-4984-b265-a8cc9eb1d225
-- title:
--   §2–§3.2 and App. A.2, pp. 7–13, 34 — continuum market, choice probabilities, Y^M, regularity, DA demand, DA operator and cutoff, budget set probabilities, DA and DA-STB classes
-- statement:
--   This file fixes the continuum model of priority-based allocation of Shi (§2 and §3) and the deferred acceptance (DA) mechanism with its cutoff vector (App. A.2).
--
--   **Market.** There are $n$ items $j \in [n]$ and an outside option $0$; write $J = [n] \cup \{0\}$. A market $M = (m, n, \lambda, c, F)$ consists of $m$ segments with masses $\lambda_t > 0$, capacities $c_j \ge 0$ of the real items (the outside option has capacity $\infty$), and, for each segment $t$, a probability distribution $F_t$ of utility vectors $u \in \mathbb{R}^{J}$. Preferences are strict: $F_t$ is concentrated on vectors with pairwise distinct components.
--
--   **Choice probabilities and feasible budget set probabilities.** For $S \subseteq J$,
--   $$P_t(j,S) = \mathbb{1}(j \in S)\,\mathbb{P}_{u \sim F_t}\Big(u_j = \max_{j' \in S} u_{j'}\Big).$$
--   A budget set probability matrix $y = (y_{tS})$ belongs to $Y^M$ (Definition 2) when
--   1. $y_{tS} \ge 0$;
--   2. $\sum_{t,S} \lambda_t P_t(j,S)\, y_{tS} \le c_j$ for each $j \in [n]$ (capacity, (11));
--   3. $\sum_S y_{tS} = 1$ for each $t$;
--   4. $y_{tS} = 0$ whenever $0 \notin S$.
--
--   The market is **regular** (Definition 4) if $\{0\} \subseteq S \subsetneq S'$ implies $P_t(0,S) > P_t(0,S')$ for every $t$. A matrix $y$ is **nested within segment** (Definition 5 a)) if $y_{tS} > 0$ and $y_{tS'} > 0$ imply $S \subseteq S'$ or $S' \subseteq S$.
--
--   **DA.** Priorities $\pi \in \Pi = [0,B]^n$ are drawn from segment-dependent laws $G_t$, independently of utilities. Under a cutoff vector $z$ the budget set of priority $\pi$ is $B_\pi = \{j \in J : j = 0 \text{ or } \pi_j \ge z_j\}$. The demand for item $j$ is
--   $$D_j(z) = \sum_{t} \lambda_t\, \mathbb{P}_{u \sim F_t,\ \pi \sim G_t}\Big(j \in \arg\max_{j' \in B_\pi} u_{j'}\Big). \tag{A.2}$$
--   Given quotas $q$, the DA operator (Algorithm 2) leaves $z_j$ unchanged when $D_j(z) \le q_j$ and otherwise raises it to $z_j + \inf\{\delta : D_j(z + \delta \mathbb{1}_j) \le q_j\}$. The DA cutoff $z^{DA(M,G,q)}$ is the minimum fixed point of this operator in $[0,B]^n$. The budget set probabilities of the mechanism are $y^X_{tS} = \mathbb{P}_{\pi \sim G_t}(B_\pi = S)$ (Definition 1).
--
--   **Classes.** A matrix $y$ is DA-implementable (Definition 3) if some DA mechanism — priority laws $G_t$ on a box $[0,B]^n$, quotas $0 \le q \le c$, and its DA cutoff — has budget set probabilities exactly $y$. DA-STB is the special case $\pi_{ij} = b_{tj} + \delta_i$ with deterministic boosts $b$ and a single tie-breaker $\delta_i \sim \mathrm{Uniform}(0,1)$. Finally the file records the constructions of the proofs: the priority law (H.1), $\pi_{ij} = \mathbb{1}(j \in S_i) + \delta_i$ with $S_i \sim y_t$, and the boosts $b_{tj} = \sum_{S \ni j} y_{tS}$ of Proposition H.3.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Items are `Option (Fin n)` with `none` the outside option. Capacities are assumed nonnegative and strict preferences are encoded as almost-sure injectivity of the utility vector. Probabilities are `toReal` of finite measures; the demand uses the product measure $F_t \otimes G_t$. The DA operator folds both cases of Algorithm 2 into one infimum over $[z_j, B]$, with $B$ added to the set so the operator maps $[0,B]^n$ to itself (the page asserts this; without the clamp an infimum over an empty set would be junk). The cutoff is characterised by `IsLeast` over the fixed points in the box. DA-STB boosts are taken in $[0, B-1]$ so priorities lie in the box $[0,B]^n$.
-- source:
--   Shi, Optimal Priority-Based Allocation Mechanisms, SSRN manuscript 3425348 (June 2020; published Management Science 2022, doi:10.1287/mnsc.2020.3925), pp. 7–13 and 34, §2, §2.1.2, §3.1–3.2, Definitions 1–5, eq. (8), (10)–(13), App. A.2 eq. (A.2) and Algorithm 2; constructions (H.1) p. 47 and Proposition H.3 p. 48

import Mathlib

namespace PriorityAlloc.DAFlex

open MeasureTheory Classical

/-! Shi, *Optimal Priority-Based Allocation Mechanisms*, SSRN 3425348 (2020; Management Science 2022).
§2 (p. 7), §2.1.2 (pp. 9–10), §3.1–3.2 Definitions 1–5 (pp. 11–13), App. A.2 (p. 34),
and the constructions of App. H.1 (pp. 47–48).

Items are `Option (Fin n)`: `none` is the outside option `0`, `some i` is item `i + 1` of `[n]`. -/

variable {m n : ℕ}

/-- A market `M = (m, n, λ, c, F)` (§2, p. 7): segment masses `λ_t`, capacities `c_j` of the
`n` real items (the outside option has capacity `∞`, so it carries no capacity), and the utility
distributions `F_t` on utility vectors `u : J → ℝ`. -/
structure Market (m n : ℕ) where
  /-- `λ_t`, the mass of agents of segment `t`. -/
  lam : Fin m → ℝ
  /-- `c_j`, the capacity of item `j ∈ [n]`. -/
  cap : Fin n → ℝ
  /-- `F_t`, the utility distribution of segment `t`. -/
  F : Fin m → Measure (Option (Fin n) → ℝ)

/-- The standing assumptions of §2, p. 7: `λ_t > 0`; `c_j ≥ 0` (a capacity is a maximum mass);
each `F_t` is a probability measure; preferences are strict, i.e. `F_t` is concentrated on
`Θ`, the utility vectors with pairwise distinct components. -/
def Market.Standing (M : Market m n) : Prop :=
  (∀ t, 0 < M.lam t) ∧ (∀ j, 0 ≤ M.cap j) ∧ (∀ t, IsProbabilityMeasure (M.F t)) ∧
    (∀ t, ∀ᵐ u ∂(M.F t), Function.Injective u)

/-- The choice probability (8), p. 12: `P_t(j,S) = 𝟙(j ∈ S) · P_{u∼F_t}(u_j = max_{j'∈S} u_{j'})`. -/
noncomputable def choiceProb (M : Market m n) (t : Fin m) (j : Option (Fin n))
    (S : Finset (Option (Fin n))) : ℝ :=
  (M.F t {u | j ∈ S ∧ ∀ j' ∈ S, u j' ≤ u j}).toReal

/-- The left-hand side of the capacity constraint (11), p. 12:
`Σ_{t,S} λ_t P_t(j,S) y_{tS}`, the mass of agents assigned to item `j` under `y`. -/
noncomputable def lhs11 (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (j : Fin n) : ℝ :=
  ∑ t, ∑ S, M.lam t * choiceProb M t (some j) S * y t S

/-- Definition 2, p. 12: `y ∈ Y^M`, i.e. `y` satisfies constraints (10)–(13). -/
def Ymem (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ) : Prop :=
  (∀ t S, 0 ≤ y t S) ∧ (∀ j, lhs11 M y j ≤ M.cap j) ∧ (∀ t, ∑ S, y t S = 1) ∧
    (∀ t S, none ∉ S → y t S = 0)

/-- Definition 4, p. 12: the market is regular if, whenever `{0} ⊆ S ⊊ S'`,
`P_t(0,S) > P_t(0,S')` for every segment `t`. -/
def Regular (M : Market m n) : Prop :=
  ∀ (t : Fin m) (S S' : Finset (Option (Fin n))), none ∈ S → S ⊂ S' →
    choiceProb M t none S' < choiceProb M t none S

/-- Definition 5 a), p. 13: `y` is nested within segment if `y_{tS} > 0` and `y_{tS'} > 0`
imply `S ⊆ S'` or `S ⊇ S'`. -/
def NestedWithinSegment (y : Fin m → Finset (Option (Fin n)) → ℝ) : Prop :=
  ∀ t (S S' : Finset (Option (Fin n))), 0 < y t S → 0 < y t S' → S ⊆ S' ∨ S' ⊆ S

/-- The budget set of priority `π` under cutoff vector `z`: `{j ∈ J : j = 0 or π_j ≥ z_j}`
((5), p. 10, and (H.3), p. 47). -/
noncomputable def budget (z π : Fin n → ℝ) : Finset (Option (Fin n)) :=
  insert none ((Finset.univ.filter fun i => z i ≤ π i).map Function.Embedding.some)

/-- The priority space `Π = [0,B]^n` (App. A.2, p. 34). -/
def box (B : ℝ) : Set (Fin n → ℝ) :=
  Set.univ.pi fun _ => Set.Icc 0 B

/-- The DA demand (A.2), p. 34: `D_j(z) = Σ_t λ_t P_{u∼F_t, π∼G_t}(j ∈ argmax_{j' ∈ J}
{u_{j'} : j' = 0 or π_{j'} ≥ z_{j'}})`, with utilities and priorities drawn independently. -/
noncomputable def demand (M : Market m n) (G : Fin m → Measure (Fin n → ℝ))
    (z : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ t, M.lam t * (((M.F t).prod (G t))
    {p | some j ∈ budget z p.2 ∧ ∀ j' ∈ budget z p.2, p.1 j' ≤ p.1 (some j)}).toReal

/-- One iteration of the DA operator, Algorithm 2, p. 34, on `Π = [0,B]^n`:
`z'_j = z_j` if `D_j(z) ≤ q_j`, and otherwise `z'_j = z_j + inf{δ : D_j(z + δ 1_j) ≤ q_j}`.
Both cases are folded into one infimum; the value is clamped at `B` (the `∪ {B}`), so that the
operator maps `[0,B]^n` to itself as the page asserts. -/
noncomputable def DAop (M : Market m n) (G : Fin m → Measure (Fin n → ℝ)) (q : Fin n → ℝ)
    (B : ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun j => sInf ({w | z j ≤ w ∧ w ≤ B ∧ demand M G (Function.update z j w) j ≤ q j} ∪ {B})

/-- `z = z^{DA(M,G,q)}` (App. A.2, p. 34): the minimum element of the set of fixed points of
the DA operator in `[0,B]^n`. -/
def IsDACutoff (M : Market m n) (G : Fin m → Measure (Fin n → ℝ)) (q : Fin n → ℝ) (B : ℝ)
    (z : Fin n → ℝ) : Prop :=
  IsLeast {z' | z' ∈ box B ∧ DAop M G q B z' = z'} z

/-- Definition 1, p. 11: the budget set probabilities `y^X_{tS} = P_{π∼G_t}(S = B^X_π)` of the
DA mechanism with priority distributions `G` and cutoff vector `z`. -/
noncomputable def bsProb (G : Fin m → Measure (Fin n → ℝ)) (z : Fin n → ℝ) (t : Fin m)
    (S : Finset (Option (Fin n))) : ℝ :=
  (G t {π | budget z π = S}).toReal

/-- Definition 3, p. 12, for the class of DA mechanisms (§2.1.2, pp. 9–10): some DA mechanism,
with priority distributions `G_t` (probability measures on a bounded box `[0,B]^n`), quotas
`0 ≤ q ≤ c` and its DA cutoff `z^{DA(M,G,q)}`, has budget set probabilities `y`. -/
def DAImplementable (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ) : Prop :=
  ∃ (B : ℝ) (G : Fin m → Measure (Fin n → ℝ)) (q z : Fin n → ℝ),
    0 < B ∧ (∀ t, IsProbabilityMeasure (G t)) ∧ (∀ t, ∀ᵐ π ∂(G t), π ∈ box B) ∧
      (∀ j, 0 ≤ q j ∧ q j ≤ M.cap j) ∧ IsDACutoff M G q B z ∧ ∀ t S, bsProb G z t S = y t S

/-- The DA-STB priority law of segment `t` (§2.1.2, p. 10): `π_{ij} = b_{tj} + δ_i` with a
single tie-breaker `δ_i ∼ Uniform(0,1)` common to all items. -/
noncomputable def stbLaw (b : Fin m → Fin n → ℝ) (t : Fin m) : Measure (Fin n → ℝ) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).map (fun δ => fun j => b t j + δ)

/-- Definition 3, p. 12, for the class of DA-STB mechanisms (§2.1.2, p. 10): some DA-STB
mechanism, with boosts `b ≥ 0` (priorities in the box `[0,B]^n`), quotas `0 ≤ q ≤ c` and its DA
cutoff, has budget set probabilities `y`. -/
def DASTBImplementable (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ) : Prop :=
  ∃ (B : ℝ) (b : Fin m → Fin n → ℝ) (q z : Fin n → ℝ),
    0 < B ∧ (∀ t j, 0 ≤ b t j ∧ b t j + 1 ≤ B) ∧ (∀ j, 0 ≤ q j ∧ q j ≤ M.cap j) ∧
      IsDACutoff M (stbLaw b) q B z ∧ ∀ t S, bsProb (stbLaw b) z t S = y t S

/-- The priority distribution (H.1) of Proposition H.1, p. 47: sample `S_i ⊆ J` with probability
`y_{tS_i}` and set `π_{ij} = 𝟙(j ∈ S_i) + δ_i` with `δ_i ∼ Uniform(0,1)`. -/
noncomputable def h1Law (y : Fin m → Finset (Option (Fin n)) → ℝ) (t : Fin m) :
    Measure (Fin n → ℝ) :=
  ∑ S, ENNReal.ofReal (y t S) •
    (volume.restrict (Set.Icc (0 : ℝ) 1)).map
      (fun δ => fun j => (if some j ∈ S then (1 : ℝ) else 0) + δ)

/-- The priority boosts of Proposition H.3, p. 48: `b_{tj} = Σ_{S ∋ j} y_{tS}`. -/
noncomputable def stbBoost (y : Fin m → Finset (Option (Fin n)) → ℝ) (t : Fin m)
    (j : Fin n) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S => some j ∈ S), y t S

end PriorityAlloc.DAFlex


