-- Prove2me | Definitions.Def_WassDRCCP_Improved_Setting
-- name    : WassDRCCP_Improved_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:25.084284+00:00
-- url     : https://prove2.me/theorems/ab862f79-62a2-49d9-a35c-822ec4cbb455
-- title:
--   (1)–(2b), (3), (4a), (5), (8), (17), (20), pp. 645–655 — safety set, distance, X_DR(S), k, q_p, [N]_p and the MIP constraint systems
-- statement:
--   This file fixes the objects of the distributionally robust chance-constrained program (DR-CCP) with right-hand side uncertainty studied by Ho-Nguyen, Kılınç-Karzan, Küçükyavuz and Lee.
--
--   **Data.** The random vector $\xi$ takes values in a finite-dimensional real normed space $E$ (the paper's $\mathbb R^K$ with an arbitrary norm $\|\cdot\|$). The decision is $x \in \mathbb R^L$, constrained to a set $\mathcal X \subseteq \mathbb R^L$. The sample is $\xi_1, \dots, \xi_N \in E$; $\epsilon$ is the risk tolerance and $\theta$ the Wasserstein radius. For each row $p \in [P]$ there are $a_p \in \mathbb R^L$, $d_p \in \mathbb R$ and a continuous linear functional $b_p$ on $E$; $b_p^\top \xi$ is the value of $b_p$ at $\xi$ and $\|b_p\|_*$ is its dual (operator) norm.
--
--   1. **Safety set (4a)** and **distance to the unsafe set (1)**:
--   $$\mathcal S(x) = \{\xi : b_p^\top\xi + d_p - a_p^\top x > 0,\ p \in [P]\},\qquad \operatorname{dist}(\xi, S) = \inf\{\|\xi - \xi'\| : \xi' \notin S\}.$$
--   2. **Feasible region (2b)** of (DR-CCP), for a safety-set map $\mathcal S$:
--   $$\mathcal X_{\mathrm{DR}}(\mathcal S) = \Big\{x \in \mathcal X : \sup_{\mathbb P \in \mathcal F_N(\theta)} \mathbb P[\xi \notin \mathcal S(x)] \le \epsilon\Big\},$$
--   where $\mathcal F_N(\theta)$ is the set of Borel probability measures $\mathbb P$ on $E$ with 1-Wasserstein distance $d_W(\mathbb P_N, \mathbb P) \le \theta$ from the empirical distribution $\mathbb P_N = \frac1N\sum_i \delta_{\xi_i}$ (cost $\|\xi - \xi'\|$).
--   3. **The right-hand side of (3)**: the set of $x \in \mathcal X$ for which there are $t \ge 0$ and $r \in \mathbb R^N_{\ge 0}$ with $\operatorname{dist}(\xi_i, \mathcal S(x)) \ge t - r_i$ for all $i$ and $\epsilon t \ge \theta + \frac1N \sum_i r_i$.
--   4. **Scalars.** $k = \lfloor \epsilon N \rfloor$; the $(j+1)$-th smallest value of a finite family (ties counted with multiplicity); $g_{i,p}(x) = (b_p^\top\xi_i + d_p - a_p^\top x)/\|b_p\|_*$; $q_p$ = the $(k+1)$-th largest value among $\{-b_p^\top\xi_i\}_{i\in[N]}$; $h_{i,p} = (-b_p^\top\xi_i - q_p)/\|b_p\|_*$; $g^*_p(x) = (-q_p + d_p - a_p^\top x)/\|b_p\|_*$; and $[N]_p = \{i \in [N] : -b_p^\top\xi_i > q_p\}$.
--   5. **Constraints**, on $(x, z, r, t) \in \mathbb R^L \times \mathbb R^N \times \mathbb R^N \times \mathbb R$, with a constant $M$:
--      - (5b) $z \in \{0,1\}^N$, $t \ge 0$, $r \ge 0$, $x \in \mathcal X$;
--      - (5c) $\epsilon t \ge \theta + \frac1N\sum_i r_i$;
--      - (5d) $M(1 - z_i) \ge t - r_i$ for all $i$;
--      - (5e) $g_{i,p}(x) + M z_i \ge t - r_i$ for all $i, p$;
--      - (8c) $\sum_i z_i \le \lfloor \epsilon N\rfloor$;
--      - (8d) $g_{i,p}(x) + M z_i \ge 0$ for all $i, p$;
--      - (17c) $g_{i,p}(x) + h_{i,p} z_i \ge t - r_i$ for all $i, p$;
--      - (20c) the same inequality only for $i \in [N]_p$, $p \in [P]$;
--      - (20d) $g^*_p(x) \ge t$ for all $p$.
--
--      The systems are: (5) = (5b)–(5e); (8) = (5b)–(5e), (8c), (8d); (17) = (5b), (5c), (5d), (8c), (17c); (20) = (5b), (5c), (5d), (8c), (20c), (20d).
--
--   These objects are shared by every statement of the mission: the reformulation theorems are equalities between $\mathcal X_{\mathrm{DR}}(\mathcal S)$ and the projections onto $x$ of these constraint systems.
--
--   **Formalization Note** The ξ-space is a type `E` with an arbitrary norm, not `Fin K → ℝ` (whose Mathlib norm is the sup norm). The worst-case probability is the published `ModelRiskOT.WorstProb.worstProb` with cost $\|u - v\|$, valued in $[0, \infty]$, and $\mathbb P_N$ is the published `WassersteinDRO.Duality.empiricalDistribution`. The distance is Mathlib's `Metric.infDist`, which is $0$ (not $+\infty$) when the unsafe set is empty; statements about a general $\mathcal S$ assume the unsafe set nonempty. The binaries $z$ are real numbers with $z_i \in \{0, 1\}$, and indices are 0-based. The order statistic sorts the multiset of values; out of range it returns the junk value $0$, and every use has rank $k < N$. In (17b) the paper prints "(5b)–(5d) and (5c)"; the second "(5c)" is read as (8c) (see Theorem 2).
-- source:
--   Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee, Math. Program. 196 (2022) 641–672, pp. 644–655: d_W and F_N(θ) p. 644; (1), (2b), (3) p. 645; (4a), (5) p. 646; (8) p. 647; k p. 649; q_p p. 650; (17) p. 651; h_{i,p}, u_p p. 652; g_{i,p}, g*_p p. 654; [N]_p and (20) p. 655

import Mathlib
import Definitions.Def_ModelRiskOT_WorstProb_WorstCaseProb
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution

open MeasureTheory
open scoped ENNReal

namespace WassDRCCP.Improved

/-! Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee, *Distributionally robust chance-constrained
programs with right-hand side uncertainty under Wasserstein ambiguity*, Math. Program. 196 (2022)
641–672, §§2–4.

Conventions. The uncertainty `ξ` lives in a real normed space `E` (the paper's `ℝ^K` with an
arbitrary norm `‖·‖`); the decision `x` lives in `Fin L → ℝ` (the paper's `ℝ^L`); the sample is
`ξ : Fin N → E`; the rows are indexed by `p : Fin P`. The vector `b_p` is a continuous linear
functional `b p : StrongDual ℝ E`, so `b_p^⊤ ξ` is `b p ξ` and the dual norm `‖b_p‖_*` is the
operator norm `‖b p‖`. Indices are 0-based. -/

/-- The safety set (4a), p. 646:
`S(x) = {ξ : b_p^⊤ξ + d_p − a_p^⊤x > 0 for every p ∈ [P]}`. -/
def safetySet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ) (x : Fin L → ℝ) :
    Set E :=
  {u | ∀ p : Fin P, 0 < b p u + d p - a p ⬝ᵥ x}

/-- The distance (1), p. 645, from `u` to the unsafe set:
`dist(u, S) = inf {‖u − u'‖ : u' ∉ S}`. Mathlib's `Metric.infDist` returns `0` when `Sᶜ` is
empty (where the paper's infimum is `+∞`); every statement using it for a general `S` assumes
`Sᶜ` nonempty. -/
noncomputable def distUnsafe {E : Type*} [NormedAddCommGroup E] (S : Set E) (u : E) : ℝ :=
  Metric.infDist u Sᶜ

/-- The feasible region (2b), p. 645, of (DR-CCP):
`X_DR(S) = {x ∈ X : sup_{P ∈ F_N(θ)} P[ξ ∉ S(x)] ≤ ϵ}`, where `F_N(θ)` is the 1-Wasserstein ball
(cost `‖u − v‖`) of radius `θ` around the empirical distribution `P_N` of the sample `ξ`, and the
supremum is over Borel probability measures on `E` (`ModelRiskOT.WorstProb.worstProb`). -/
noncomputable def XDR {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {L N : ℕ}
    (S : (Fin L → ℝ) → Set E) (X : Set (Fin L → ℝ)) (ξ : Fin N → E) (ϵ θ : ℝ) :
    Set (Fin L → ℝ) :=
  {x | x ∈ X ∧
    ModelRiskOT.WorstProb.worstProb (fun u v : E => ‖u - v‖)
      (WassersteinDRO.Duality.empiricalDistribution ξ) θ (S x)ᶜ ≤ ENNReal.ofReal ϵ}

/-- The right-hand side of (3), p. 645:
`{x ∈ X : ∃ t ≥ 0, r ≥ 0, dist(ξ_i, S(x)) ≥ t − r_i (i ∈ [N]), ϵ t ≥ θ + (1/N) Σ_i r_i}`. -/
noncomputable def dualSet {E : Type*} [NormedAddCommGroup E] {L N : ℕ}
    (S : (Fin L → ℝ) → Set E) (X : Set (Fin L → ℝ)) (ξ : Fin N → E) (ϵ θ : ℝ) :
    Set (Fin L → ℝ) :=
  {x | x ∈ X ∧ ∃ (t : ℝ) (r : Fin N → ℝ), 0 ≤ t ∧ (∀ i, 0 ≤ r i) ∧
    (∀ i, distUnsafe (S x) (ξ i) ≥ t - r i) ∧
    ϵ * t ≥ θ + (1 / (N : ℝ)) * ∑ i, r i}

/-- `k = ⌊ϵN⌋` (pp. 649, 653). -/
noncomputable def kOf (ϵ : ℝ) (N : ℕ) : ℕ := ⌊ϵ * N⌋₊

/-- The order statistic of rank `j` (0-based) of `v : Fin N → ℝ`, counting ties with
multiplicity: `kthSmallest v j` is the `(j+1)`-th smallest value among `v 0, …, v (N−1)`.
(Out of range, `j ≥ N`, it is the junk value `0`; every use has `j < N`.) -/
noncomputable def kthSmallest {N : ℕ} (v : Fin N → ℝ) (j : ℕ) : ℝ :=
  ((Finset.univ.val.map v).sort (· ≤ ·)).getD j 0

/-- The `(j+1)`-th largest value among `v 0, …, v (N−1)`, ties counted with multiplicity. -/
noncomputable def kthLargest {N : ℕ} (v : Fin N → ℝ) (j : ℕ) : ℝ :=
  -kthSmallest (fun i => -v i) j

/-- `g_{i,p}(x) = (b_p^⊤ξ_i + d_p − a_p^⊤x)/‖b_p‖_*` (proof of Proposition 1, p. 654). -/
noncomputable def gip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ) (ξ : Fin N → E)
    (x : Fin L → ℝ) (i : Fin N) (p : Fin P) : ℝ :=
  (b p (ξ i) + d p - a p ⬝ᵥ x) / ‖b p‖

/-- `q_p`, the `(k+1)`-th largest value among `{−b_p^⊤ξ_i}_{i ∈ [N]}` (pp. 650, 652). -/
noncomputable def qp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N P : ℕ}
    (b : Fin P → StrongDual ℝ E) (ξ : Fin N → E) (k : ℕ) (p : Fin P) : ℝ :=
  kthLargest (fun i => -(b p (ξ i))) k

/-- `h_{i,p} = (−b_p^⊤ξ_i − q_p)/‖b_p‖_*` (p. 652). -/
noncomputable def hip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N P : ℕ}
    (b : Fin P → StrongDual ℝ E) (ξ : Fin N → E) (k : ℕ) (i : Fin N) (p : Fin P) : ℝ :=
  (-(b p (ξ i)) - qp b ξ k p) / ‖b p‖

/-- `g*_p(x) = (−q_p + d_p − a_p^⊤x)/‖b_p‖_*` (proof of Proposition 1, p. 654); the quantity
`u_p` of p. 652 is `g*_p(x) − t`. -/
noncomputable def gstar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ) (ξ : Fin N → E)
    (k : ℕ) (x : Fin L → ℝ) (p : Fin P) : ℝ :=
  (-(qp b ξ k p) + d p - a p ⬝ᵥ x) / ‖b p‖

/-- The index set `[N]_p = {i ∈ [N] : −b_p^⊤ξ_i > q_p}` (p. 655). -/
noncomputable def Np {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N P : ℕ}
    (b : Fin P → StrongDual ℝ E) (ξ : Fin N → E) (k : ℕ) (p : Fin P) : Finset (Fin N) :=
  Finset.univ.filter (fun i => -(b p (ξ i)) > qp b ξ k p)

/-! ### The constraints of the MIP formulations (5), (8), (17), (20) -/

/-- (5b), p. 646: `z ∈ {0,1}^N`, `t ≥ 0`, `r ≥ 0`, `x ∈ X`. -/
def c5b {L N : ℕ} (X : Set (Fin L → ℝ)) (x : Fin L → ℝ) (z r : Fin N → ℝ) (t : ℝ) : Prop :=
  (∀ i, z i = 0 ∨ z i = 1) ∧ 0 ≤ t ∧ (∀ i, 0 ≤ r i) ∧ x ∈ X

/-- (5c), p. 646: `ϵ t ≥ θ + (1/N) Σ_i r_i`. -/
noncomputable def c5c {N : ℕ} (ϵ θ : ℝ) (r : Fin N → ℝ) (t : ℝ) : Prop :=
  ϵ * t ≥ θ + (1 / (N : ℝ)) * ∑ i, r i

/-- (5d), p. 646: `M(1 − z_i) ≥ t − r_i` for `i ∈ [N]`. -/
def c5d {N : ℕ} (M : ℝ) (z r : Fin N → ℝ) (t : ℝ) : Prop :=
  ∀ i, M * (1 - z i) ≥ t - r i

/-- (5e), p. 646: `(b_p^⊤ξ_i + d_p − a_p^⊤x)/‖b_p‖_* + M z_i ≥ t − r_i` for `i ∈ [N]`,
`p ∈ [P]`. -/
noncomputable def c5e {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ) (ξ : Fin N → E)
    (M : ℝ) (x : Fin L → ℝ) (z r : Fin N → ℝ) (t : ℝ) : Prop :=
  ∀ i p, gip a b d ξ x i p + M * z i ≥ t - r i

/-- (8c), p. 647: `Σ_i z_i ≤ ⌊ϵN⌋`. -/
noncomputable def c8c {N : ℕ} (ϵ : ℝ) (z : Fin N → ℝ) : Prop :=
  ∑ i, z i ≤ (kOf ϵ N : ℝ)

/-- (8d), p. 647: `(b_p^⊤ξ_i + d_p − a_p^⊤x)/‖b_p‖_* + M z_i ≥ 0` for `i ∈ [N]`, `p ∈ [P]`. -/
noncomputable def c8d {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ) (ξ : Fin N → E)
    (M : ℝ) (x : Fin L → ℝ) (z : Fin N → ℝ) : Prop :=
  ∀ i p, gip a b d ξ x i p + M * z i ≥ 0

/-- (17c), p. 651: `(b_p^⊤ξ_i + d_p − a_p^⊤x)/‖b_p‖_* + ((−b_p^⊤ξ_i − q_p)/‖b_p‖_*) z_i ≥ t − r_i`
for `i ∈ [N]`, `p ∈ [P]`, with `q_p` taken at `k = ⌊ϵN⌋`. -/
noncomputable def c17c {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ) (ξ : Fin N → E)
    (ϵ : ℝ) (x : Fin L → ℝ) (z r : Fin N → ℝ) (t : ℝ) : Prop :=
  ∀ i p, gip a b d ξ x i p + hip b ξ (kOf ϵ N) i p * z i ≥ t - r i

/-- (20c), p. 655: the inequality of (17c), imposed only for `i ∈ [N]_p`, `p ∈ [P]`. -/
noncomputable def c20c {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ) (ξ : Fin N → E)
    (ϵ : ℝ) (x : Fin L → ℝ) (z r : Fin N → ℝ) (t : ℝ) : Prop :=
  ∀ p, ∀ i ∈ Np b ξ (kOf ϵ N) p, gip a b d ξ x i p + hip b ξ (kOf ϵ N) i p * z i ≥ t - r i

/-- (20d), p. 655: `(−q_p + d_p − a_p^⊤x)/‖b_p‖_* ≥ t` for `p ∈ [P]`. -/
noncomputable def c20d {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ) (ξ : Fin N → E)
    (ϵ : ℝ) (x : Fin L → ℝ) (t : ℝ) : Prop :=
  ∀ p, gstar a b d ξ (kOf ϵ N) x p ≥ t

/-- The constraints (5b)–(5e) of formulation (5), p. 646. -/
noncomputable def sys5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ) (ξ : Fin N → E)
    (X : Set (Fin L → ℝ)) (ϵ θ M : ℝ) (x : Fin L → ℝ) (z r : Fin N → ℝ) (t : ℝ) : Prop :=
  c5b X x z r t ∧ c5c ϵ θ r t ∧ c5d M z r t ∧ c5e a b d ξ M x z r t

/-- The constraints (8b)–(8d) of formulation (8), p. 647: (5b)–(5e), (8c) and (8d). -/
noncomputable def sys8 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ) (ξ : Fin N → E)
    (X : Set (Fin L → ℝ)) (ϵ θ M : ℝ) (x : Fin L → ℝ) (z r : Fin N → ℝ) (t : ℝ) : Prop :=
  c5b X x z r t ∧ c5c ϵ θ r t ∧ c5d M z r t ∧ c5e a b d ξ M x z r t ∧
    c8c ϵ z ∧ c8d a b d ξ M x z

/-- The constraints (17b)–(17c) of formulation (17), p. 651: (5b), (5c), (5d), the cardinality
constraint (8c) (printed "(5c)" a second time in (17b); see the Formalization Note), and (17c). -/
noncomputable def sys17 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ) (ξ : Fin N → E)
    (X : Set (Fin L → ℝ)) (ϵ θ M : ℝ) (x : Fin L → ℝ) (z r : Fin N → ℝ) (t : ℝ) : Prop :=
  c5b X x z r t ∧ c5c ϵ θ r t ∧ c5d M z r t ∧ c8c ϵ z ∧ c17c a b d ξ ϵ x z r t

/-- The constraints (20b)–(20d) of the improved formulation (20), p. 655: (5b), (5c), (5d),
(8c), (20c) for `i ∈ [N]_p`, and (20d). -/
noncomputable def sys20 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ) (ξ : Fin N → E)
    (X : Set (Fin L → ℝ)) (ϵ θ M : ℝ) (x : Fin L → ℝ) (z r : Fin N → ℝ) (t : ℝ) : Prop :=
  c5b X x z r t ∧ c5c ϵ θ r t ∧ c5d M z r t ∧ c8c ϵ z ∧ c20c a b d ξ ϵ x z r t ∧
    c20d a b d ξ ϵ x t

end WassDRCCP.Improved


