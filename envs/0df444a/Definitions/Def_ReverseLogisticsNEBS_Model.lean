-- Prove2me | Definitions.Def_ReverseLogisticsNEBS_Model
-- name    : ReverseLogisticsNEBS_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:02.354657+00:00
-- url     : https://prove2.me/theorems/320443ea-0c84-4bed-ac51-e55cba0eee85
-- title:
--   Reverse logistics supply chain with $N$ locations, Markov-modulated demand and standing assumptions
-- statement:
--   A **reverse logistics supply chain** has $N$ locations in series. Units from an outside supplier enter at location $N$, the most upstream one, and customer demand $D_t$ occurs at location $1$. An exogenous state $\omega_t$ of a countable Markov chain modulates the demand.
--
--   The model data are:
--
--   1. unit holding costs $H_j$, a unit backlogging cost $p$, and unit regular, expedited and reverse-order costs $k_j$, $k^E_j$, $k^R_j$;
--   2. a discount factor $\alpha$;
--   3. for every period $t$ and Markov state $\omega$, the joint law $\kappa_t(\omega)$ of $(D_t, \omega_{t+1})$ given $\omega_t = \omega$.
--
--   Derived quantities: $h_j := H_j - H_{j+1}$ with $H_{N+1} := 0$, $c^E_j := k^E_j + k^R_j$, $c^R_j := k^R_j + k_j - h_j$, $c_j := k_j$, and
--   $$
--   \gamma_t(\omega, x) := (p + H_1)\,\mathbb E_\omega[(D_t(\omega) - x)^+] - H_1\,\mathbb E_\omega[D_t(\omega)].
--   $$
--
--   The **standing assumptions** (`Model.Standing`) are: $N \ge 1$; $k_j > 0$ and $k^E_j \ge k_j$; $k^R_j > 0$ for $j \le N-1$ and $k_N \ge -k^R_N$; $p \ge 0$, $H_j \ge 0$; $0 \le \alpha < 1$; every $\kappa_t(\omega)$ is a probability measure whose demand marginal is supported on $[0, \infty)$ and has a finite mean. The module also defines the cost condition $c^R_j \ge 0$ for all $j$ (`Model.RevRegNonneg`), which the paper's proofs use without stating it, and Assumption 2 (`Model.Stationary`, a time-homogeneous kernel), together with $[x]^- := \min(x, 0)$.
--
--   Every result of the mission is stated for this model.
--
--   **Formalization Note** Locations are `Fin N`: index $j$ is the paper's location $j+1$, and index $N-1$ is location $N$. Periods are $1$-based. A joint kernel for $(D_t, \omega_{t+1})$ is more general than conditional independence of the two and is all the paper's $\mathbb E_\omega$ needs. The signs $p \ge 0$, $H_j \ge 0$ are the field's convention for unit costs and are not written in the paper; nonnegative, integrable demand is implicit in "customer demand" and in $\gamma_t$.
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), §2, pp.7–11 (decisions p.8, timing p.9, costs pp.9–10, α and h_j p.11, γ_t p.11, c^E_j, c^R_j, c_j p.12, Assumption 2 p.16)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

/-- **The reverse logistics model** of Angelus–Özer, *When Variability Trumps Volatility*,
SSRN 3508009 (Dec. 21, 2019), §2, pp.7–11.

`N` locations in series (location `N` is the most upstream one, customer demand occurs at
location `1`), an exogenous Markov state `ω ∈ Ω`, and per-period data:

* `H j` — unit holding cost at location `j` (p.9);
* `p` — unit backlogging cost (p.10);
* `k j`, `kE j`, `kR j` — unit regular, expedited and reverse-order costs (p.10);
* `α` — the single-period discount factor (p.11);
* `κ t ω` — the joint law of `(D_t, ω_{t+1})` given `ω_t = ω`, i.e. of the period-`t` demand
  and the next Markov state (p.8, p.11: "The expectation `E_ω` … is over both `D_t(ω)` and
  `ω_{t+1}`, given `ω`").

**Formalization Note.** Locations are `Fin N`: the index `j` is the paper's location `j + 1`,
and index `N − 1` is the upstream location `N`. Periods are natural numbers, `1`-based; the
kernel at period `0` is never used. A joint kernel for `(D_t, ω_{t+1})` is more general than
"`D_t` and `ω_{t+1}` independent given `ω_t`" and is all the paper's `E_ω` needs. The
standing assumptions of p.10–11 are the separate predicate `Model.Standing`. -/
structure Model (N : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- Unit holding cost `H_j`. -/
  H : Fin N → ℝ
  /-- Unit backlogging cost `p`. -/
  p : ℝ
  /-- Unit regular-order cost `k_j`. -/
  k : Fin N → ℝ
  /-- Unit expedited-order cost `k^E_j`. -/
  kE : Fin N → ℝ
  /-- Unit reverse-order cost `k^R_j` (a revenue when negative at location `N`). -/
  kR : Fin N → ℝ
  /-- Single-period discount factor `α`. -/
  α : ℝ
  /-- Joint law of `(D_t, ω_{t+1})` given `ω_t`, period by period. -/
  κ : ℕ → Kernel Ω (ℝ × Ω)

namespace Model

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model N Ω)

/-- The holding cost extended by `H_{N+1} := 0` (indices `≥ N` give `0`). -/
def Hext (j : ℕ) : ℝ := if h : j < N then M.H ⟨j, h⟩ else 0

/-- Echelon holding cost `h_j := H_j − H_{j+1}` (p.11), with `H_{N+1} := 0`. -/
def h (j : Fin N) : ℝ := M.H j - M.Hext (j.val + 1)

/-- `c^E_j := k^E_j + k^R_j` (p.12). -/
def cE (j : Fin N) : ℝ := M.kE j + M.kR j

/-- `c^R_j := k^R_j + k_j − h_j` (p.12). -/
def cR (j : Fin N) : ℝ := M.kR j + M.k j - M.h j

/-- `c_j := k_j` (p.12). -/
def c (j : Fin N) : ℝ := M.k j

/-- The expected shortage–holding function of p.11,
`γ_t(ω, x) := (p + H_1) E_ω[(D_t(ω) − x)^+] − H_1 E_ω[D_t(ω)]`. -/
noncomputable def gamma (t : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  (M.p + M.Hext 0) * ∫ z, max (z.1 - x) 0 ∂(M.κ t ω) - M.Hext 0 * ∫ z, z.1 ∂(M.κ t ω)

/-- **Standing assumptions** of the model (pp.7–11):

1. at least one location;
2. `k_j > 0` and `k^E_j ≥ k_j` for every `j` (p.10; `k^E_j > 0` follows);
3. `k^R_j > 0` at locations `1, …, N − 1`, and `k_N ≥ −k^R_N` at location `N` (p.10);
4. `p ≥ 0`, `H_j ≥ 0` (unit costs; the field's standing convention, not written in the paper);
5. `0 ≤ α < 1` (p.11);
6. every `κ t` is a Markov kernel whose demand marginal is supported on `[0, ∞)` and has a
   finite mean (customer demand, p.7; the expectation `E_ω[D_t(ω)]` in `γ_t`, p.11). -/
structure Standing : Prop where
  N_pos : 0 < N
  k_pos : ∀ j, 0 < M.k j
  k_le_kE : ∀ j, M.k j ≤ M.kE j
  kR_pos : ∀ j : Fin N, j.val + 1 < N → 0 < M.kR j
  k_top : ∀ j : Fin N, j.val + 1 = N → -M.kR j ≤ M.k j
  p_nonneg : 0 ≤ M.p
  H_nonneg : ∀ j, 0 ≤ M.H j
  α_nonneg : 0 ≤ M.α
  α_lt_one : M.α < 1
  markov : ∀ t, IsMarkovKernel (M.κ t)
  demand_nonneg : ∀ t ω, M.κ t ω {z | z.1 < 0} = 0
  demand_integrable : ∀ t ω, Integrable (fun z : ℝ × Ω => z.1) (M.κ t ω)

/-- The cost condition `c^R_j = k^R_j + k_j − h_j ≥ 0` at every location: the echelon holding
cost `h_j` does not exceed the round-trip cost `k^R_j + k_j` of sending a unit up and ordering it
back. The paper does not state it, but its proofs use it (proof of Proposition 2, p.37, with the
cost (29); proof of Theorem 5, p.42, "`−c^R_N[Ŷ^R_Nt − Ȳ^R_Nt] ≥ 0`"); Theorems 1, 2 and 5 are
false without it (see the theorem items). -/
def RevRegNonneg : Prop := ∀ j, 0 ≤ M.cR j

/-- **Assumption 2** (p.16) together with time-homogeneous data: the law of
`(D_t, ω_{t+1})` given `ω_t` does not depend on the period `t ≥ 1`. -/
def Stationary : Prop := ∀ t, 1 ≤ t → M.κ t = M.κ 1

end Model

/-- `[x]^− := min(x, 0)` (p.9). -/
def negPartMin (x : ℝ) : ℝ := min x 0

/-- The first coordinate of a vector over the locations (location `1`); `0` if `N = 0`. -/
def firstLoc {N : ℕ} (v : Fin N → ℝ) : ℝ := if h : 0 < N then v ⟨0, h⟩ else 0

end ReverseLogisticsNEBS


