-- Prove2me | Definitions.Def_PerishablePricing_Bounds_Model
-- name    : PerishablePricing_Bounds_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T21:15:26.987649+00:00
-- url     : https://prove2.me/theorems/b4dbb380-4b39-4ab9-a29d-5e41a21919ba
-- title:
--   §3–§4, pp. 288–291 — the backlogging perishable inventory–pricing model at zero lead time: data, dynamics (2), recursion (4)–(6)
-- statement:
--   A single perishable product with lifetime $l=L+1\ge 2$ periods is reviewed periodically; the replenishment lead time is zero and unmet demand is backlogged.
--
--   **Data.** Unit costs: ordering $c$, holding $h^+$, backlogging $h^-$, disposal $\theta$; discount factor $\gamma$. The decision variable for pricing is the expected demand $d\in\mathcal D=[\underline d,\bar d]$; $P$ is the inverse demand function, so the expected revenue is $R(d,\cdot)=P(d)\,d$. The realized demand is $d_t=d+\varepsilon_t$, where the noise $\varepsilon_t$ has one law $\mu$ in every period. The standing assumptions (§3) are: all unit costs are nonnegative and $0\le\gamma\le 1$; $\underline d\le\bar d$; $P$ is strictly decreasing on $\mathcal D$; **Assumption 1**, backlogging case: $d\mapsto P(d)d$ is continuous and concave on $\mathcal D$; $\mu$ is a probability law with mean zero and support in $[A,B]$, $A\le 0\le B$; and $\underline d+A\ge 0$, so demand is nonnegative.
--
--   **State and dynamics.** The state is $s=(s_1,\dots,s_{l-1})$ in $\mathcal S=\mathcal V_{l-1,l-1}=\{s_1\le\dots\le s_{l-1}\}$, where $s_i$ is the inventory (or, if negative, the shortfall) with residual lifetime at most $i$ periods and $s_{l-1}$ is the inventory position. The decisions are the order-up-to level $s_l\ge s_{l-1}$, the expected demand $d\in\mathcal D$, and the depletion $a$ with $s_1\vee d_t\le a\le s_l\vee d_t$. The next state is
--
--   $$\tilde s=(s_2-a,\dots,s_{l-1}-a,\ s_l-a).\tag{2}$$
--
--   **Recursion.** With $f_{T+1}=0$ and, for $t\le T$,
--
--   $$\varphi_t(s,s_l,d,a\mid\varepsilon_t)=\gamma c\,\tilde s_{l-1}-cs_l-\theta(a-d_t)-h^+(s_l-a)^+-h^-(a-s_l)^++\gamma f_{t+1}(\tilde s),\tag{6}$$
--
--   $$g_t(s,s_l,d\mid\varepsilon_t)=\max_{s_1\vee d_t\le a\le s_l\vee d_t}\varphi_t(s,s_l,d,a\mid\varepsilon_t),\tag{5}$$
--
--   $$G_t(s,s_l,d)=P(d)d+\mathbb E\big[g_t(s,s_l,d\mid\varepsilon_t)\big],\qquad f_t(s)=\max_{s_l\ge s_{l-1},\ d\in\mathcal D}G_t(s,s_l,d).\tag{4}$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** States are `s : Fin L → ℝ` with $L=l-1$; the paper's $s_i$ is `s ⟨i-1, _⟩`, `sFirst s` is $s_1$ and `sLast s` is $s_{l-1}$ (both default to $0$ when $L=0$, a case every theorem excludes with `1 ≤ L`). Time is counted in periods to go, using stationarity: `f 0 = 0` is $f_{T+1}=0$, and `f (n+1)` is $f_t$ with continuation `f n` $=f_{t+1}$; `g (f n)`, `G (f n)` and `phi (f n)` are $g_t$, $G_t$, $\varphi_t$ for the period with $n+1$ periods to go. The maxima are `sSup` over images of nonempty feasible sets: the depletion interval is compact and nonempty, and the set in (4) is nonempty and its values are bounded above (revenue is bounded on $\mathcal D$, and the cost terms are bounded using $a\ge d_t\ge 0$), so the suprema are not Lean's junk value. The expectation is a Bochner integral against $\mu$; $g_t$ depends on $\varepsilon$ only through $d_t$, in which it is concave, hence bounded and measurable on the bounded support. The value of `f` off $\mathcal S$ is never used: every statement evaluates it on $\mathcal S$ (the paper's "$f_t=+\infty$ off $\mathcal S$" would be $-\infty$ for a maximization). In $\varphi$ the term $\tilde s_{l-1}$ is written out as $s_l-a$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, §3 (eq. (1), Assumption 1, state space 𝒮_b, eq. (2), eqs. (4)–(6)), pp. 288–290, and §4, p. 291, with lead time k = 0

import Mathlib

namespace PerishablePricing.Bounds

open MeasureTheory

/-!
# Chen, Pang and Pan (2014), §3–§4, pp. 288–291: the backlogging model at zero lead time

The perishable product has lifetime `l = L + 1 ≥ 2` periods and the replenishment lead time is
`k = 0`. A state is `s : Fin L → ℝ`; the paper's `s_i` is `s ⟨i − 1, _⟩` (0-based), so `s₁` is
`sFirst s` and the inventory position `s_{l−1}` is `sLast s`. The order-up-to level `s_l` is a
real number `sl`; with `k = 0` the paper's `s_{l−k}` is `s_l`.

Time is counted in periods to go: data are stationary (p. 288), so `f 0 = 0` is `f_{T+1} = 0`, and
`f (n+1)` is `f_t` for the period with `n + 1` periods to go, whose continuation `f_{t+1}` is `f n`.
-/

/-- The data of the model (§3, pp. 288–289; §4, p. 291), backlogging case:
* `c` unit ordering cost, `hp` = `h⁺` unit holding cost, `hm` = `h⁻` unit backlogging cost,
  `θ` unit disposal cost, `γ` discount factor;
* `𝒟 = [dlo, dhi]` the range of the expected demand `d`, and `P` the inverse demand function, so
  that the expected revenue is `R(d, ·) = P(d) d`;
* `μ` the law of the demand noise `ε_t` (one law for every period: the noise is i.i.d.), with
  support in `[A, B]`. -/
structure Model where
  c : ℝ
  hp : ℝ
  hm : ℝ
  θ : ℝ
  γ : ℝ
  dlo : ℝ
  dhi : ℝ
  P : ℝ → ℝ
  A : ℝ
  B : ℝ
  μ : Measure ℝ

namespace Model

/-- The standing assumptions of §3 (pp. 288–289), backlogging case: nonnegative unit costs,
`γ ∈ [0, 1]`, `d̲ ≤ d̄`, `P` strictly decreasing on `𝒟`, Assumption 1 (the expected revenue
`P(d) d` is continuous and concave on `𝒟`), the noise is a zero-mean probability law supported in
`[A, B]` with `A ≤ 0 ≤ B`, and `D(p̄) + A = d̲ + A ≥ 0` (nonnegative demand). -/
structure Standing (M : Model) : Prop where
  c_nonneg : 0 ≤ M.c
  hp_nonneg : 0 ≤ M.hp
  hm_nonneg : 0 ≤ M.hm
  θ_nonneg : 0 ≤ M.θ
  γ_nonneg : 0 ≤ M.γ
  γ_le_one : M.γ ≤ 1
  dlo_le_dhi : M.dlo ≤ M.dhi
  P_strictAntiOn : StrictAntiOn M.P (Set.Icc M.dlo M.dhi)
  revenue_continuousOn : ContinuousOn (fun d => M.P d * d) (Set.Icc M.dlo M.dhi)
  revenue_concaveOn : ConcaveOn ℝ (Set.Icc M.dlo M.dhi) (fun d => M.P d * d)
  isProbabilityMeasure : IsProbabilityMeasure M.μ
  A_nonpos : M.A ≤ 0
  B_nonneg : 0 ≤ M.B
  support : M.μ (Set.Icc M.A M.B)ᶜ = 0
  mean_zero : ∫ x, x ∂M.μ = 0
  demand_nonneg : 0 ≤ M.dlo + M.A

end Model

/-- The state space `𝒮 = 𝒱_{l−1,l−1} = {s : s₁ ≤ s₂ ≤ ⋯ ≤ s_{l−1}}` (p. 289). -/
def stateSpace (L : ℕ) : Set (Fin L → ℝ) := {s | Monotone s}

/-- `s₁`, the first coordinate of the state (0 when `L = 0`, a case every statement excludes). -/
def sFirst {L : ℕ} (s : Fin L → ℝ) : ℝ := if h : 0 < L then s ⟨0, h⟩ else 0

/-- `s_{l−1}`, the last coordinate of the state: the inventory position (0 when `L = 0`, a case
every statement excludes). -/
def sLast {L : ℕ} (s : Fin L → ℝ) : ℝ := if h : 0 < L then s ⟨L - 1, by omega⟩ else 0

/-- The dynamics (2) at `k = 0`: `s̃ = (s₂ − a, …, s_{l−1} − a, s_l − a)`, i.e. `s̃_i = s_{i+1} − a`
on the extended vector `(s₁, …, s_{l−1}, s_l)`. -/
def next {L : ℕ} (s : Fin L → ℝ) (sl a : ℝ) : Fin L → ℝ :=
  fun i => Fin.snoc (α := fun _ => ℝ) s sl i.succ - a

namespace Model

variable (M : Model) {L : ℕ}

/-- `φ_t(s, s_l, d, a | ε_t)`, (6) at `k = 0` (p. 290), for a continuation `F` (standing for
`f_{t+1}`), with realized demand `d_t = d + ε`:
`γ c s̃_{l−1} − c s_l − θ (a − d_t) − h⁺ (s_l − a)⁺ − h⁻ (a − s_l)⁺ + γ F(s̃)`,
where `s̃_{l−1} = s_l − a` is the last coordinate of `s̃ = next s s_l a`. -/
noncomputable def phi (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d a ε : ℝ) : ℝ :=
  M.γ * M.c * (sl - a) - M.c * sl - M.θ * (a - (d + ε)) - M.hp * max (sl - a) 0
    - M.hm * max (a - sl) 0 + M.γ * F (next s sl a)

/-- `g_t(s, s_l, d | ε_t)`, (5) at `k = 0` (p. 290): the supremum of `φ` over the depletion
interval `s₁ ∨ d_t ≤ a ≤ s_l ∨ d_t`. -/
noncomputable def g (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d ε : ℝ) : ℝ :=
  sSup ((fun a => M.phi F s sl d a ε) '' Set.Icc (max (sFirst s) (d + ε)) (max sl (d + ε)))

/-- `G_t(s, s_l, d) = R(d, s_l) + E[g_t(s, s_l, d | ε_t)]` (p. 290), with the backlogging revenue
`R(d, s_l) = P(d) d`. -/
noncomputable def G (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d : ℝ) : ℝ :=
  M.P d * d + ∫ ε, M.g F s sl d ε ∂M.μ

/-- The profit-to-go `f`, (4) (p. 290), indexed by periods to go: `f 0 = 0` (`f_{T+1} = 0`) and
`f (n+1) s = sup {G(f n)(s, s_l, d) : s_l ≥ s_{l−1}, d ∈ 𝒟}`. -/
noncomputable def f : ℕ → (Fin L → ℝ) → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun s =>
      sSup ((fun p : ℝ × ℝ => M.G (f n) s p.1 p.2) ''
        {p | sLast s ≤ p.1 ∧ p.2 ∈ Set.Icc M.dlo M.dhi})

end Model

end PerishablePricing.Bounds


