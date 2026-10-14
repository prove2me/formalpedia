-- Prove2me | Definitions.Def_PerishablePricing_Backlog_Model
-- name    : PerishablePricing_Backlog_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:25:20.527954+00:00
-- url     : https://prove2.me/theorems/c1b73fc2-a207-4ed8-98e1-1ef27a241c6b
-- title:
--   §3, pp. 288–290, (1)–(6) — the backlogging perishable inventory–pricing model and its recursion
-- statement:
--   A single perishable product is managed over a finite horizon with periodic review. It has a lifetime of exactly $l = L + 1 \ge 2$ periods, and orders arrive after a lead time of $k$ periods, $0 \le k \le l - 1$. Unmet demand is backlogged.
--
--   **Data and standing assumptions (§3).** The unit costs are $c$ (ordering), $h^+$ (holding), $h^-$ (backlogging) and $\theta$ (disposal), all nonnegative, and $\gamma \in [0,1]$ is the discount factor. The expected demand $d$ is the decision variable in place of the price; it ranges over $\mathcal{D} = [\underline d, \bar d]$, and $P(d)$ is the price that induces expected demand $d$, strictly decreasing on $\mathcal{D}$. The realized demand is $d_t = d + \varepsilon$, where the noise $\varepsilon$ has a law $\mu$ that is a probability distribution supported in $[A, B]$ with $A \le 0 \le B$ and mean zero, the same in every period, and $\underline d + A \ge 0$. Assumption 1 in the backlogging case says that the expected revenue $R(d) = P(d)d$ is continuous and concave on $\mathcal{D}$.
--
--   **State and dynamics.** The state is $s = (s_1, \dots, s_{l-1})$ with $s_1 \le \dots \le s_{l-1}$, so the state space is $\mathcal{S} = \mathcal{V}_{l-1,l-1}$; $s_{l-1}$ is the inventory position. The decisions are the order-up-to level $s_l \ge s_{l-1}$, the expected demand $d \in \mathcal{D}$, and the depletion $a$, with $s_1 \vee d_t \le a \le s_{l-k} \vee d_t$. The coordinate $s_{l-k}$ of $(s_1, \dots, s_l)$ is the net inventory. The next state is (2):
--
--   $$\tilde s = (s_2 - a, \dots, s_l - a).$$
--
--   **Recursion (4)–(6).** For a continuation function $F$ (standing for $f_{t+1}$),
--
--   $$\phi(s, s_l, d, a \mid \varepsilon) = \gamma c\,\tilde s_{l-1} - c s_l - \theta(a - d_t) - h^+(s_{l-k} - a)^+ - h^-(a - s_{l-k})^+ + \gamma F(\tilde s),$$
--
--   $$g(s, s_l, d \mid \varepsilon) = \sup_{s_1 \vee d_t \le a \le s_{l-k} \vee d_t} \phi(s, s_l, d, a \mid \varepsilon), \qquad \tilde g(s, s_l, d \mid \varepsilon) = \sup_{a \ge s_1 \vee d_t} \phi(s, s_l, d, a \mid \varepsilon),$$
--
--   $$G(s, s_l, d) = P(d)d + \mathbb{E}_\mu\big[g(s, s_l, d \mid \varepsilon)\big].$$
--
--   The modified profit-to-go satisfies $f_{T+1} = 0$ and
--
--   $$f_t(s) = \sup_{s_l \ge s_{l-1},\ d \in \mathcal{D}} G_t(s, s_l, d),$$
--
--   where $G_t$, $g_t$, $\phi_t$ use the continuation $f_{t+1}$.
--
--   **Optimal decisions.** A pair $(s_l, d)$ is optimal at $s$ if it is feasible and $G_t(s, s_l, d) = f_t(s)$; it is the **largest** optimal pair (the paper's $s_{lt}(s)$, $d_t(s)$) if moreover every optimal pair $(s_l', d')$ has $s_l' \le s_l$ and $d' \le d$. Likewise $a$ is an optimal depletion if it lies in the interval of (5) and attains $g_t$, and the paper's $a_t(s, s_l, d \mid \varepsilon)$ is the largest optimal depletion.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Indices are 0-based: the state is `s : Fin L → ℝ` with $L = l - 1 \ge 1$, the paper's $s_i$ is `s ⟨i-1, _⟩`, `ext s sl = Fin.snoc s sl` is $(s_1, \dots, s_l)$, and $s_{l-k}$ is its coordinate $L - k$ (`netInv`); at $k = 0$ this is the decision $s_l$, at $k = L$ it is $s_1$. Time is counted in periods to go, which is faithful because the data are stationary (p. 288; hence $\mathcal{D}_t = \mathcal{D}$): `f 0 = 0` is $f_{T+1}$, `f (n+1)` is $f_t$ with continuation `f n` $= f_{t+1}$, and `phiN n`, `gN n`, `GN n` are $\phi_t, g_t, G_t$ for the period with $n + 1$ periods to go. Every "max" of the page is `sSup` of the image of a nonempty feasible set: the depletion interval is nonempty and compact because $s_1 \le s_{l-k}$ on $\mathcal{S}$, and $\phi$ is bounded above on it; the set of $G$-values is bounded above because revenue is bounded on $\mathcal{D}$ and the other terms are at most $-(1-\gamma)c\,s_l$ plus discounted continuation values with $a \ge d_t \ge \underline d + A \ge 0$. The expectation is a Bochner integral against $\mu$; $g$ is bounded and concave in $d_t$ on the support, so the integral is the paper's expectation (this is argued, not proved here). The paper defines $f_t = +\infty$ off $\mathcal{S}$, a slip for $-\infty$ in a maximization; the functions here are total but every statement evaluates them on $\mathcal{S}$ only. The page writes $\phi_t(s, s_l, a, d)$ in (9) and in $\tilde g_t$; the argument order of (6), $(s, s_l, d, a)$, is used throughout. `gJoint` and `phiJoint` view $g$ and $\phi$ as functions of the joint vectors $(s_1, \dots, s_l, d)$ and $(s_1, \dots, s_l, d, a)$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, §3, eqs. (1), (2), (4)–(6), Assumption 1, pp. 288–290 (PDF pp. 6–8); g̃_t and the largest optimal decisions, p. 291 (PDF p. 9)

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex

namespace PerishablePricing.Backlog

open MeasureTheory

/-!
# The backlogging model of Chen, Pang, Pan (2014), §3, pp. 288–290, and its recursion (4)–(6)

* The product has lifetime `l = L + 1` periods (`L ≥ 1`) and the lead time is `k ≤ L` (`k < l`).
* The state `s = (s_1, …, s_{l−1})` is `s : Fin L → ℝ`, 0-based: the paper's `s_i` is
  `s ⟨i − 1, _⟩`. The feasible states are `𝒮 = 𝒱_{l−1,l−1} = V L L`.
* `ext s sl : Fin (L+1) → ℝ` is `(s_1, …, s_{l−1}, s_l)`; the paper's `s_{l−k}` is its coordinate
  `L − k` (`netInv`).
* Time is counted in periods to go: `f 0 = 0` is `f_{T+1} = 0`, and `f (n+1)` is `f_t` with
  continuation `f n = f_{t+1}`. `gN n`, `phiN n`, `GN n` are `g_t`, `φ_t`, `G_t` for the period with
  `n + 1` periods to go. Data are stationary (p. 288), so `𝒟_t = 𝒟`.
* Every "max" of the page is an `sSup` of the image of a nonempty feasible set.
-/

/-- The data of the backlogging model and the standing assumptions of §3 (pp. 288–289):
* unit costs `c` (ordering), `hp` (`h⁺`, holding), `hm` (`h⁻`, backlogging), `θ` (disposal), all
  nonnegative, and the discount factor `γ ∈ [0, 1]`;
* the expected-demand range `𝒟 = [dlo, dhi]` and the inverse demand function `P` (price as a
  function of expected demand), strictly decreasing on `𝒟`;
* Assumption 1 in the backlogging case: the expected revenue `d ↦ P(d)d` is continuous and concave
  on `𝒟`;
* the law `μ` of the i.i.d. additive noise `ε_t`: a probability measure with support in `[A, B]`,
  `A ≤ 0 ≤ B`, and zero mean;
* nonnegativity of demand, `D(p̄) + A = dlo + A ≥ 0`. -/
structure Model (L k : ℕ) where
  one_le_L : 1 ≤ L
  k_le_L : k ≤ L
  c : ℝ
  hp : ℝ
  hm : ℝ
  θ : ℝ
  γ : ℝ
  c_nonneg : 0 ≤ c
  hp_nonneg : 0 ≤ hp
  hm_nonneg : 0 ≤ hm
  θ_nonneg : 0 ≤ θ
  γ_nonneg : 0 ≤ γ
  γ_le_one : γ ≤ 1
  dlo : ℝ
  dhi : ℝ
  dlo_le_dhi : dlo ≤ dhi
  P : ℝ → ℝ
  P_strictAnti : StrictAntiOn P (Set.Icc dlo dhi)
  revenue_continuous : ContinuousOn (fun d => P d * d) (Set.Icc dlo dhi)
  revenue_concave : ConcaveOn ℝ (Set.Icc dlo dhi) (fun d => P d * d)
  μ : Measure ℝ
  isProb : IsProbabilityMeasure μ
  A : ℝ
  B : ℝ
  A_nonpos : A ≤ 0
  B_nonneg : 0 ≤ B
  support : μ (Set.Icc A B)ᶜ = 0
  mean_zero : ∫ x, x ∂μ = 0
  demand_nonneg : 0 ≤ dlo + A

namespace Model

variable {L k : ℕ} (M : Model L k)

/-- The feasible state space `𝒮 = 𝒱_{l−1,l−1}` (p. 289): `s_1 ≤ ⋯ ≤ s_{l−1}`. -/
def StateSpace (L : ℕ) : Set (Fin L → ℝ) := V L L

/-- `s_1`, the first coordinate of the state. -/
def s1 (s : Fin L → ℝ) : ℝ := s ⟨0, by have := M.one_le_L; omega⟩

/-- `s_{l−1}`, the last coordinate of the state (the inventory position). -/
def sLast (s : Fin L → ℝ) : ℝ := s ⟨L - 1, by have := M.one_le_L; omega⟩

/-- The extended vector `(s_1, …, s_{l−1}, s_l)`, `s_l` the order-up-to level. -/
def ext (s : Fin L → ℝ) (sl : ℝ) : Fin (L + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) s sl

/-- `s_{l−k}`, the net inventory level: coordinate `L − k` of `(s_1, …, s_l)`. -/
def netInv (s : Fin L → ℝ) (sl : ℝ) : ℝ := ext s sl ⟨L - k, by have := M.k_le_L; omega⟩

/-- The dynamics (2): `s̃ = (s_2 − a, …, s_l − a)`, i.e. `s̃_i = s_{i+1} − a`. -/
def next (s : Fin L → ℝ) (sl a : ℝ) : Fin L → ℝ := fun i => ext s sl i.succ - a

/-- The depletion interval of (5): `s_1 ∨ d_t ≤ a ≤ s_{l−k} ∨ d_t`, with `d_t = d + ε`. -/
def depletionSet (s : Fin L → ℝ) (sl d ε : ℝ) : Set ℝ :=
  Set.Icc (max (M.s1 s) (d + ε)) (max (M.netInv s sl) (d + ε))

/-- `φ_t(s, s_l, d, a | ε)` of (6), with continuation `F` standing for `f_{t+1}` and `d_t = d + ε`:
`γc s̃_{l−1} − c s_l − θ(a − d_t) − h⁺(s_{l−k} − a)⁺ − h⁻(a − s_{l−k})⁺ + γ F(s̃)`. -/
noncomputable def phi (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d a ε : ℝ) : ℝ :=
  M.γ * M.c * M.sLast (next s sl a) - M.c * sl - M.θ * (a - (d + ε))
    - M.hp * max (M.netInv s sl - a) 0 - M.hm * max (a - M.netInv s sl) 0
    + M.γ * F (next s sl a)

/-- `g_t(s, s_l, d | ε)` of (5): the supremum of `φ_t` over the depletion interval. -/
noncomputable def g (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d ε : ℝ) : ℝ :=
  sSup ((fun a => M.phi F s sl d a ε) '' M.depletionSet s sl d ε)

/-- `g̃_t(s, s_l, d | ε)` (p. 291): the supremum of `φ_t` over `a ≥ s_1 ∨ d_t`, without the upper
bound `a ≤ s_{l−k} ∨ d_t`. -/
noncomputable def gtilde (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d ε : ℝ) : ℝ :=
  sSup ((fun a => M.phi F s sl d a ε) '' Set.Ici (max (M.s1 s) (d + ε)))

/-- `G_t(s, s_l, d) = R(d, s_{l−k}) + E[g_t(s, s_l, d | ε_t)]` with `R(d, y) = P(d)d` in the
backlogging case (p. 290). -/
noncomputable def G (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d : ℝ) : ℝ :=
  M.P d * d + ∫ ε, M.g F s sl d ε ∂M.μ

/-- The feasible decisions of (4): `s_l ≥ s_{l−1}` and `d ∈ 𝒟`. -/
def orderSet (s : Fin L → ℝ) : Set (ℝ × ℝ) :=
  {p | M.sLast s ≤ p.1 ∧ p.2 ∈ Set.Icc M.dlo M.dhi}

/-- The modified profit-to-go `f` with `n` periods to go: `f 0 = 0` (`f_{T+1} = 0`) and
`f (n+1)(s) = sup_{s_l ≥ s_{l−1}, d ∈ 𝒟} G(s, s_l, d)` with continuation `f n`, which is (4). -/
noncomputable def f : ℕ → (Fin L → ℝ) → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun s => sSup ((fun p : ℝ × ℝ => M.G (f n) s p.1 p.2) '' M.orderSet s)

/-- `φ_t` for the period with `n + 1` periods to go (continuation `f n`). -/
noncomputable def phiN (n : ℕ) (s : Fin L → ℝ) (sl d a ε : ℝ) : ℝ := M.phi (M.f n) s sl d a ε

/-- `g_t` for the period with `n + 1` periods to go. -/
noncomputable def gN (n : ℕ) (s : Fin L → ℝ) (sl d ε : ℝ) : ℝ := M.g (M.f n) s sl d ε

/-- `g̃_t` for the period with `n + 1` periods to go. -/
noncomputable def gtildeN (n : ℕ) (s : Fin L → ℝ) (sl d ε : ℝ) : ℝ := M.gtilde (M.f n) s sl d ε

/-- `G_t` for the period with `n + 1` periods to go. -/
noncomputable def GN (n : ℕ) (s : Fin L → ℝ) (sl d : ℝ) : ℝ := M.G (M.f n) s sl d

/-- `g_t` as a function of the joint vector `w = (s_1, …, s_{l−1}, s_l, d) : Fin (L+2) → ℝ`. -/
noncomputable def gJoint (n : ℕ) (ε : ℝ) (w : Fin (L + 2) → ℝ) : ℝ :=
  M.gN n (fun i : Fin L => w ⟨i, by omega⟩) (w ⟨L, by omega⟩) (w ⟨L + 1, by omega⟩) ε

/-- `φ_t` as a function of the joint vector `w = (s_1, …, s_{l−1}, s_l, d, a) : Fin (L+3) → ℝ`. -/
noncomputable def phiJoint (n : ℕ) (ε : ℝ) (w : Fin (L + 3) → ℝ) : ℝ :=
  M.phiN n (fun i : Fin L => w ⟨i, by omega⟩) (w ⟨L, by omega⟩) (w ⟨L + 1, by omega⟩)
    (w ⟨L + 2, by omega⟩) ε

/-- `(s_l, d)` is an optimal order-up-to level and demand level at the state `s`, with `n + 1`
periods to go: it is feasible for (4) and attains `f (n+1)(s)`. -/
def IsOptOrder (n : ℕ) (s : Fin L → ℝ) (sl d : ℝ) : Prop :=
  (sl, d) ∈ M.orderSet s ∧ M.GN n s sl d = M.f (n + 1) s

/-- `(s_l, d)` is the componentwise-largest optimal decision at `s` (the paper's `s_{lt}(s)`,
`d_t(s)`): it is optimal and every optimal `(s_l', d')` has `s_l' ≤ s_l` and `d' ≤ d`. -/
def IsLargestOptOrder (n : ℕ) (s : Fin L → ℝ) (sl d : ℝ) : Prop :=
  M.IsOptOrder n s sl d ∧ ∀ sl' d', M.IsOptOrder n s sl' d' → sl' ≤ sl ∧ d' ≤ d

/-- `a` is an optimal depletion at `(s, s_l, d | ε)`, with `n + 1` periods to go: it lies in the
interval of (5) and attains `g_t`. -/
def IsOptDepletion (n : ℕ) (s : Fin L → ℝ) (sl d ε a : ℝ) : Prop :=
  a ∈ M.depletionSet s sl d ε ∧ M.phiN n s sl d a ε = M.gN n s sl d ε

/-- `a` is the largest optimal depletion at `(s, s_l, d | ε)` (the paper's `a_t(s, s_l, d | ε_t)`). -/
def IsLargestOptDepletion (n : ℕ) (s : Fin L → ℝ) (sl d ε a : ℝ) : Prop :=
  IsGreatest {a' | M.IsOptDepletion n s sl d ε a'} a

end Model

end PerishablePricing.Backlog


