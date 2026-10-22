-- Prove2me | Definitions.Def_PartialLostSales_ACOI_Model
-- name    : PartialLostSales_ACOI_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:52.222574+00:00
-- url     : https://prove2.me/theorems/563bef74-207e-4f8c-9080-3fee02c6cc3f
-- title:
--   §2.1 and §3.1, pp. 7–11 — lost-sales inventory observed only at zero: cost c, beliefs with finite second moment, posterior H, belief kernel q, belief cost c̄
-- statement:
--   This file sets up the partially observed lost-sales inventory model of Bai, Chen and Stolyar and the completely observable MDP (COMDP) on beliefs that the paper works with.
--
--   **Model (§2.1, pp. 7–8).** In each period the decision maker holds inventory $x_t\in\mathbb R_+$, orders $a_t\in\mathbb A=[0,K]$ (delivered immediately, ordering cost zero), and then an i.i.d. demand $D_t\sim D$ is realized. Unmet demand is lost and the next inventory level is
--   $$x_{t+1}=(x_t+a_t-D_t)^+ .$$
--   The expected one-period cost is
--   $$c(x,a)=\mathbb E_D\big[h^+(x+a-D)^+ + h^-(x+a-D)^-\big].$$
--   The **standing assumptions** are: $K>0$; $h^+,h^->0$; $D$ is a probability distribution with a density, a finite positive mean and a strictly positive variance; and $D\ge 0$.
--
--   **Beliefs.** The inventory level is observed only when it is $0$. The COMDP state is the belief $z$, the conditional distribution of the current inventory level. By Assumption 1 (p. 8) the state space is the set $\mathbb P_2(\mathbb R_+)$ of probability measures on $\mathbb R_+$ with finite second moment $\int x^2\,z(dx)<\infty$, with the topology of weak convergence. $\delta_0$ is the Dirac belief at inventory $0$.
--
--   **Transition (§3.1, pp. 9–10).** Given $z$ and $a$, let $\nu_{z,a}$ be the law of $(x+a-D)^+$ with $x\sim z$ independent of $D$. The signal $y=\mathbf 1\{x_{t+1}>0\}$ has law $R(\cdot\mid z,a)$, with
--   $$R(1\mid z,a)=\nu_{z,a}\big((0,\infty)\big),\qquad R(0\mid z,a)=\nu_{z,a}(\{0\}).$$
--   The posterior is $H(z,a,0)=\delta_0$ and $H(z,a,1)=\nu_{z,a}(\,\cdot\mid(0,\infty))$, the law of $x_{t+1}$ conditioned on $x_{t+1}>0$; this is the paper's density $p_{t+1}$. The belief transition kernel (6) and the belief cost (7) are
--   $$q(\cdot\mid z,a)=R(0\mid z,a)\,\delta_{\delta_0}+R(1\mid z,a)\,\delta_{H(z,a,1)},\qquad \bar c(z,a)=\int c(x,a)\,z(dx).$$
--
--   **COMDP.** An MDP on $\mathbb P_2(\mathbb R_+)\times\mathbb A$ (in the sense of the published `FeinbergLiang.ACOE.MDP`) *is the COMDP* when its cost is $\bar c$ (with lower bound $0$) and its transition probability is $q$.
--
--   **Assumption (B), paper version (p. 11).** For a general MDP: (i) $w^*=\inf_x w(x)<\infty$; (ii) there is $\alpha_*\in(0,1)$ such that $\sup_{\alpha\in[\alpha_*,1)}u_\alpha(x)<\infty$ for every state $x$.
--
--   **Coupled processes of Lemma 4 (p. 14).** On a probability space, demands $D_t$ and order amounts $\zeta_t\in[0,K]$ (a control rule, which may anticipate) drive $x_0=x$, $x_{t+1}=(x_t+\zeta_t-D_t)^+$. Its expected discounted cost is
--   $$V^\zeta_\alpha(x)=\mathbb E\sum_{t\ge0}\alpha^t\big(h^+(x_t+\zeta_t-D_t)^++h^-(x_t+\zeta_t-D_t)^-\big).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Inventory levels live in `ℝ≥0` and actions in the subtype `[0, K]` of `ℝ`, both with the Euclidean topology. Beliefs are the subtype `Bel` of `ProbabilityMeasure ℝ≥0` with finite second moment. It carries the subspace of Mathlib's weak-convergence topology and of Mathlib's σ-algebra on `ProbabilityMeasure`, which is the Giry σ-algebra. For the Polish space $\mathbb R_+$ the Giry σ-algebra is the Borel σ-algebra of the weak topology, so this is the paper's $\mathscr B(\mathbb P(\mathbb X))$. All costs are in $[0,\infty]$.
--
--   The nonnegativity of demand is **added**; the paper takes it for granted in calling $D$ a demand. The variance condition is stated with the extended variance, so infinite variance is allowed, as on the page.
--
--   Two `if … then … else` branches are totality devices whose else branches never matter. The first is the posterior when $R(1\mid z,a)\in\{0,\infty\}$: it then has weight $0$ (under the standing assumptions $R(1\mid z,a)\le 1$). The second maps a posterior to `Bel`: the posterior of a belief with finite second moment again has finite second moment, since $x_{t+1}\le x_t+K$.
--
--   Periods of Lemma 4 are indexed from $0$ with weight $\alpha^t$; the paper uses $t\ge1$ with $\alpha^{t-1}$. The costs of Lemma 4 are realized costs, because the control rule may anticipate future demand (p. 14).
-- source:
--   Bai, Chen & Stolyar, Average Cost Optimality in Partially Observed Lost-Sales Inventory Systems, SSRN preprint 3865728, pp. 7–11 and 14, §2.1 (1)–(4), Assumption 1, §3.1 (5)–(7), Assumption (B), §4 (definition of V^ζ_α)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP

namespace PartialLostSales.ACOI

open MeasureTheory ProbabilityTheory FeinbergLiang.ACOE
open scoped ENNReal NNReal

/-- The primitive data of the lost-sales model of §2.1 (p. 7): the order capacity `K`
(orders lie in `[0, K]`), the unit holding cost `h⁺`, the unit lost-sales penalty `h⁻`,
and the distribution of the one-period demand `D`. -/
structure Params where
  /-- the order capacity: orders lie in `[0, K]` -/
  K : ℝ
  /-- the unit holding cost `h⁺` -/
  hplus : ℝ
  /-- the unit lost-sales penalty cost `h⁻` -/
  hminus : ℝ
  /-- the distribution of the one-period demand `D` -/
  demand : Measure ℝ

/-- The standing assumptions of §2.1 (p. 7): `K > 0`; `h⁺, h⁻ > 0`; `D` is a probability
distribution with a density (absolutely continuous w.r.t. Lebesgue measure), with a finite
positive mean and a strictly positive (possibly infinite) variance. Added: `D ≥ 0` almost surely (demand is
nonnegative). -/
def Standing (P : Params) : Prop :=
  0 < P.K ∧ 0 < P.hplus ∧ 0 < P.hminus ∧
  IsProbabilityMeasure P.demand ∧ P.demand ≪ volume ∧
  Integrable id P.demand ∧ 0 < ∫ s, s ∂P.demand ∧
  0 < evariance id P.demand ∧
  P.demand (Set.Iio 0) = 0

/-- The action space `𝔸 = [0, K]` (p. 8). -/
abbrev Act (P : Params) : Type := Set.Icc (0 : ℝ) P.K

/-- The expected one-period cost `c(x, a) = E_D[h⁺(x + a − D)⁺ + h⁻(x + a − D)⁻]` (p. 8), for
inventory level `x ≥ 0` and order quantity `a`. -/
noncomputable def c (P : Params) (x : ℝ≥0) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ s, ENNReal.ofReal (P.hplus * max ((x : ℝ) + a - s) 0 + P.hminus * max (s - x - a) 0)
    ∂P.demand

/-- The second moment `∫ x² μ(dx)` of a measure on `ℝ₊`, in `[0, ∞]`. -/
noncomputable def secondMoment (μ : Measure ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ x, (x : ℝ≥0∞) ^ 2 ∂μ

/-- The COMDP state space: probability distributions `z` of the inventory level on `ℝ₊` with a
finite second moment (Assumption 1, p. 8; the process "lives" on these states, pp. 9, 11).
Topology: the subspace topology of weak convergence; measurable structure: the subspace of
Mathlib's σ-algebra on `ProbabilityMeasure ℝ≥0`. -/
abbrev Bel (_P : Params) : Type :=
  {z : ProbabilityMeasure ℝ≥0 // secondMoment (z : Measure ℝ≥0) < ⊤}

/-- A probability measure on `ℝ₊` as a COMDP state. This is a totality device: it is applied
only to posteriors of beliefs with a finite second moment, which again have a finite second
moment (`x_{t+1} ≤ x_t + K`), so the `else` branch (value `δ₀`) is never used. -/
noncomputable def toBel (P : Params) (μ : ProbabilityMeasure ℝ≥0) : Bel P :=
  if h : secondMoment (μ : Measure ℝ≥0) < ⊤ then ⟨μ, h⟩
  else ⟨⟨Measure.dirac 0, inferInstance⟩, by
    simp [secondMoment, lintegral_dirac]⟩

/-- The atomic belief `δ₀` centered at inventory level `0` (p. 9). -/
noncomputable def δ0 (P : Params) : Bel P :=
  ⟨⟨Measure.dirac 0, inferInstance⟩, by simp [secondMoment, lintegral_dirac]⟩

/-- The law of the next inventory level `x_{t+1} = (x_t + a − D_t)⁺` (eq. (1), (2)) when
`x_t ∼ z` is independent of `D_t`. -/
noncomputable def nextLaw (P : Params) (z : ProbabilityMeasure ℝ≥0) (a : ℝ) : Measure ℝ≥0 :=
  ((z : Measure ℝ≥0).prod P.demand).map (fun p : ℝ≥0 × ℝ => Real.toNNReal ((p.1 : ℝ) + a - p.2))

/-- `R(1 | z, a)` (eq. (5)): the probability that `y_{t+1} = 1`, i.e. `x_{t+1} > 0`. -/
noncomputable def R1 (P : Params) (z : ProbabilityMeasure ℝ≥0) (a : ℝ) : ℝ≥0∞ :=
  nextLaw P z a (Set.Ioi 0)

/-- `R(0 | z, a)` (eq. (5)): the probability that `y_{t+1} = 0`, i.e. `x_{t+1} = 0`. -/
noncomputable def R0 (P : Params) (z : ProbabilityMeasure ℝ≥0) (a : ℝ) : ℝ≥0∞ :=
  nextLaw P z a {0}

/-- The posterior `H(z, a, 1)` (p. 9, (ii)): the conditional law of `x_{t+1}` given
`x_{t+1} > 0`. When `R(1 | z, a) = 0` the observation `y = 1` has probability zero and the
value (here `δ₀`) is immaterial. -/
noncomputable def post (P : Params) (z : ProbabilityMeasure ℝ≥0) (a : ℝ) :
    ProbabilityMeasure ℝ≥0 :=
  if h : nextLaw P z a (Set.Ioi 0) ≠ 0 ∧ nextLaw P z a (Set.Ioi 0) ≠ ⊤ then
    ⟨ProbabilityTheory.cond (nextLaw P z a) (Set.Ioi 0),
      ProbabilityTheory.cond_isProbabilityMeasure_of_finite h.1 h.2⟩
  else ⟨Measure.dirac 0, inferInstance⟩

/-- The COMDP transition `q(· | z, a)` (eq. (6)): with probability `R(0 | z, a)` the next belief
is `δ₀` (`H(z, a, 0) = δ₀`), with probability `R(1 | z, a)` it is the posterior `H(z, a, 1)`. -/
noncomputable def qBel (P : Params) (z : Bel P) (a : Act P) : Measure (Bel P) :=
  R0 P z.1 a • Measure.dirac (δ0 P) + R1 P z.1 a • Measure.dirac (toBel P (post P z.1 a))

/-- The COMDP one-step cost `c̄(z, a) = ∫ c(x, a) z(dx)` (eq. (7)). -/
noncomputable def cbar (P : Params) (z : Bel P) (a : Act P) : ℝ≥0∞ :=
  ∫⁻ x, c P x a ∂(z.1 : Measure ℝ≥0)

/-- `M` is the COMDP of §3.1 (pp. 9–10): cost `c̄` (with lower bound `0`) and transition
probability `q`. -/
def IsCOMDP (P : Params) (M : MDP (Bel P) (Act P)) : Prop :=
  M.lower = 0 ∧ (∀ z a, M.cost z a = cbar P z a) ∧ ∀ z a, M.q (z, a) = qBel P z a

/-- Assumption (B) of the paper (p. 11), for a general MDP: (i) `w* = inf_x w(x) < ∞`;
(ii) there is `α* ∈ (0, 1)` with `sup_{α ∈ [α*, 1)} u_α(x) < ∞` for every state `x`. -/
def AssumptionBpaper {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (M : MDP X A) :
    Prop :=
  (⨅ x, wOpt M x) ≠ ⊤ ∧
    ∃ αstar ∈ Set.Ioo (0 : ℝ) 1, ∀ x, (⨆ α ∈ Set.Ico αstar 1, uRel M α x) ≠ ⊤

/-- The inventory process of Lemma 4 (p. 14), driven by demands `D t` and order amounts
`ζ t` (a control rule): `inv 0 = x`, `inv (t + 1) = (inv t + ζ t − D t)⁺` (eq. (1)).
Periods are indexed from `0`. -/
noncomputable def inv {Ω : Type*} (x : ℝ) (ζ D : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x
  | t + 1 => fun ω => max (inv x ζ D t ω + ζ t ω - D t ω) 0

/-- The realized cost of period `t` in Lemma 4: `h⁺(x_t + ζ_t − D_t)⁺ + h⁻(x_t + ζ_t − D_t)⁻`. -/
noncomputable def stageCost (P : Params) (y a d : ℝ) : ℝ :=
  P.hplus * max (y + a - d) 0 + P.hminus * max (d - y - a) 0

/-- `V^ζ_α(x)` (p. 14): the expected total discounted cost of the inventory process started at
`x` under the control rule `ζ`, `E Σ_{t ≥ 0} α^t (h⁺(x_t + ζ_t − D_t)⁺ + h⁻(x_t + ζ_t − D_t)⁻)`. -/
noncomputable def Vζ {Ω : Type*} [MeasurableSpace Ω] (P : Params) (μ : Measure Ω) (α x : ℝ)
    (ζ D : ℕ → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' t, ENNReal.ofReal (α ^ t) *
    ENNReal.ofReal (stageCost P (inv x ζ D t ω) (ζ t ω) (D t ω)) ∂μ

end PartialLostSales.ACOI


