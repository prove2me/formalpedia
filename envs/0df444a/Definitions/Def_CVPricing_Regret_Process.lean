-- Prove2me | Definitions.Def_CVPricing_Regret_Process
-- name    : CVPricing_Regret_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T10:14:35.29817+00:00
-- url     : https://prove2.me/theorems/f03880e0-9be4-4596-9ad9-400656bfd1c2
-- title:
--   §2, pp. 773–774 and eq. (9) — the stochastic demand process, condition (2), the regret and the random time T_ρ
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space with a filtration $(\mathcal F_t)_{t \ge 0}$, where $\mathcal F_t$ is the information available after period $t$. Random prices $p_t$ and demands $d_t$ ($t \ge 1$) follow the demand model when $p_t$ is $\mathcal F_{t-1}$-measurable, $d_t$ is $\mathcal F_t$-measurable, and the noise $e_t = d_t - h(a_0^{(0)} + a_1^{(0)} p_t)$ satisfies
--
--   $$\mathbb E[e_t \mid \mathcal F_{t-1}] = 0, \qquad \mathbb E[e_t^2 \mid \mathcal F_{t-1}] = \sigma^2 v\big(h(a_0^{(0)} + a_1^{(0)} p_t)\big),$$
--
--   and, for some $r > 3$,
--
--   $$\sup_{t \in \mathbb N} \mathbb E\big[|e_t|^r \mid \mathcal F_{t-1}\big] < \infty \quad \text{a.s.} \tag{2}$$
--
--   The **regret** after $T$ periods is
--
--   $$\operatorname{Regret}(T) = \mathbb E\Big[\sum_{t=1}^T r(p_{\mathrm{opt}}, a^{(0)}) - r(p_t, a^{(0)})\Big].$$
--
--   For $\rho > 0$ the random time
--
--   $$T_\rho = \sup\{t \in \mathbb N \mid \text{there is no solution } \hat a_t \text{ of (3) such that } \|\hat a_t - a^{(0)}\| \le \rho\} \tag{9}$$
--
--   takes values in $\mathbb N \cup \{\infty\}$ ($\|\cdot\|$ Euclidean). Finally $\hat a_t$ denotes the MQLE along a path, a root of (3) when one exists.
--
--   **Formalization Note** Only the first two conditional moments and (2) are imposed, as the paper's analysis uses (p. 771); the page's statement that $D_t(p_t)$ is distributed as $D(p)$, independently across periods given the prices, is not encoded. The filtration may be larger than the history of prices and demands; the natural filtration is a special case. $e_t$, $e_t^2$ and $|e_t|^r$ are assumed integrable so that the conditional expectations are genuine. The empty supremum in (9) is $0$. The MQLE along a path is chosen by choice when a root exists and is $(0,0)$ otherwise; statements only evaluate it where a root exists.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 773 (PDF 5), §2, eqs. (1)–(2); p. 774 (PDF 6), regret; p. 776 (PDF 8), eq. (9)

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP

open MeasureTheory KeskinZeevi.SufficientConditions

namespace CVPricing.Regret

/-- The demand noise `e_t = d_t − h(a₀⁽⁰⁾ + a₁⁽⁰⁾ p_t)` of period `t` (p. 773). -/
noncomputable def noise (M : Model) {Ω : Type*} (p d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  d t ω - M.h (M.a0.1 + M.a0.2 * p t ω)

/-- The stochastic demand model of den Boer–Zwart 2014, §2, p. 773 (eqs. (1), (2)), for random prices
`p t` and demands `d t` (periods `t ≥ 1`; index `0` unused) on `(Ω, P)` with a filtration `ℱ`,
where `ℱ t` is the information available after period `t`.

* `p t` is `ℱ (t − 1)`-measurable (the price of period `t` is set from the past) and `d t` is
  `ℱ t`-measurable.
* The noise `e_t` is integrable with square-integrable values, `E[e_t | ℱ_{t−1}] = 0` (the mean in
  (1)) and `E[e_t² | ℱ_{t−1}] = σ² v(h(a₀⁽⁰⁾ + a₁⁽⁰⁾ p_t))` (the variance in (1)).
* (2): for some `r > 3`, `sup_t E[|e_t|^r | ℱ_{t−1}] < ∞` almost surely; each `|e_t|^r` is integrable,
  so that the conditional expectations are genuine.

Only the first two conditional moments and (2) are imposed (p. 771: the analysis uses only "the
relation between the first two moments and the selling price"); the page's statement that
`D_t(p_t)` is distributed as `D(p)`, independently across periods given the prices, is not encoded. -/
structure DemandModel (M : Model) {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (p d : ℕ → Ω → ℝ) : Prop where
  price_meas : ∀ t, 1 ≤ t → StronglyMeasurable[ℱ (t - 1)] (p t)
  demand_meas : ∀ t, 1 ≤ t → StronglyMeasurable[ℱ t] (d t)
  noise_integrable : ∀ t, 1 ≤ t → Integrable (noise M p d t) P
  noise_sq_integrable : ∀ t, 1 ≤ t → Integrable (fun ω => noise M p d t ω ^ 2) P
  cond_mean : ∀ t, 1 ≤ t → P[noise M p d t | ℱ (t - 1)] =ᵐ[P] 0
  cond_var : ∀ t, 1 ≤ t → P[fun ω => noise M p d t ω ^ 2 | ℱ (t - 1)] =ᵐ[P]
    fun ω => M.σ ^ 2 * M.v (M.h (M.a0.1 + M.a0.2 * p t ω))
  moment : ∃ r : ℝ, 3 < r ∧
    (∀ t, 1 ≤ t → Integrable (fun ω => |noise M p d t ω| ^ r) P) ∧
    ∀ᵐ ω ∂P, BddAbove (Set.range fun t : {t : ℕ // 1 ≤ t} =>
      (P[fun ω' => |noise M p d t.1 ω'| ^ r | ℱ (t.1 - 1)]) ω)

/-- The regret after `T` periods (p. 774):
`Regret(T) = E[Σ_{t=1}^T r(p_opt, a⁽⁰⁾) − r(p_t, a⁽⁰⁾)]`. -/
noncomputable def regret (M : Model) {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (p : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  ∫ ω, ∑ t ∈ Finset.Icc 1 T, (revenue M.h M.a0 (pOpt M) - revenue M.h M.a0 (p t ω)) ∂P

/-- The random time (9) (p. 776):
`T_ρ = sup{t ∈ ℕ | there is no solution â_t of (3) such that ‖â_t − a⁽⁰⁾‖ ≤ ρ}`, with values in
`ℕ∞` (`⊤` if the set is unbounded, `0` if it is empty). Periods `t ≥ 1`; the norm is Euclidean. -/
noncomputable def Tρ (M : Model) {Ω : Type*} (p d : ℕ → Ω → ℝ) (ρ : ℝ) (ω : Ω) : ℕ∞ :=
  sSup {n : ℕ∞ | ∃ t : ℕ, (t : ℕ∞) = n ∧ 1 ≤ t ∧
    ¬ ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) t a ∧ euclidNorm (a - M.a0) ≤ ρ}

open Classical in
/-- The MQLE `â_t` along the path `ω`: a solution of (3) if one exists (unique under
`MQLEUnique`), and the junk value `(0, 0)` otherwise. Statements only evaluate it on events where a
solution exists. -/
noncomputable def mqle (M : Model) {Ω : Type*} (p d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ × ℝ :=
  if ha : ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) t a then Classical.choose ha else 0

end CVPricing.Regret


