-- Prove2me | Definitions.Def_PlatformPrecommit_KS_Setting
-- name    : PlatformPrecommit_KS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:07.462619+00:00
-- url     : https://prove2.me/theorems/f775bf92-35b0-419c-81f3-1ba4279e130e
-- title:
--   §3 and §3.5 — two-sided platform market, quantity game, and capacity-precommitment game
-- statement:
--   Two platforms face a market of potential size $\Omega>0$. Let $\gamma,\beta\in[0,1)$ measure substitution on the consumer and service-provider sides. Given prices $p_i$ and wages $w_i$, demand and supply are
--
--   $$d_i(p)=[\Omega-p_i+\gamma p_j]^+,\qquad s_i(w)=[w_i-\beta w_j]^+,\qquad j\ne i.$$
--
--   In **quantity competition**, each platform chooses $z_i\ge0$. Market-clearing prices and wages are $p_i=((1+\gamma)\Omega-z_i-\gamma z_j)/(1-\gamma^2)$ and $w_i=(z_i+\beta z_j)/(1-\beta^2)$, giving profit $(p_i-w_i)z_i$. A quantity equilibrium permits every unilateral deviation to another nonnegative quantity.
--
--   In **capacity precommitment**, platforms first choose $q_i\ge0$ and then jointly set prices and wages. Their matches and profits are $m_i=\min\{d_i(p),s_i(w),q_i\}$ and $(p_i-w_i)m_i$. A second-stage Nash equilibrium permits every joint price-and-wage deviation by either platform. A subgame-perfect equilibrium comprises first-stage capacities and a continuation profile for every admissible capacity pair. Every continuation is a second-stage Nash equilibrium; for each platform, if some equilibrium gives it positive profit, the selected continuation gives that platform positive profit. No unilateral capacity deviation, followed by its specified continuation, increases profit.
--
--   These definitions connect the paper's two competition modes to the equilibrium comparisons in Lemmas 6–7 and Proposition 1.
--
--   **Formalization Note** The quantity game reuses the published pure Nash predicate for nonnegative real actions from `CachonCoord.Proportional.Nash`. Prices and wages range over all real numbers; quantities and capacities are nonnegative. The rival of `Fin 2` platform 0 is 1, and conversely. The per-platform positive-profit continuation selection is added to resolve the manuscript's unqualified equilibrium claim: zero-profit subgame equilibria otherwise support off-path punishments. No equilibrium outcome is built from the paper's closed forms by definition.
-- source:
--   Hu, Liu, Precommitments in Two-Sided Market Competition, submitted manuscript (SSRN 3734828; TSpace), pp. 8–9, (1)–(3); pp. 14–15, §3.5; Online Appendix p. 1, (A.1)–(A.3); Online Appendix p. 32, (F.3)

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Nash

namespace PlatformPrecommit.KS

noncomputable section

/-- The parameters of the two-sided platform market. -/
structure Model where
  Ω : ℝ
  β : ℝ
  γ : ℝ

/-- The paper's substitution ranges, with positive potential market size. -/
def Model.Standing (M : Model) : Prop :=
  0 < M.Ω ∧ 0 ≤ M.γ ∧ M.γ < 1 ∧ 0 ≤ M.β ∧ M.β < 1

/-- The other of the two platforms. -/
def rival : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

/-- Demand (1), with its positive part. -/
def Model.demand (M : Model) (p : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  max (M.Ω - p i + M.γ * p (rival i)) 0

/-- Supply (2), with its positive part. -/
def Model.supply (M : Model) (w : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  max (w i - M.β * w (rival i)) 0

/-- Market-clearing price for quantity competition (proof of Lemma 6). -/
def Model.qPrice (M : Model) (z : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  ((1 + M.γ) * M.Ω - z i - M.γ * z (rival i)) / (1 - M.γ ^ 2)

/-- Market-clearing wage for quantity competition (proof of Lemma 6). -/
def Model.qWage (M : Model) (z : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  (z i + M.β * z (rival i)) / (1 - M.β ^ 2)

/-- Profit (F.3) in the quantity game. -/
def Model.qProfit (M : Model) (z : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  (M.qPrice z i - M.qWage z i) * z i

/-- Nash equilibrium of the quantity game over nonnegative matching quantities. -/
def Model.IsQNE (M : Model) (z : Fin 2 → ℝ) : Prop :=
  CachonCoord.Proportional.IsNash (fun i x => M.qProfit x i) z

/-- Matches in the price-and-wage subgame after capacity commitments. -/
def Model.ksMatch (M : Model) (q : Fin 2 → ℝ)
    (pw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (i : Fin 2) : ℝ :=
  min (min (M.demand pw.1 i) (M.supply pw.2 i)) (q i)

/-- Profit in the capacity-constrained price-and-wage subgame. -/
def Model.ksProfit (M : Model) (q : Fin 2 → ℝ)
    (pw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (i : Fin 2) : ℝ :=
  (pw.1 i - pw.2 i) * M.ksMatch q pw i

/-- Subgame Nash equilibrium; a platform changes its price and wage jointly. -/
def Model.IsSubNE (M : Model) (q : Fin 2 → ℝ)
    (pw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : Prop :=
  ∀ i (a b : ℝ),
    M.ksProfit q (Function.update pw.1 i a, Function.update pw.2 i b) i ≤
      M.ksProfit q pw i

/-- Select a positive profit for each platform whenever an equilibrium permits it.
This also covers a subgame in which the rival committed zero capacity. -/
def Model.IsSelSubNE (M : Model) (q : Fin 2 → ℝ)
    (pw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : Prop :=
  M.IsSubNE q pw ∧
    ∀ i, (∃ pw', M.IsSubNE q pw' ∧ 0 < M.ksProfit q pw' i) →
      0 < M.ksProfit q pw i

/-- Subgame-perfect equilibrium of the capacity-precommitment game, with the
per-platform positive-profit selection in every admissible continuation subgame. -/
def Model.IsSPE (M : Model) (q : Fin 2 → ℝ)
    (σ : (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ)) : Prop :=
  (∀ y, (∀ i, 0 ≤ y i) → M.IsSelSubNE y (σ y)) ∧
  (∀ i, 0 ≤ q i) ∧
  (∀ i v, 0 ≤ v →
    M.ksProfit (Function.update q i v) (σ (Function.update q i v)) i ≤
      M.ksProfit q (σ q) i)

end

end PlatformPrecommit.KS


