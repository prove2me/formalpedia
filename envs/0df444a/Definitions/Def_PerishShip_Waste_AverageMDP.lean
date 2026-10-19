-- Prove2me | Definitions.Def_PerishShip_Waste_AverageMDP
-- name    : PerishShip_Waste_AverageMDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:10:42.484124+00:00
-- url     : https://prove2.me/theorems/a6f6d8f4-38c8-4b8f-bc11-9b7641b44c81
-- title:
--   §4.2, p. 15 — Markov policies and long-run expected cost for a controlled process with i.i.d. shocks
-- statement:
--   Let $S$ be a countable state space, $A$ an action space, and $\Omega$ a countable shock space. A fixed probability law $p$ supplies an independent shock each period. Given a state $s$, action $a$, and shock $\omega$, the next state is $F(s,a,\omega)$. A deterministic Markov policy $\sigma_t(s)$ may vary with period $t$.
--
--   From an initial state $s_0$, the module defines the induced state law $P_t$ and, for a nonnegative extended cost $c$, the expected period cost and its Cesàro average:
--
--   $$
--   P_0=\delta_{s_0},\qquad P_{t+1}=\operatorname{Law}\bigl(F(s,\sigma_t(s),\omega)\bigr)_{s\sim P_t,\,\omega\sim p},\qquad C_T=\frac1T\sum_{t=0}^{T-1}\sum_sP_t(s)\sum_\omega p(\omega)c(s,\sigma_t(s),\omega).
--   $$
--
--   The upper and lower long-run costs are $\limsup_{T\to\infty} C_T$ and $\liminf_{T\to\infty} C_T$. This general layer makes the paper's long-run waste criteria explicit and is reusable for other discrete controlled systems.
--
--   **Formalization Note** Costs and expectations take values in $[0,\infty]$; the value at $T=0$ is irrelevant to the long-run limits. The policy class is time-dependent deterministic Markov, and shocks are i.i.d.
-- source:
--   Akkaş & Honhon, Shipment policies for products with fixed shelf lives: impact on profits and waste, SSRN 3247290 (manuscript of 2021-03-20), p. 15 (PDF 15), §4.2 and §4.2.1

import Mathlib

namespace PerishShip.Waste

/-- A deterministic Markov decision rule, allowed to change with time. -/
abbrev MarkovPolicy (S A : Type) := ℕ → S → A

/-- State law for a controlled process with independent, identically distributed shocks. -/
noncomputable def controlledStateLaw {S A Ω : Type} [Countable S] [Countable Ω]
    (demand : PMF Ω) (step : S → A → Ω → S) (σ : MarkovPolicy S A)
    (s₀ : S) : ℕ → PMF S
  | 0 => PMF.pure s₀
  | t + 1 => (controlledStateLaw demand step σ s₀ t).bind
      (fun s => demand.map (step s (σ t s)))

/-- Expected nonnegative one-period cost, including the current shock. -/
noncomputable def controlledExpectedCost {S A Ω : Type} [Countable S] [Countable Ω]
    (demand : PMF Ω) (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (σ : MarkovPolicy S A) (s₀ : S) (t : ℕ) : ENNReal :=
  ∑' s, controlledStateLaw demand step σ s₀ t s *
    ∑' ω, demand ω * cost s (σ t s) ω

/-- The average of the expected period costs over the first `T` periods. -/
noncomputable def controlledCesaro {S A Ω : Type} [Countable S] [Countable Ω]
    (demand : PMF Ω) (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (σ : MarkovPolicy S A) (s₀ : S) (T : ℕ) : ENNReal :=
  (∑ t ∈ Finset.range T, controlledExpectedCost demand step cost σ s₀ t) / T

/-- Upper long-run Cesàro average. -/
noncomputable def controlledAvgUpper {S A Ω : Type} [Countable S] [Countable Ω]
    (demand : PMF Ω) (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (σ : MarkovPolicy S A) (s₀ : S) : ENNReal :=
  Filter.limsup (controlledCesaro demand step cost σ s₀) Filter.atTop

/-- Lower long-run Cesàro average. -/
noncomputable def controlledAvgLower {S A Ω : Type} [Countable S] [Countable Ω]
    (demand : PMF Ω) (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (σ : MarkovPolicy S A) (s₀ : S) : ENNReal :=
  Filter.liminf (controlledCesaro demand step cost σ s₀) Filter.atTop

end PerishShip.Waste


