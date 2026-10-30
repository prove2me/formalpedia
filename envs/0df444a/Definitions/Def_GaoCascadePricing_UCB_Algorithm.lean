-- Prove2me | Definitions.Def_GaoCascadePricing_UCB_Algorithm
-- name    : GaoCascadePricing_UCB_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:14:54.929417+00:00
-- url     : https://prove2.me/theorems/93c6eb2d-6b95-43dc-8202-bc865a92b249
-- title:
--   Exact UCB-Cascade objective, initialization and regret
-- statement:
--   For a history of length $n$, let $t=n+1$ and $r(t,m)=\sqrt{2\ln(t)/m}$. At each selected product-price pair, $u^e=\min\{r(t,n^e),1\}$ and $u^c=\min\{r(t,n^c),1\}$. At a nonterminal product, $u^\gamma=\min\{r(t,n^\gamma),1\}$ and $u^\zeta=r(t,n^\zeta)$, the latter uncapped as printed. Both continuation bonuses are zero at the last product. Put $u_j=u^e+u^c+u^\gamma+u^\zeta$ and $g_t(p)=\sum_j\widehat w_j(p)u_j$, where $\widehat w_j$ is empirical reach. The exact optimization objective is
--   $$U_t(p)=\rho(p;\widehat\theta_t)+\|p\|_\infty g_t(p).$$
--
--   UCB-Cascade comprises all history-dependent randomized policies whose actions of positive probability maximize this objective whenever the initialization counters are positive. Before that time the policy continues testing, with its distribution unconstrained by the optimization condition. This quantifies every unspecified testing rule and every randomized tie choice using only public history, independently of the unknown model. The first initialized calendar time is an extended natural number, allowed to be infinity; the testing branch remains in force forever if initialization never completes.
--
--   Regret at positive horizon $T$ is the finite expectation of $\sum_{t=1}^T[\rho^*(\theta)-\rho(p_t;\theta)]$, using the actual history law and including all initialization rounds. No condition on reachability, optimism, estimation accuracy or the duration of initialization is imposed.
--
--   **Formalization Note.** The algorithm is specified by the complete conditional support rule on normalized PMFs. Maximizers exist because the action set is finite and nonempty. This leaves exactly the choices unspecified by the algorithm box. A total radius at unavailable counts is never used by an enabled UCBOPT call.
-- source:
--   Gao, Jasin, Najafi and Zhang (2022), Joint Learning and Optimization for Multi-Product Pricing (and Ranking) Under a General Cascade Click Model, DOI https://doi.org/10.1287/mnsc.2021.4246; published basis, supplied manuscript-paginated PDF; §4.1, pp. 14–16, UCBOPT and algorithm box

import Definitions.Def_GaoCascadePricing_UCB_Market
import Definitions.Def_GaoCascadePricing_UCB_History

open scoped BigOperators

namespace GaoCascadePricing.UCB

/-- Uncapped confidence radius; calendar time is n+1 for a length-n history. -/
noncomputable def radius (t m : ℕ) : ℝ := Real.sqrt (2 * Real.log t / m)

/-- The printed four bonuses, including the uncapped zeta radius. -/
noncomputable def bonus {J K n : ℕ} (h : History J K n) (p : Action J K)
    (j : Fin J) : ℝ :=
  min (radius (n + 1) (ne h j (p j))) 1 +
  min (radius (n + 1) (nc h j (p j))) 1 +
  (if j.val + 1 < J then min (radius (n + 1) (ng h j)) 1 else 0) +
  (if j.val + 1 < J then radius (n + 1) (nz h j) else 0)

noncomputable def weightedBonus {J K n : ℕ} (θ : Cascade J K)
    (h : History J K n) (p : Action J K) : ℝ :=
  ∑ j, reach θ p j * bonus h p j

noncomputable def objective {J K n : ℕ} (M : Market J K)
    (h : History J K n) (p : Action J K) : ℝ :=
  revenue M (estimate h) p + priceNorm M p * weightedBonus (estimate h) h p

/-- All resolutions of the printed algorithm: test freely before initialization;
afterwards randomize only over exact UCBOPT maximizers. The rule sees only public history. -/
def IsUCBCascade {J K : ℕ} (M : Market J K) (π : Policy J K) : Prop :=
  ∀ n (h : History J K n), Initialized h →
    ∀ p, (π n h) p ≠ 0 → ∀ q, objective M h q ≤ objective M h p

/-- First initialized calendar time of a path, possibly infinity. -/
noncomputable def initializationTime {J K : ℕ}
    (h : ℕ → Action J K × Observation J) : ENat := by
  classical
  exact ⨅ n : ℕ, if Initialized (fun i : Fin n => h i.val) then (n + 1 : ℕ) else ⊤

/-- Regret from period one, including every testing round. -/
noncomputable def regret {J K : ℕ} (M : Market J K) (θ : Cascade J K)
    (π : Policy J K) (T : ℕ) : ℝ :=
  ∑ h : History J K T, historyWeight θ π h *
    ∑ i, (optimalRevenue M θ - revenue M θ (h i).1)

end GaoCascadePricing.UCB


