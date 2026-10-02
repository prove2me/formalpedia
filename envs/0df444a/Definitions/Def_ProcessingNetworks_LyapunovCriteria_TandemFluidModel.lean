-- Prove2me | Definitions.Def_ProcessingNetworks_LyapunovCriteria_TandemFluidModel
-- name    : ProcessingNetworks_LyapunovCriteria_TandemFluidModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:56:11.067771+00:00
-- url     : https://prove2.me/theorems/06af2c40-effe-4a9a-a98f-f76e21c3e418
-- title:
--   The tandem queueing network's fluid model (Figure 1.1, restated locally)
-- statement:
--   The **tandem queueing network** (Figure 1.1, Chapter 1) has two single-server stations in
--   series: external Poisson arrivals of rate $\lambda_1$ join buffer 1, served at rate $\mu_1$
--   by station 1; on completion, jobs move to buffer 2, served at rate $\mu_2$ by station 2. Both
--   stations use a non-idling FCFS policy. Its fluid model — (6.1)-(6.6) plus the non-idling
--   equation (6.7), specialized to this two-station structure — reduces to Eqs. (8.11)-(8.15):
--   $$
--   Z_1(t) = Z_1(0) + \lambda_1 t - \mu_1 T_1(t), \qquad
--   Z_2(t) = Z_2(0) + \mu_1 T_1(t) - \mu_2 T_2(t),
--   $$
--   $Z_i(t) \ge 0$, $T_i(0)=0$ with $T_i$ `1`-Lipschitz and nondecreasing, and the non-idling
--   conditions $Z_i(t) > 0 \Rightarrow \dot T_i(t) = 1$, for $i=1,2$.
--
--   `TandemFluidStable` specializes Definition 6.3 (fluid model stability) to this model:
--   $\exists \gamma > 0$ such that every solution reaches $Z_1=Z_2=0$ by $t = \gamma(Z_1(0)+Z_2(0))$.
--
--   **Formalization note.** Figure 1.1 and its fluid-model reduction (8.11)-(8.15) are Chapter 1
--   material, outside this mission series (no chunk is assigned to Chapter 1, per
--   `missions/README.md`); this mission restates the two-station system's already-reduced fluid
--   equations directly, as `BRIEF.md` instructs, rather than citing an unmissioned chapter or
--   re-deriving (8.11)-(8.15) from the general (6.1)-(6.6) plus (6.7).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 141, Eqs. (8.11)-(8.15) (Figure 1.1 restated locally)

import Mathlib

namespace ProcessingNetworks.LyapunovCriteria

/-- The fluid model of the two-station tandem queueing network (Figure 1.1, Chapter 1 — out of
series scope, restated locally per `BRIEF.md`), specialized from (6.1)-(6.6) plus the non-idling
condition (6.7): buffer 1 receives external arrivals at rate `lam1` and is served by station 1
at rate `mu1`; departures from buffer 1 feed buffer 2, served by station 2 at rate `mu2`. `Z1, Z2`
are the buffer contents, `T1, T2` the cumulative service efforts (Eqs. 8.11-8.15). -/
def TandemFluidSolution (lam1 mu1 mu2 : ℝ) (Z1 Z2 T1 T2 : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → Z1 t = Z1 0 + lam1 * t - mu1 * T1 t) ∧
  (∀ t : ℝ, 0 ≤ t → Z2 t = Z2 0 + mu1 * T1 t - mu2 * T2 t) ∧
  (∀ t : ℝ, 0 ≤ t → 0 ≤ Z1 t ∧ 0 ≤ Z2 t) ∧
  (T1 0 = 0 ∧ T2 0 = 0) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → 0 ≤ T1 t - T1 s ∧ T1 t - T1 s ≤ t - s) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → 0 ≤ T2 t - T2 s ∧ T2 t - T2 s ≤ t - s) ∧
  (∀ t : ℝ, 0 < t → 0 < Z1 t → ∀ d, HasDerivAt T1 d t → d = 1) ∧
  (∀ t : ℝ, 0 < t → 0 < Z2 t → ∀ d, HasDerivAt T2 d t → d = 1)

/-- Definition 6.3 (fluid model stability), specialized to the tandem queueing network's fluid
model: there is `γ > 0` such that every solution has `Z1(t) = Z2(t) = 0` for `t ≥ γ(Z1(0)+Z2(0))`. -/
def TandemFluidStable (lam1 mu1 mu2 : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Z1 Z2 T1 T2 : ℝ → ℝ), TandemFluidSolution lam1 mu1 mu2 Z1 Z2 T1 T2 →
    ∀ t : ℝ, γ * (Z1 0 + Z2 0) ≤ t → Z1 t = 0 ∧ Z2 t = 0

end ProcessingNetworks.LyapunovCriteria


