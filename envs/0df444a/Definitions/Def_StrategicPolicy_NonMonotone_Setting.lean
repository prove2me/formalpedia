-- Prove2me | Definitions.Def_StrategicPolicy_NonMonotone_Setting
-- name    : StrategicPolicy_NonMonotone_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T14:38:58.335108+00:00
-- url     : https://prove2.me/theorems/1e0dc7be-2a23-4c55-85d6-cb5682eaafd6
-- title:
--   Strategic policy model: policies, best responses, utility, and monotonicity
-- statement:
--   For a finite nonempty feature set $\{x_1,\ldots,x_m\}$ and a policy $\pi$, where $\pi(x_j)\in[0,1]$ is the probability of a positive decision at $x_j$, an individual initially at $x_i$ best-responds by choosing a destination in
--
--   $$
--   \operatorname{bestSet}_{c,\pi}(x_i)=\operatorname*{argmax}_{k}\ \pi(x_k)-c(x_i,x_k),
--   $$
--
--   equation (5) with benefit $b(x)=\pi(x)$. Among tied destinations the individual chooses one with the greatest outcome probability $q(x_j)=P(y=1\mid x_j)$ (standing assumption (ii)); any remaining tie is settled by the least index. This defines $\operatorname{br}_{c,q,\pi}(x_i)$ from the model data.
--
--   The admissible policies, the utility (7), outcome monotonic policies (1) and outcome monotonic costs (p. 6) are taken from the shared model modules `StrategicPolicy.MonotoneBinary.Setting` and `StrategicPolicy.StochasticOpt.Setting`, which this module imports; their utility uses the same best-response rule.
--
--   **Formalization Note** Feature $x_i$ is represented by `Fin m` index $i-1$, and `[NeZero m]` makes the feature set nonempty. The least-index choice only resolves equal-outcome ties left unspecified by the paper; it never fires when outcomes are distinct.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, pp. 3–6, (1), (2), (5), (7), §4 cost definition

import Mathlib
import Definitions.Def_StrategicPolicy_MonotoneBinary_Setting
import Definitions.Def_StrategicPolicy_StochasticOpt_Setting

namespace StrategicPolicy.NonMonotone

/-- All maximizers of the individual's benefit less the cost of changing features. -/
noncomputable def bestSet {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ)
    (π : Fin m → ℝ) (i : Fin m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun k => ∀ l, π l - c i l ≤ π k - c i k)

/-- The cost-benefit maximizers having the greatest outcome probability. -/
noncomputable def preferredSet {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ)
    (q π : Fin m → ℝ) (i : Fin m) : Finset (Fin m) := by
  classical
  exact (bestSet c π i).filter (fun k => ∀ l ∈ bestSet c π i, q l ≤ q k)

/-- Best response (5), with the paper's outcome tie-break; remaining ties use the least index. -/
noncomputable def br {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ)
    (q π : Fin m → ℝ) (i : Fin m) : Fin m := by
  classical
  let s := bestSet c π i
  have hs : s.Nonempty := by
    obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image
      (Finset.univ : Finset (Fin m)) (fun k => π k - c i k) Finset.univ_nonempty
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, fun l => hmax l (Finset.mem_univ l)⟩⟩
  have ht : (preferredSet c q π i).Nonempty := by
    obtain ⟨k, hk, hq⟩ := Finset.exists_max_image s q hs
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, fun l hl => hq l hl⟩⟩
  exact (preferredSet c q π i).min' ht

end StrategicPolicy.NonMonotone


