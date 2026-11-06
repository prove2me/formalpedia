-- Prove2me | Definitions.Def_DelayedGamesMAO_IsMAOOMDRun
-- name    : DelayedGamesMAO_IsMAOOMDRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:17.555799+00:00
-- url     : https://prove2.me/theorems/4228aeb9-d269-4ccd-940c-9eec7eeb7034
-- title:
--   A run of MAO-OMD as instantiated in Theorem 1
-- statement:
--   Let $W$, $\psi$ (with gradient field $d\psi$), $w_0$, constants $M,L,G$, a horizon $T$, delays $(d_t)$ and gradients $(g_t)$ be given. Actions $(w_t)$ and learning rates $(\eta_t)$ form a **run of MAO-OMD** if
--
--   1. $(\eta_t)$ follows the tuning (9) with $\gamma=\max\{4L,2G/\sqrt M\}$, the congestion schedule (10) and the hints $h_t$ of Algorithm 1;
--   2. $(w_t)$ is a run of Algorithm 1 with the same $\gamma$, schedule (10) and learning rates $(\eta_t)$.
--
--   This is the algorithm whose guarantees Theorems 1, 2 and 3 state.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, Theorem 1, p.12

import Mathlib
import Definitions.Def_DelayedGamesMAO_IsAlg1Run
import Definitions.Def_DelayedGamesMAO_IsTuning
import Definitions.Def_DelayedGamesMAO_congAlloc
import Definitions.Def_DelayedGamesMAO_gammaMAO

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **A run of MAO-OMD as instantiated in Theorem 1**: Algorithm 1 with the congestion schedule
(10), the learning rates (9), and the optimism weight `γ = max{4L, 2G/√M}`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, Theorem 1, p.12: "Consider the allocation schedule `(α_s^{(t)})_{s≤t}` in (10) and the
sequence `0 = η_1 ≤ ⋯ ≤ η_{T+1}` following (9). Then Algorithm 1 with `γ = max{4L, 2G/√M}` …".

`g t` is the gradient of round `t`, `w t` the action of round `t`, `η t` the learning rate.

**Formalization Note.** (9) uses the hints `h = hint d T g` of Algorithm 1 and `α = congAlloc d`;
`η` is a parameter constrained by (9), which determines it. -/
def IsMAOOMDRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Set E)
    (ψ : E → ℝ) (dψ : E → E →L[ℝ] ℝ) (w0 : E) (M L G : ℝ) (T : ℕ) (d : ℕ → ℕ)
    (g : ℕ → E →L[ℝ] ℝ) (w : ℕ → E) (η : ℕ → ℝ) : Prop :=
  IsTuning d T M (gammaMAO L G M) (congAlloc d) g (hint d T g) η ∧
    IsAlg1Run W ψ dψ w0 (gammaMAO L G M) T d (congAlloc d) η g w

end DelayedGamesMAO


