-- Prove2me | Definitions.Def_FirstOrderFG_Alg4_prepare
-- name    : FirstOrderFG_Alg4_prepare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:52:32.489871+00:00
-- url     : https://prove2.me/theorems/ba56fcb4-ef02-42f6-a4cf-53e6934a1bd9
-- title:
--   Lines 4–9 of Algorithm 4
-- statement:
--   Before round $t$ is sampled, if $0\in\mathcal B$: compute $q_t$ in the current instance; while $\mathcal H^{G_{\mathrm{self}}}(q_t)>A_m$, double $A$, set $\theta=c/\Gamma_{A}$ and $S=0$, and start a fresh instance at round $t$. Several doublings can occur in one round.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 4, lines 4–9, p.32

import Mathlib
import Definitions.Def_FirstOrderFG_Alg4_State
import Definitions.Def_FirstOrderFG_Alg4_doublingIndex

namespace FirstOrderFG

/-- **Lines 4–9 of Algorithm 4 (before round `t` is sampled).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 4, lines 4–9,
p.32: if `0 ∈ B`, compute `q_t` in the current instance; while `H^{G_self}(q_t) > A_m`, double the
guess, set `θ = c/Γ_A` for the new guess, `S ← 0`, and start a fresh instance at round `t`.

**Formalization Note.** Several doublings may happen in one round; only the last fresh instance
survives (the intermediate meta-epochs have no rounds, p.32). If the test passes for the current
instance, the state is unchanged. -/
noncomputable def Alg4.prepare {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ)
    (st : Alg4.State K) : Alg4.State K :=
  if (Vself E).Nonempty ∧ st.inst.A < Hself E T (Alg2.qOf E T q₀ st.inst) then
    ⟨Alg2.init E (st.inst.A * 2 ^ Alg4.doublingIndex E T q₀ st.inst.A)
      (cConst / GammaA E T (st.inst.A * 2 ^ Alg4.doublingIndex E T q₀ st.inst.A)), 0⟩
  else st

end FirstOrderFG


