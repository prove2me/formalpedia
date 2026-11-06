-- Prove2me | Definitions.Def_FirstOrderFG_Alg4_step
-- name    : FirstOrderFG_Alg4_step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:53:57.795901+00:00
-- url     : https://prove2.me/theorems/93d30f32-70f5-4e9e-bbf8-6d5252c3a210
-- title:
--   One round of Algorithm 4
-- statement:
--   After lines 4–9, round $t$ of the current instance is executed with the played arm $I_t$; then $\tilde Z_t=\langle x_t,\tilde g_t\rangle$, $S\leftarrow S+\tilde Z_t$, and if $t<T$ and $\Gamma_{A_m}\theta_{m,\lambda}^2S\ge\ln(MT)$, the rate is halved, $S\leftarrow0$, and a fresh instance with the same $A_m$ starts at round $t+1$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 4, lines 4–14, p.32

import Mathlib
import Definitions.Def_FirstOrderFG_Alg4_prepare
import Definitions.Def_FirstOrderFG_Alg2_step
import Definitions.Def_FirstOrderFG_binner
import Definitions.Def_FirstOrderFG_gtilde

namespace FirstOrderFG

/-- **One round of Algorithm 4.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 4, lines 4–14, p.32.

Lines 4–9 (`Alg4.prepare`); line 10 executes round `t` of the current instance with played arm `I`;
line 11 sets `Z̃_t = ⟨x_t, g̃_t⟩` and `S ← S + Z̃_t`; lines 12–14: if `t < T` and
`Γ_{A_m} θ_{m,λ}² S ≥ ln(MT)`, halve `θ`, set `S ← 0` and start a fresh instance of Algorithm 2 with
the same `A_m` from round `t + 1`.

**Formalization Note.** `ln` is `Real.log`, `M = |B|`. -/
noncomputable def Alg4.step {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (t : ℕ) (st : Alg4.State K) (I : Fin K) : Alg4.State K :=
  let st' := Alg4.prepare E T q₀ st
  let S' := st'.S + binner E st'.inst.x (gtilde E (ℓ t) st'.inst.x I)
  if t < T ∧ Real.log (((Bset E).card : ℝ) * T) ≤ GammaA E T st'.inst.A * st'.inst.θ ^ 2 * S' then
    ⟨Alg2.init E st'.inst.A (st'.inst.θ / 2), 0⟩
  else ⟨Alg2.step E T ℓ q₀ t st'.inst I, S'⟩

end FirstOrderFG


