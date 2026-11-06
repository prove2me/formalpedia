-- Prove2me | Definitions.Def_FirstOrderFG_Alg2_step
-- name    : FirstOrderFG_Alg2_step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:51:48.554935+00:00
-- url     : https://prove2.me/theorems/5834aa0c-d005-40b4-b817-d19ec762568c
-- title:
--   One round of Algorithm 2
-- statement:
--   Given the state before round $t$ and the played arm $I_t$, one round of Algorithm 2: compute $\eta_t$ and $q_t$ (lines 5–6), form $\pi_t$ (line 7), the estimates $\tilde\ell_t$, $\tilde g_t$ (lines 11–12), update $p_{t+1}$ (line 13) and $x_{t+1}$ (line 14), and if $1/x_{t+1,0}>\rho_t$ set $\rho_{t+1}=2/x_{t+1,0}$ and $\theta_{t+1,0}=\sigma\theta_{t,0}$, otherwise keep both (lines 15–16).
--
--   **Formalization Note** When $0\notin\mathcal B$ only the master update runs. The global round index $t$ selects the loss vector $\ell_t$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, lines 5–16, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Alg2_qOf
import Definitions.Def_FirstOrderFG_piDist
import Definitions.Def_FirstOrderFG_ltilde
import Definitions.Def_FirstOrderFG_gtilde
import Definitions.Def_FirstOrderFG_baseUpdate
import Definitions.Def_FirstOrderFG_masterUpdate
import Definitions.Def_FirstOrderFG_sigmaConst

namespace FirstOrderFG

/-- **One round of an instance of Algorithm 2.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 2, lines 5–16, p.10.

`Alg2.step E T ℓ q₀ t st I` is the state after round `t` (a global round index; the loss vector is
`ℓ t`) when the played arm is `I = I_t`: line 6 computes `q_t`, line 7 forms `π_t`, lines 11–12 the
estimates `ℓ̃_t`, `g̃_t`, line 13 updates `p`, line 14 updates `x`, lines 15–16 update `ρ` and
`θ_{t,0}` (if `1/x_{t+1,0} > ρ_t` then `ρ_{t+1} = 2/x_{t+1,0}` and `θ_{t+1,0} = σθ_{t,0}`), and the sum
of line 5 gains `g̃_{t,0}/x_{t,0}`.

**Formalization Note.** When `0 ∉ B` (`V_self = ∅`) lines 5, 6, 11, 13, 15, 16 do not run and only
the master update is performed. The draw of `B_t` and `I_t` (lines 7–9) is the argument `I`; the
law of `I` is `π_t` (`piDist`). -/
noncomputable def Alg2.step {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (t : ℕ) (st : Alg2.State K) (I : Fin K) : Alg2.State K :=
  let q := Alg2.qOf E T q₀ st
  let π := piDist E st.x q
  let g := gtilde E (ℓ t) st.x I
  let x' := masterUpdate E T st.θ0 st.θ st.x g
  if (Vself E).Nonempty then
    { st with
      p := baseUpdate E T (Alg2.eta E T st) st.p (ltilde E (ℓ t) π I)
      x := x'
      gsum := st.gsum + g none / st.x none
      ρ := if st.ρ < 1 / x' none then 2 / x' none else st.ρ
      θ0 := if st.ρ < 1 / x' none then sigmaConst E T * st.θ0 else st.θ0
      n := st.n + 1 }
  else { st with x := x', n := st.n + 1 }

end FirstOrderFG


