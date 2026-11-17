-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg3_step
-- name    : FirstOrderFG_Supplement_Alg3_step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:53:45.988726+00:00
-- url     : https://prove2.me/theorems/be98c7a6-6626-49bd-b2c5-ae7a0715b054
-- title:
--   One sampled round of Algorithm 3
-- statement:
--   After completing all pre-round doublings, Algorithm 3 executes the current Algorithm 1 round, adds the realized loss $\ell_{t,I_t}$ to $S$, and, when $t<T$ and $A_m\eta_{m,\lambda}^2S\ge\ln K$, starts a fresh epoch with
--
--   $$
--   \eta_{m,\lambda+1}=\max\left\{\frac1{KT},\frac{\eta_{m,\lambda}}2\right\}.
--   $$
--
--   Thus $S$ is incurred loss, not expected or observable loss.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 3, lines 4–13, p.15

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg3_prepare
import Definitions.Def_FirstOrderFG_Supplement_Alg1_step
import Definitions.Def_FirstOrderFG_Supplement_Alg1_init

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **One sampled round of Algorithm 3.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, Algorithm 3, lines 4–13, p.15. After the pre-sampling doublings,
the current Algorithm 1 instance plays arm `I`; `S` gains the realized incurred loss
`ℓ_{t,I}`. If `t < T` and `A η² S ≥ ln K`, the next epoch starts from uniform with
rate `max{1/(KT),η/2}` and `S = 0`. -/
noncomputable def Alg3.step {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (t : ℕ) (st : Alg3.State K) (I : Fin K) :
    Alg3.State K :=
  let st' := Alg3.prepare E T st
  let S' := st'.S + ℓ t I
  if t < T ∧ Real.log K ≤ st'.A * st'.inst.η ^ 2 * S' then
    ⟨st'.A,
      Alg1.init K (max (1 / ((K : ℝ) * T)) (st'.inst.η / 2)), 0⟩
  else
    ⟨st'.A, Alg1.step E T ℓ t st'.inst I, S'⟩

end FirstOrderFG.Supplement


