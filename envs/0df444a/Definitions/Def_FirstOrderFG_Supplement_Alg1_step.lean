-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_step
-- name    : FirstOrderFG_Supplement_Alg1_step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:39:48.617135+00:00
-- url     : https://prove2.me/theorems/508d9e87-147e-4bc0-bdee-971395f331cc
-- title:
--   One round of Algorithm 1
-- statement:
--   One round computes $q_t$, samples an arm $I_t$, forms the unbiased graph-feedback estimate
--
--   $$
--   \widehat\ell_{t,j}=\frac{\ell_{t,j}\mathbf 1\{I_t\to j\}}{Q_j^G(q_t)},
--   $$
--
--   and applies the ordinary-simplex EXP3 update to obtain $p_{t+1}$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 1, lines 3–5, p.7; Eq. (5), p.4

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg1_qOf
import Definitions.Def_FirstOrderFG_Supplement_Alg1_update
import Definitions.Def_FirstOrderFG_ltilde

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **One played round of Algorithm 1.** Zhang–Zhang–Luo–Mineiro,
*Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
Algorithm 1, lines 3–5, p.7: compute `q_t`, use the unbiased graph-feedback estimate (5)
from the sampled arm `I_t`, and perform the ordinary-simplex update (1). -/
noncomputable def Alg1.step {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (t : ℕ) (st : Alg1.State K) (I : Fin K) :
    Alg1.State K :=
  let q := Alg1.qOf E T st
  ⟨st.η, Alg1.update st.η st.p (FirstOrderFG.ltilde E (ℓ t) q I)⟩

end FirstOrderFG.Supplement


