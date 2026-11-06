-- Prove2me | Definitions.Def_FirstOrderFG_Alg4_doublingIndex
-- name    : FirstOrderFG_Alg4_doublingIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:51:38.892426+00:00
-- url     : https://prove2.me/theorems/c521cc1b-88f3-459a-b467-f81e00c3f02a
-- title:
--   Number of doublings of the guess in one round
-- statement:
--   Once $\mathcal H^{G_{\mathrm{self}}}(q_t)>A$ for the current instance, the while loop of Algorithm 4 doubles the guess and restarts with $\theta=c/\Gamma_A$ until the fresh instance passes the test. The number of doublings is the least $j\ge1$ with
--   $$
--   \mathcal H^{G_{\mathrm{self}}}\big(q^{\mathrm{fresh}}_{A\cdot2^j}\big)\le A\cdot 2^j .
--   $$
--
--   **Formalization Note** Defined as the infimum of that set of $j$; it is nonempty since $\mathcal H^{G_{\mathrm{self}}}\le s$ on $\Delta(V_{\mathrm{self}})$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 4, lines 6–9, p.32

import Mathlib
import Definitions.Def_FirstOrderFG_Alg2_init
import Definitions.Def_FirstOrderFG_Alg2_qOf
import Definitions.Def_FirstOrderFG_Hself
import Definitions.Def_FirstOrderFG_cConst
import Definitions.Def_FirstOrderFG_GammaA

namespace FirstOrderFG

/-- **Number of doublings in the while loop of Algorithm 4.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 4, lines 6–9, p.32:
"while `H^{G_self}(q_t) > A_m` do `A_{m+1} = 2A_m`, `θ_{m+1,1} = c/Γ_{A_{m+1}}`, … initializing a new
instance of Algorithm 2 … Compute `q_t` by Line 6 of this new instance".

Once the test has failed for the current instance with guess `A`, the loop stops after the first
`j ≥ 1` for which the fresh instance with guess `A·2^j` passes it. `doublingIndex E T q₀ A` is that
`j`.

**Formalization Note.** Defined as `sInf` of the set of such `j`; the set is nonempty because
`H^{G_self}(q) ≤ |V_self|` on `∆(V_self)` (proved in the verification file). -/
noncomputable def Alg4.doublingIndex {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ)
    (A : ℝ) : ℕ :=
  sInf {j : ℕ | 1 ≤ j ∧
    Hself E T (Alg2.qOf E T q₀ (Alg2.init E (A * 2 ^ j) (cConst / GammaA E T (A * 2 ^ j))))
      ≤ A * 2 ^ j}

end FirstOrderFG


