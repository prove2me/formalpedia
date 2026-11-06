-- Prove2me | Definitions.Def_FirstOrderFG_Alg4_epochReg
-- name    : FirstOrderFG_Alg4_epochReg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:00:17.948138+00:00
-- url     : https://prove2.me/theorems/5c6052be-c3b8-4968-a794-86b6154e1d7f
-- title:
--   Epoch regret $\mathrm{Reg}_{m,\lambda,k}$
-- statement:
--   For an epoch $(m,\lambda)$ of Algorithm 4 with rounds $\mathcal T_{m,\lambda}$ and first round $t^{\mathrm{start}}_{m,\lambda}$,
--   $$
--   \mathrm{Reg}_{m,\lambda,k}=\mathbb E_{t^{\mathrm{start}}_{m,\lambda}}\Big[\sum_{t\in\mathcal T_{m,\lambda}}\big(\langle x_t,g_t\rangle-\ell_{t,k}\big)\Big],
--   $$
--   conditional on the history before $t^{\mathrm{start}}_{m,\lambda}$. For a history $h_0$ of rounds $1,\dots,t_0-1$, the epoch is that of the instance playing round $t_0$; a later round belongs to it iff no restart occurred in between.
--
--   **Formalization Note** This is $\mathrm{Reg}_{m,\lambda,k}$ when the epoch starts at $t_0$, i.e. when the instance playing round $t_0$ has played no earlier round.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.6, p.33

import Mathlib
import Definitions.Def_FirstOrderFG_Alg4_condExp
import Definitions.Def_FirstOrderFG_Alg4_sumAlong
import Definitions.Def_FirstOrderFG_binner
import Definitions.Def_FirstOrderFG_gvec
import Definitions.Def_FirstOrderFG_Alg2_qOf

namespace FirstOrderFG

/-- **`Reg_{m,λ,k}`, the expected regret of an epoch conditional on its start.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
Lemma B.6, p.33: "For an epoch `(m, λ)` of Algorithm 4, denote by `T_{m,λ}` its rounds, by
`t^start_{m,λ}` … its first … round, and by
`Reg_{m,λ,k} ≜ E_{t^start}[∑_{t ∈ T_{m,λ}} (⟨x_t, g_t⟩ − ℓ_{t,k})]` its expected regret conditional on
the history before `t^start_{m,λ}`."

For a history `h0` of rounds `1, …, t₀ − 1` (`t₀ = |h0| + 1`), the epoch is that of the instance
playing round `t₀`; a later round `t` belongs to it iff that instance has, at round `t`, played
exactly `t − t₀` rounds (no restart in between). `epochReg` is the conditional expectation, given
`h0`, of `∑_{t ∈ T_{m,λ}} (⟨x_t, g_t⟩ − ℓ_{t,k})`.

**Formalization Note.** This equals `Reg_{m,λ,k}` when the epoch starts at round `t₀`, i.e. when
the instance playing round `t₀` has played no earlier round (field `n = 0`); the milestone states
the bound under that condition. Every history has positive probability (all `π_t` are interior),
so the conditional expectation is defined at every `h0`. -/
noncomputable def Alg4.epochReg {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (h0 : List (Fin K)) (k : Fin K) : ℝ :=
  Alg4.condExp E T ℓ q₀ h0 (fun h =>
    Alg4.sumAlong E T ℓ q₀
      (fun t st => if st.inst.n = t - (h0.length + 1) then
          binner E st.inst.x (gvec E (ℓ t) (Alg2.qOf E T q₀ st.inst)) - ℓ t k
        else 0)
      (h0.length + 1) (Alg4.run E T ℓ q₀ h0) (h.drop h0.length))

end FirstOrderFG


