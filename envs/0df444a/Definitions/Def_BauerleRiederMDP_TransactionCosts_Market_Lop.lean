-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Lop
-- name    : BauerleRiederMDP_TransactionCosts_Market_Lop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:01.787251+00:00
-- url     : https://prove2.me/theorems/8a797885-f218-4508-a2d8-359a6df1c752
-- title:
--   The operator $L_nv(x,a)$ of the transaction cost model
-- statement:
--   For $v:E\to[-\infty,\infty)$, a state $x$ and an action $a=(a_0,a_1)$,
--   $$L_nv(x,a)=\mathbb E\, v\big(a_0(1+i_{n+1}),\ a_1\tilde R_{n+1}\big),$$
--   the operator $L_nv(x,a)=r_n(x,a)+\mathbb E\,v(T_n(x,a,Z_{n+1}))$ of Definition 2.3.1 and Remark 2.3.2 c) for this model ($r_n\equiv0$, $Z_{n+1}=\tilde R_{n+1}$).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.3.1 a), Remark 2.3.2 c), pp.19–20 (PDF 34–35); §4.5, p.108 (PDF 122)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_transition
import Definitions.Def_BauerleRiederMDP_TransactionCosts_eexp

namespace BauerleRiederMDP.TransactionCosts

/-- The operator `L_n v(x, a) = r_n(x, a) + IE v(T_n(x, a, Z_{n+1}))` (Bäuerle & Rieder 2011,
Definition 2.3.1 a) and Remark 2.3.2 c), pp.19–20, PDF 34–35) for the transaction cost model of
§4.5 (r_n ≡ 0, Z_{n+1} = R̃_{n+1}, T_n of (4.24)):
`L_n v(x, (a₀, a₁)) = IE v(a₀(1 + i_{n+1}), a₁ R̃_{n+1})`, for `v : E → [−∞, ∞)`.

**Formalization Note.** The expectation is `eexp` (`IE v⁺ − IE v⁻` in `EReal`). -/
noncomputable def Market.Lop {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (v : ℝ × ℝ → EReal) (_x : ℝ × ℝ) (a : ℝ × ℝ) : EReal :=
  eexp M.P (fun ω => v (M.transition n a (M.R (n + 1) ω)))

end BauerleRiederMDP.TransactionCosts


