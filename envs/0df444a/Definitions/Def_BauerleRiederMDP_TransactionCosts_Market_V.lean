-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_V
-- name    : BauerleRiederMDP_TransactionCosts_Market_V
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:28:46.394441+00:00
-- url     : https://prove2.me/theorems/567c6d07-d50f-4efe-99bd-8718732860b4
-- title:
--   Value function $V_n$ of the terminal wealth problem with transaction costs
-- statement:
--   The value function is the supremum of $V_{n\pi}$ over all Markov policies,
--   $$V_n(x)=\sup_\pi\ \mathbb E^\pi_{nx}\,U\big(X^0_N+X^1_N\big),\qquad x\in E,$$
--   which at $n=0$ is the terminal wealth problem with transaction costs (4.25).
--
--   **Formalization Note** The supremum is taken in `EReal` over the subtype of policies, so no default value enters. Policies choose both holdings $(a_0,a_1)\in D(x)$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.18 (PDF 33); §4.5, eq. (4.25), p.107 (PDF 121)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_IsPolicy
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Vpi

namespace BauerleRiederMDP.TransactionCosts

/-- The value function `V_n(x) := sup_π V_{nπ}(x)` of the terminal wealth problem with
transaction costs (Bäuerle & Rieder 2011, p.18, PDF 33; (4.25), p.107, PDF 121), the supremum
over all Markov policies `π = (f_n, …, f_{N−1})` of decision rules.

**Formalization Note.** The supremum is taken in `EReal` over the subtype of policies, so it is
the book's supremum with no default value. Markov policies, as in the book's definition of `V_n`
(history-dependent policies give the same value, Theorem 2.2.3). -/
noncomputable def Market.V {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (x : ℝ × ℝ) : EReal :=
  ⨆ π : {π : ℕ → ℝ × ℝ → ℝ × ℝ // M.IsPolicy n π}, M.Vpi π.1 n x

end BauerleRiederMDP.TransactionCosts


