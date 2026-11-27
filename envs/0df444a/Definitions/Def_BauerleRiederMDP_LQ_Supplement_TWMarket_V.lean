-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_V
-- name    : BauerleRiederMDP_LQ_Supplement_TWMarket_V
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:37:09.433109+00:00
-- url     : https://prove2.me/theorems/292e4f2d-2439-5801-a5e4-7ab56e89c788
-- title:
--   The value functions of the terminal wealth problem
-- statement:
--   **The value functions of the terminal wealth problem** $V_n(x) = \sup _\pi  \mathbb E ^\pi _{nx} U(X_N)$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (4.6), p.80, PDF 94), the supremum over all policies $\pi $ of the Markov Decision Model with state sets $E_n$; $V_0(x)$ is the value of problem (4.3).
--
--   **Formalization Note.** A supremum in `EReal` over the policies (`IsPolicy`), never the Bellman recursion. The zero rule $f_n ≡ 0$ is a policy for the state sets of §4.2 ($E_n = dom U$, and the HARA sets of p.88), so the supremum is over a nonempty set there.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (4.6), p.80, PDF 94), the supremum over all policies `π` of the Markov Decision Model with state sets `E_n`; `V_0(x)` is the value of problem (4.3

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_IsPolicy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_Vpi

namespace BauerleRiederMDP.LQ.Supplement

/-- **The value functions of the terminal wealth problem** `V_n(x) = sup_π 𝔼^π_{nx} U(X_N)`
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (4.6),
p.80, PDF 94), the supremum over all policies `π` of the Markov Decision Model with state sets
`E_n`; `V_0(x)` is the value of problem (4.3).

**Formalization Note.** A supremum in `EReal` over the policies (`IsPolicy`), never the Bellman
recursion. The zero rule `f_n ≡ 0` is a policy for the state sets of §4.2 (`E_n = dom U`, and the
HARA sets of p.88), so the supremum is over a nonempty set there. -/
noncomputable def TWMarket.V {d : ℕ} (Mk : TWMarket d) (Es : ℕ → Set ℝ) (U : ℝ → ℝ) (N n : ℕ)
    (x : ℝ) : EReal :=
  ⨆ f ∈ {f : ℕ → ℝ → Fin d → ℝ | Mk.IsPolicy Es N f}, Mk.Vpi U N f n x

end BauerleRiederMDP.LQ.Supplement


