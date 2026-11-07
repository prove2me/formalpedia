-- Prove2me | Definitions.Def_StochAutoreg_e2eLaw
-- name    : StochAutoreg_e2eLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:20:17.970708+00:00
-- url     : https://prove2.me/theorems/86f9cbb8-c37e-42e2-a2f0-dec8535b22a7
-- title:
--   Law of an end-to-end sample
-- statement:
--   The law of one **end-to-end** sample $(X,Z_M)$: a chain-of-thoughts sample of which only the final bit is kept. Its mass at $(x,y)$ is $P(x)\mathrm{Bern}(q_g^{\mathrm{e2e}-M}(x))(y)$ for $M\ge1$.
--
--   **Formalization Note** It is defined as the push-forward of the chain-of-thoughts law, which makes the label the last token of a real trajectory.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.2

import Mathlib
import Definitions.Def_StochAutoreg_cotLaw
import Definitions.Def_StochAutoreg_lastToken

namespace StochAutoreg

/-- The law of one **end-to-end** sample `(X, Z_M)`: a chain-of-thoughts sample of which only the final
bit is kept. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.2.

**Formalization Note.** It is the push-forward of `cotLaw` under keeping the last token. The mass at
`(x, y)` is `P x * bernMass (qE2E g M x) y` for `1 ≤ M` (verification file). -/
noncomputable def e2eLaw (g : Generator) (M : ℕ) (P : PMF (List Bool)) : PMF (List Bool × Bool) :=
  (cotLaw g M P).map fun w => (w.1, lastToken w.2)

end StochAutoreg


