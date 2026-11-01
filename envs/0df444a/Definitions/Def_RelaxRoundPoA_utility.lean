-- Prove2me | Definitions.Def_RelaxRoundPoA_utility
-- name    : RelaxRoundPoA_utility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:56.638821+00:00
-- url     : https://prove2.me/theorems/a754cad9-3811-46ba-a2b1-b1ba17d3b2be
-- title:
--   Quasi-linear expected utility $u_i(b,w)$
-- statement:
--   Agents have quasi-linear utilities and are risk neutral. Agent $i$'s **expected utility** in the mechanism $M=(f,p)$ on bid profile $b$, when its valuation is $w$, is
--
--   $$
--   u_i(b,w)=\mathbf E\bigl[w(f(b))\bigr]-\mathbf E\bigl[p_i(b)\bigr].
--   $$
--
--   The expectation of $w$ is taken under the outcome law of $M$ on $b$.
--
--   **Formalization Note** The expectation is a Bochner integral, which is $0$ for a non-integrable function; every theorem that uses utilities assumes the integrability of the weights involved.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §2, p.7

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **Quasi-linear expected utility.**
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §2, p.7: "agent `i`'s expected utility in
mechanism `M = (f, p)` is given by `u_i(b, v_i) = E[v_i(f(b))] − E[p_i(b)]`."

`utility M i b w` is `u_i(b, w)`: the expectation of `w` under the outcome law of `M` on bid profile
`b`, minus agent `i`'s expected payment.

**Formalization Note** The expectation is a Bochner integral, which is `0` for a non-integrable
function; every theorem of this mission assumes integrability of the weights it integrates
(`ExpFinite`, and an `Integrable` clause in `IsSmooth`). -/
noncomputable def utility {N : Type*} {Ω' : Type*} [MeasurableSpace Ω'] (M : Mechanism N Ω') (i : N)
    (b : N → Ω' → ℝ≥0) (w : Ω' → ℝ≥0) : ℝ :=
  ∫ x, (w x : ℝ) ∂(M.outcome b) - M.expPay b i

end RelaxRoundPoA


