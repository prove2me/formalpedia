-- Prove2me | Definitions.Def_DiffCtrlRobust_SolvesMarkov
-- name    : DiffCtrlRobust_SolvesMarkov
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:45.331065+00:00
-- url     : https://prove2.me/theorems/13639c00-8fa9-4e98-a597-c504ed36e44f
-- title:
--   Strong solution of (2.1) under a stationary Markov control
-- statement:
--   Let $W$ be a $d$-dimensional standard Wiener process and $v\in\mathfrak U_{\mathsf{sm}}$. A process $X$ is a strong solution of (2.1) from $x$ under $v$ if it is continuous, adapted to the completed filtration of $W$, and almost surely, for all $t\ge0$,
--
--   $$
--   X_t=x+\int_0^t b(X_s,v(X_s))\,\mathrm ds+\int_0^t\sigma(X_s)\,\mathrm dW_s,
--   $$
--
--   where $b(x,v(x))=\int_{\mathbb U}b(x,\zeta)\,v(x)(\mathrm d\zeta)$.
--
--   **Formalization Note** This is the published `EthierKurtz.SolvesBrownianSDE` with time-independent coefficients.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2, p.5, (2.1), and p.6, stationary Markov controls

import Definitions.Def_DiffCtrlRobust_relaxed
import Definitions.Def_DiffCtrlRobust_Usm
import Definitions.Def_EthierKurtz_SolvesBrownianSDE

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- `X` is a strong solution of (2.1) from `x` under the stationary Markov control `v`
(arXiv:2205.05894v2, §2, p.6): `dX_t = b(X_t, v(X_t)) dt + σ(X_t) dW_t`, `X_0 = x`, with the
relaxed drift `b(x, v(x)) = ∫ b(x, ζ) v(x)(dζ)`.

**Formalization Note.** This is `EthierKurtz.SolvesBrownianSDE` with time-independent coefficients:
`X` has continuous paths, is adapted to the completed filtration of `W`, and satisfies the
equation almost surely for all times simultaneously. -/
def SolvesMarkov {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {U : Type*} [MeasurableSpace U]
    (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d) (b : SDEState d → U → SDEState d)
    (σ : SDEState d → SDEDiffusion d) (v : Usm d U) (x : SDEState d)
    (X : ℝ≥0 → Ω → SDEState d) : Prop :=
  SolvesBrownianSDE P (fun p => σ p.2) (fun p => relaxed b p.2 (v.1 p.2)) W (fun _ => x) X

end DiffCtrlRobust


