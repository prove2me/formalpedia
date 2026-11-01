-- Prove2me | Definitions.Def_WiretapFeedback_IsWiretapCode
-- name    : WiretapFeedback_IsWiretapCode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:15.196324+00:00
-- url     : https://prove2.me/theorems/3402c0d1-7f69-4cfe-8fe4-497cbfefe2a0
-- title:
--   $(N,n,\epsilon,\delta)$ wiretap code
-- statement:
--   A wiretap code with $N$ messages and block length $n$ is an **$(N,n,\epsilon,\delta)$ wiretap code** for $W$ if, for a uniformly distributed message $M\sim\mathrm{unif}\{1,\dots,N\}$,
--
--   1. (reliability) $P(M\ne\hat M)\le\epsilon$, and
--   2. (secrecy) $\|P_{MZ^n\mathbf F}-P_M\times P_{Z^n\mathbf F}\|_1\le\delta$,
--
--   where $\|\cdot\|_1$ is the variation distance (with the factor $\tfrac12$).
--
--   **Formalization Note** The uniform message law needs $N\ge1$, which every $N=\lfloor2^{nR}\rfloor$ with $R>0$ satisfies. $P_M$ and $P_{Z^n\mathbf F}$ are the marginals of the induced law.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §II, p.2 (definition of an (N, n, ϵ, δ) wiretap code)

import Mathlib
import Definitions.Def_WiretapFeedback_tvDist
import Definitions.Def_WiretapFeedback_WiretapCode_law

namespace WiretapFeedback

/-- An **`(N, n, ϵ, δ)` wiretap code** for the channel `W : X → Y × Z`, Hayashi–Tyagi–Watanabe,
arXiv:1410.0443v1, §II, p. 2: for a uniformly distributed message `M ∼ unif{1, …, N}`, the
induced law `P = P_{M M̂ Zⁿ 𝐅}` satisfies
1. `P(M ≠ M̂) ≤ ϵ` (reliability), and
2. `‖P_{M Zⁿ 𝐅} − P_M × P_{Zⁿ 𝐅}‖₁ ≤ δ` (secrecy), with the variation distance `tvDist`
   (which carries the paper's factor `½`).

**Formalization Note** The uniform message law needs `N ≥ 1` (`[NeZero N]`); every `N` the paper
uses is `⌊2^{nR}⌋ ≥ 1`. `P_M` and `P_{Zⁿ 𝐅}` are the marginals of `P`, and their product is
`P_M.bind (m ↦ P_{Zⁿ𝐅}.map (zf ↦ (m, zf)))`. The thresholds enter as `ENNReal.ofReal ϵ`,
`ENNReal.ofReal δ`, exact for the paper's `ϵ, δ ≥ 0`. -/
def IsWiretapCode {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ} [NeZero N]
    (W : WildeQIT.Channel X (Y × Z)) (c : WiretapCode X Y N n) (ε δ : ℝ) : Prop :=
  let P := c.law (PMF.uniformOfFintype (Fin N)) W
  P.toOuterMeasure {t | t.1 ≠ t.2.1} ≤ ENNReal.ofReal ε ∧
    tvDist (P.map fun t => (t.1, t.2.2))
        ((P.map Prod.fst).bind fun m => (P.map fun t => t.2.2).map fun zf => (m, zf))
      ≤ ENNReal.ofReal δ

end WiretapFeedback


