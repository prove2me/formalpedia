-- Prove2me | Definitions.Def_FMMM_TSM_expRatio
-- name    : FMMM_TSM_expRatio
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:18:59.572844+00:00
-- url     : https://prove2.me/theorems/46222566-57c6-4b6a-a9b4-8837c1b5dc85
-- title:
--   Expected approximation factor $E[\mathrm{ALG}/\mathrm{OPT}]$ of a TSM run
-- statement:
--   Consider an instance with $e_j = 1$ for every impression type, so that $n = |J|$ impressions are drawn i.i.d. uniformly from $J$. For a flow support $F$ and a TSM colouring with blue edges $B$, the **expected approximation factor** of the two suggested matchings algorithm is
--
--   $$E\left[\frac{\mathrm{ALG}}{\mathrm{OPT}}\right] = \frac{1}{|J|^n} \sum_{\omega \in J^n} \frac{\mathrm{ALG}(\omega)}{\mathrm{OPT}(\omega)},$$
--
--   where $\mathrm{ALG}(\omega)$ is the number of ads assigned by the online phase on the arrival sequence $\omega$ and $\mathrm{OPT}(\omega)$ is the maximum matching of the realization graph.
--
--   **Formalization Note** A scenario with $\mathrm{OPT}(\omega) = 0$ contributes $0$ (Lean's convention $x/0 = 0$); in the tight family every scenario has $\mathrm{OPT} \ge 1$.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §2, p. 4 (expected approximation factor E[ALG(Î)/OPT(Î)])

import Mathlib
import Definitions.Def_FMMM_TSM_tsmRun
import Definitions.Def_FMMM_TSM_realOPT

namespace FMMM.TSM

/-- **Expected approximation factor `E[ALG(Î)/OPT(Î)]` of a TSM run (instance with `e_i = 1`).**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §2, p. 4: "E[ALG(Î)/OPT(Î)] (the expected approximation factor)".

For an instance with ads `A`, impression types `J` (each with `e_j = 1`, so `n = |J|` and draws are
uniform on `J`), edges `E`, flow support `F` and blue edges `blue`,
`expRatio E F blue = |J|^{−n} ∑_{ω : Fin n → J} ALG(ω)/OPT(ω)`, where `ALG(ω)` is the number of
ads assigned by `tsmRun blue (F \ blue) ω` and `OPT(ω) = realOPT E ω`.

**Formalization Note.** Lean's `x / 0 = 0` makes a scenario with `OPT = 0` contribute `0`; on the
tight family every scenario has `OPT ≥ 1`. -/
noncomputable def expRatio {A J : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (E F blue : Finset (A × J)) : ℝ :=
  (∑ ω : Fin (Fintype.card J) → J,
      ((tsmRun blue (F \ blue) ω).card : ℝ) / (realOPT E ω : ℝ)) /
    (Fintype.card J : ℝ) ^ Fintype.card J

end FMMM.TSM


