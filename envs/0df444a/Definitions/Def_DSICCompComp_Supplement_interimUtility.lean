-- Prove2me | Definitions.Def_DSICCompComp_Supplement_interimUtility
-- name    : DSICCompComp_Supplement_interimUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:19:37.581715+00:00
-- url     : https://prove2.me/theorems/baee9d9b-27aa-4da5-b546-860e7425e06e
-- title:
--   Interim utility $\mathbb E_{v_{-i}\sim D^{n-1}}[\,\cdot\,]$ of bidder $i$
-- statement:
--   Let $D = D_1 \times \cdots \times D_m$ be a product distribution on $\mathbb R_{\ge 0}^m$ from which each of $n$ bidders draws her value vector independently. For a mechanism $(x, p)$, a bidder $i$, values $v_i$ and a report $v'_i$, the **interim utility** is
--
--   $$
--   U_i(v_i \to v'_i) \;=\; \mathbb E_{v_{-i} \sim D^{n-1}}\Big[\sum_{j=1}^m x_{ij}(v'_i, v_{-i})\, v_{ij} - p_i(v'_i, v_{-i})\Big],
--   $$
--
--   the expected utility of bidder $i$ when the other bidders report their values truthfully.
--
--   **Formalization Note** The expectation is a Bochner integral of the ex-post utility (`interimIntegrand`) against the full profile law $D^n$ (the published `profileLaw n D`). The integrand ignores the $i$-th coordinate, whose law is a probability measure, so this equals the expectation over $v_{-i} \sim D^{n-1}$. The definition takes a proof that the integrand is integrable, excluding Lean's default value $0$ for a non-integrable Bochner integral.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Section 2, pp.5–6 (pdf pp.6–7)

import Mathlib
import Definitions.Def_DSICCompComp_profileLaw
import Definitions.Def_DSICCompComp_Supplement_interimIntegrand

open MeasureTheory
open scoped NNReal

namespace DSICCompComp

namespace Supplement

/-- The interim utility of bidder `i` with values `v_i` reporting `v'_i`, when the other `n − 1`
bidders report truthfully with values drawn iid from the product distribution `D`
(Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Section 2, pp.5–6 (pdf pp.6–7)):
`E_{v_{-i} ∼ D^{n-1}}[∑_j x_ij(v'_i, v_{-i}) · v_ij − p_i(v'_i, v_{-i})]`.

**Formalization Note** The expectation is the Bochner integral of `interimIntegrand M i vi vi'`
against the full profile law `D^n` (the published `profileLaw n D`); since the integrand ignores
the `i`-th coordinate and that coordinate's law is a probability measure, this is the expectation
over `v_{-i} ∼ D^{n-1}`. The proof argument records that the integrand is integrable, excluding
Lean's default value `0` for a non-integrable Bochner integral. -/
noncomputable def interimUtility {n m : ℕ} (D : Fin m → ProbabilityMeasure ℝ≥0)
    (M : MultiItemRev.MultiBuyer.MechanismN n (Fin m)) (i : Fin n) (vi vi' : Fin m → ℝ≥0)
    (_h : Integrable (interimIntegrand M i vi vi') (profileLaw n D)) : ℝ :=
  ∫ v, interimIntegrand M i vi vi' v ∂(profileLaw n D)

end Supplement

end DSICCompComp


