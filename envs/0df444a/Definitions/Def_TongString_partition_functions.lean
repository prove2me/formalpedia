-- Prove2me | Definitions.Def_TongString_partition_functions
-- name    : TongString_partition_functions
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T20:55:37.339773+00:00
-- url     : https://prove2.me/theorems/3117c49c-e16a-4c2c-bc37-08a5d57a0c0f
-- title:
--   The scalar and string one-loop partition functions $Z_{\rm scalar}(\tau)$ and $F(\tau)=(\operatorname{Im}\tau)^{-12}|\eta(\tau)|^{-48}$
-- statement:
--   For $\tau$ in the upper half-plane let $\eta$ be the Dedekind eta function.
--
--   1. The (oscillator plus zero-mode) partition function of a single free scalar field on the torus, with constant factors dropped as in eq. (6.20), is
--   $$
--   Z_{\text{scalar}}(\tau)=\frac{1}{\sqrt{\operatorname{Im}\tau}}\;\frac{1}{|\eta(\tau)|^{2}}.
--   $$
--   2. The integrand of the bosonic string partition function, $Z_{\text{string}}=\int\frac{d^2\tau}{(\operatorname{Im}\tau)^2}F(\tau)$, is
--   $$
--   F(\tau)=\left(\frac{1}{\sqrt{\operatorname{Im}\tau}}\;\frac{1}{\eta(\tau)\,\overline{\eta(\tau)}}\right)^{24}=\frac{1}{(\operatorname{Im}\tau)^{12}\,|\eta(\tau)|^{48}}.
--   $$
--
--   **Formalization Note** Both are real-valued. The factors $1/\sqrt{\alpha'}$ and the other constant prefactors that Tong explicitly neglects are omitted. Real division by $0$ returns $0$ in Lean, which is irrelevant on the upper half-plane where $\operatorname{Im}\tau>0$ and $\eta(\tau)\ne0$.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.4.2, p. 150 eq. (6.20) and p. 151 (string partition function written in terms of η)

import Mathlib
import Definitions.Def_TongString_dedekind_eta

namespace TongString

/-- The free-scalar partition function (6.20), up to constant factors:
`Z_scalar(τ) = 1 / (√(Im τ) |η(τ)|²)`. -/
noncomputable def scalarPartitionFunction (τ : ℂ) : ℝ :=
  1 / Real.sqrt τ.im * (1 / ‖dedekindEta τ‖) ^ 2

/-- The integrand of the bosonic string partition function (after (6.21)), up to constant
factors: `(1/√(Im τ) · 1/(η η̄))^24 = (Im τ)^(-12) |η(τ)|^(-48)`. -/
noncomputable def stringPartitionIntegrand (τ : ℂ) : ℝ :=
  (1 / τ.im) ^ 12 * (1 / ‖dedekindEta τ‖) ^ 48

end TongString


