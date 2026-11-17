-- Prove2me | Definitions.Def_GevreyGibbsSep_Supplement_wsSuccessProb
-- name    : GevreyGibbsSep_Supplement_wsSuccessProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:00:48.324972+00:00
-- url     : https://prove2.me/theorems/233d98d4-3667-4d0f-875f-0cddba1e961f
-- title:
--   Heralded success probability $p_{\mathrm{succ}}(E,\phi)$
-- statement:
--   For a warm-started first-order quantum algorithm $A$, a potential $E$ and a warm-start state $\phi$, the **heralded success probability** is the probability that the final computational-basis measurement of $\psi_T$ returns a successful label:
--   $$
--   p_{\mathrm{succ}}(E,\phi)\;=\;\sum_{z:\ \mathrm{flag}(z)} |\psi_T(z)|^2 .
--   $$
--
--   Theorem A.3 asks for this probability to be bounded below by a constant.
--
--   **Formalization Note** The value lies in $[0,\infty]$ (extended nonnegative reals); the sum is over the uncountable label set, with only countably many nonzero terms, and is at most $1$ for a unit state.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem A.3, p.31

import Mathlib
import Definitions.Def_GevreyGibbsSep_QReg
import Definitions.Def_GevreyGibbsSep_Grid
import Definitions.Def_GevreyGibbsSep_Supplement_WarmStartQAlg
import Definitions.Def_GevreyGibbsSep_Supplement_wsFinalState

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

namespace Supplement

/-- The heralded success probability `p_succ(E, ϕ) = ∑_{z : flag z} |ψ_T(z)|²` of a warm-started
first-order quantum algorithm: the probability that the final computational-basis measurement
returns a label `z` with `flag z = true` (arXiv:2608.24527 (sha256 d4fd40eb…), Theorem A.3, p.31:
"heralded success of constant probability").

**Formalization Note** Valued in `ℝ≥0∞` (the sum is over the uncountable label set; only
countably many terms are nonzero for an `ℓ²` state, and the sum is at most `1` for a unit
state). -/
noncomputable def wsSuccessProb {d : ℕ} {W : Type} {N T : ℕ} (A : WarmStartQAlg d W N T)
    (E : (Fin d → ℝ) → ℝ) (ϕ : EuclideanSpace ℂ (Grid d N)) : ℝ≥0∞ :=
  ∑' z : QReg d W,
    if A.flag z then ENNReal.ofReal (‖(wsFinalState A E ϕ : QReg d W → ℂ) z‖ ^ 2) else 0

end Supplement

end GevreyGibbsSep


