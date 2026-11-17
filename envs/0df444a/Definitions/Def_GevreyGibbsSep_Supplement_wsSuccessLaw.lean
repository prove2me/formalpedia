-- Prove2me | Definitions.Def_GevreyGibbsSep_Supplement_wsSuccessLaw
-- name    : GevreyGibbsSep_Supplement_wsSuccessLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:01:22.182665+00:00
-- url     : https://prove2.me/theorems/0527697f-ffaf-44a2-b26f-caefc1514733
-- title:
--   Output law $\eta$ conditional on heralded success
-- statement:
--   For a warm-started first-order quantum algorithm $A$, a potential $E$ and a warm-start state $\phi$, the **output law on heralded success** is the distribution on $\mathbb T^d$
--   $$
--   \eta \;=\; \frac{1}{p_{\mathrm{succ}}(E,\phi)} \sum_{z:\ \mathrm{flag}(z)} |\psi_T(z)|^2\,\mathrm{post}(z),
--   $$
--   i.e. the law of the post-processed measurement outcome conditioned on the herald reporting success.
--
--   This is the law $\eta$ of the sample returned "on heralded success" in Theorem A.3.
--
--   **Formalization Note** When $p_{\mathrm{succ}}=0$ the formula gives the zero measure; Theorem A.3 bounds $p_{\mathrm{succ}}$ below by a positive constant, so that value never enters.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem A.3, p.31

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus
import Definitions.Def_GevreyGibbsSep_QReg
import Definitions.Def_GevreyGibbsSep_Grid
import Definitions.Def_GevreyGibbsSep_Supplement_WarmStartQAlg
import Definitions.Def_GevreyGibbsSep_Supplement_wsFinalState
import Definitions.Def_GevreyGibbsSep_Supplement_wsSuccessProb

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

namespace Supplement

/-- The output law `η` of a warm-started first-order quantum algorithm **conditional on heralded
success** (arXiv:2608.24527 (sha256 d4fd40eb…), Theorem A.3, p.31: "on heralded success …,
returns a sample from a random variable `X ∼ η`"):
`η = p_succ⁻¹ ∑_{z : flag z} |ψ_T(z)|² · post(z)`.

**Formalization Note** The final state is measured in the computational basis; a label `z` with
`flag z = true` is a success and is post-processed by `post z`. When `p_succ = 0` the value is
the zero measure (`⊤ · 0 = 0`); every statement that uses it bounds `p_succ` below by a positive
constant, so this value never enters. -/
noncomputable def wsSuccessLaw {d : ℕ} {W : Type} {N T : ℕ} (A : WarmStartQAlg d W N T)
    (E : (Fin d → ℝ) → ℝ) (ϕ : EuclideanSpace ℂ (Grid d N)) : Measure (Torus d) :=
  (wsSuccessProb A E ϕ)⁻¹ • Measure.sum (fun z : QReg d W =>
    if A.flag z then
      ENNReal.ofReal (‖(wsFinalState A E ϕ : QReg d W → ℂ) z‖ ^ 2) • (A.post z : Measure (Torus d))
    else 0)

end Supplement

end GevreyGibbsSep


