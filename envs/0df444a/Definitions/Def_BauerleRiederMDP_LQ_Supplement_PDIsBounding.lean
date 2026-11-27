-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_PDIsBounding
-- name    : BauerleRiederMDP_LQ_Supplement_PDIsBounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:22:39.552663+00:00
-- url     : https://prove2.me/theorems/bbe388e0-8cd0-4f1f-89f5-0b86ecbcc099
-- title:
--   A bounding function of a Piecewise Deterministic Markov Decision Model
-- statement:
--   **A bounding function of a Piecewise Deterministic Markov Decision Model** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.255, PDF 266: "an upper bounding function $b$ with $r$ replaced by $|r|$", Definition 8.2.4, p.251, PDF 262): a measurable $b : E \to  \mathbb R _+$ with constants $c_r, c_Q, c_\varphi  \ge  0$ such that (i) $|r(x, u)| \le  c_r b(x)$, (ii) $\int  b(z) Q(dz|x, u) \le  c_Q b(x)$, (iii) $\lambda  \int _0^\infty  e^{-(\lambda +\beta )t} b(\varphi ^\alpha _t(x)) dt \le  c_\varphi  b(x)$ for all $x \in  E$, $u \in  U$, $\alpha  \in  R$.
--
--   **Formalization Note.** The published `JumpModel.IsUpperBounding` with $|r|$ in place of $r^+$; the integrals of $b \ge  0$ are Lebesgue integrals.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.255, PDF 266: "an upper bounding function `b` with `r` replaced by `|r|`", Definition 8.2.4, p.251, PDF 262

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel

open MeasureTheory
open BauerleRiederMDP.PDMDP

namespace BauerleRiederMDP.LQ.Supplement

/-- **A bounding function of a Piecewise Deterministic Markov Decision Model** (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), p.255, PDF 266: "an upper bounding
function `b` with `r` replaced by `|r|`", Definition 8.2.4, p.251, PDF 262): a measurable
`b : E → ℝ₊` with constants `c_r, c_Q, c_φ ≥ 0` such that (i) `|r(x, u)| ≤ c_r b(x)`,
(ii) `∫ b(z) Q(dz|x, u) ≤ c_Q b(x)`, (iii) `λ ∫_0^∞ e^{−(λ+β)t} b(φ^α_t(x)) dt ≤ c_φ b(x)` for all
`x ∈ E`, `u ∈ U`, `α ∈ R`.

**Formalization Note.** The published `JumpModel.IsUpperBounding` with `|r|` in place of `r⁺`;
the integrals of `b ≥ 0` are Lebesgue integrals. -/
def PDIsBounding {E U : Type*} [TopologicalSpace E] [MeasurableSpace E] [MeasurableSpace U]
    (M : JumpModel E U) (b : E → ℝ) : Prop :=
  Measurable b ∧ (∀ x, 0 ≤ b x) ∧ ∃ cr cQ cφ : ℝ, 0 ≤ cr ∧ 0 ≤ cQ ∧ 0 ≤ cφ ∧
    (∀ x u, |M.r (x, u)| ≤ cr * b x) ∧
    (∀ x u, ∫⁻ z, ENNReal.ofReal (b z) ∂(M.Q (x, u)) ≤ ENNReal.ofReal (cQ * b x)) ∧
    ∀ x (α : RelaxedControl U),
      ENNReal.ofReal M.lam * ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(M.lam + M.β) * t) * b (M.flow α x t)) ≤
      ENNReal.ofReal (cφ * b x)

end BauerleRiederMDP.LQ.Supplement


