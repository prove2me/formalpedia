-- Prove2me | Definitions.Def_HoneycombCodes_kappaH
-- name    : HoneycombCodes_kappaH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:27.607763+00:00
-- url     : https://prove2.me/theorems/784e39e7-6871-44a7-b00f-20e042c0e458
-- title:
--   Whole-cube exponent $\kappa_H(\delta)$ and the closed whole-cube region
-- statement:
--   The **whole-cube spectral function** of OpenAI's moving-projection bound is
--
--   $$
--   \Gamma_H(a,b)=\frac{2(a-b)(1-a-b)}{\sqrt{a(1-a)}},
--   $$
--
--   and the **whole-cube exponent** is
--
--   $$
--   \kappa_H(\delta)=\inf\bigl\{H_2(a)-H_2(b) : 0\le b<a\le \tfrac12,\ \Gamma_H(a,b)>1-2\delta\bigr\}.
--   $$
--
--   The module also names the **closed region** of Lemma 6.2, $0<a\le 1/2$, $0\le b\le a$, $\Gamma_H(a,b)\ge 1-2\delta$, and a **minimizing whole-cube point**: a point of this closed region at which $H_2(a)-H_2(b)$ attains its minimum over the region.
--
--   **Formalization Note** $\kappa_H$ is the real `sInf` of the set of objective values over strictly feasible pairs. For $0<\delta<1/2$ the set is nonempty ($(1/2,0)$ gives $\Gamma_H=1$) and bounded below. Mirrors the published `MetricCodes.Hamming.variationalRate`.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), eq. (55), p.28 (PDF 30); closed region and minimizers: Lemma 6.2, p.30 (PDF 32)

import Mathlib
import Definitions.Def_HoneycombCodes_H2

set_option autoImplicit false

namespace HoneycombCodes

/-- The **whole-cube spectral function** `Γ_H(a, b) = 2(a − b)(1 − a − b)/√(a(1 − a))`,
Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2
(sha256 f4b07e31…cd51), eq. (55), p.28 (PDF 30). Mirrors the published `MetricCodes.hammingGamma`. -/
noncomputable def GammaH (a b : ℝ) : ℝ :=
  2 * (a - b) * (1 - a - b) / Real.sqrt (a * (1 - a))

/-- The **whole-cube exponent** of [OAI26],
`κ_H(δ) = inf { H₂(a) − H₂(b) : 0 ≤ b < a ≤ 1/2, Γ_H(a, b) > 1 − 2δ }`, arXiv:2608.20287v2,
eq. (55), p.28 (PDF 30).

**Formalization Note.** A real `sInf` of the set of objective values over the strictly feasible
pairs (strict spectral constraint, as printed). For `0 < δ < 1/2` the set is nonempty (the pair
`(1/2, 0)` has `Γ_H = 1`) and bounded below (it lies in `[−1, 1]`), so this is the printed
infimum. Mirrors the published `MetricCodes.Hamming.variationalRate`. -/
noncomputable def kappaH (δ : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ a b : ℝ, 0 ≤ b ∧ b < a ∧ a ≤ 1 / 2 ∧ 1 - 2 * δ < GammaH a b ∧
    r = H2 a - H2 b}

/-- The **closed whole-cube feasible region** of Lemma 6.2, arXiv:2608.20287v2, p.30 (PDF 32):
`0 < a ≤ 1/2`, `0 ≤ b ≤ a`, `Γ_H(a, b) ≥ 1 − 2δ`. -/
def WholeCubeClosed (δ a b : ℝ) : Prop :=
  0 < a ∧ a ≤ 1 / 2 ∧ 0 ≤ b ∧ b ≤ a ∧ 1 - 2 * δ ≤ GammaH a b

/-- A **minimizing whole-cube point** (Lemma 6.2, Theorem 6.6, arXiv:2608.20287v2, pp.30, 32):
a point of the closed region `WholeCubeClosed δ` at which `H₂(a) − H₂(b)` attains its minimum over
that region. -/
def IsWholeCubeMinimizer (δ a b : ℝ) : Prop :=
  WholeCubeClosed δ a b ∧
    ∀ a' b' : ℝ, WholeCubeClosed δ a' b' → H2 a - H2 b ≤ H2 a' - H2 b'

end HoneycombCodes


