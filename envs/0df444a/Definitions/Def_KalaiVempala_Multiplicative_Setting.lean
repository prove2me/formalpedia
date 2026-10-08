-- Prove2me | Definitions.Def_KalaiVempala_Multiplicative_Setting
-- name    : KalaiVempala_Multiplicative_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:54.461934+00:00
-- url     : https://prove2.me/theorems/f4885a76-8a12-4f78-974f-4dacf29a47db
-- title:
--   §1.1, p. 294 — the FPL* perturbation law dμ(x) ∝ e^{−ε|x|₁} and the expected cost of FPL*(ε)
-- statement:
--   This file fixes the two objects of the multiplicative analysis of Kalai and Vempala that are not already in the setting of the additive analysis. The argmin oracle $M(x) = \arg\min_{d\in\mathcal D} d\cdot x$ is the shared definition `KalaiVempala.Additive.IsArgminOracle`, imported here.
--
--   1. **The perturbation law of FPL\*.** For $\varepsilon > 0$, $\mu_\varepsilon$ is the probability measure on $\mathbb R^n$ with density
--   $$\frac{d\mu_\varepsilon}{dx}(x) = \Big(\frac{\varepsilon}{2}\Big)^n e^{-\varepsilon |x|_1}, \qquad |x|_1 = \sum_{i=1}^n |x_i|.$$
--   Equivalently, the coordinates are independent and each equals $\pm r/\varepsilon$ with $r$ a standard exponential variable and a fair random sign.
--
--   2. **The expected cost of FPL\*(ε).** For a fixed state sequence $s_1, \dots, s_T$ write $s_{1:t} = s_1 + \dots + s_t$ (so $s_{1:0} = 0$). On period $t$ the algorithm FPL\*(ε) draws $p_t \sim \mu_\varepsilon$ and plays $M(s_{1:t-1} + p_t)$. Its expected total cost is
--   $$\mathbb E[\text{cost of FPL}^*(\varepsilon)] = \sum_{t=1}^T \int_{\mathbb R^n} s_t \cdot M(s_{1:t-1} + p)\, d\mu_\varepsilon(p).$$
--
--   These are the objects of Theorem 1.1(b) and of every step of its proof in §4; the law $\mu_\varepsilon$ is also the starting law of FLL\*(ε) (p. 304).
--
--   **Formalization Note** Vectors are `Fin n → ℝ` and $d\cdot s$ is the dot product `⬝ᵥ`. The page's "$\propto$" is made explicit by the normalising constant $(\varepsilon/2)^n$; for $\varepsilon > 0$ the measure has total mass $1$ (checked in a sorry-free sanity file). For $\varepsilon \le 0$ the formula gives no probability measure (the zero measure at $\varepsilon = 0$, $n \ge 1$; an infinite one for $\varepsilon < 0$); every theorem using it assumes $\varepsilon > 0$. The prefix sum $s_{1:t}$ is the published `OracleRO.ApproxFPL.prefixSum`, which is referenced, not redefined. By linearity of expectation the expected cost is a sum of one-period integrals, so it is the same number whether the $p_t$ are drawn fresh each period or shared, as the paper notes (p. 303). A Bochner integral of a non-integrable function is $0$ in Lean; the theorems carry measurability of $M$ and boundedness of $\mathcal D$, under which every integrand is bounded and integrable.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 294 (FPL*(ε) and its density dμ(x) ∝ e^{−ε|x|₁}); p. 303 (fresh vs. shared perturbations)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Additive_Setting

open MeasureTheory

namespace KalaiVempala.Multiplicative

/-- The perturbation law of FPL*(ε) (Kalai–Vempala 2005, p. 294): the density
`dμ(x) ∝ e^{-ε|x|₁}` on `ℝⁿ`, normalised by `(ε/2)ⁿ`. For `ε > 0` it is the product of `n`
one-dimensional Laplace laws with density `(ε/2) e^{-ε|x_i|}`, i.e. each coordinate is `±r/ε`
with `r` standard exponential, and it is a probability measure. -/
noncomputable def laplaceLaw (n : ℕ) (ε : ℝ) : Measure (Fin n → ℝ) :=
  volume.withDensity (fun x => ENNReal.ofReal ((ε / 2) ^ n * Real.exp (-(ε * ∑ i, |x i|))))

/-- The expected cost `E[∑_{t=1}^T M(s_{1:t-1} + p_t) · s_t]` of FPL*(ε) (p. 294) against a fixed
(oblivious) state sequence `s_1, …, s_T`, with `p_t` drawn from `laplaceLaw n ε`. By linearity
of expectation it is the sum over `t` of one integral against `μ`; this is the same number
whether the `p_t` are fresh each period or all equal (p. 303). -/
noncomputable def fplStarExpectedCost {n : ℕ} (M : (Fin n → ℝ) → (Fin n → ℝ))
    (s : ℕ → Fin n → ℝ) (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T,
    ∫ p, s t ⬝ᵥ M (OracleRO.ApproxFPL.prefixSum s (t - 1) + p) ∂(laplaceLaw n ε)

end KalaiVempala.Multiplicative


