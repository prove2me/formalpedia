-- Prove2me | Definitions.Def_IsingLTL_FreeEntropy_BetheFunctional
-- name    : IsingLTL_FreeEntropy_BetheFunctional
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:19.564072+00:00
-- url     : https://prove2.me/theorems/556e69fd-ea27-4029-9efe-4620129df161
-- title:
--   The Bethe functional $\varphi_h(\beta,B)$ and the Bethe prediction $\phi(\beta,B)$ ((2.9))
-- statement:
--   Let $P$ be a degree distribution with $\bar P<\infty$ and $h$ a real random variable with law $Q$. With $L\sim P$ independent of the i.i.d. copies $h_1,h_2,\dots$ of $h$, the **Bethe functional** is the right-hand side of (2.9):
--   $$\varphi_h(\beta,B)=\frac{\bar P}{2}\log\cosh(\beta)-\frac{\bar P}{2}\,\mathbb E\log[1+\tanh(\beta)\tanh(h_1)\tanh(h_2)]+\mathbb E\log\Big\{e^B\prod_{i=1}^L[1+\tanh(\beta)\tanh(h_i)]+e^{-B}\prod_{i=1}^L[1-\tanh(\beta)\tanh(h_i)]\Big\}.$$
--   The **Bethe prediction** for the free entropy density is $\phi(\beta,B)=\varphi_{h^*}(\beta,B)$, with $h^*$ the fixed point of Lemma 2.3 at $(\beta,B)$.
--
--   **Formalization Note** The expectation over $L$ is the series $\sum_l P_l\,\mathbb E[\cdots]$, each inner expectation an integral against the product law $Q^{\otimes l}$. All logarithms have positive arguments since $|\tanh|<1$, the integrands are continuous and bounded by an affine function of $l$, and the series converges absolutely because $\bar P<\infty$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 5, (2.9); p. 23 (the functional $h\mapsto\varphi_h$)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_DistRecursion

namespace IsingLTL.FreeEntropy

open MeasureTheory

/-- The **Bethe free-entropy functional** `φ_h(β, B)` (Dembo–Montanari, *Ising Models on Locally
Tree-Like Graphs*, arXiv:0804.4726v3, (2.9) p. 5; "the functional `h ↦ φ_h` that, given a random
variable `h`, evaluates the right-hand side of Equation (2.9)", p. 23), for a law `Q` of `h`:
with `L ∼ P` independent of the i.i.d. `h_i ∼ Q`,
`φ_h(β, B) = (P̄/2) log cosh β − (P̄/2) E log[1 + tanh β tanh h₁ tanh h₂]
  + E log{e^B ∏_{i=1}^L [1 + tanh β tanh h_i] + e^{−B} ∏_{i=1}^L [1 − tanh β tanh h_i]}`.

Formalization Note: the expectation over `L` is the series `∑_l P_l E[…]` with the inner
expectation an integral against the product law `Q^{⊗l}` (`Q^{⊗2}` for the pair term). Every
logarithm has a positive argument (`|tanh| < 1`), and the integrands are continuous with
`|log{…}| ≤ |B| + (l + 1) log 2 + l·|log(1 − |tanh β|)|`, so every integral is finite and the series
converges absolutely because `P̄ < ∞`. -/
noncomputable def betheFunctional (β B : ℝ) (D : DegreeDist) (Q : ProbabilityMeasure ℝ) : ℝ :=
  D.Pbar / 2 * Real.log (Real.cosh β)
    - D.Pbar / 2 * ∫ h : Fin 2 → ℝ,
        Real.log (1 + Real.tanh β * Real.tanh (h 0) * Real.tanh (h 1))
        ∂(Measure.pi fun _ => (Q : Measure ℝ))
    + ∑' l : ℕ, D.P l * ∫ h : Fin l → ℝ,
        Real.log (Real.exp B * ∏ i, (1 + Real.tanh β * Real.tanh (h i))
          + Real.exp (-B) * ∏ i, (1 - Real.tanh β * Real.tanh (h i)))
        ∂(Measure.pi fun _ => (Q : Measure ℝ))

/-- The **Bethe prediction** `φ(β, B) = φ_{h*}(β, B)` of (2.9) (p. 5), evaluated at the law of the
fixed point `h*` of Lemma 2.3 (the fixed point of (2.6) at `(β, B)` supported on `[0, ∞)`). -/
noncomputable def betheFreeEntropy (β B : ℝ) (D : DegreeDist) : ℝ :=
  betheFunctional β B D (nonnegFixedPoint β B D)

end IsingLTL.FreeEntropy


