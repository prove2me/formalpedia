-- Prove2me | Definitions.Def_FourierEntropyApprox_entropyFun
-- name    : FourierEntropyApprox_entropyFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:28.724198+00:00
-- url     : https://prove2.me/theorems/9f62d50e-01e3-4442-ae1a-2196930a33db
-- title:
--   The Fourier entropy functional $\mathcal E(\widehat g^2)$ (Fourier entropy $\mathbb H(\widehat f^2)$ for Boolean $f$)
-- statement:
--   For an arbitrary function $g:\{-1,1\}^n\to\mathbb C$ (or $\mathbb R$), the **entropy functional** of its squared Fourier coefficients is
--
--   $$\mathcal E(\widehat g^2)=\sum_{S\subseteq[n]}|\widehat g(S)|^2\log_2\frac{1}{|\widehat g(S)|^2},$$
--
--   with the convention $0\log(1/0)=0$. When $f:\{-1,1\}^n\to\{-1,1\}$ is Boolean, Parseval's identity gives $\sum_S|\widehat f(S)|^2=1$, so $\{|\widehat f(S)|^2\}_S$ is a probability distribution on subsets of $[n]$, and $\mathcal E(\widehat f^2)$ is its Shannon entropy, the **Fourier entropy** $\mathbb H(\widehat f^2)$ of $f$ (Definition 2.2).
--
--   The Fourier entropy is the quantity of the Fourier Entropy-Influence conjecture; the functional $\mathcal E$ on arbitrary functions is what the approximation theorem (Theorem 3.1) bounds.
--
--   **Formalization Note** The term $p\log_2(1/p)$ is written as $\mathrm{negMulLog}(p)/\ln 2$ with $\mathrm{negMulLog}(p)=-p\ln p$, which is $0$ at $p=0$. Logarithms are to base two, as the paper fixes on p.2. No separate definition is made for Boolean $f$.
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Definition 2.2 and display (8), p.9 (PDF p.9); logarithm convention p.2

import Mathlib
import Definitions.Def_FourierEntropyApprox_fourierCoeff

namespace FourierEntropyApprox

/-!
# The Fourier entropy functional

M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…). Definition 2.2, p.9: "For a Boolean function f : {−1, 1}ⁿ → {−1, 1}, its Fourier entropy
(denoted ℍ(f̂²)) […] ℍ(f̂²) := ∑_{S⊆[n]} |f̂(S)|² log 1/|f̂(S)|²". Display (8), p.9: "For an arbitrary function
g : {−1, 1}ⁿ → ℂ, we will define ℰ(ĝ²) := ∑_{S⊆[n]} |ĝ(S)|² log 1/|ĝ(S)|²." Logarithms convention, p.2:
"logarithms are to base two unless otherwise indicated, and 0 log(1/0) = 0."

**Formalization Note.**
* `entropyFun g` is `ℰ(ĝ²)` of (8); for a Boolean `f` it is the Fourier entropy `ℍ(f̂²)` of Definition 2.2,
  so no separate definition is made.
* The term `p log₂(1/p)` with `p = |ĝ(S)|²` is `Real.negMulLog p / Real.log 2`; `Real.negMulLog 0 = 0`
  gives the convention `0 log(1/0) = 0`.
-/

/-- The entropy functional `ℰ(ĝ²) = ∑_S |ĝ(S)|² log₂(1/|ĝ(S)|²)` ((8), p.9; Definition 2.2 for Boolean `g`). -/
noncomputable def entropyFun {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (g : Cube n → 𝕜) : ℝ :=
  ∑ S : Finset (Fin n), Real.negMulLog (‖fourierCoeff g S‖ ^ 2) / Real.log 2

end FourierEntropyApprox


