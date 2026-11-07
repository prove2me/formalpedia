-- Prove2me | Definitions.Def_FourierEntropyApprox_approxSpectralNorm
-- name    : FourierEntropyApprox_approxSpectralNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:17.554646+00:00
-- url     : https://prove2.me/theorems/151ded51-c80a-4807-b970-61afdc201002
-- title:
--   The $\varepsilon$-approximate spectral norm $\|\widehat f\|_{1,\varepsilon}$
-- statement:
--   Let $f:\{-1,1\}^n\to\{-1,1\}$ be Boolean and $0\le\varepsilon<1$. The **$\varepsilon$-approximate spectral norm** of $f$ is the least spectral norm of a real polynomial that approximates $f$ pointwise within $\varepsilon$:
--
--   $$\|\widehat f\|_{1,\varepsilon}=\min\Big\{\sum_{S}|\widehat p(S)| \;:\; |p(x)-f(x)|\le\varepsilon\ \text{for every }x\in\{-1,1\}^n\Big\}.$$
--
--   A function can have a large spectral norm while having a pointwise approximant of small spectral norm; the approximate spectral norm is the complexity measure in which the paper's main entropy bound, Theorem 3.2, is stated.
--
--   **Formalization Note** The approximants are all real functions on the cube, which are exactly the real multilinear polynomials. The minimum is written as an infimum (`sInf`) of the set of feasible spectral norms. For Boolean $f$ and $\varepsilon\ge0$ this set is nonempty ($p=f$) and bounded below by $0$, and the minimum is attained, so the infimum is the page's minimum. The definition is total in $\varepsilon$ and $f$; the mission uses it only for Boolean $f$ and $0\le\varepsilon<1$.
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), §2, pp.8–9 (PDF pp.8–9): definition of the ε-approximate spectral norm

import Mathlib
import Definitions.Def_FourierEntropyApprox_fourierCoeff

namespace FourierEntropyApprox

/-!
# The ε-approximate spectral norm

M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), §2, pp.8–9: "For 0 ≤ ε < 1, the ε-approximate spectral norm ‖f̂‖_{1,ε} of a Boolean function
f is defined as ‖f̂‖_{1,ε} = min { ∑_S |p̂(S)| : |p(x) − f(x)| ≤ ε for every x ∈ {−1, 1}ⁿ }."

**Formalization Note.**
* The approximants `p` are arbitrary real functions on the cube, i.e. real multilinear polynomials.
* The minimum is written as `sInf` of the set of spectral norms of feasible `p`. For a Boolean `f` and `ε ≥ 0`
  the set is nonempty (`p = f`) and bounded below by `0`, and the minimum is attained (a coercive continuous
  objective on a closed set in finite dimension), so `sInf` is the page's minimum.
* The definition is total in `ε` and `f`; the paper uses it for `0 ≤ ε < 1` and Boolean `f`, which is how
  every statement of this mission applies it.
-/

/-- `‖f̂‖_{1,ε}`: the least spectral norm of a real `p` with `|p(x) − f(x)| ≤ ε` for every `x` (pp.8–9). -/
noncomputable def approxSpectralNorm {n : ℕ} (ε : ℝ) (f : Cube n → ℝ) : ℝ :=
  sInf {s : ℝ | ∃ p : Cube n → ℝ, (∀ x, |p x - f x| ≤ ε) ∧ spectralNorm p = s}

end FourierEntropyApprox


