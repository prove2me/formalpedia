-- Prove2me | Definitions.Def_HWMaskLeak_fhat
-- name    : HWMaskLeak_fhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:35.24265+00:00
-- url     : https://prove2.me/theorems/381ed4c2-5167-4401-aafd-bdd3a44c9bc2
-- title:
--   Normalized Fourier transform $\hat f(t)$ on $\mathbb Z/N\mathbb Z$
-- statement:
--   With the standard additive character $e_N(x):=\exp(2\pi\imath x/N)$, the normalized Fourier transform of $f:G\to\mathbb C$, $G=\mathbb Z/N\mathbb Z$, at $t\in G$ is
--   $$
--   \hat f(t):=\frac1N\sum_{x\in G}f(x)\,e_N(-xt).
--   $$
--
--   With this normalization $f(x)=\sum_t\hat f(t)e_N(xt)$ and Parseval reads $\frac1N\sum_x|f(x)|^2=\sum_t|\hat f(t)|^2$. All energies and spectral quantities of the mission are written with it.
--
--   **Formalization Note** $e_N(y)$ for $y\in\mathbb Z/N\mathbb Z$ is Mathlib's `ZMod.stdAddChar y` $=\exp(2\pi\imath\,y.\mathrm{val}/N)$, which is $N$-periodic and so agrees with $\exp(-2\pi\imath xt/N)$ on representatives.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §2.1, p.15

import Mathlib

namespace HWMaskLeak

/-- **The normalized Fourier transform on `ℤ/Nℤ`** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks
Leak Their Weight: From Additive Sharing to Learning with Physical Rounding*, preprint (version of
October 31, 2026, sha256 ab686360…), §2.1, p.15): with `e_N(x) := exp(2πı x/N)`, for `f : G → ℂ` and
`t ∈ G`, `f̂(t) := (1/N) Σ_{x ∈ G} f(x) e_N(−xt)`.

**Formalization Note** `e_N(y)` for `y ∈ ZMod N` is `ZMod.stdAddChar y = exp(2πı·y.val/N)`; since
`e_N` is `N`-periodic this equals `exp(−2πı x t/N)` on the representatives when `y = −(x t)`. -/
noncomputable def fhat (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (t : ZMod N) : ℂ :=
  (1 / (N : ℂ)) * ∑ x : ZMod N, f x * ZMod.stdAddChar (-(x * t))

end HWMaskLeak


