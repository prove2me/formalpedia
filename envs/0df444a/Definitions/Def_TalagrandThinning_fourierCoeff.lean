-- Prove2me | Definitions.Def_TalagrandThinning_fourierCoeff
-- name    : TalagrandThinning_fourierCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:50.693593+00:00
-- url     : https://prove2.me/theorems/95fb67ce-1847-487a-b89e-1166b2644ed1
-- title:
--   The $s$-biased characters $\phi_s$, $\omega^{(s)}_I$ and Fourier coefficients $\hat f_s(I)$
-- statement:
--   For $s\in(0,1)$ and $x\in\{0,1\}$ let
--
--   $$\phi_s(x)=\frac{x-s}{\sqrt{s(1-s)}},\qquad \omega^{(s)}_I(x)=\prod_{i\in I}\phi_s(x_i),\qquad \omega^{(s)}_\emptyset=1,$$
--
--   and for a real function $f$ on the cube let $\hat f_s(I)=\mathbb E_{\mu_s}[f\,\omega^{(s)}_I]$ be its **$s$-biased Fourier coefficient**.
--
--   These are the $p$-biased Fourier analysis tools of the kernel argument: the $\omega^{(s)}_I$ form an orthonormal basis of $L^2(\mu_s)$.
--
--   **Formalization Note** A bit $x\in\{0,1\}$ is a `Bool` read as $1$ (`true`) or $0$ (`false`). The definitions are total in $s$; outside $(0,1)$ the square root or division takes a Lean default value, and every statement assumes $0<s<1$.
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), §2, p.3, displays before (2.1) and eq. (2.1)

import Mathlib
import Definitions.Def_TalagrandThinning_prodLaw

set_option autoImplicit false

namespace TalagrandThinning

/-- The one-coordinate `s`-biased character `ϕ_s(x) = (x − s)/√(s(1 − s))` for `x ∈ {0,1}`
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, §2, p.3).

**Formalization Note** `x ∈ {0,1}` is a `Bool` read as `1` (`true`) or `0` (`false`). The paper
defines `ϕ_s` for `s ∈ (0,1)`; outside that range the square root or the division takes a Lean
default value, and every statement assumes `0 < s < 1`. -/
noncomputable def phi (s : ℝ) (b : Bool) : ℝ :=
  ((if b then 1 else 0) - s) / Real.sqrt (s * (1 - s))

/-- The `s`-biased Walsh function `ω^{(s)}_I(x) = ∏_{i∈I} ϕ_s(x_i)`, with `ω^{(s)}_∅ = 1`
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, §2, p.3). -/
noncomputable def omega {N : ℕ} (s : ℝ) (I : Finset (Fin N)) (x : Cube N) : ℝ :=
  ∏ i ∈ I, phi s (x i)

/-- The `s`-biased Fourier coefficient `f̂_s(I) = E_{µ_s}[f ω^{(s)}_I]`
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, §2, eq. (2.1), p.3). -/
noncomputable def fourierCoeff {N : ℕ} (s : ℝ) (f : Cube N → ℝ) (I : Finset (Fin N)) : ℝ :=
  expect s (fun x => f x * omega s I x)

end TalagrandThinning


