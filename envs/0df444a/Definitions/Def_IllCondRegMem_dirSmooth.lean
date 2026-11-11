-- Prove2me | Definitions.Def_IllCondRegMem_dirSmooth
-- name    : IllCondRegMem_dirSmooth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:00.116191+00:00
-- url     : https://prove2.me/theorems/256de7b4-c20e-4c64-b4ba-efbaa8f2cf5c
-- title:
--   Directional convolution $f^u(x)=\int f(x-tu)\phi(t)\,dt$
-- statement:
--   For a function $f:\mathbb R^d\to\mathbb R$, a direction $u\in\mathbb R^d$ and the kernel $\phi$ with parameters $R,r$, the **directional convolution** is
--   $$
--   f^u(x)=\int_{\mathbb R}f(x-tu)\,\phi(t)\,dt .
--   $$
--   It smooths $f$ along the line $\mathbb Ru$ only, and $\widehat{f^u}(\xi)=\hat f(\xi)\hat\phi(\xi^\top u)$. Lemma 13 bounds the $L^1$ distance between a pruned Gaussian mixture density and its directional convolution.
--
--   **Formalization Note** The integral is a Bochner integral; it is applied to densities in $L^1(\mathbb R^d)$, for which the integrand is integrable for almost every $x$.
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), eq. (10), p.12 (PDF p.13)

import Mathlib
import Definitions.Def_IllCondRegMem_projMat
import Definitions.Def_IllCondRegMem_phi

open MeasureTheory

namespace IllCondRegMem

/-- **Directional convolution** `f^u` (eq. (10)).
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), eq. (10),
p.12: "f^u(x) := ∫_ℝ f(x − tu) ϕ(t) dt", with the kernel `ϕ` of eq. (6) (parameters `R, r`).

**Formalization Note.** The integral is a Bochner integral over `t ∈ ℝ`. It is applied to
densities `f ∈ L¹(ℝ^d)`; `ϕ` is bounded and integrable, so for almost every `x` the integrand is
integrable and the value is the genuine convolution. -/
noncomputable def dirSmooth {d : ℕ} (R r : ℝ) (f : Vec d → ℝ) (u : Vec d) (x : Vec d) : ℝ :=
  ∫ t : ℝ, f (x - t • u) * phi R r t

end IllCondRegMem


