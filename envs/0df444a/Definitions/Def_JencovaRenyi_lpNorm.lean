-- Prove2me | Definitions.Def_JencovaRenyi_lpNorm
-- name    : JencovaRenyi_lpNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:38.24768+00:00
-- url     : https://prove2.me/theorems/d3903d80-7f88-465a-bc2d-7304d5e1bd0d
-- title:
--   Kosaki's $L_p(\mathcal M,\varphi)$ norm $\|\cdot\|_{p,\varphi}$, $1\le p\le\infty$
-- statement:
--   For a normal positive functional $\varphi$ and $1\le p\le\infty$, the norm of $L_p(\mathcal M,\varphi)\subseteq L_1(\mathcal M)$ is, as a $[0,\infty]$-valued gauge on $L_1(\mathcal M)$:
--
--   1. $p=\infty$: $\|k\|_{\infty,\varphi}$;
--   2. $p = 1$: $\|k\|_1$ if $k = eke$ ($e = s(\varphi)$), and $\infty$ otherwise;
--   3. $1<p<\infty$: the interpolation norm $\|k\|_{1/p}$ of $C_{1/p}(L_\infty(\mathcal M,\varphi), L_1(\mathcal M))$.
--
--   Then $L_p(\mathcal M,\varphi) = \{k : \|k\|_{p,\varphi}<\infty\}$. For faithful $\varphi$ this is Kosaki's space; on finite-dimensional algebras $\|X\|_{p,\varphi} = \|\rho_\varphi^{-1/2q}X\rho_\varphi^{-1/2q}\|_p$ (Example 2.4), so $\log\|h_\psi\|_{\alpha,\varphi}$ gives the sandwiched Rényi divergence.
--
--   **Formalization Note** For non-faithful $\varphi$ the paper works on $e\mathcal Me$ (p.10). Here the interpolation is between $\{h_x\}$ (equal to $\{h_{exe}\}$) and all of $L_1(\mathcal M)$; this gives the same space and norm, because for an admissible $f$ the function $f - efe$ is bounded, analytic in the strip and zero on $\operatorname{Re}z=0$, hence zero. Only $p=1$ needs the explicit support clause. Exponents $p<1$ are never used.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §2.2, p.5 ($L_p(\mathcal M,\varphi) := C_{1/p}(L_\infty(\mathcal M,\varphi), L_1(\mathcal M))$); §3, p.10 (non-faithful $\varphi$)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_symmEmbed
import Definitions.Def_JencovaRenyi_infNorm
import Definitions.Def_JencovaRenyi_interpNorm

open scoped ENNReal
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Kosaki's norm `‖k‖_{p,φ}` of `L_p(M, φ) := C_{1/p}(L_∞(M, φ), L_1(M))` (Jenčová,
arXiv:1609.08462v4, §2.2, p.5; extended to non-faithful `φ` in §3, p.10), as an extended gauge on
`L_1(M) ≃ M_*`, for `1 ≤ p ≤ ∞`:

* `p = ∞`: the norm `‖·‖_{∞,φ}` of `L_∞(M, φ)` (`infNorm`, p.4);
* `p = 1`: `‖k‖_1` (the predual norm) if `k = eke` with `e = s(φ)` (p.10), and `∞` otherwise;
* `1 < p < ∞`: the interpolation norm `‖k‖_{1/p}` of `C_{1/p}(L_∞(M, φ), L_1(M))` (B.9), p.22.

`L_p(M, φ) = {k : ‖k‖_{p,φ} < ∞}`.

**Formalization Note.** The value `⊤` means "not in `L_p(M, φ)`". For `φ` not faithful the paper
works on `eMe` (p.10); here the interpolation is between `L_∞(M, φ) = {h_x}` (which equals
`{h_{exe}}`) and all of `L_1(M)`. Both give the same space and norm: for an admissible `f`, the
function `z ↦ f(z) − e f(z) e` is bounded, continuous on the strip, analytic inside and zero on
`Re z = 0`, hence zero. The exponent `p < 1` is never used. -/
noncomputable def lpNorm {A : StarSubalgebra ℂ (H →L[ℂ] H)} (S : StandardForm A)
    (φ : Predual A) (p : ℝ≥0∞) (k : Predual A) : ℝ≥0∞ :=
  open Classical in
  if p = ⊤ then infNorm S φ k
  else if p = 1 then (if IsSupported φ k then (‖k‖₊ : ℝ≥0∞) else ⊤)
  else interpNorm (infNorm S φ) (p⁻¹).toReal k

end JencovaRenyi


