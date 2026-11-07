-- Prove2me | Definitions.Def_EllipsoidFitting_massShift
-- name    : EllipsoidFitting_massShift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:56.485342+00:00
-- url     : https://prove2.me/theorems/e7342ebb-a1a3-48be-a848-56322dc1979a
-- title:
--   The perturbed function $\tilde F_\delta$ and its variance mass $A_\delta$
-- statement:
--   For $\delta>0$ let $\tilde F_\delta(x)=\max(2x,\delta)$ with Chebyshev coefficients $\tilde a_j=\mathbb E_{x\sim\mu_{\mathrm{sc}}}[\tilde F_\delta(x)P_j(x)]$ (so $\tilde C_F=\tilde a_0$). Rescaling by the $P_1$-coefficient,
--   $$
--   C_\delta=\frac{\tilde a_0}{\tilde a_1},\qquad b^{(\delta)}_j=\frac{\tilde a_j}{\tilde a_1},\qquad A_\delta=C_\delta^2+\sum_{j\ge2}\bigl(b^{(\delta)}_j\bigr)^2.
--   $$
--   $A_\delta$ is the variance mass that fixes the threshold $\gamma=1/(1+A_\delta)$ of the iteration run with $F_\delta=\tilde F_\delta/\tilde a_1$.
--
--   **Formalization Note** The sum is a `tsum` of nonnegative terms; the Claim 6.6 milestone asserts its summability.
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), §6.1, Step-2, p.83 (PDF p.85)

import Mathlib
import Definitions.Def_EllipsoidFitting_Fpos

set_option autoImplicit false

namespace EllipsoidFitting

open MeasureTheory

/-- **The perturbed function `F̃_δ`, its rescaled Chebyshev coefficients and the variance mass
`A_δ`.** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase Transition for Ellipsoid Fitting*,
arXiv:2608.12415 (version of Nov 3, 2026), §6.1, Step-2, p.83: "F̃δ(x) := max(2x, δ). Write its
Chebyshev expansion as F̃δ(x) = C̃F + ã1x + ∑_{j≥2} ãjPj(x). … Fδ(x) := F̃δ(x)/ã1 = Cδ + x +
∑_{j≥2} b(δ)_j Pj(x), where Cδ := C̃F/ã1, b(δ)_j := ãj/ã1. … Aδ := C²_δ + ∑_{j≥2} (b(δ)_j)²."

`Ftilde δ x = max(2x, δ)`. -/
noncomputable def Ftilde (δ x : ℝ) : ℝ := max (2 * x) δ

/-- `atilde δ j = E_{x∼µsc}[F̃_δ(x) P_j(x)]`, the `j`-th Chebyshev coefficient of `F̃_δ`
(`C̃_F = atilde δ 0`, `ã_1 = atilde δ 1`). -/
noncomputable def atilde (δ : ℝ) (j : ℕ) : ℝ := ∫ x, Ftilde δ x * (chebP j).eval x ∂muSC

/-- `Cdelta δ = C̃_F / ã_1`. -/
noncomputable def Cdelta (δ : ℝ) : ℝ := atilde δ 0 / atilde δ 1

/-- `bdelta δ j = ã_j / ã_1` (used for `j ≥ 2`). -/
noncomputable def bdelta (δ : ℝ) (j : ℕ) : ℝ := atilde δ j / atilde δ 1

/-- `Adelta δ = C_δ² + ∑_{j≥2} (b_j^{(δ)})²`.

**Formalization Note** The Chebyshev coefficients are the `L²(µsc)` inner products with the
orthonormal `P_j` (Definition 2.1). The sum is a `tsum` of nonnegative terms; Claim 6.6's
statement asserts its summability separately, so the junk value of a non-summable `tsum` is never
used. -/
noncomputable def Adelta (δ : ℝ) : ℝ := Cdelta δ ^ 2 + ∑' j : ℕ, bdelta δ (j + 2) ^ 2

end EllipsoidFitting


