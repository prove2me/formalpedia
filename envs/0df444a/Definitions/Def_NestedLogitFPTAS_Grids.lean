-- Prove2me | Definitions.Def_NestedLogitFPTAS_Grids
-- name    : NestedLogitFPTAS_Grids
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:35.540491+00:00
-- url     : https://prove2.me/theorems/39fd89d1-5da7-4ba0-b93a-ce78d55ca713
-- title:
--   §3.3–§3.4, pp.12–13 — accuracy levels and the corrected grids $\mathcal D_\omega$, $\mathcal D_\rho$
-- statement:
--   With $\hat\epsilon=\min(\epsilon,1)$, the accuracy levels of §3.4 are
--   $$
--   \xi_\omega=\frac{\hat\epsilon\gamma^-}{2560M\gamma^+},\quad \xi_\rho=\frac{\hat\epsilon}{640M},\quad \delta_\rho=\frac{\hat\epsilon}{80},\quad \delta_\omega=\frac{\hat\epsilon}{640\gamma^+}.
--   $$
--   The grids are $\mathcal D_\omega=\{0\}\cup\{(1+\xi_\omega)^p\,(W^\downarrow)^{\gamma^+}:0\le p\le P_\omega\}$ and $\mathcal D_\rho=\{0\}\cup\{(1+\xi_\rho)^q\,L_\rho:0\le q\le Q_\rho\}$, where
--   $$
--   P_\omega=\Big\lceil\frac{\gamma^+\log(W^\uparrow/W^\downarrow)+\log M}{\log(1+\xi_\omega)}\Big\rceil+M+1,\quad L_\rho=(1-\xi_\rho)^M\pi_{\min}r_{\min}(W^\downarrow)^{\gamma^+},\quad Q_\rho=\Big\lceil\frac{\log\big(M r_{\max}(W^\uparrow)^{\gamma^+}/L_\rho\big)}{\log(1+\xi_\rho)}\Big\rceil.
--   $$
--   The module also defines the rounding $\langle x\rangle_{\mathcal D}$ down to a grid, and the factors $L_w=1+\log M+\log(W^\uparrow/W^\downarrow)$, $L_r=1+\log M+\log(r_{\max}/(\pi_{\min}r_{\min}))$ of the running time.
--
--   **Formalization Note** The paper's grids stop at the range of a single nest and start at $\pi_{\min}r_{\min}(W^\downarrow)^{\gamma^+}$. Both ends are corrected, since the printed ones refute Lemmas 3.2, 3.4 and 3.6 on $M=2$ singleton nests with unit data, $w_0=2$, $\mathcal C=2$; see the docstrings of `Pomega` and `Lrho`. `omegaAt p` and `rhoAt q` list the grids in ascending order, with index $0$ the point $0$.
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), §3.3, p.12; §3.4, p.13; §3.7, p.16 ("round their argument down"); §3.4, p.14

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model

namespace NestedLogitFPTAS

/-- `ϵ̂ = min(ϵ, 1)`, the accuracy that enters all the parameters.

**Formalization Note.** Theorem 1.1 says "any accuracy level ϵ > 0", but the parameters need `ϵ ≤ 80`
and the proofs `ϵ ≤ 4`. At `ϵ ≥ 1` the claim is empty because `(1 - ϵ)·R ≤ 0`. So the program replaces
`ϵ` with `ϵ̂`, which changes nothing for `ϵ ≤ 1`. -/
noncomputable def epsHat (ε : ℝ) : ℝ := min ε 1

namespace Instance

variable {n M : ℕ} (I : Instance n M)

/-- `ξω = ϵγ⁻/(2560Mγ⁺)`, §3.4, p.13, with `ϵ̂` for `ϵ`. -/
noncomputable def xiOmega (ε : ℝ) : ℝ :=
  epsHat ε * I.gammaMinus / (2560 * (M : ℝ) * I.gammaPlus)

/-- `ξρ = ϵ/(640M)`, §3.4, p.13, with `ϵ̂` for `ϵ`. -/
noncomputable def xiRho (_I : Instance n M) (ε : ℝ) : ℝ := epsHat ε / (640 * (M : ℝ))

/-- `δρ = ϵ/80`, §3.4, p.13, with `ϵ̂` for `ϵ`. -/
noncomputable def deltaRho (_I : Instance n M) (ε : ℝ) : ℝ := epsHat ε / 80

/-- `δω = ϵ/(640γ⁺)`, §3.4, p.13, with `ϵ̂` for `ϵ`. -/
noncomputable def deltaOmega (ε : ℝ) : ℝ := epsHat ε / (640 * I.gammaPlus)

/-- The last exponent `Pω` of `Dω` (**corrected**).

**Formalization Note.** §3.3, p.12 prints `p ≤ γ⁺·log_{1+ξω}(W↑/W↓)`, the range of one nest, but the
states of the DP hold sums over nests. On `M = 2`, one unit product per nest, `w₀ = 2`, `C = 2` and no
nest weight, the printed grid is `{0, 1}` and the DP cannot offer both products: `R(S̃) ≤ 1/3`, while
the optimum is `1/2`. The top is raised by `log M` and by `M + 1` steps, which is what the rounding of
Lemma 3.6 needs. -/
noncomputable def Pomega (ε : ℝ) : ℕ :=
  ⌈(I.gammaPlus * Real.log (I.wUp / I.wDown) + Real.log (M : ℝ)) /
      Real.log (1 + I.xiOmega ε)⌉₊ + M + 1

/-- The first positive point `Lρ = (1 - ξρ)^M·π_min·r_min·W↓^{γ⁺}` of `Dρ` (**corrected**).

**Formalization Note.** §3.3, p.12 starts at `π_min·r_min·W↓^{γ⁺}`. Rounding
`(1 - ξρ)^{M-k}·Rₖ·w₊^{γₖ}` down to that grid can give `0` for a nonempty `Sₖ`, after which
`A(k, ω*ₖ, 0) = ∞` and Lemma 3.6(3) fails. -/
noncomputable def Lrho (ε : ℝ) : ℝ :=
  (1 - I.xiRho ε) ^ M * I.piMin * I.rMin * I.wDown ^ I.gammaPlus

/-- The last exponent `Qρ = ⌈log(M·r_max·W↑^{γ⁺}/Lρ)/log(1+ξρ)⌉` of `Dρ` (**corrected**, see
`Pomega` and `Lrho`). -/
noncomputable def Qrho (ε : ℝ) : ℕ :=
  ⌈Real.log ((M : ℝ) * I.rMax * I.wUp ^ I.gammaPlus / I.Lrho ε) /
      Real.log (1 + I.xiRho ε)⌉₊

/-- The point of index `p` of `Dω`, ascending: index `0` is `0`, and index `p + 1` is
`(1 + ξω)^p·W↓^{γ⁺}`, for `0 ≤ p ≤ Pω`. -/
noncomputable def omegaAt (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | p + 1 => (1 + I.xiOmega ε) ^ p * I.wDown ^ I.gammaPlus

/-- The point of index `q` of `Dρ`, ascending: index `0` is `0`, and index `q + 1` is
`(1 + ξρ)^q·Lρ`, for `0 ≤ q ≤ Qρ`. -/
noncomputable def rhoAt (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | q + 1 => (1 + I.xiRho ε) ^ q * I.Lrho ε

/-- `Dω = {(1+ξω)^p·W↓^{γ⁺} : 0 ≤ p ≤ Pω} ∪ {0}`, the corrected grid of §3.3, p.12. -/
noncomputable def Domega (ε : ℝ) : Finset ℝ :=
  (Finset.range (I.Pomega ε + 2)).image (I.omegaAt ε)

/-- `Dρ = {(1+ξρ)^q·Lρ : 0 ≤ q ≤ Qρ} ∪ {0}`, the corrected grid of §3.3, p.12. -/
noncomputable def Drho (ε : ℝ) : Finset ℝ :=
  (Finset.range (I.Qrho ε + 2)).image (I.rhoAt ε)

/-- `L_w = 1 + log M + log(W↑/W↓)`, the logarithmic factor of the corrected running time.

**Formalization Note.** The printed expression of §3.4, p.14 has `log(W↑/W↓)`, which vanishes at
`W↑ = W↓` although the program does work there, and the corrected grids add `log M`. -/
noncomputable def Lw : ℝ := 1 + Real.log (M : ℝ) + Real.log (I.wUp / I.wDown)

/-- `L_r = 1 + log M + log(r_max/(π_min·r_min))`, the second logarithmic factor of the corrected
running time; see `Lw`. -/
noncomputable def Lr : ℝ := 1 + Real.log (M : ℝ) + Real.log (I.rMax / (I.piMin * I.rMin))

end Instance

open Classical in
/-- `⟨x⟩_D`, the rounding of `x` down to the nearest number of the grid `D`, §3.7, p.16. It is used
only for `x ≥ 0` and grids containing `0`, so the set below is nonempty there. -/
noncomputable def roundDown (D : Finset ℝ) (x : ℝ) : ℝ := maxOn (D.filter (· ≤ x)) id

end NestedLogitFPTAS


