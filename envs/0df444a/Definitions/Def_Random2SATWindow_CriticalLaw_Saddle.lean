-- Prove2me | Definitions.Def_Random2SATWindow_CriticalLaw_Saddle
-- name    : Random2SATWindow_CriticalLaw_Saddle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:40:10.929357+00:00
-- url     : https://prove2.me/theorems/48781631-a932-4971-86ae-563ecaaac46f
-- title:
--   The Gaussian Hadamard integral $\Psi_\gamma(v,h;c)$, the tree function $T(v)$, $U(v)$ and the coefficient radius $\varrho(w)$
-- statement:
--   * (88) $\Psi_\gamma(v,h;c)=\dfrac1{\sqrt{2\pi h}}\displaystyle\int_{\mathbb R}\exp\Big(-\frac{t^2}{2h}-\frac{ve^{-it}}h\Big)(1-ve^{-it})^\gamma e^{cve^{-it}}\,dt$ (`Psi γ v h c`), with the principal power $(1-ve^{-it})^\gamma=\exp(\gamma\operatorname{Log}(1-ve^{-it}))$; it is used for $|v|<1$, $h>0$, real $\gamma$, $c$.
--   * §5.1.5: $T(v)$ solves $T=ve^T$, $T(0)=0$; on the closed disk $|v|\le e^{-1}$ it is given by its Lagrange series $T(v)=\sum_{m\ge1}\frac{m^{m-1}}{m!}v^m$ (`treeT`), and $U(v)=T(v)-T(v)^2/2$ (`treeU`).
--   * (110) $\varrho(w)=\dfrac1{ew(1+w)}$ (`coeffRadius`).
--
--   **Formalization Note.** $T$ is defined by the series the paper gives for it; the series converges absolutely on $|v|\le e^{-1}$ (Stirling: $m^{m-1}/m!\sim e^m/(\sqrt{2\pi}m^{3/2})$), and there it is the continuous extension of the solution of $T=ve^T$.
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), (88) printed p. 38 (PDF 40); §5.1.5 printed p. 43 (PDF 45); (110) printed p. 45 (PDF 47)

import Mathlib

set_option autoImplicit false

open Complex MeasureTheory

namespace Random2SATWindow.CriticalLaw

/-! # The Gaussian Hadamard integral `Ψ_γ`, the tree function and the coefficient radius

Ravelomanana, *Inside the Critical Window of Random 2-SAT*, STOC 2027 submission (manuscript
sha256 eef2fa67…), (88) printed p. 38 (PDF 40); §5.1.5 printed p. 43 (PDF 45); (110) printed
p. 45 (PDF 47). -/

/-- The elementary Gaussian Hadamard integral (88):
`Ψ_γ(v, h; c) = (1/√(2πh)) ∫_ℝ exp(-t²/(2h) - v e^{-it}/h) (1 - v e^{-it})^γ e^{c v e^{-it}} dt`,
with the principal power `(1 - v e^{-it})^γ = exp(γ Log(1 - v e^{-it}))` (used for `|v| < 1`,
`h > 0`, real `γ` and `c`). -/
noncomputable def Psi (γ : ℝ) (v : ℂ) (h c : ℝ) : ℂ :=
  ((Real.sqrt (2 * Real.pi * h))⁻¹ : ℝ) *
    ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2 / (2 * h) - v * Complex.exp (-Complex.I * t) / h) *
      (1 - v * Complex.exp (-Complex.I * t)) ^ (γ : ℂ) *
      Complex.exp (c * v * Complex.exp (-Complex.I * t))

/-- The tree function `T(v)`, the solution of `T = v e^T` with `T(0) = 0`, given on the closed
disk `|v| ≤ e^{-1}` by its Lagrange series `T(v) = Σ_{m ≥ 1} m^{m-1} v^m / m!` (§5.1.5). -/
noncomputable def treeT (v : ℂ) : ℂ :=
  ∑' m : ℕ, (((m + 1 : ℕ) : ℂ) ^ m / ((m + 1).factorial : ℂ)) * v ^ (m + 1)

/-- `U(v) = T(v) - T(v)²/2` (§5.1.5). -/
noncomputable def treeU (v : ℂ) : ℂ := treeT v - treeT v ^ 2 / 2

/-- The coefficient radius (110): `ϱ(w) = 1 / (e w (1 + w))`. -/
noncomputable def coeffRadius (w : ℝ) : ℝ := 1 / (Real.exp 1 * w * (1 + w))

end Random2SATWindow.CriticalLaw


