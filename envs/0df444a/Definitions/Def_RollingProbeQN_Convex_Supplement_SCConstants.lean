-- Prove2me | Definitions.Def_RollingProbeQN_Convex_Supplement_SCConstants
-- name    : RollingProbeQN_Convex_Supplement_SCConstants
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:43:15.061991+00:00
-- url     : https://prove2.me/theorems/93f20d10-e20f-49ae-96e7-d78c6b64033a
-- title:
--   The constants $T_\sharp$ and $C_\sharp$ of (70)
-- statement:
--   For $\sigma\in(0,1)$, $\mu>0$ and the bounds $\chi,L_1,L_2,R$, with $C_x=1+\sigma/\sqrt{1-\sigma^2}$ and the smoothness step $\underline\lambda$ (the positive root of $\lambda L_1=\sigma\sqrt{1+\mu\lambda}$),
--   $$T_\sharp=\Big(1+C_x+\frac1{\sqrt{1-\sigma^2}}\Big)\Big(2+\log_+\frac1{\mu\underline\lambda}\Big)+4\sqrt2+\frac2{\sqrt{1-\sigma^2}},\qquad C_\sharp=\frac2\sigma\Big[\chi L_1+2L_2R+(2\chi+1)L_2R\,T_\sharp\Big],$$
--   where $\log_+=\max\{0,\log\}$. The superlinear scale of Theorem 4.2 is $B_\sharp=C_\sharp/\mu$.
--
--   $T_\sharp$ bounds the path length of the strongly convex iterates by $T_\sharp R$, and $C_\sharp$ bounds the inverse-stepsize moment (20).
--
--   **Formalization Note** $C_x$ is the published constant `Cx`.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, (70), p. 52; §4.2, p. 15

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Cx
import Definitions.Def_RollingProbeQN_Convex_Supplement_SCSubroutine

namespace RollingProbeQN.Convex.Supplement

/-- **The path-length factor `T♯`, (70).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, (70), p. 52:
"`T♯ = (1 + Cx + 1/√(1 − σ²))(2 + log+ 1/(μλ)) + 4√2 + 2/√(1 − σ²)`", where
`Cx = 1 + σ/√(1 − σ²)` (p. 53) and `λ` (underlined) is the smoothness step.

**Formalization Note.** `Cx` is the published `RollingProbeQN.Convex.Cx`; the smoothness step `λ̲` is
`rootSC L₁ σ μ`; `log₊ = max{0, log}` (p. 13). -/
noncomputable def Tsharp (σ μ L₁ : ℝ) : ℝ :=
  (1 + Cx σ + 1 / Real.sqrt (1 - σ ^ 2)) *
      (2 + max 0 (Real.log (1 / (μ * rootSC L₁ σ μ)))) +
    4 * Real.sqrt 2 + 2 / Real.sqrt (1 - σ ^ 2)

/-- **The moment constant `C♯`, (70).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §4.2, p. 15 and (70), p. 52:
"`C♯ = (2/σ)[χL1 + 2L2R + (2χ + 1)L2R T♯]`, `B♯ = C♯/μ`".

`Csharp σ μ χ L₁ L₂ R` is `C♯`; the theorems write `B♯ = C♯/μ`. -/
noncomputable def Csharp (σ μ : ℝ) (χ : ℕ) (L₁ L₂ R : ℝ) : ℝ :=
  (2 / σ) * ((χ : ℝ) * L₁ + 2 * L₂ * R + (2 * (χ : ℝ) + 1) * L₂ * R * Tsharp σ μ L₁)

end RollingProbeQN.Convex.Supplement


