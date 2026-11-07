-- Prove2me | Definitions.Def_ErasureQTanner_kp22Kappa
-- name    : ErasureQTanner_kp22Kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:45.037289+00:00
-- url     : https://prove2.me/theorems/79185af1-10f0-42f0-9edc-65cdfbb54c5c
-- title:
--   Binary entropy, $h^{-1}$, and the robustness constant of Theorem 12
-- statement:
--   Let $h(x)=-x\log_2x-(1-x)\log_2(1-x)$ be the binary entropy and $h^{-1}$ its inverse on $[0,\tfrac12]$. The robustness constant of Theorem 12 is
--   $$\kappa(\rho_1,\rho_2):=\frac12\min\Big\{\frac14h^{-1}\big(\frac{\rho_1}8\big)h^{-1}\big(\frac{\rho_2}8\big),\ h^{-1}\big(\frac{\rho_1\rho_2}8\big)\Big\}.$$
--
--   **Formalization Note** $h$ is Mathlib's `Real.binEntropy` (natural logarithm) divided by $\log2$, since §6 takes $\log$ in base 2. $h^{-1}$ is the `sInf` of the roots in $[0,\frac12]$, a singleton on $[0,1]$. Off $[0,1]$ it returns the junk value $0$, but Theorem 12's arguments lie in $(0,\frac18)$.
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), §6, p.13; Theorem 12, p.20

import Mathlib

set_option autoImplicit false

namespace ErasureQTanner

/-- Binary entropy in bits (§6, p.13: `log` is base 2). -/
noncomputable def binH (x : ℝ) : ℝ := Real.binEntropy x / Real.log 2

/-- `h⁻¹`, the inverse of the binary entropy on `[0, 1/2]`. On `[0, 1]` the root is unique and `sInf` returns it; the
statements using it take arguments in `(0, 1)`. -/
noncomputable def binHInv (y : ℝ) : ℝ := sInf {x | x ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ binH x = y}

/-- The constant of Theorem 12: Pfister, Sprumont, Zémor, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.20:
"`κ := (1/2) min{ (1/4) h⁻¹(ρ₁/8) h⁻¹(ρ₂/8), h⁻¹(ρ₁ρ₂/8) }`".

**Formalization Note.** The binary entropy is `Real.binEntropy` (nats) divided by `log 2`. `binHInv` is an `sInf` of the
roots in `[0, 1/2]`: the set is a singleton on `[0, 1]`; outside it the set is empty and the value `0` is junk, but
Theorem 12's arguments are in `(0, 1/8)`. -/
noncomputable def kp22Kappa (ρ₁ ρ₂ : ℝ) : ℝ :=
  (1 / 2) * min ((1 / 4) * binHInv (ρ₁ / 8) * binHInv (ρ₂ / 8)) (binHInv (ρ₁ * ρ₂ / 8))

end ErasureQTanner


