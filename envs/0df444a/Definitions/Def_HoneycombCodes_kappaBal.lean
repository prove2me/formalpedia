-- Prove2me | Definitions.Def_HoneycombCodes_kappaBal
-- name    : HoneycombCodes_kappaBal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:29:41.168474+00:00
-- url     : https://prove2.me/theorems/42763c9d-5751-4a70-a970-39c090886f55
-- title:
--   Entropy-balanced exponent $\kappa_{bal}(\delta)$, $\kappa_{explicit}$ and $\kappa_{pair}$
-- statement:
--   For $0<x\le 1/2$ and $0<t<\pi/(4(1-x))$ put
--
--   $$
--   S_+=\sqrt{x(1-x)}\cos((1-2x)t),\quad S_-=\sqrt{x(1-x)}\sin t,\quad
--   A_{bal}=(1-x)\cos(2xt),\quad B_{bal}=x\cos(2(1-x)t),
--   $$
--
--   $$
--   P_{bal}=\frac{s_\delta/2-S_-}{S_+-S_-},\qquad E_{bal}=\sqrt{(A_{bal}-B_{bal})^2+4A_{bal}B_{bal}P_{bal}},\qquad z_{bal}=\frac{1-E_{bal}}{2},
--   $$
--
--   with $s_\delta=1-2\delta$, and
--
--   $$
--   \Phi_{bal}(x,t;\delta)=H_2(x)+(1-x)H_2(\sin^2(xt))+xH_2(\sin^2((1-x)t))-H_2(z_{bal}).
--   $$
--
--   Let $D_{bal}(\delta)$ be the pairs in this range with $0<P_{bal}<1$ and $0<E_{bal}<1$. The **entropy-balanced exponent** is $\kappa_{bal}(\delta)=\inf_{D_{bal}(\delta)}\Phi_{bal}$, and
--
--   $$
--   \kappa_{explicit}=\min\{\kappa_{CW},\kappa_{face},\kappa_{bal}\},\qquad \kappa_{pair}=\min\{\kappa_{CW},\kappa_{bal}\}.
--   $$
--
--   On $D_{bal}(\delta)$ the honeycomb parameters $\eta=\sin^2(xt)$, $\rho=\sin^2((1-x)t)$, $z=z_{bal}$ lie on the spectral boundary $\Gamma_{HC}=s_\delta$.
--
--   **Formalization Note** A real `sInf` of the objective values over $D_{bal}(\delta)$.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), eqs. (60)–(63), pp.28–29 (PDF 30–31); κ_explicit, κ_pair: p.29 (PDF 31)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaCW
import Definitions.Def_HoneycombCodes_kappaFace

set_option autoImplicit false

namespace HoneycombCodes

/-- `S₊(x, t) = √(x(1 − x)) cos((1 − 2x)t)`, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework
for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), eq. (61), p.28 (PDF 30). -/
noncomputable def Splus (x t : ℝ) : ℝ :=
  Real.sqrt (x * (1 - x)) * Real.cos ((1 - 2 * x) * t)

/-- `S₋(x, t) = √(x(1 − x)) sin t`, arXiv:2608.20287v2, eq. (61), p.28. -/
noncomputable def Sminus (x t : ℝ) : ℝ :=
  Real.sqrt (x * (1 - x)) * Real.sin t

/-- `A_bal(x, t) = (1 − x) cos(2xt)`, arXiv:2608.20287v2, eq. (61), p.28. -/
noncomputable def Abal (x t : ℝ) : ℝ :=
  (1 - x) * Real.cos (2 * x * t)

/-- `B_bal(x, t) = x cos(2(1 − x)t)`, arXiv:2608.20287v2, eq. (61), p.28. -/
noncomputable def Bbal (x t : ℝ) : ℝ :=
  x * Real.cos (2 * (1 - x) * t)

/-- `P_bal(x, t; δ) = (s_δ/2 − S₋(x, t))/(S₊(x, t) − S₋(x, t))`, `s_δ = 1 − 2δ`,
arXiv:2608.20287v2, eq. (62), p.29 (PDF 31). -/
noncomputable def Pbal (x t δ : ℝ) : ℝ :=
  ((1 - 2 * δ) / 2 - Sminus x t) / (Splus x t - Sminus x t)

/-- `E_bal(x, t; δ) = √((A_bal − B_bal)² + 4A_bal B_bal P_bal)`, arXiv:2608.20287v2, eq. (62),
p.29 (PDF 31). -/
noncomputable def Ebal (x t δ : ℝ) : ℝ :=
  Real.sqrt ((Abal x t - Bbal x t) ^ 2 + 4 * Abal x t * Bbal x t * Pbal x t δ)

/-- `z_bal(x, t; δ) = (1 − E_bal(x, t; δ))/2`, arXiv:2608.20287v2, eq. (62), p.29. -/
noncomputable def zbal (x t δ : ℝ) : ℝ :=
  (1 - Ebal x t δ) / 2

/-- The balanced objective (63),
`Φ_bal(x, t; δ) = H₂(x) + (1 − x)H₂(sin²(xt)) + xH₂(sin²((1 − x)t)) − H₂(z_bal(x, t; δ))`,
arXiv:2608.20287v2, p.29 (PDF 31). -/
noncomputable def PhiBal (x t δ : ℝ) : ℝ :=
  H2 x + (1 - x) * H2 (Real.sin (x * t) ^ 2) + x * H2 (Real.sin ((1 - x) * t) ^ 2) -
    H2 (zbal x t δ)

/-- The **entropy-balanced exponent** `κ_bal(δ) = inf_{(x, t) ∈ D_bal(δ)} Φ_bal(x, t; δ)`, where
`D_bal(δ)` is the set of pairs with `0 < x ≤ 1/2`, `0 < t < π/(4(1 − x))` (60), `0 < P_bal < 1`
and `0 < E_bal < 1`, arXiv:2608.20287v2, §6.1, pp.28–29 (PDF 30–31).

**Formalization Note.** A real `sInf` of the set of objective values over `D_bal(δ)`. -/
noncomputable def kappaBal (δ : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x t : ℝ, 0 < x ∧ x ≤ 1 / 2 ∧ 0 < t ∧ t < Real.pi / (4 * (1 - x)) ∧
    0 < Pbal x t δ ∧ Pbal x t δ < 1 ∧ 0 < Ebal x t δ ∧ Ebal x t δ < 1 ∧
    r = PhiBal x t δ}

/-- `κ_explicit = min{κ_CW, κ_face, κ_bal}`, arXiv:2608.20287v2, §6.1, p.29 (PDF 31). -/
noncomputable def kappaExplicit (δ : ℝ) : ℝ :=
  min (kappaCW δ) (min (kappaFace δ) (kappaBal δ))

/-- `κ_pair = min{κ_CW, κ_bal}`, arXiv:2608.20287v2, §6.1, p.29 (PDF 31). -/
noncomputable def kappaPair (δ : ℝ) : ℝ :=
  min (kappaCW δ) (kappaBal δ)

end HoneycombCodes


