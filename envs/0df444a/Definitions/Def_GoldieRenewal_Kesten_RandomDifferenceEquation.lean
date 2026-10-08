-- Prove2me | Definitions.Def_GoldieRenewal_Kesten_RandomDifferenceEquation
-- name    : GoldieRenewal_Kesten_RandomDifferenceEquation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:28.477323+00:00
-- url     : https://prove2.me/theorems/2ddf8bba-0728-49fe-ac6d-9ff904c2abd9
-- title:
--   The random difference equation R =_L Q + MR (1.1) as a fixed point of a law operator, and Kesten's constants C₊, C₋ of (4.3)–(4.4)
-- statement:
--   Let $(Q,M)$ be a pair of real random variables with joint law $\mu$ on $\mathbb R^2$; no independence between $Q$ and $M$ and no sign condition is imposed. The **random difference equation** (1.1) is
--
--   $$
--   R \overset{\mathcal L}{=} Q + MR,\qquad R \text{ independent of } (Q,M),
--   $$
--
--   where $\overset{\mathcal L}{=}$ denotes equality of laws. For a probability law $\rho$ on $\mathbb R$ write $T_\mu\rho$ for the law of $Q+MR$ when $R$ has law $\rho$ and is independent of $(Q,M)$, i.e. the image of $\mu\otimes\rho$ under $((q,m),r)\mapsto q+mr$. A law $\rho$ **for $R$ satisfying (1.1)** is a probability law with $T_\mu\rho=\rho$.
--
--   For $\kappa>0$, with $x^+ = x\vee 0$, $x^- = (-x)\vee 0$, $m = \mathbf E|M|^\kappa\log|M|$ and $R$ of law $\rho$ independent of $(Q,M)$, the file defines Kesten's constants of Theorem 4.1. If $M\ge 0$ a.s.,
--
--   $$
--   C_+ = \frac{\mathbf E\big(((Q+MR)^+)^\kappa - ((MR)^+)^\kappa\big)}{\kappa m},\qquad
--   C_- = \frac{\mathbf E\big(((Q+MR)^-)^\kappa - ((MR)^-)^\kappa\big)}{\kappa m}\qquad\text{(4.3)},
--   $$
--
--   while otherwise
--
--   $$
--   C_+ = C_- = \frac{1}{2\kappa m}\,\mathbf E\big(|Q+MR|^\kappa - |MR|^\kappa\big)\qquad\text{(4.4)}.
--   $$
--
--   The three integrands $((Q+MR)^\pm)^\kappa - ((MR)^\pm)^\kappa$ and $|Q+MR|^\kappa-|MR|^\kappa$ are also named, as functions of $((Q,M),R)$.
--
--   These are the objects of Kesten's theorem: the stationary law of the affine recursion $R_n = Q_n + M_nR_{n-1}$ and the constants in its power tails.
--
--   **Formalization Note** The first coordinate of $\mu$ is $Q$, the second $M$. "$M\ge0$ a.s." is $\mu\{M<0\}=0$. Expectations are Bochner integrals against $\mu\otimes\rho$, which is what makes $R$ independent of $(Q,M)$; Theorem 4.1 asserts the integrability of the integrands for the stationary law, so the constants there are the paper's.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 126, (1.1); p. 135, (4.1), (4.3); p. 136, (4.4)

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory

/-- **The law-level operator of the random difference equation (1.1)** (Goldie 1991, p. 126;
§4, (4.1), p. 135). For the joint law `μ` of `(Q, M)` on `ℝ × ℝ` and a law `ρ` on `ℝ`,
`rdeOperator μ ρ` is the law of `Q + M R` when `R` has law `ρ` and is independent of `(Q, M)`:
the image of `μ ⊗ ρ` under `((q, m), r) ↦ q + m r`.

A law `ρ` "for `R` satisfying (1.1)", i.e. `R =_L Q + MR` with `R` independent of `(M, Q)`, is a
probability measure with `rdeOperator μ ρ = ρ`.

**Formalization Note** The first coordinate of `μ` is `Q` and the second is `M`. No independence
between `Q` and `M` and no sign condition is assumed. -/
noncomputable def rdeOperator (μ : Measure (ℝ × ℝ)) (ρ : Measure ℝ) : Measure ℝ :=
  (μ.prod ρ).map (fun p : (ℝ × ℝ) × ℝ => p.1.1 + p.1.2 * p.2)

/-- `((Q + MR)⁺)^κ − ((MR)⁺)^κ` as a function of `((Q, M), R)`, the integrand of (4.3) for `C₊`
and of (2.16)/(2.18) with `Ψ(R) = Q + MR` (Goldie 1991, pp. 130, 135). -/
noncomputable def posDiff (κ : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  (max (p.1.1 + p.1.2 * p.2) 0) ^ κ - (max (p.1.2 * p.2) 0) ^ κ

/-- `((Q + MR)⁻)^κ − ((MR)⁻)^κ` as a function of `((Q, M), R)`, with `x⁻ = (−x) ∨ 0`; the
integrand of (4.3) for `C₋` and of (2.17)/(2.19) (Goldie 1991, pp. 130, 135). -/
noncomputable def negDiff (κ : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  (max (-(p.1.1 + p.1.2 * p.2)) 0) ^ κ - (max (-(p.1.2 * p.2)) 0) ^ κ

/-- `|Q + MR|^κ − |MR|^κ` as a function of `((Q, M), R)`, the integrand of (4.4) and (2.20)
(Goldie 1991, pp. 130, 136). -/
noncomputable def absDiff (κ : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  |p.1.1 + p.1.2 * p.2| ^ κ - |p.1.2 * p.2| ^ κ

/-- **The constant `C₊` of Theorem 4.1** (Goldie 1991, (4.3) p. 135 and (4.4) p. 136), for the
joint law `μ` of `(Q, M)`, a law `ρ` of `R` (independent of `(Q, M)`) and the exponent `κ`, with
`m = E|M|^κ log|M|` (2.7):

* if `M ≥ 0` a.s.: `C₊ = E(((Q + MR)⁺)^κ − ((MR)⁺)^κ) / (κ m)`;
* otherwise: `C₊ = E(|Q + MR|^κ − |MR|^κ) / (2 κ m)`.

**Formalization Note** "`M ≥ 0` a.s." is `μ {M < 0} = 0`. The expectations are Bochner integrals
against `μ ⊗ ρ` (so `R` is independent of `(Q, M)`); Theorem 4.1 proves the integrands integrable
for the stationary law, so these are the paper's constants there. -/
noncomputable def kestenCplus (κ : ℝ) (μ : Measure (ℝ × ℝ)) (ρ : Measure ℝ) : ℝ :=
  if μ {p | p.2 < 0} = 0 then
    (∫ p, posDiff κ p ∂(μ.prod ρ)) / (κ * GoldieRenewal.Implicit.cramerMean κ (μ.map Prod.snd))
  else
    (∫ p, absDiff κ p ∂(μ.prod ρ)) / (2 * κ * GoldieRenewal.Implicit.cramerMean κ (μ.map Prod.snd))

/-- **The constant `C₋` of Theorem 4.1** (Goldie 1991, (4.3) p. 135 and (4.4) p. 136):

* if `M ≥ 0` a.s.: `C₋ = E(((Q + MR)⁻)^κ − ((MR)⁻)^κ) / (κ m)`;
* otherwise: `C₋ = C₊ = E(|Q + MR|^κ − |MR|^κ) / (2 κ m)`.

Conventions as for `kestenCplus`. -/
noncomputable def kestenCminus (κ : ℝ) (μ : Measure (ℝ × ℝ)) (ρ : Measure ℝ) : ℝ :=
  if μ {p | p.2 < 0} = 0 then
    (∫ p, negDiff κ p ∂(μ.prod ρ)) / (κ * GoldieRenewal.Implicit.cramerMean κ (μ.map Prod.snd))
  else
    (∫ p, absDiff κ p ∂(μ.prod ρ)) / (2 * κ * GoldieRenewal.Implicit.cramerMean κ (μ.map Prod.snd))

end GoldieRenewal.Kesten


