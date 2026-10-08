-- Prove2me | Definitions.Def_GoldieRenewal_Rates_Model
-- name    : GoldieRenewal_Rates_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:10:10.567978+00:00
-- url     : https://prove2.me/theorems/7ac80c22-3aa9-4443-b403-0ea64ed381f6
-- title:
--   Theorem 3.2 objects: law of log|M| given M ≠ 0, tilted law η, m, g₁, g₋₁ (3.5)–(3.6), C₊, C₋ (2.12)–(2.13)
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space and $M,R$ real random variables, with $M\ge 0$ in the setting of Theorem 3.2, and $\kappa>0$.
--
--   1. The **conditional law of $\log|M|$ given $M\neq0$**: the law of $\log|M|$ under $P(\,\cdot\mid M\neq 0)$.
--   2. The **tilted law** $\eta(dx):=e^{\kappa x}\,P(\log M\in dx)$, where $P(\log M\in dx)$ is computed on $\{M>0\}$.
--   3. The constant $m:=\mathbf E\,M^\kappa\log M$, with the convention $0^\kappa\log 0:=0$.
--   4. For $t\in\mathbb R$,
--   $$g_1(t):=e^{\kappa t}\big(P(R>e^t)-P(MR>e^t)\big),\qquad g_{-1}(t):=e^{\kappa t}\big(P(R<-e^t)-P(MR<-e^t)\big).$$
--   5. The constants
--   $$C_+:=\frac1m\int_0^\infty\big(P(R>t)-P(MR>t)\big)t^{\kappa-1}\,dt,\qquad C_-:=\frac1m\int_0^\infty\big(P(R<-t)-P(MR<-t)\big)t^{\kappa-1}\,dt .$$
--
--   $C_\pm$ are the limits of $t^\kappa P(\pm R>t)$ in the implicit renewal theorem; $g_{\pm1}$ are the functions whose transforms enter the second-order terms of Theorem 3.2.
--
--   **Formalization Note** $m$ and the integrals in $C_\pm$ are Bochner integrals (Lean's integral is $0$ when the integrand is not integrable); in every statement that uses them their integrands are integrable by the hypotheses. Lean's `Real.log 0 = 0` and `0 ^ κ = 0` reproduce the convention $0^\kappa\log0=0$. $\eta$ is defined as the image of $P$ restricted to $\{M>0\}$ under $\log M$, with density $e^{\kappa x}$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 129, (2.7); p. 130, (2.12)–(2.13); p. 132, Theorem 3.2, (3.4)–(3.6)

import Mathlib
import Definitions.Def_GoldieRenewal_Rates_Transforms

open MeasureTheory ProbabilityTheory

namespace GoldieRenewal.Rates

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The conditional law of `log|M|` given `M ≠ 0` (Goldie 1991, (3.4), p. 132): the image of
`P[· | M ≠ 0]` under `ω ↦ log|M ω|`. Formalization Note: conditioning on `M ≠ 0` keeps Lean's
junk value `Real.log 0 = 0` out of this law. -/
noncomputable def logLawGivenNonzero (P : Measure Ω) (M : Ω → ℝ) : Measure ℝ :=
  (P[|{ω | M ω ≠ 0}]).map (fun ω => Real.log |M ω|)

/-- The tilted law `η(dx) := e^{κx} P(log M ∈ dx)` of Goldie 1991, Theorem 3.2 (p. 132), for
`M ≥ 0`. Formalization Note: `P(log M ∈ dx)` is the image of `P` restricted to `{M > 0}` under
`ω ↦ log M ω` (on `{M = 0}`, `log M = −∞` lies outside `ℝ`); `η` is that image measure with
density `x ↦ e^{κx}`. -/
noncomputable def tiltedLaw (P : Measure Ω) (M : Ω → ℝ) (κ : ℝ) : Measure ℝ :=
  ((P.restrict {ω | 0 < M ω}).map (fun ω => Real.log (M ω))).withDensity
    (fun x => ENNReal.ofReal (Real.exp (κ * x)))

/-- `m := E M^κ log M` (Goldie 1991, (2.7), p. 129), for `M ≥ 0`, with the convention
`0^κ log 0 := 0` (p. 127), which Lean's `0 ^ κ * Real.log 0 = 0` reproduces.
Formalization Note: a Bochner integral; its integrand is integrable under (2.3) and (3.3). -/
noncomputable def mConst (P : Measure Ω) (M : Ω → ℝ) (κ : ℝ) : ℝ :=
  ∫ ω, M ω ^ κ * Real.log (M ω) ∂P

/-- `g₁(t) := e^{κt}(P(R > e^t) − P(MR > e^t))` (Goldie 1991, (3.5), p. 132). -/
noncomputable def gPos (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) (t : ℝ) : ℝ :=
  Real.exp (κ * t) *
    (P.real {ω | Real.exp t < R ω} - P.real {ω | Real.exp t < M ω * R ω})

/-- `g₋₁(t) := e^{κt}(P(R < −e^t) − P(MR < −e^t))` (Goldie 1991, (3.6), p. 132). -/
noncomputable def gNeg (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) (t : ℝ) : ℝ :=
  Real.exp (κ * t) *
    (P.real {ω | R ω < -Real.exp t} - P.real {ω | M ω * R ω < -Real.exp t})

/-- `C₊ := m⁻¹ ∫₀^∞ (P(R > t) − P(MR > t)) t^{κ−1} dt` (Goldie 1991, (2.12), p. 130), with
`m = mConst P M κ`. Formalization Note: the integral is a Bochner integral over `(0, ∞)`;
under the hypotheses where it is used its integrand is integrable. -/
noncomputable def CPlus (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) : ℝ :=
  (mConst P M κ)⁻¹ *
    ∫ t in Set.Ioi (0 : ℝ),
      (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ - 1)

/-- `C₋ := m⁻¹ ∫₀^∞ (P(R < −t) − P(MR < −t)) t^{κ−1} dt` (Goldie 1991, (2.13), p. 130). -/
noncomputable def CMinus (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) : ℝ :=
  (mConst P M κ)⁻¹ *
    ∫ t in Set.Ioi (0 : ℝ),
      (P.real {ω | R ω < -t} - P.real {ω | M ω * R ω < -t}) * t ^ (κ - 1)

end GoldieRenewal.Rates


