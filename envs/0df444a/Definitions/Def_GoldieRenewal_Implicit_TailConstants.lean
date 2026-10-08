-- Prove2me | Definitions.Def_GoldieRenewal_Implicit_TailConstants
-- name    : GoldieRenewal_Implicit_TailConstants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:40.054825+00:00
-- url     : https://prove2.me/theorems/1e7eb70d-bc5d-4df3-9b92-d6a8bf05fa1f
-- title:
--   Tail conditions (2.8)–(2.9), constants C₊, C₋ (2.12)–(2.14), and r, g₁, g₋₁ of (9.3), (3.5), (3.6)
-- statement:
--   Let $M$ and $R$ be real random variables on a probability space $(\Omega,\mathcal A,P)$ and let $\kappa>0$; let $m$ be the constant (2.7) of the law of $M$.
--
--   **Tail conditions** (p. 129):
--   $$
--   \text{(2.8)}\ \int_0^\infty |P(R>t)-P(MR>t)|\,t^{\kappa-1}\,dt<\infty,\qquad
--   \text{(2.9)}\ \int_0^\infty |P(R<-t)-P(MR<-t)|\,t^{\kappa-1}\,dt<\infty .
--   $$
--
--   **Constants** (p. 130):
--   $$
--   C_+ = \frac1m\int_0^\infty \bigl(P(R>t)-P(MR>t)\bigr)t^{\kappa-1}\,dt,\qquad
--   C_- = \frac1m\int_0^\infty \bigl(P(R<-t)-P(MR<-t)\bigr)t^{\kappa-1}\,dt
--   $$
--   ((2.12), (2.13)) and, for Case 2 of Theorem 2.3,
--   $$
--   \text{(2.14)}\qquad C_+ = C_- = \frac1{2m}\int_0^\infty \bigl(P(|R|>t)-P(|MR|>t)\bigr)t^{\kappa-1}\,dt .
--   $$
--
--   **Functions in logarithmic scale** ((9.3) p. 144, (3.5)–(3.6) p. 132): for $t\in\mathbb R$,
--   $$
--   r(t) := e^{\kappa t}P(R>e^t),\quad g_1(t) := e^{\kappa t}\bigl(P(R>e^t)-P(MR>e^t)\bigr),\quad g_{-1}(t) := e^{\kappa t}\bigl(P(R<-e^t)-P(MR<-e^t)\bigr).
--   $$
--
--   These are the quantities in which the implicit renewal theorem and the steps of its proof are stated.
--
--   **Formalization Note** Probabilities are real numbers in $[0,1]$. (2.8) and (2.9) are integrability of the signed integrands on $(0,\infty)$, equivalent to finiteness of the integrals of their absolute values. The constants are Bochner integrals: they are the paper's values under (2.8), (2.9) respectively (and under both for (2.14)), which every statement using them assumes. All tail events keep the paper's strict inequalities.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, pp. 129–130, Theorem 2.3, (2.8)–(2.9), (2.12)–(2.14); p. 132, (3.5)–(3.6); p. 144, (9.3)

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions

namespace GoldieRenewal.Implicit

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The integrand of (2.8) and (2.12) (Goldie 1991, pp. 129–130):
`t ↦ (P(R > t) − P(MR > t)) t^{κ−1}` for `t > 0`.

**Formalization Note** Probabilities are real numbers `P.real s ∈ [0, 1]`; `t ^ (κ - 1)` is the real
power `Real.rpow`, only ever integrated over `t > 0`. -/
noncomputable def tailDiffPlus (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) (t : ℝ) : ℝ :=
  (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ - 1)

/-- The integrand of (2.9) and (2.13) (Goldie 1991, pp. 129–130):
`t ↦ (P(R < −t) − P(MR < −t)) t^{κ−1}` for `t > 0`. -/
noncomputable def tailDiffMinus (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) (t : ℝ) : ℝ :=
  (P.real {ω | R ω < -t} - P.real {ω | M ω * R ω < -t}) * t ^ (κ - 1)

/-- The integrand of (2.14) (Goldie 1991, p. 130):
`t ↦ (P(|R| > t) − P(|MR| > t)) t^{κ−1}` for `t > 0`. -/
noncomputable def tailDiffAbs (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) (t : ℝ) : ℝ :=
  (P.real {ω | t < |R ω|} - P.real {ω | t < |M ω * R ω|}) * t ^ (κ - 1)

/-- **Condition (2.8)** (Goldie 1991, p. 129): `∫₀^∞ |P(R > t) − P(MR > t)| t^{κ−1} dt < ∞`.

**Formalization Note** Encoded as integrability of the signed integrand on `(0, ∞)`; the integrand
is measurable (a difference of monotone functions times a continuous one), so this is exactly
finiteness of the integral of its absolute value. -/
def TailCondPlus (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) : Prop :=
  IntegrableOn (tailDiffPlus P M R κ) (Set.Ioi 0)

/-- **Condition (2.9)** (Goldie 1991, p. 129): `∫₀^∞ |P(R < −t) − P(MR < −t)| t^{κ−1} dt < ∞`,
encoded as integrability on `(0, ∞)` as for (2.8). -/
def TailCondMinus (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) : Prop :=
  IntegrableOn (tailDiffMinus P M R κ) (Set.Ioi 0)

/-- **The constant `C₊`** of (2.12) (Goldie 1991, p. 130):
`C₊ = (1/m) ∫₀^∞ (P(R > t) − P(MR > t)) t^{κ−1} dt`, with `m = E|M|^κ log|M|` (2.7).

**Formalization Note** Bochner integral; it is the paper's value under (2.8) (`TailCondPlus`), which
every statement using `Cplus` assumes. `m` is `cramerMean κ (P.map M)`, positive under the
conditions of Lemma 2.2. -/
noncomputable def Cplus (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) : ℝ :=
  (cramerMean κ (P.map M))⁻¹ * ∫ t in Set.Ioi 0, tailDiffPlus P M R κ t

/-- **The constant `C₋`** of (2.13) (Goldie 1991, p. 130):
`C₋ = (1/m) ∫₀^∞ (P(R < −t) − P(MR < −t)) t^{κ−1} dt`; the paper's value under (2.9). -/
noncomputable def Cminus (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) : ℝ :=
  (cramerMean κ (P.map M))⁻¹ * ∫ t in Set.Ioi 0, tailDiffMinus P M R κ t

/-- **The common constant of Case 2** (2.14) (Goldie 1991, p. 130):
`C₊ = C₋ = (1/(2m)) ∫₀^∞ (P(|R| > t) − P(|MR| > t)) t^{κ−1} dt`.

**Formalization Note** Under (2.8) and (2.9) the integrand is the sum of the integrands of (2.8) and
(2.9) (for `t > 0`, `{|X| > t}` is the disjoint union of `{X > t}` and `{X < −t}`), so it is
integrable and the Bochner integral is the paper's value. -/
noncomputable def Ctwo (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) : ℝ :=
  (2 * cramerMean κ (P.map M))⁻¹ * ∫ t in Set.Ioi 0, tailDiffAbs P M R κ t

/-- `r(t) := e^{κt} P(R > e^t)`, `t ∈ ℝ` (Goldie 1991, (9.3), p. 144). -/
noncomputable def rFun (P : Measure Ω) (R : Ω → ℝ) (κ : ℝ) (t : ℝ) : ℝ :=
  Real.exp (κ * t) * P.real {ω | Real.exp t < R ω}

/-- `g₁(t) := e^{κt}(P(R > e^t) − P(MR > e^t))`, `t ∈ ℝ` (Goldie 1991, (3.5), p. 132). -/
noncomputable def gOne (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) (t : ℝ) : ℝ :=
  Real.exp (κ * t) * (P.real {ω | Real.exp t < R ω} - P.real {ω | Real.exp t < M ω * R ω})

/-- `g₋₁(t) := e^{κt}(P(R < −e^t) − P(MR < −e^t))`, `t ∈ ℝ` (Goldie 1991, (3.6), p. 132). -/
noncomputable def gNegOne (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) (t : ℝ) : ℝ :=
  Real.exp (κ * t) *
    (P.real {ω | R ω < -Real.exp t} - P.real {ω | M ω * R ω < -Real.exp t})

end GoldieRenewal.Implicit


