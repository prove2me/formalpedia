-- Prove2me | Definitions.Def_HoneycombCodes_kappaHC
-- name    : HoneycombCodes_kappaHC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:29:40.437984+00:00
-- url     : https://prove2.me/theorems/759fa5f5-b7d1-41e0-840c-24125522be0c
-- title:
--   First honeycomb exponent $\kappa_{HC}(\delta)$ (Definition 1.1) and $\kappa_{best}=\min\{\kappa_{CW},\kappa_{HC}\}$
-- statement:
--   For parameters $0<x\le 1/2$, $0\le\eta,\rho<1/2$, $0\le z\le 1/2$ put
--
--   $$
--   A=(1-x)(1-2\eta),\qquad B=x(1-2\rho),\qquad E=1-2z,\qquad P=\frac{E^2-(A-B)^2}{4AB}.
--   $$
--
--   The **honeycomb domain** $D_{HC}$ is the set of quadruples in these ranges with $|A-B|\le E\le A+B$ (equivalently $0\le P\le 1$). The **spectral symbol** and **entropy potential** are
--
--   $$
--   \Gamma_{HC}=2\sqrt{x(1-x)}\Bigl[P\bigl(\sqrt{(1-\eta)(1-\rho)}+\sqrt{\eta\rho}\bigr)+(1-P)\bigl(\sqrt{\rho(1-\eta)}+\sqrt{\eta(1-\rho)}\bigr)\Bigr],
--   $$
--
--   $$
--   \Phi_{HC}=H_2(x)+(1-x)H_2(\eta)+xH_2(\rho)-H_2(z),
--   $$
--
--   and the **first honeycomb exponent** is
--
--   $$
--   \kappa_{HC}(\delta)=\inf\bigl\{\Phi_{HC}(q): q\in D_{HC},\ \Gamma_{HC}(q)>1-2\delta\bigr\}.
--   $$
--
--   The module also names the strict region (49) of Lemma 5.1 ($0<x<1/2$, $0<\eta,\rho<1/2$, $|A-B|<E<A+B$) and the combined exponent $\kappa_{best}=\min\{\kappa_{CW},\kappa_{HC}\}$.
--
--   **Formalization Note** On the domain $A,B>0$, so $P$ never divides by zero. $\kappa_{HC}$ is a real `sInf`; for $0<\delta<1/2$ its set is nonempty ($(1/2,0,0,0)$ has $\Gamma_{HC}=1$) and bounded below.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), Definition 1.1, eqs. (3)–(9), pp.2–3 (PDF 4–5); strict region: eq. (49), p.25 (PDF 27); κ_best: Theorem 1.2(iii), p.4 (PDF 6)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaCW

set_option autoImplicit false

namespace HoneycombCodes

/-- `A = (1 − x)(1 − 2η)`, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*,
arXiv:2608.20287v2 (sha256 f4b07e31…cd51), Definition 1.1, eq. (4), p.3 (PDF 5). -/
def Avar (x η : ℝ) : ℝ := (1 - x) * (1 - 2 * η)

/-- `B = x(1 − 2ρ)`, arXiv:2608.20287v2, eq. (4), p.3. -/
def Bvar (x ρ : ℝ) : ℝ := x * (1 - 2 * ρ)

/-- `E = 1 − 2z`, arXiv:2608.20287v2, eq. (4), p.3. -/
def Evar (z : ℝ) : ℝ := 1 - 2 * z

/-- `P = (E² − (A − B)²)/(4AB)`, arXiv:2608.20287v2, eq. (5), p.3 (PDF 5).

**Formalization Note.** On the domain (3) one has `A, B > 0`, so the denominator never vanishes
there. -/
noncomputable def PHC (x η ρ z : ℝ) : ℝ :=
  (Evar z ^ 2 - (Avar x η - Bvar x ρ) ^ 2) / (4 * Avar x η * Bvar x ρ)

/-- The honeycomb domain `D_HC`: the parameter ranges (3) `0 < x ≤ 1/2`, `0 ≤ η, ρ < 1/2`,
`0 ≤ z ≤ 1/2`, together with the triangle inequalities (6) `|A − B| ≤ E ≤ A + B`,
arXiv:2608.20287v2, Definition 1.1, pp.2–3 (PDF 4–5). -/
def InDHC (x η ρ z : ℝ) : Prop :=
  0 < x ∧ x ≤ 1 / 2 ∧ 0 ≤ η ∧ η < 1 / 2 ∧ 0 ≤ ρ ∧ ρ < 1 / 2 ∧ 0 ≤ z ∧ z ≤ 1 / 2 ∧
    |Avar x η - Bvar x ρ| ≤ Evar z ∧ Evar z ≤ Avar x η + Bvar x ρ

/-- The strict region (49) of Lemma 5.1, arXiv:2608.20287v2, p.25 (PDF 27):
`0 < x < 1/2`, `0 < η, ρ < 1/2`, `|A − B| < E < A + B`. -/
def InStrictHC (x η ρ z : ℝ) : Prop :=
  0 < x ∧ x < 1 / 2 ∧ 0 < η ∧ η < 1 / 2 ∧ 0 < ρ ∧ ρ < 1 / 2 ∧
    |Avar x η - Bvar x ρ| < Evar z ∧ Evar z < Avar x η + Bvar x ρ

/-- The **spectral symbol** (7),
`Γ_HC = 2√(x(1 − x)) [P(√((1 − η)(1 − ρ)) + √(ηρ)) + (1 − P)(√(ρ(1 − η)) + √(η(1 − ρ)))]`,
arXiv:2608.20287v2, Definition 1.1, p.3 (PDF 5). -/
noncomputable def GammaHC (x η ρ z : ℝ) : ℝ :=
  2 * Real.sqrt (x * (1 - x)) *
    (PHC x η ρ z * (Real.sqrt ((1 - η) * (1 - ρ)) + Real.sqrt (η * ρ)) +
      (1 - PHC x η ρ z) * (Real.sqrt (ρ * (1 - η)) + Real.sqrt (η * (1 - ρ))))

/-- The **entropy potential** (8), `Φ_HC = H₂(x) + (1 − x)H₂(η) + xH₂(ρ) − H₂(z)`,
arXiv:2608.20287v2, Definition 1.1, p.3 (PDF 5). -/
noncomputable def PhiHC (x η ρ z : ℝ) : ℝ :=
  H2 x + (1 - x) * H2 η + x * H2 ρ - H2 z

/-- The **first honeycomb exponent** (9),
`κ_HC(δ) = inf { Φ_HC(q) : q ∈ D_HC, Γ_HC(q) > 1 − 2δ }`, arXiv:2608.20287v2, Definition 1.1,
p.3 (PDF 5).

**Formalization Note.** A real `sInf` of the set of objective values over the strictly feasible
quadruples. For `0 < δ < 1/2` the set is nonempty (`(1/2, 0, 0, 0)` has `Γ_HC = 1`) and bounded
below, so this is the printed infimum. -/
noncomputable def kappaHC (δ : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x η ρ z : ℝ, InDHC x η ρ z ∧ 1 - 2 * δ < GammaHC x η ρ z ∧
    r = PhiHC x η ρ z}

/-- The combined exponent `κ_best = min{κ_CW, κ_HC}`, arXiv:2608.20287v2, Theorem 1.2(iii), p.4
(PDF 6), and §6.1, p.29. -/
noncomputable def kappaBest (δ : ℝ) : ℝ :=
  min (kappaCW δ) (kappaHC δ)

end HoneycombCodes


