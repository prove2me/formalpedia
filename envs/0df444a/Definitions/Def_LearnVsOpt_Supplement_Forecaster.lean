-- Prove2me | Definitions.Def_LearnVsOpt_Supplement_Forecaster
-- name    : LearnVsOpt_Supplement_Forecaster
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:19:51.672837+00:00
-- url     : https://prove2.me/theorems/19877e99-cacb-4a53-a95b-3cbcecbb1d93
-- title:
--   Randomized forecasts over $\mathcal{UC}$, the response $f\mapsto y(f)$, and the expected calibration errors $R_T$, $L_t$
-- statement:
--   Shared objects for Algorithm 1 run with an **arbitrary randomized forecaster**.
--
--   A **forecast** is a point $f\in\Delta_{\hat n_O}$ over a duplicate-free enumeration $D=(uc^{(1)},\dots,uc^{(\hat n_O)})$ of the game's utility-cost set
--   $$\mathcal{UC}=\{(U_L[i,:],C_L[i,:]) : i\in[n_O]\},$$
--   stored as a function $\mathbb N\to\mathbb R$ that vanishes past $\hat n_O$. The forecast space carries its product $\sigma$-algebra, so a forecast distribution $F$ may be any probability measure on it. Given a selector (the learner's tie-breaking rule), the learner's response to $f$ is the selector's output $(\vec J(f),Q(f),\lambda(f))$ at the predicted vector $uc(f)=\sum_k f_k\,uc^{(k)}$. The response is called **measurable** when $f\mapsto j_1(f),j_2(f),Q(f),\lambda(f)$ are measurable.
--
--   For a forecast distribution $F$ and a realized vector $v=uc^{(k)}$, the **expected single-round error** $\mathbb E_{f\sim F}[\delta(f,k)]$ integrates every coordinate of the single-round error $\delta=(\delta^R,\delta^L)$ of (3) and (10) against $F$. The coordinatewise sum of these over a set of rounds is the response-calibration error $R_T=\sum_{t\in\mathcal T}\mathbb E_{f\sim F_t}[\delta^R(f,k_t)]$ of (4) and the Lagrangian-calibration error $L_t$ of p.12.
--
--   These objects let Theorems 4.2 and 5.2 be stated for every forecaster, not only for the forecaster of Algorithm 2.
--
--   **Formalization Note** The expectation is the Bochner integral, and it means what the paper means only when the response is measurable; the theorems assume this.
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, §3 p.7 (𝒰𝒞, forecasts, Algorithm 1), (3)–(4) pp.8–9, (9)–(10) p.12

import Mathlib
import Definitions.Def_LearnVsOpt_Errors

set_option autoImplicit false

open MeasureTheory
open scoped Matrix

namespace LearnVsOpt.Supplement

variable {nO nL : ℕ}

/-- **The forecast space** (Fikioris, Sivan & Tardos, *Learning vs. Optimizing Players in Budgeted
Games*, arXiv:2611.05580, §3, p.7). A forecast `f ∈ Δ_{n̂_O}` is a function `ℕ → ℝ` that vanishes past
`n̂_O` (the base convention of `LearnVsOpt.ucOf` and `LearnVsOpt.IsForecast`).

**Formalization Note.** The space carries the product σ-algebra of `ℕ → ℝ`, so a randomized forecast
`F_t` can be an arbitrary probability measure on it, not only a finitely supported one. -/
abbrev Forecast : Type := ℕ → ℝ

/-- The learner's response `(J⃗(f), Q(f), λ(f))` to the forecast `f` over the dictionary `D`: the
selector applied to the predicted vector `uc(f) = (u(f), c(f))` (Algorithm 1, p.7; p.8; (9), p.12). -/
noncomputable def selAt (sel : Selector nL) (D : List (UC nL)) (f : Forecast) : Selection nL :=
  (sel (ucOf D f).1 (ucOf D f).2).val

/-- The response is a measurable function of the forecast: `f ↦ j₁(f)`, `j₂(f)`, `Q(f)`, `λ(f)` are
measurable.

**Formalization Note.** The paper takes expectations `E_{f∼F_t}[·]` of functions of `y(f)` and `λ(f)`
for a general distribution `F_t`; they are defined only when these maps are measurable (otherwise
Lean's Bochner integral returns the junk value `0`). This is the reading of the paper's `E`. -/
def SelMeasurable (sel : Selector nL) (D : List (UC nL)) : Prop :=
  Measurable (fun f : Forecast => (selAt sel D f).j₁) ∧
  Measurable (fun f : Forecast => (selAt sel D f).j₂) ∧
  Measurable (fun f : Forecast => (selAt sel D f).Q) ∧
  Measurable (fun f : Forecast => (selAt sel D f).lam)

/-- `D` is a duplicate-free enumeration `uc^(1), …, uc^(n̂_O)` of the game's utility-cost set
`𝒰𝒞 = {(U_L[i, :], C_L[i, :]) : i ∈ [n_O]}` (§3, p.7). Then `D.length = n̂_O`, and the index `k_t` of
the realized vector `uc_t` is the unique `k` with `D[k] = uc_t`. -/
def IsUCEnum (G : Game nO nL) (D : List (UC nL)) : Prop :=
  D.Nodup ∧ ∀ v, v ∈ D ↔ ∃ i, (G.UL i, G.CL i) = v

/-- **The expected single-round error** `E_{f∼F}[δ(f, k)]` for a forecast distribution `F` and the
realized vector `v = uc^(k)`: every coordinate of the base `LearnVsOpt.delta` ((3), p.8; (10), p.12)
integrated against `F`, the response-calibration coordinates pointwise in `q ∈ [−1, 1]`. -/
noncomputable def expDelta (ρL : ℝ) (sel : Selector nL) (D : List (UC nL)) (F : Measure Forecast)
    (v : UC nL) : JointVec nL where
  R := fun k j₁ j₂ q => ∫ f, (delta ρL D (selAt sel D f) f v).R k j₁ j₂ q ∂F
  Lu := fun j => ∫ f, (delta ρL D (selAt sel D f) f v).Lu j ∂F
  Lc := fun j => ∫ f, (delta ρL D (selAt sel D f) f v).Lc j ∂F
  Luy := ∫ f, (delta ρL D (selAt sel D f) f v).Luy ∂F
  Lcy := ∫ f, (delta ρL D (selAt sel D f) f v).Lcy ∂F

/-- The coordinatewise sum `Σ_{t ∈ s} Z_t` of elements of the joint space. With
`Z_t = E_{f∼F_t}[δ(f, k_t)]` this is the response-calibration error `R_T` of (4), p.9, over the
rounds `s`, and the Lagrangian-calibration error `L_t` of p.12. -/
noncomputable def sumJ (s : Finset ℕ) (Z : ℕ → JointVec nL) : JointVec nL where
  R := fun k j₁ j₂ q => ∑ t ∈ s, (Z t).R k j₁ j₂ q
  Lu := fun j => ∑ t ∈ s, (Z t).Lu j
  Lc := fun j => ∑ t ∈ s, (Z t).Lc j
  Luy := ∑ t ∈ s, (Z t).Luy
  Lcy := ∑ t ∈ s, (Z t).Lcy

end LearnVsOpt.Supplement


