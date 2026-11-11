-- Prove2me | Definitions.Def_DataDepProb_Discrete_MW
-- name    : DataDepProb_Discrete_MW
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:10:43.219716+00:00
-- url     : https://prove2.me/theorems/9ae6986e-2af4-4202-bd1f-2dd9a4ca346b
-- title:
--   The multiplicative weights update $\mathrm{MW}_\eta(r,f,b)$ (discrete and for densities), $h$, $H$ and the penalty $P_s=8H(\cdot-e_s)^2$
-- statement:
--   For a positive distribution $r$ on $[d]$, $f:[d]\to[0,1]$, $b\in[0,1]$ and $\eta>0$, the **multiplicative weights update** (§4.4) is
--   $$\mathrm{MW}_\eta(r,f,b)(x)=\frac{r(x)\exp\{\eta(b-E_r[f])f(x)\}}{\sum_y r(y)\exp\{\eta(b-E_r[f])f(y)\}}.$$
--   For a probability density $r$ with respect to a measure $\mu$ the same formula with $E_r[f]=\int rf\,d\mu$ and the normalizer $\int r\exp\{\eta(b-E_r[f])f\}\,d\mu$ defines the density version used in the last clause of Fact 4.9.
--
--   For $a\in\mathbb R$ and $z\in\mathbb R^d$ (Eq. (16)) let
--   $$h(a)=|a|\log(1+2d|a|),\qquad H(z)=\sum_x h(z(x)),$$
--   and for a centre $e\in\mathbb R^d$ the **penalty** $p\mapsto 8H(p-e)^2$; the paper's $P_s(p)=8H(p-e_s)^2$ (Eq. (17)) is the penalty centred at $e_s$.
--
--   **Formalization Note.** The formulas are total in Lean; the ranges above ($r>0$, $f\in[0,1]$, $b\in[0,1]$, $\eta>0$) are hypotheses of the theorems that use them. $h$ depends on $d$, which is read from the index type `Fin d`.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 10, §4.4; p. 16, Eqs. (16)–(17)

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex

open MeasureTheory

namespace DataDepProb.Discrete

/-!
# The multiplicative weights update, the functions `h`, `H`, and the penalty `P_s`

Feldman, Kale, Majid, Talwar, *Data-Dependent Probability Estimation via Sample Amplification*,
STOC 2027 submission (manuscript sha256 28400f1c…), §4.4 p. 10 (`MW_η`), §6 p. 16
(Eqs. (16)–(17): `h`, `H`, `P_s`).

* `mw η r f b` is `MW_η(r, f, b)(x) ∝ r(x) exp{η(b − E_r[f]) f(x)}`, normalized to sum `1`.
  The paper uses it for a positive distribution `r`, `f : [d] → [0, 1]`, `b ∈ [0, 1]`, `η > 0`;
  then the normalizer is positive. Statements carry these ranges as hypotheses.
* `hFun d a = |a| log(1 + 2d|a|)`, `HFun z = ∑_x h(z(x))` for `z ∈ ℝ^d`, and
  `penalty e p = 8 H(p − e)²`; the paper's `P_s` is `penalty (eInit s)`.
* `mwDensity μ η r f b` is the same update for a probability density `r` with respect to a measure
  `μ` (the last clause of Fact 4.9): `r(x) exp{η(b − ∫ r f dμ) f(x)}` divided by its integral.
-/

/-- The multiplicative weights update `MW_η(r, f, b)` (§4.4):
`MW_η(r, f, b)(x) = r(x) exp{η(b − E_r[f]) f(x)} / ∑_y r(y) exp{η(b − E_r[f]) f(y)}`. -/
noncomputable def mw {d : ℕ} (η : ℝ) (r f : Fin d → ℝ) (b : ℝ) : Fin d → ℝ :=
  fun x => r x * Real.exp (η * (b - expect r f) * f x) /
    ∑ y, r y * Real.exp (η * (b - expect r f) * f y)

/-- The multiplicative weights update of a density `r` with respect to `μ` (Fact 4.9, last
clause): `x ↦ r(x) exp{η(b − E_r[f]) f(x)} / ∫ r(y) exp{η(b − E_r[f]) f(y)} dμ(y)`,
`E_r[f] = ∫ r f dμ`. -/
noncomputable def mwDensity {α : Type*} [MeasurableSpace α] (μ : Measure α) (η : ℝ)
    (r f : α → ℝ) (b : ℝ) : α → ℝ :=
  fun x => r x * Real.exp (η * (b - ∫ y, r y * f y ∂μ) * f x) /
    ∫ y, r y * Real.exp (η * (b - ∫ z, r z * f z ∂μ) * f y) ∂μ

/-- `h(a) = |a| log(1 + 2d|a|)` for `a ∈ ℝ` (Eq. (16)). -/
noncomputable def hFun (d : ℕ) (a : ℝ) : ℝ :=
  |a| * Real.log (1 + 2 * (d : ℝ) * |a|)

/-- `H(z) = ∑_x h(z(x))` for `z ∈ ℝ^d` (Eq. (16)). -/
noncomputable def HFun {d : ℕ} (z : Fin d → ℝ) : ℝ :=
  ∑ x, hFun d (z x)

/-- The penalty centered at `e`: `p ↦ 8 H(p − e)²` (Eq. (17)); `P_s = penalty (eInit s)`. -/
noncomputable def penalty {d : ℕ} (e p : Fin d → ℝ) : ℝ :=
  8 * HFun (p - e) ^ 2

end DataDepProb.Discrete


