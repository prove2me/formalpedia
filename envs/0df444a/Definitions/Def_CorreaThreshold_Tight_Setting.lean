-- Prove2me | Definitions.Def_CorreaThreshold_Tight_Setting
-- name    : CorreaThreshold_Tight_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:14.895666+00:00
-- url     : https://prove2.me/theorems/05a7bc77-7c50-430b-8ad8-d1dfeee01c0e
-- title:
--   §3.1 and Appendix B — the three point i.i.d. instance and random-order threshold reward
-- statement:
--   For each integer $n\ge2$, let $H_n=n/(e-2)$ and let $\mu_n$ put mass $1/n^3$ at $H_n$, mass $1/n$ at $1$, and the remaining mass at $0$. Draw $n^2$ independent rewards with law $\mu_n$.
--
--   For thresholds $\tau_i\in[0,\infty]$ and sample $x=(x_i)$, set $A(x,\tau)=\{i:x_i>\tau_i\}$. The expected reward under a uniformly random arrival order, conditional on $x$, is
--
--   $$
--   R_n(x,\tau)=\frac{\sum_{i\in A(x,\tau)}x_i}{|A(x,\tau)|},\qquad 0/0=0.
--   $$
--
--   The setting defines $V_n(\tau)=\mathbb E_{\mu_n^{\otimes n^2}}[R_n(X,\tau)]$, the prophet value $P_n=\mathbb E[\max_i X_i]$, and $K$, the number of coordinates equal to $H_n$. It also defines the canonical rule $\tau^{(k)}$: the first $k$ coordinates accept $1$ and $H_n$, while the rest accept only $H_n$. These definitions support the paper's i.i.d. upper bound on nonadaptive thresholds.
--
--   **Formalization Note** Coordinates are 0-based. The strict crossing convention uses thresholds $0$ and $1$ for $\tau^{(k)}$, equivalent on this law to the page's weak thresholds $1$ and $H_n$. All expectations are extended nonnegative integrals. The law is a probability measure for $n\ge2$; statements concerning it either assume that bound or take an eventual limit. The general product law and expected maximum are reused from the published Samuel-Cahn i.i.d. setting.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), https://doi.org/10.1287/moor.2020.1105, pp. 1460–1461, §3.1; p. 1474, Appendix B

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

namespace CorreaThreshold.Tight

open MeasureTheory

/-- The exceptional high prize in §3.1. -/
noncomputable def hi (n : ℕ) : ℝ := (n : ℝ) / (Real.exp 1 - 2)

/-- The three point law in §3.1, used for `n ≥ 2`. -/
noncomputable def lawN (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 / (n : ℝ) ^ 3) • Measure.dirac (hi n) +
  ENNReal.ofReal (1 / (n : ℝ)) • Measure.dirac 1 +
  ENNReal.ofReal (1 - 1 / (n : ℝ) - 1 / (n : ℝ) ^ 3) • Measure.dirac 0

/-- Random order reward conditional on a sample: average of the values above their fixed thresholds.
An empty accepting set has reward zero, using Lean's `0 / 0 = 0`. -/
noncomputable def ratioS {m : ℕ} (τ : Fin m → ENNReal) (x : Fin m → ℝ) : ℝ := by
  classical
  let acc := Finset.univ.filter (fun i => τ i < ENNReal.ofReal (x i))
  exact (∑ i ∈ acc, x i) / (acc.card : ℝ)

/-- Expected reward of a fixed nonadaptive threshold vector on `n²` i.i.d. samples. -/
noncomputable def value (n : ℕ) (τ : Fin (n ^ 2) → ENNReal) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (ratioS τ x) ∂(SamuelCahnProphet.IID.iidLaw (lawN n) (n ^ 2))

/-- The prophet's expected maximum for the same sample. The zero-coordinate case is outside §3.1. -/
noncomputable def prophet (n : ℕ) : ENNReal :=
  if h : n = 0 then 0 else by
    haveI : NeZero (n ^ 2) := ⟨by positivity⟩
    exact SamuelCahnProphet.IID.Emax (lawN n) (n ^ 2)

/-- The canonical two-level rule: first `k` indices accept 1 or high, others only high. -/
noncomputable def kRule (n k : ℕ) : Fin (n ^ 2) → ENNReal :=
  fun i => if (i : ℕ) < k then 0 else 1

/-- The number of exceptional high prizes in a sample. -/
noncomputable def Kcount (n : ℕ) (x : Fin (n ^ 2) → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => x i = hi n)).card

end CorreaThreshold.Tight


