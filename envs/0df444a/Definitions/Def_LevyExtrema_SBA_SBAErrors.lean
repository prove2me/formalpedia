-- Prove2me | Definitions.Def_LevyExtrema_SBA_SBAErrors
-- name    : LevyExtrema_SBA_SBAErrors
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:01.306276+00:00
-- url     : https://prove2.me/theorems/69821a32-d142-4b97-9763-c34d0f619968
-- title:
--   The SBA $\chi_n$ (1.2) and its errors $\Delta_n,\delta_n,\Delta^{SB}_n,\delta^{SB}_n$ (1.3)
-- statement:
--   Given a stick-breaking coupling $(X,\ell,Y)$ on $[0,T]$ and $n\ge1$, the **stick-breaking approximation** (SBA) of $\chi=(X_T,\overline X_T,\tau_T)$ is
--
--   $$\chi_n=\sum_{k=1}^n\Big(Y_{L_{k-1}}-Y_{L_k},(Y_{L_{k-1}}-Y_{L_k})^+,\ell_k\mathbb 1_{\{Y_{L_{k-1}}-Y_{L_k}>0\}}\Big)+\Big(Y_{L_n},Y_{L_n}^+,L_n\mathbb 1_{\{Y_{L_n}>0\}}\Big).\tag{1.2}$$
--
--   Its errors are defined in (1.3):
--
--   $$\Delta_n=\overline X_T-\sum_{k=1}^n(Y_{L_{k-1}}-Y_{L_k})^+,\qquad \delta_n=\tau_T-\sum_{k=1}^n\ell_k\mathbb 1_{\{Y_{L_{k-1}}-Y_{L_k}>0\}},$$
--
--   $$\Delta^{SB}_n=\Delta_n-Y^+_{L_n},\qquad \delta^{SB}_n=\delta_n-L_n\mathbb 1_{\{Y_{L_n}>0\}}.$$
--
--   $\Delta_n,\delta_n$ are the errors of the partial sums, and $\Delta^{SB}_n,\delta^{SB}_n$ the errors of the SBA itself, whose last step uses the remaining stick $[0,L_n]$.
--
--   **Formalization Note** The objects are defined for any $X,Y,V,T$; the theorems apply them to a coupling. Sticks are 0-based as in `StickBreaking`.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, (1.2), p. 2; Theorem 1, (1.3), p. 3

import Mathlib
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_LevyExtrema_SBA_supTime
import Definitions.Def_LevyExtrema_SBA_StickBreaking
import Definitions.Def_LevyExtrema_SBA_stickSummand

open scoped NNReal

namespace LevyExtrema.SBA

/-- **The stick-breaking approximation χ_n, (1.2).**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, (1.2), p. 2:
"χ_n = Σ_{k=1}^n (Y_{L_{k−1}} − Y_{L_k}, (Y_{L_{k−1}} − Y_{L_k})^+, ℓ_k · 1{Y_{L_{k−1}}−Y_{L_k}>0})
+ (Y_{L_n}, Y^+_{L_n}, L_n · 1{Y_{L_n}>0})".
Lean's `Σ_{k ∈ range n}` is the paper's `Σ_{k=1}^n` (0-based sticks). -/
noncomputable def sba (T : ℝ≥0) {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ × ℝ × ℝ :=
  (∑ k ∈ Finset.range n, stickSummand T Y V k ω) +
    (atStick T Y V n ω, max (atStick T Y V n ω) 0,
      if 0 < atStick T Y V n ω then stickRem T V n ω else 0)

/-- **Error Δ_n of the supremum, (1.3)** (p. 3):
"Δ_n = X̄_T − Σ_{k=1}^n (Y_{L_{k−1}} − Y_{L_k})^+". -/
noncomputable def errSup (T : ℝ≥0) {Ω : Type*} (X Y : ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  runSup (fun s => X s ω) T -
    ∑ k ∈ Finset.range n, max (atStick T Y V k ω - atStick T Y V (k + 1) ω) 0

/-- **Error δ_n of the time of the supremum, (1.3)** (p. 3):
"δ_n = τ_T − Σ_{k=1}^n ℓ_k · 1{Y_{L_{k−1}}−Y_{L_k}>0}". -/
noncomputable def errTime (T : ℝ≥0) {Ω : Type*} (X Y : ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  ((supTime (fun s => X s ω) T : ℝ≥0) : ℝ) -
    ∑ k ∈ Finset.range n,
      (if 0 < atStick T Y V k ω - atStick T Y V (k + 1) ω then stickLen T V k ω else 0)

/-- **SBA error of the supremum Δ^SB_n = Δ_n − Y^+_{L_n}** (Theorem 1, (1.3), p. 3). -/
noncomputable def errSupSB (T : ℝ≥0) {Ω : Type*} (X Y : ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  errSup T X Y V n ω - max (atStick T Y V n ω) 0

/-- **SBA error of the time δ^SB_n = δ_n − L_n · 1{Y_{L_n} > 0}** (Theorem 1, (1.3), p. 3). -/
noncomputable def errTimeSB (T : ℝ≥0) {Ω : Type*} (X Y : ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  errTime T X Y V n ω - (if 0 < atStick T Y V n ω then stickRem T V n ω else 0)

end LevyExtrema.SBA


