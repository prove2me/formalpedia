-- Prove2me | Definitions.Def_UCalibDirichlet_Supplement_lapRegret
-- name    : UCalibDirichlet_Supplement_lapRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:10:17.001058+00:00
-- url     : https://prove2.me/theorems/9d4334c7-7c85-4798-bce8-a3b7109cd708
-- title:
--   Worst-case expected regret $R^{\mathrm{LP}}_F(T)$ of Algorithm 1 (the Laplace forecaster)
-- statement:
--   For a loss $\ell$ on $\Delta_K\times[K]$ and a horizon $T$, the worst-case expected regret of Algorithm 1 is
--   $$R^{\mathrm{LP}}_\ell(T)=\max_{i_1,\dots,i_T\in[K]}\mathrm{Reg}_\ell(T;\,i_{1:T}),$$
--   where $\mathrm{Reg}_\ell(T;i_{1:T})$ is the expected regret (display (2)) of Algorithm 1, which forecasts $P_t\sim\mathrm{Dir}(\mathbf 1+N_{t-1})$, on the fixed outcome sequence $i_{1:T}$.
--
--   At $K=2$ Algorithm 1 is the Laplace forecaster of Appendix E, $P_t\sim\mathrm{Beta}(1+N_{t-1,1},\,1+N_{t-1,0})$, and $R^{\mathrm{LP}}_F(T)$ is this quantity for the canonical loss $\ell_F$. A worst-case bound "$\mathrm{Reg}_F(T)=O(\cdot)$ for Algorithm 1" is a bound on $R^{\mathrm{LP}}$.
--
--   **Formalization Note** The maximum is the extended-real supremum over all sequences $\{0,\dots,T-1\}\to[K]$, using the base mission's regret and Algorithm 1.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), App. E.1.1, p.40 (R^LP_F(T)); Algorithm 1, p.3

import Mathlib
import Definitions.Def_UCalibDirichlet_regret
import Definitions.Def_UCalibDirichlet_alg1

namespace UCalibDirichlet.Supplement

/-- **Worst-case expected regret of Algorithm 1 (the Laplace forecaster), `R^LP_F(T)`.** Frongillo,
Luo, Mehta & Schneider (manuscript, STOC 2027 submission), App. E.1.1, p.40: "We write `R^LP_F(T)`
for the Laplace forecaster's worst-case expected regret"; "The forecaster draws `P_t ∼ Beta(a_t, b_t)`,
where `a_t = 1 + N_{t−1,1}` and `b_t = 1 + N_{t−1,0}`", which is Algorithm 1 (p.3) at `K = 2`.

`lapRegret ℓ T = sup_{i_{1:T}} Reg_ℓ(T; i_{1:T})`, the supremum over all outcome sequences of the
expected regret of `alg1`.

**Formalization Note.** The supremum is the `EReal` supremum over `Fin T → Fin K` (finite, so it
is a maximum). The base `alg1` at `K = 2` draws `P ∼ Dir(1 + N_{t−1,0}, 1 + N_{t−1,1})`, whose
coordinate `P₁` has law `Beta(1 + N_{t−1,1}, 1 + N_{t−1,0})`, the Laplace forecaster of App. E. The
definition is stated for every `K`; `Reg_F(T)` of Algorithm 1 in a worst-case bound is this
quantity. -/
noncomputable def lapRegret {K : ℕ} (ℓ : (Fin K → ℝ) → Fin K → EReal) (T : ℕ) : EReal :=
  ⨆ i : Fin T → Fin K, regret ℓ alg1 i

end UCalibDirichlet.Supplement


