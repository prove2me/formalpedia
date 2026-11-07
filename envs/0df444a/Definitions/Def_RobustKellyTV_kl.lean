-- Prove2me | Definitions.Def_RobustKellyTV_kl
-- name    : RobustKellyTV_kl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:08.648257+00:00
-- url     : https://prove2.me/theorems/c4d64bcc-dbde-49d0-adc6-2be2c96faf32
-- title:
--   Kullback–Leibler divergence on $\Delta_d$ and the information number $\Gamma(S)$
-- statement:
--   For probability mass functions $S,R$ on $\{1,\dots,d\}$ the **Kullback–Leibler divergence** is
--
--   $$D_{\mathrm{KL}}(S\|R)=\sum_{i=1}^d S_i\log\frac{S_i}{R_i}\in[0,\infty],$$
--
--   with $0\log 0=0$ and $D_{\mathrm{KL}}(S\|R)=\infty$ whenever $R_i=0<S_i$ for some $i$. The **information number** of an alternative $S\in\Delta_d$ is
--
--   $$\Gamma(S)=\inf_{R\in\mathcal P_0}D_{\mathrm{KL}}(S\|R).$$
--
--   It is finite for every $S$ in the simplex (take $R=P$, which has full support), and it is the optimal growth rate of evidence against $\mathcal P_0$ under $S$.
--
--   **Formalization Note** The divergence is valued in $[0,\infty]$; when no $R_i=0<S_i$ occurs it is the real sum (nonnegative for probability vectors). $\Gamma$ is the infimum in $[0,\infty]$, converted to a real number; it is defined on the whole simplex, including $S$ with zero coordinates.
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, eq. (1) p.2; §3 p.11

import Mathlib
import Definitions.Def_RobustKellyTV_Setting

open scoped ENNReal

namespace RobustKellyTV

variable {d : ℕ}

/-- The Kullback–Leibler divergence `D_KL(S‖R) = Σᵢ Sᵢ log(Sᵢ / Rᵢ)` between probability mass
functions on `Fin d`, valued in `[0, ∞]` (arXiv:2611.02130v1, eq. (1), p.2).

**Formalization Note.** The value is `∞` when some `Rᵢ = 0 < Sᵢ`; otherwise it is the finite sum,
with the convention `0 log 0 = 0` (Lean's `0 * Real.log _ = 0`). For probability vectors the finite
sum is nonnegative (Gibbs), so `ENNReal.ofReal` loses nothing; the definition is only applied to
points of the simplex. -/
noncomputable def kl (S R : Fin d → ℝ) : ℝ≥0∞ :=
  if ∃ i, 0 < S i ∧ R i = 0 then ⊤ else ENNReal.ofReal (∑ i, S i * Real.log (S i / R i))

/-- The information number `Γ(S) = inf_{R ∈ P0} D_KL(S‖R)` (arXiv:2611.02130v1, eq. (1), p.2,
with `P = P0` from §2 on; restated p.11). It is defined on the whole simplex, including `S` with
zero coordinates.

**Formalization Note.** The infimum is taken in `[0, ∞]`, where it is finite because `P ∈ P0` has
full support (`D_KL(S‖P) < ∞`); `Γ` is that infimum as a real number. -/
noncomputable def Gamma (σ : Setting d) (S : Fin d → ℝ) : ℝ :=
  (⨅ R ∈ nullBall σ, kl S R).toReal

end RobustKellyTV


