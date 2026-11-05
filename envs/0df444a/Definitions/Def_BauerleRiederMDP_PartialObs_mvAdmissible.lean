-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_mvAdmissible
-- name    : BauerleRiederMDP_PartialObs_mvAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:03:18.513182+00:00
-- url     : https://prove2.me/theorems/db93df5f-70e5-4428-9a47-787fa1ddda5a
-- title:
--   Admissible strategies of the mean-variance problem (MV)
-- statement:
--   In the mean–variance problem (MV) with partial observation (horizon $N$, initial wealth $x_0$, target $\mu$, interest rates $i_n$, $E_X=\mathbb R$, unconstrained actions $D_n(x)=\mathbb R^d$), a portfolio strategy $\varphi=(\varphi_0,\dots,\varphi_{N-1})$ is admissible if
--
--   1. each $\varphi_n$ is a measurable function of the observed returns $(R_1,\dots,R_n)$ (history dependence is allowed);
--   2. the terminal wealth $X_N$ has a finite second moment under the market law with $Y_0\sim Q_0$;
--   3. $\mathbb E X_N\ge\mu$.
--
--   **Formalization Note** A strategy whose terminal wealth is not square integrable has infinite variance (or no mean) and cannot compete in (MV); requiring 2. does not change the value of (MV).
-- source:
--   Bäuerle & Rieder (2011), §6.2, problem (MV), p.184 (PDF 197)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_returnLaw
import Definitions.Def_BauerleRiederMDP_PartialObs_wealth

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **Admissible strategies of the mean-variance problem (MV) with partial observation.**
Bäuerle & Rieder (2011), §6.2, p.184 (PDF 197): `(MV)`: `Var^π_{x_0}(X_N) → min`,
`IE^π_{x_0}[X_N] ≥ μ`, `π ∈ Π_N`, where `Π_N` is the set of history-dependent policies
(`f_n : H_n → A` depends on the observable history), `A = ℝ^d`, `D_n(x) = A`, and
`T_{n,X}(x, a, z) = (1 + i_{n+1})(x + a · z)`.

`mvAdmissible M i N x0 μ φ`: each `φ_n`, `n < N`, is a measurable function of the observed returns
`(R_1, …, R_n)`; the terminal wealth `X_N` from `x_0` (rates `i_n`) has finite second moment under the
market law `M.returnLaw M.Q0 N`; and `IE X_N ≥ μ`.

**Formalization Note.** A strategy whose `X_N` is not square integrable has `Var = +∞` (or an
undefined mean) and cannot compete in (MV); restricting to `L²` changes no infimum. -/
def mvAdmissible {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) (i : ℕ → ℝ)
    (N : ℕ) (x0 μ : ℝ) (φ : (n : ℕ) → (Fin n → Fin d → ℝ) → Fin d → ℝ) : Prop :=
  (∀ n < N, Measurable (φ n)) ∧ MemLp (wealth i x0 φ N) 2 (M.returnLaw M.Q0 N) ∧
    μ ≤ ∫ r, wealth i x0 φ N r ∂M.returnLaw M.Q0 N

end BauerleRiederMDP.PartialObs


