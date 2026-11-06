-- Prove2me | Definitions.Def_MemQueryFeas_condNum
-- name    : MemQueryFeas_condNum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:32.878202+00:00
-- url     : https://prove2.me/theorems/89077e0e-4ff1-4fda-b5ce-4c18c12df8d2
-- title:
--   Condition number $\kappa(T)$
-- statement:
--   The **condition number** of a linear map $T$ of $\mathbb R^d$ is
--   $$
--   \kappa(T)=\frac{\lambda_{\max}(T)}{\lambda_{\min}(T)} .
--   $$
--
--   **Formalization Note** $\lambda_{\max}(T)$ is the operator norm and $\lambda_{\min}(T)=\inf_{\|x\|=1}\|Tx\|$ is the platform's `DissolveCDF.sigmaMin` (the minimum singular value). For singular $T$ the quotient is $0$ in Lean; every statement using $\kappa(T)$ assumes $T$ invertible.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MemQueryFeas_Op
import Definitions.Def_DissolveCDF_sigmaMin

namespace MemQueryFeas

/-- **Condition number `κ(T)`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8): "We then denote by
`κ(T) := λ_max(T)/λ_min(T)` its condition number."

**Formalization Note.** `λ_max(T) = ‖T‖` (operator norm) and `λ_min(T) = inf_{‖x‖=1} ‖T x‖` is the
platform's `DissolveCDF.sigmaMin`. For a singular `T`
the division returns `0`; every statement using `κ(T)` assumes `T` invertible. -/
noncomputable def condNum {d : ℕ} (T : Op d) : ℝ :=
  ‖T‖ / DissolveCDF.sigmaMin T

end MemQueryFeas


