-- Prove2me | Definitions.Def_MatrixLeeSidford_Supplement_updateWeight
-- name    : MatrixLeeSidford_Supplement_updateWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:17:19.479766+00:00
-- url     : https://prove2.me/theorems/707e039c-cf7b-4a19-ab8a-f8b974b15f05
-- title:
--   Damped inverse update $\mathrm{UpdateWeight}(G,\hat R)$ (Algorithm 8, Eq. (8.2))
-- statement:
--   Given a weight $G$, a symmetric estimate $\hat R$ of the stationarity matrix and a step size $\gamma_G$, the procedure $\mathrm{UpdateWeight}(G,\hat R)$ computes $L=\operatorname{chol}(G)$, checks
--   $$
--   I+\hat R\succ0\qquad\text{and}\qquad(1-\gamma_G)I+2\gamma_G(I+\hat R)^{-1}\succ0,
--   $$
--   reports failure if a check or the factorization fails, and otherwise returns the **damped inverse update**
--   $$
--   G^+=L\big((1-\gamma_G)I+2\gamma_G(I+\hat R)^{-1}\big)L^\top .
--   $$
--   Algorithm 8 uses $\gamma_G=1/(1000s)$.
--
--   **Formalization Note** Failure is the value `none`. The Cholesky factorization of $G$ fails exactly when $G$ is not positive definite, so that is checked too. The step size is a parameter.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Algorithm 8, p.82; Eq. (8.2), p.54

import Mathlib
import Definitions.Def_MatrixLeeSidford_Supplement_cholFactor

open Matrix

namespace MatrixLeeSidford.Supplement

/-- The **damped inverse update** `UpdateWeight(G, R̂)` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Algorithm 8, p.82, and Eq. (8.2),
p.54): compute `L = chol(G)`; check `I + R̂ ≻ 0` and `(1 − γ_G)I + 2γ_G(I + R̂)⁻¹ ≻ 0`, reporting failure if a
check or a factorization fails; return `L((1 − γ_G)I + 2γ_G(I + R̂)⁻¹)Lᵀ`.

**Formalization Note** Failure is `none`. The factorization `chol(G)` fails exactly when `G` is not
positive definite, so `G ≻ 0` is checked as well. The step size `γ_G` is a parameter (Algorithm 8
computes `γ_G = 1/(1000 s)`, which the theorems pass). -/
noncomputable def updateWeight {m : ℕ} (γG : ℝ) (G R : Matrix (Fin m) (Fin m) ℝ) :
    Option (Matrix (Fin m) (Fin m) ℝ) :=
  open Classical in
  if G.PosDef ∧ (1 + R).PosDef ∧ ((1 - γG) • (1 : Matrix (Fin m) (Fin m) ℝ) + (2 * γG) • (1 + R)⁻¹).PosDef
  then some (cholFactor G * ((1 - γG) • (1 : Matrix (Fin m) (Fin m) ℝ) + (2 * γG) • (1 + R)⁻¹) *
    (cholFactor G)ᵀ)
  else none

end MatrixLeeSidford.Supplement


