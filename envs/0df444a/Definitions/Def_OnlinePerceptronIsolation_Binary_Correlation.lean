-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Correlation
-- name    : OnlinePerceptronIsolation_Binary_Correlation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:16.336076+00:00
-- url     : https://prove2.me/theorems/75dba9c7-ef8e-4328-b14c-6dc937dab8ed
-- title:
--   Euclidean spectral lower bounds
-- statement:
--   For a symmetric real matrix $R$, the condition $\lambda_{\min}(R)\ge b$ is written as
--   $$\forall x\in\mathbb R^m,\qquad x^TRx\ge b\sum_{j=1}^m x_j^2.$$
--   The correlation matrix itself reuses the published function $\operatorname{corr}(\Sigma)_{ij}=\Sigma_{ij}/\sqrt{\Sigma_{ii}\Sigma_{jj}}$. At the positive covariance diagonals in A.1 and A.5 this equals $D^{-1}\Sigma D^{-1}$, where $D$ has entries $\sqrt{\Sigma_{jj}}$. This definition supplies only the quadratic-form predicate; it adds no nondegeneracy, boundedness, or source conclusion to any model. The Euclidean sum of squares is explicit and is independent of the default function-space norm.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Theorem A.1, printed p.18, PDF p.20; Lemma A.5, printed p.22, PDF p.24; Eqs. (A.46)-(A.51), printed p.23, PDF p.25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Covariance
import Definitions.Def_CODATA_uncert
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- For symmetric matrices, λ_min(R) ≥ b, expressed without an arbitrary eigenvalue ordering. -/
def HasSpectralLowerBound {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (b : ℝ) : Prop :=
  ∀ x : Fin m → ℝ, b * (∑ i : Fin m, x i ^ 2) ≤
    ∑ i : Fin m, ∑ j : Fin m, x i * R i j * x j

end OnlinePerceptronIsolation.Binary


