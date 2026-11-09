-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_SignedGaussian
-- name    : OnlinePerceptronIsolation_Binary_SignedGaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:23.395675+00:00
-- url     : https://prove2.me/theorems/d9d08f24-d8a5-4fef-8b6a-7ebfc4efcfe8
-- title:
--   Signed Gaussian columns and their actual centered versions
-- statement:
--   Under the independent standard Gaussian matrix law, for a fixed measurable sign map $\phi$ define
--   $$S_i=\phi(Y_i)Y_i,\qquad W_i=S_i-\mathbb E[S_i].$$
--   Each coordinate of the mean is integrated under that same matrix law. Neither the mean nor covariance is a free parameter. These are derived random vectors to which the four conclusions of A.5 apply. Since $|S_{ij}|=|Y_{ij}|$, their moments exist for every measurable sign map, even if the signed vectors are not centered before subtracting the mean. No moment or spectral estimate is built into this definition.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Lemma A.5, Eq. (A.32), printed pp.21-22, PDF pp.23-24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Uniqueness
import Definitions.Def_OnlinePerceptronIsolation_Binary_Covariance
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- S_i = ϕ(Y_i)Y_i from the actual matrix column, (A.32). -/
def signedColumn {m r : ℕ} (ϕ : (Fin m → ℝ) → ℝ) (i : Fin r)
    (Y : Fin m × Fin r → ℝ) : Fin m → ℝ :=
  fun j => ϕ (fun k => Y (k, i)) * Y (j, i)

/-- W_i = S_i - E S_i, under the genuine product Gaussian law. -/
noncomputable def centeredColumn {m r : ℕ} (ϕ : (Fin m → ℝ) → ℝ) (i : Fin r)
    (Y : Fin m × Fin r → ℝ) : Fin m → ℝ :=
  fun j => signedColumn ϕ i Y j -
    ∫ T, signedColumn ϕ i T j ∂(ABPOnline.gaussMat m r)

end OnlinePerceptronIsolation.Binary


