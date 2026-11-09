-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Covariance
-- name    : OnlinePerceptronIsolation_Binary_Covariance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:29.571114+00:00
-- url     : https://prove2.me/theorems/ab9a51f0-8eba-4132-8f19-1be23ffa1958
-- title:
--   Covariance, marginal standard deviations and normalized sums
-- statement:
--   For a random vector $X$ under a probability law $P$, write
--   $$\Sigma_{jk}=\mathbb E[(X_j-\mathbb EX_j)(X_k-\mathbb EX_k)],\qquad \sigma_j=\sqrt{\Sigma_{jj}}.$$
--   For summands $X_1,\ldots,X_r$, the normalized sum is $W=r^{-1/2}\sum_iX_i$. Covariance uses Mathlib's covariance integral, and all values are computed from the supplied vectors and law. This interface names the quantities used throughout the Gaussian approximation statements. Their moments exist under the actual Gaussian sign model, and under A.1's finite Orlicz bounds and positive marginal variances; no expectation of a nonintegrable variable is being used as a genuine zero.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Theorem A.1, Eq. (A.1), printed p.18, PDF p.20; Lemma A.5, Eq. (A.32), printed pp.21-22, PDF pp.23-24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- Coordinate covariance; finite moments are stated or follow from Gaussian inputs. -/
noncomputable def covMatrix {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) (X : Ω → Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => covariance (fun ω => X ω i) (fun ω => X ω j) P

/-- The source's σ_j is the nonnegative square root of the covariance diagonal. -/
noncomputable def marginalSD {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) : ℝ :=
  Real.sqrt (S j j)

/-- The normalized sum in (A.1) and (A.32), computed from the summands. -/
noncomputable def normalizedSum {Ω : Type*} {m r : ℕ}
    (X : Fin r → Ω → Fin m → ℝ) (ω : Ω) : Fin m → ℝ :=
  fun j => (∑ i : Fin r, X i ω j) / Real.sqrt r

end OnlinePerceptronIsolation.Binary


