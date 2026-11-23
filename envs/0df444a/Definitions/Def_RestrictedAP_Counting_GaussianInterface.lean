-- Prove2me | Definitions.Def_RestrictedAP_Counting_GaussianInterface
-- name    : RestrictedAP_Counting_GaussianInterface
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:56:53.544851+00:00
-- url     : https://prove2.me/theorems/06c99377-f1e0-42ee-b6c3-d0366abfb43a
-- title:
--   Multilinear polynomials and proper Gaussian interfaces for the counting lemma
-- statement:
--   Interfaces for the finite Fourier/Gaussian dictionary in §5.1 and §5.2.5. For coefficients $c_\alpha$, `multiEval c a` is $\sum_\alpha c_\alpha\prod_i a_{i,\alpha_i}$, with index $0$ interpreted as the constant factor. `gaussianPoly` evaluates this polynomial on one of three jointly proper complex Gaussian blocks. `gaussianLaw A` is the law of $AZ$ for independent standard $\mathcal{CN}(0,1)$ entries of $Z$, so its covariance is $AA^*$. `gaussianTruncError` and `gaussianTruncTriple` are respectively $\mathbb E|\operatorname{trunc}_{[0,1]}M-M|$ and $\mathbb E\prod_{i=0}^2\operatorname{trunc}_{[0,1]}M_i$ in Gaussian space.
--
--   The map `baseCoord` embeds the $nq'$ variables used by the polynomial into dimension $nq'+1$. The extra dummy coordinate is deliberately independent; it ensures that the ambient dimension is positive even when $n=0$ or $q'=0$, which is necessary for reverse hypercontractivity.
--
--   For $z\in\mathbb C$ the module also records $0\leq\operatorname{trunc}_{[0,1]}z\leq1$ and $\operatorname{trunc}_{[0,1]}z-\operatorname{Re}z\leq|\operatorname{trunc}_{[0,1]}z-z|$.
-- source:
--   Bhangale–Khot–Liu–Minzer, arXiv:2608.17365 (paper #1020), Definition 2.22 pp.13–14 (proper complex Gaussian covariance representation), Definition 3.4 p.18 (multilinear representation), and §5.2.5 pp.43–47 (Gaussian polynomials, truncation errors, and truncated triple correlation). The explicit dummy coordinate and elementary truncation lemmas are formalization infrastructure needed for n=0 edge cases and Claims 5.25/5.26.

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_LowInfluence
import Definitions.Def_BraneBrauer_Orthogonal_ComplexGaussian

namespace RestrictedAP.Counting

open MeasureTheory ComplexOrder

/-- The multilinear polynomial associated with a Fourier coefficient function. Index zero
means that a variable is absent; the other indices select the nonconstant basis vectors. -/
noncomputable def multiEval {n q' : ℕ} (coeff : (Fin n → Fin (q' + 1)) → ℂ)
    (a : Fin n × Fin q' → ℂ) : ℂ :=
  ∑ α : Fin n → Fin (q' + 1), coeff α * ∏ i : Fin n,
    if h : α i = 0 then 1 else a (i, (α i).pred h)

/-- Embed the original `n * q'` Gaussian coordinates into a space with one additional
independent dummy coordinate. -/
def baseCoord {n q' : ℕ} (k : Fin n × Fin q') : Fin (n * q' + 1) :=
  Fin.castAdd 1 (finProdFinEquiv k)

/-- The proper complex Gaussian law determined by a square root of its covariance. -/
noncomputable def gaussianLaw {ℓ N : ℕ}
    (A : Matrix (Fin ℓ × Fin N) (Fin ℓ × Fin N) ℂ) : Measure (Fin ℓ × Fin N → ℂ) :=
  (Measure.pi (fun _ : Fin ℓ × Fin N => BraneBrauer.Orthogonal.complexGaussian)).map
    (fun z => A.mulVec z)

/-- Evaluate the same multilinear polynomial on the `i`-th Gaussian block. -/
noncomputable def gaussianPoly {n q' : ℕ} (coeff : (Fin n → Fin (q' + 1)) → ℂ)
    (G : Fin 3 × Fin (n * q' + 1) → ℂ) (i : Fin 3) : ℂ :=
  multiEval coeff (fun k => G (i, baseCoord k))

/-- The first moment of the truncation discrepancy in Gaussian space. -/
noncomputable def gaussianTruncError {n q' : ℕ} (coeff : (Fin n → Fin (q' + 1)) → ℂ)
    (A : Matrix (Fin 3 × Fin (n * q' + 1)) (Fin 3 × Fin (n * q' + 1)) ℂ) (i : Fin 3) : ℝ :=
  ∫ G, ‖(trunc01 (gaussianPoly coeff G i) : ℂ) - gaussianPoly coeff G i‖ ∂gaussianLaw A

/-- The triple correlation after truncation in Gaussian space. -/
noncomputable def gaussianTruncTriple {n q' : ℕ} (coeff : (Fin n → Fin (q' + 1)) → ℂ)
    (A : Matrix (Fin 3 × Fin (n * q' + 1)) (Fin 3 × Fin (n * q' + 1)) ℂ) : ℝ :=
  ∫ G, (trunc01 (gaussianPoly coeff G 0) * trunc01 (gaussianPoly coeff G 1) *
    trunc01 (gaussianPoly coeff G 2)) ∂gaussianLaw A

lemma trunc01_nonneg (z : ℂ) : 0 ≤ trunc01 z := by
  exact le_max_left _ _

lemma trunc01_le_one (z : ℂ) : trunc01 z ≤ 1 := by
  exact max_le (by norm_num) (min_le_left _ _)

lemma trunc01_sub_re_le_norm (z : ℂ) : trunc01 z - z.re ≤ ‖(trunc01 z : ℂ) - z‖ := by
  have hre : ((trunc01 z : ℂ) - z).re = trunc01 z - z.re := by simp
  rw [← hre]
  exact le_trans (le_abs_self _) (Complex.abs_re_le_norm _)

end RestrictedAP.Counting


