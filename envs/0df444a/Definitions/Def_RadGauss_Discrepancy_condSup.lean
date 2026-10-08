-- Prove2me | Definitions.Def_RadGauss_Discrepancy_condSup
-- name    : RadGauss_Discrepancy_condSup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:08:46.939702+00:00
-- url     : https://prove2.me/theorems/741c2692-6b15-4af5-91ae-5d7f72b1d38d
-- title:
--   Appendix A — s(N) = (2/n) E[sup_{f∈F} Σ σ_i f(X_i) | Σ σ_i = N]
-- statement:
--   Let $\mu$ be a probability measure on $\mathcal X$, $F$ a class of functions $\mathcal X\to\mathbb R$, $X_1,\dots,X_n$ i.i.d. from $\mu$, and $\sigma_1,\dots,\sigma_n$ independent uniform $\{\pm1\}$-valued signs, independent of the sample. For an integer $N$ define
--
--   $$
--   s(N) = \frac{2}{n}\,\mathbf E\left[\sup_{f\in F}\sum_{i=1}^n \sigma_i f(X_i)\;\middle|\;\sum_{i=1}^n \sigma_i = N\right].
--   $$
--
--   Given $\sum_i\sigma_i = N$, the sign vector is uniform on the sign vectors with that sum, so $s(N)$ is the average over those sign vectors $\sigma$ of $\frac2n\,\mathbf E\sup_{f\in F}\sum_i\sigma_i f(X_i)$. Note that there is no absolute value. The function $s$ interpolates between the Rademacher complexity (signs drawn at random) and the maximum discrepancy (exactly half the signs positive).
--
--   **Formalization Note** `sumSign σ` is the integer $\sum_i \sigma_i$. The value is meaningful only for $N$ attained by some sign vector ($N \equiv n \bmod 2$, $|N| \le n$); otherwise the average is over the empty set and the definition returns $0$. The supremum is a real supremum over the subtype $F$.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 478 (PDF p. 16), Appendix A, display after 'Define'

import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

open MeasureTheory

namespace RadGauss.Discrepancy

/-- The integer sum `Σ_{i=1}^n σ_i` of a sign vector (`true ↦ 1`, `false ↦ -1`, as in
`signVal`). -/
def sumSign {n : ℕ} (σ : Fin n → Bool) : ℤ := ∑ i, if σ i then (1 : ℤ) else -1

/-- The function `s` of Appendix A (p. 478):
`s(N) = (2/n) E[ sup_{f ∈ F} Σ_{i=1}^n σ_i f(X_i) | Σ_{i=1}^n σ_i = N ]`,
where `X_1, …, X_n` are i.i.d. from `μ` and `σ_1, …, σ_n` are independent uniform signs,
independent of the sample. Conditioning on `Σ σ_i = N` makes `σ` uniform on the sign vectors with
that sum, so `s(N)` is the average, over those sign vectors, of
`(2/n) ∫ sup_{f ∈ F} Σ σ_i f(x_i) dμⁿ(x)`. No absolute value. The supremum is a real supremum
over the subtype `F`; the value is meaningful for `N` attained by some sign vector (otherwise the
average is over the empty set and equals `0`). -/
noncomputable def condSup {X : Type*} [MeasurableSpace X] (μ : Measure X) (n : ℕ)
    (F : Set (X → ℝ)) (N : ℤ) : ℝ :=
  (2 / (n : ℝ)) *
    (((Finset.univ.filter fun σ : Fin n → Bool => sumSign σ = N).card : ℝ)⁻¹ *
      ∑ σ ∈ Finset.univ.filter (fun σ : Fin n → Bool => sumSign σ = N),
        ∫ x, (⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) ∂(Measure.pi fun _ : Fin n => μ))

end RadGauss.Discrepancy


