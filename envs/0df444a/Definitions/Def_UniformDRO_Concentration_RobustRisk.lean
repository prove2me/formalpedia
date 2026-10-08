-- Prove2me | Definitions.Def_UniformDRO_Concentration_RobustRisk
-- name    : UniformDRO_Concentration_RobustRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:00:55.871983+00:00
-- url     : https://prove2.me/theorems/67ed9190-8566-478c-a961-368c3eaa49c0
-- title:
--   (6), (7), (3), p. 38 — Cressie–Read f_k, the robust risk R_k(Z; P), the empirical measure P̂ₙ and the dual objective g_k(η; P)
-- statement:
--   This module fixes the objects of Duchi and Namkoong's finite-sample analysis of the Cressie–Read robust risk.
--
--   Throughout, $k\in(1,\infty)$ and $\rho>0$.
--
--   1. **Conjugate exponent and constant.** $k_*=k/(k-1)$ and $c_k(\rho)=(1+k(k-1)\rho)^{1/k}$.
--   2. **The Cressie–Read function** (6): for $t\ge 0$,
--   $$
--   f_k(t)=\frac{t^k-kt+k-1}{k(k-1)} ,
--   $$
--   a convex nonnegative function with $f_k(1)=0$; the paper sets $f_k(t)=+\infty$ for $t<0$.
--   3. **The robust risk** (7), written through likelihood ratios as in (3). For a probability measure $P$ on $(\mathcal X,\mathcal A)$ and a loss $Z=\ell(\theta;\cdot):\mathcal X\to\mathbb R$,
--   $$
--   \mathcal R_k(Z;P)=\sup\Big\{\mathbb E_P[LZ]\;:\;L\ge 0\text{ measurable},\ \mathbb E_P[L]=1,\ \mathbb E_P[f_k(L)]\le\rho\Big\},
--   $$
--   which equals $\sup_{Q\ll P}\{\mathbb E_Q[Z]: D_{f_k}(Q\|P)\le\rho\}$ with $L=dQ/dP$.
--   4. **The empirical measure** of a sample $x_1,\dots,x_n$ is $\widehat P_n=\frac1n\sum_{i=1}^n\delta_{x_i}$.
--   5. **The dual objective** of Appendix C.1:
--   $$
--   g_k(\eta;P)=c_k(\rho)\,\big(\mathbb E_P[(Z-\eta)_+^{k_*}]\big)^{1/k_*}+\eta ,\qquad \eta\in\mathbb R .
--   $$
--
--   By Lemma 1, $\mathcal R_k(Z;P)=\inf_\eta g_k(\eta;P)$; the concentration of $\mathcal R_k(Z;\widehat P_n)$ around $\mathcal R_k(Z;P_0)$ (Theorem 2) is proved through $g_k$.
--
--   **Formalization Note** Powers $t^k$, $(\cdot)^{1/k}$, $(\cdot)^{k_*}$ are real powers (`Real.rpow`). $f_k$ is a real function evaluated only at $t\ge 0$; its value $+\infty$ on $t<0$ is never needed, since likelihood ratios are nonnegative. In the robust risk, the divergence constraint is a lower Lebesgue integral of $f_k(L)\ge0$, so a ratio with $\mathbb E_P[f_k(L)]=\infty$ is excluded; $L$ and $LZ$ are required integrable, so $\mathbb E_P[LZ]$ is a genuine expectation. The supremum is a real `sSup`: every statement using it has $Z$ bounded (or $Z\in L^{k_*}(P)$), which makes the value set nonempty ($L\equiv1$) and bounded above. The empirical measure is a probability measure for $n\ge1$, which every statement assumes. On a measurable space whose σ-algebra does not separate two sample points, a measurable $Z$ takes the same value at both, so the supremum over measurable $L$ is still the paper's $\mathcal R_k(Z;\widehat P_n)$.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, Notation p. 5 (k*), (3) p. 5, (6) and (7) p. 6, c_k(ρ) in Lemma 1 p. 6, P̂ₙ p. 2, g_k(η; P) App. C.1 p. 38

import Mathlib

namespace UniformDRO.Concentration

open MeasureTheory

/-- The conjugate exponent `k* = k / (k - 1)` (Duchi & Namkoong, arXiv:1810.08750v6, Notation,
p. 5). Used for `k ∈ (1, ∞)`, where `k* ∈ (1, ∞)`. -/
noncomputable def kstar (k : ℝ) : ℝ := k / (k - 1)

/-- The constant `c_k(ρ) = (1 + k(k - 1)ρ)^{1/k}` of Lemma 1 (p. 6), Theorem 2 (p. 20) and
App. C.1 (p. 38), a real power (`Real.rpow`). For `k > 1` and `ρ > 0` it is `> 1`. -/
noncomputable def ck (k ρ : ℝ) : ℝ := (1 + k * (k - 1) * ρ) ^ (1 / k)

/-- The Cressie–Read divergence function of (6), p. 6:
`f_k(t) = (t^k - k t + k - 1) / (k (k - 1))`, with `t^k` the real power `Real.rpow`.
It is used only at `t ≥ 0`, where for `k > 1` it is finite, convex and `≥ 0` with `f_k(1) = 0`.
The paper sets `f_k(t) = +∞` for `t < 0`; that value is never evaluated here, because the
robust risk below only feeds nonnegative likelihood ratios to `f_k`, and the published conjugate
`PhiDivRobust.Counterpart.conj` takes its supremum over `t ≥ 0`. -/
noncomputable def cressieRead (k t : ℝ) : ℝ := (t ^ k - k * t + k - 1) / (k * (k - 1))

/-- The Cressie–Read robust risk (7), p. 6, in the likelihood-ratio form (3), p. 5:
`R_k(Z; P) = sup { E_P[L Z] : L ≥ 0 measurable, E_P[L] = 1, E_P[f_k(L)] ≤ ρ }`,
where `L = dQ/dP` ranges over the densities of the distributions `Q ≪ P`, and `Z = ℓ(θ; ·)` is the
loss at a fixed parameter.

* The divergence constraint is a lower Lebesgue integral of `f_k(L) ≥ 0`, so a density with
  `E_P[f_k(L)] = ∞` is excluded (no Bochner junk value `0`).
* `E_P[L Z]` is required to be integrable, so it is a genuine expectation.
* The value set always contains `E_P[Z]` (take `L ≡ 1`, `f_k(1) = 0`) when `Z` is integrable,
  and it is bounded above when `Z` is bounded above, or when `Z ∈ L^{k*}(P)` (Hölder, since
  `E_P[f_k(L)] ≤ ρ` and `E_P[L] = 1` give `E_P[L^k] ≤ 1 + k(k - 1)ρ`). Every statement using
  `robustRisk` assumes one of these, so the real `sSup` is the paper's supremum. -/
noncomputable def robustRisk {X : Type*} [MeasurableSpace X] (k ρ : ℝ) (P : Measure X)
    (Z : X → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ L : X → ℝ, Measurable L ∧ (∀ x, 0 ≤ L x) ∧ Integrable L P ∧
    ∫ x, L x ∂P = 1 ∧ Integrable (fun x => L x * Z x) P ∧
    ∫⁻ x, ENNReal.ofReal (cressieRead k (L x)) ∂P ≤ ENNReal.ofReal ρ ∧
    v = ∫ x, L x * Z x ∂P}

/-- The empirical measure `P̂_n = n⁻¹ ∑ᵢ δ_{xᵢ}` of a sample `s = (x₁, …, x_n)` (p. 2).
It is a probability measure when `0 < n`; every statement using it assumes `0 < n`. -/
noncomputable def empiricalMeasure {X : Type*} [MeasurableSpace X] {n : ℕ} (s : Fin n → X) :
    Measure X :=
  ((n : ENNReal)⁻¹) • ∑ i, Measure.dirac (s i)

/-- The dual objective of App. C.1, p. 38:
`g_k(η; P) = c_k(ρ) (E_P[(Z - η)_+^{k*}])^{1/k*} + η`, with real powers. By Lemma 1,
`R_k(Z; P) = inf_η g_k(η; P)`. -/
noncomputable def dualObjective {X : Type*} [MeasurableSpace X] (k ρ : ℝ) (P : Measure X)
    (Z : X → ℝ) (η : ℝ) : ℝ :=
  ck k ρ * (∫ x, (max (Z x - η) 0) ^ kstar k ∂P) ^ (1 / kstar k) + η

end UniformDRO.Concentration


