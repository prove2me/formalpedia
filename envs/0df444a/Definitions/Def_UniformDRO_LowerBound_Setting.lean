-- Prove2me | Definitions.Def_UniformDRO_LowerBound_Setting
-- name    : UniformDRO_LowerBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:10.597561+00:00
-- url     : https://prove2.me/theorems/eb6619fa-2f5f-4c52-b4e9-6596d1d11ffa
-- title:
--   (16), Thm 3, Lemma 12, (37) — p_k, β_k, two-point laws on {0, M}, the minimax risk 𝔐ₙ(𝒫, f_k) of the Cressie–Read robust risk R_k, and ‖P₀ⁿ − P₁ⁿ‖_TV
-- statement:
--   This file fixes the objects of the estimation lower bound of Duchi and Namkoong (Section 5.1).
--
--   **Parameters.** Let $k \in (1,\infty)$ and $\rho > 0$. Write $k_* = k/(k-1)$ for the Hölder conjugate of $k$ and
--   $$c_k(\rho) = (1 + k(k-1)\rho)^{1/k}, \qquad p_k = (1 + k(k-1)\rho)^{-1/(k-1)}, \qquad \beta_k = \frac{k(k-1)\rho}{2(1+k(k-1)\rho)}.$$
--   Equivalently $p_k = c_k^{-k/(k-1)} = c_k^{-k_*}$ and $\beta_k = \tfrac12(1 - c_k^{-k})$, the forms used in Lemma 12. For $k > 1$ and $\rho > 0$ one has $c_k > 1$, $p_k \in (0,1)$ and $\beta_k \in (0, \tfrac12)$.
--
--   **The Cressie–Read divergence and the robust risk** (recalled here; $k_*$, $c_k$, $f_k$ and $\mathcal R_k$ are defined in the imported shared module `UniformDRO.Concentration.RobustRisk`). The Cressie–Read function is
--   $$f_k(t) = \frac{t^k - kt + k - 1}{k(k-1)}, \qquad t \ge 0,$$
--   with $f_k(t) = +\infty$ for $t < 0$. For a probability measure $P$ and a real function $Z$, the robust risk is
--   $$\mathcal R_k(Z; P) = \sup\Bigl\{ \mathbb E_P[L Z] \;:\; L \ge 0 \text{ measurable},\ \mathbb E_P[L] = 1,\ \mathbb E_P[f_k(L)] \le \rho \Bigr\},$$
--   which is $\sup\{\mathbb E_Q[Z] : D_{f_k}(Q\|P) \le \rho\}$ written through the likelihood ratio $L = dQ/dP$ (so $Q \ll P$).
--
--   **Two-point laws.** For reals $z_0, z_1$ and $p \in [0,1]$, the law of $Z = z_0$ with probability $1-p$ and $Z = z_1$ with probability $p$ is $(1-p)\delta_{z_0} + p\,\delta_{z_1}$. Its robust risk $\mathcal R_k(Z)$ is the quantity of Lemma 12.
--
--   **The minimax risk.** Fix $M > 0$ and let $\mathcal P$ be the set of all distributions on $\{0, M\}$; each is the two-point law with some mass $p \in [0,1]$ at $M$. For $n$ i.i.d. draws $Z_1^n = (Z_1,\dots,Z_n)$ from $P_0 \in \mathcal P$, and an estimator $\widehat R : \{0,M\}^n \to \mathbb R$, the mean absolute error is $\mathbb E_{P_0^n}|\widehat R(Z_1^n) - \mathcal R_k(Z)|$, and
--   $$\mathfrak M_n(\mathcal P, f_k) = \inf_{\widehat R}\ \sup_{P_0 \in \mathcal P}\ \mathbb E_{P_0^n}\bigl|\widehat R(Z_1^n) - \mathcal R_k(Z)\bigr| \qquad (16).$$
--
--   **Total variation.** For the $n$-fold products $P^n, P'^n$ of the laws on $\{0,M\}$ with masses $p, p'$ at $M$,
--   $$\|P^n - P'^n\|_{\mathrm{TV}} = \sup_A |P^n(A) - P'^n(A)| = \tfrac12 \sum_{z \in \{0,M\}^n} |P^n\{z\} - P'^n\{z\}|.$$
--
--   These objects are shared by the goal (Theorem 3) and by every milestone of the mission.
--
--   **Formalization Note.** Real powers are `Real.rpow`. The robust risk is the real supremum of the feasible values; the feasible set always contains the value at $L \equiv 1$ and, for a two-point law, lies in $[\min(z_0,z_1), \max(z_0,z_1)]$, so the supremum is genuine. The divergence constraint is a lower Lebesgue integral of $f_k(L) \ge 0$, so a non-integrable $f_k(L)$ is excluded rather than counted as $0$. Expectations under $P_0^n$ are finite sums over $\{0,M\}^n$, indexed by $b \in \{\text{false},\text{true}\}^n$ (coordinate $M$ when true), with $P_0^n\{z\} = \prod_i (p \text{ if } b_i \text{ else } 1-p)$. The minimax risk takes values in $[0,\infty]$ (infimum over all real functions of the sample, outside a supremum over $p \in [0,1]$); for these laws it agrees with the platform's general `HighDimStat.Minimax.minimaxRisk`. The total variation is the half-$\ell^1$ distance of the point masses, which equals the supremum over events on the finite space.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, (3) p. 5; Notation p. 5 (k*); (6), (7) p. 6; §5.1 (16) p. 21; Theorem 3 pp. 21–22 (c_k, p_k, β_k); Lemma 12 p. 45 (two-point Z); (37) p. 45 (‖P₀ⁿ − P₁ⁿ‖_TV)

import Mathlib
import Definitions.Def_UniformDRO_Concentration_RobustRisk

namespace UniformDRO.LowerBound

open MeasureTheory

/-- The threshold `p_k = (1 + k(k - 1)ρ)^{-1/(k-1)}` of Theorem 3 (pp. 21–22). Lemma 12 (p. 45) writes
the same number as `c_k^{-k/(k-1)} = c_k^{-k*}`. For `k > 1`, `ρ > 0` it lies in `(0, 1)`. -/
noncomputable def pk (k ρ : ℝ) : ℝ := (1 + k * (k - 1) * ρ) ^ (-(1 / (k - 1)))

/-- The constant `β_k = k(k - 1)ρ / (2(1 + k(k - 1)ρ))` of Theorem 3 (p. 22). Lemma 12 (p. 45) writes
the same number as `½(1 - c_k^{-k})`, since `c_k^k = 1 + k(k - 1)ρ`. For `k > 1`, `ρ > 0` it lies in
`(0, ½)`. -/
noncomputable def βk (k ρ : ℝ) : ℝ := k * (k - 1) * ρ / (2 * (1 + k * (k - 1) * ρ))

/-- The law of the two-point random variable `Z = z₀` w.p. `1 - p`, `Z = z₁` w.p. `p`
(Lemma 12, p. 45): `(1 - p) δ_{z₀} + p δ_{z₁}` on `ℝ`. A probability measure for `p ∈ [0, 1]`.
The robust risk `R_k(Z)` of Lemma 12 is `robustRisk k ρ (twoPointLaw z₀ z₁ p) id`. -/
noncomputable def twoPointLaw (z₀ z₁ p : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac z₀ + ENNReal.ofReal p • Measure.dirac z₁

/-- The sample point of `{0, M}ⁿ` indexed by `b : Fin n → Bool`: coordinate `i` is `M` if `b i`,
else `0`. -/
def sampleVec {n : ℕ} (M : ℝ) (b : Fin n → Bool) : Fin n → ℝ := fun i => if b i then M else 0

/-- The probability `P₀ⁿ{Z₁ⁿ = sampleVec M b} = ∏ᵢ (p if bᵢ else 1 - p)` of a sample point when
`Z₁, …, Zₙ` are i.i.d. with `P₀{Z = M} = p`, `P₀{Z = 0} = 1 - p` (and `M > 0`, so the points are
distinct). -/
noncomputable def sampleProb {n : ℕ} (p : ℝ) (b : Fin n → Bool) : ℝ :=
  ∏ i, if b i then p else 1 - p

/-- The mean absolute error `E_{P₀ⁿ} |R̂(Z₁ⁿ) - R_k(Z)|` of an estimator `R̂` when `P₀` is the law on
`{0, M}` with mass `p` at `M` (the integrand of (16), p. 21), computed as a finite sum over `{0, M}ⁿ`
in `ℝ≥0∞`. -/
noncomputable def estRisk (k ρ M : ℝ) (n : ℕ) (R : (Fin n → ℝ) → ℝ) (p : ℝ) : ENNReal :=
  ∑ b : Fin n → Bool, ENNReal.ofReal
    (sampleProb p b * |R (sampleVec M b) - UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p) id|)

/-- The minimax risk (16), p. 21,
`𝔐ₙ(𝒫, f_k) = inf_{R̂} sup_{P₀ ∈ 𝒫} E_{P₀ⁿ} |R̂(Z₁ⁿ) - R_k(Z)|`,
where `𝒫` is the collection of all distributions on `{0, M}` (each is the law with mass `p ∈ [0, 1]`
at `M`) and the infimum is over all estimators `R̂ : {0, M}ⁿ → ℝ`. An estimator is any real function
of the sample; its values off `{0, M}ⁿ` are never used. Computed in `ℝ≥0∞`, with the infimum over
estimators outside the supremum over laws. -/
noncomputable def minimaxRisk (k ρ M : ℝ) (n : ℕ) : ENNReal :=
  ⨅ R : (Fin n → ℝ) → ℝ, ⨆ p ∈ Set.Icc (0 : ℝ) 1, estRisk k ρ M n R p

/-- The total variation distance `‖P₀ⁿ - P₁ⁿ‖_TV = sup_A |P₀ⁿ(A) - P₁ⁿ(A)| = ½ Σ_b |P₀ⁿ{b} - P₁ⁿ{b}|`
between the `n`-fold products of the laws on `{0, M}` with masses `p` and `p'` at `M`, computed on
the finite space `{0, M}ⁿ` (independent of `M > 0`). -/
noncomputable def tvDist (n : ℕ) (p p' : ℝ) : ℝ :=
  (1 / 2) * ∑ b : Fin n → Bool, |sampleProb p b - sampleProb p' b|

end UniformDRO.LowerBound


