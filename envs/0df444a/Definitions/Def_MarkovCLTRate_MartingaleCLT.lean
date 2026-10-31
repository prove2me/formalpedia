-- Prove2me | Definitions.Def_MarkovCLTRate_MartingaleCLT
-- name    : MarkovCLTRate_MartingaleCLT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:06.133495+00:00
-- url     : https://prove2.me/theorems/f7d442db-c8f6-4b54-beec-df0307c08b42
-- title:
--   Martingale setting of Theorem 1: Assumption 1, $\Sigma_k$, $V_k$, $D_k$, $\Lambda_k$, $H_k$, the Taylor remainders and $\Delta_n$
-- statement:
--   Let $\{m_k\}_{k\ge1}$ be a $d$-dimensional martingale difference sequence with respect to a filtration $\{\mathcal F_k\}_{k\ge0}$: $m_k$ is $\mathcal F_k$-adapted, $E\|m_k\|<\infty$ and $E(m_k\mid\mathcal F_{k-1})=0$. **Assumption 1** (for a fixed $\beta\in(0,1)$) requires $E\|m_k\|^{2+\beta}<\infty$ and that $\Sigma_k=E(m_km_k^T\mid\mathcal F_{k-1})$ exists, for every $k\ge1$.
--
--   With $S_k=\sum_{j=1}^k m_j$ and a horizon $n$, define
--   $$
--   V_k=\sum_{j=k}^nE(\Sigma_j),\qquad D_k=V_k^{-1/2}E(\Sigma_k)V_k^{-1/2},\qquad \Lambda_k=V_k^{-1/2}V_{k+1}V_k^{-1/2},
--   $$
--   with $V_{n+1}=0$, and the matrices $A_{k,h}(\mathcal F_{k-1})$ (the Stein-solution average at the shift $S_{k-1}$) and $H_k=V_k^{-1/2}A_{k,h}(\mathcal F_{k-1})V_k^{-1/2}$. The two Taylor remainders of Theorem 1 are
--   $$
--   \frac1{\sqrt n}\sum_{k=1}^n\Big[\tilde C_1(d,\beta)\|V_k^{1/2}\|_{op}E\big(\|V_k^{-1/2}m_k\|^{2+\beta}\big)+\tilde C_1(d,\beta)\operatorname{Tr}(D_k)\|V_k^{1/2}\|_{op}E\big(\|V_k^{-1/2}m_k\|^{\beta}\big)\Big],
--   $$
--   and the covariance-interaction term is
--   $$
--   \Delta_n=\sup_{h\in Lip_1}\frac1{\sqrt n}\Big|\sum_{k=1}^nE\Big[\operatorname{Tr}\Big(A_{k,h}(\mathcal F_{k-1})V_k^{-1/2}\big(E(\Sigma_k)-\Sigma_k\big)V_k^{-1/2}\Big)\Big]\Big|.
--   $$
--
--   **Formalization Note** Conditional expectations and expectations of matrices are taken entrywise. The existence of $\Sigma_k$ in Assumption 1 follows from the $(2+\beta)$th moment and is not a separate field. $\Delta_n$ takes values in $[0,\infty]$.
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, §2.1, Assumption 1 and (1), p.4; Theorem 1, p.6; proof of Theorem 1, p.7; H_k, p.20

import Mathlib
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_Stein

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

variable {d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The martingale setting and Assumption 1 of arXiv:2401.15719v5, §2.1, p.4, for a fixed
`β ∈ (0, 1)`. The sequence `(m_k)_{k ≥ 1}` (the value `m 0` is never used) is a `d`-dimensional
martingale difference sequence with respect to the filtration `(𝓕_k)_{k ≥ 0}`:
`m_k` is `𝓕_k`-adapted, `E‖m_k‖ < ∞` and `E(m_k | 𝓕_{k−1}) = 0` for `k ≥ 1`; moreover
1. `E‖m_k‖^{2+β} < ∞` for every `k ≥ 1`;
2. `Σ_k = E(m_k m_kᵀ | 𝓕_{k−1})` exists for every `k ≥ 1`.

**Formalization Note.** Item 2 follows from item 1 (the entries of `m_k m_kᵀ` are integrable), so
it is not repeated as a separate field. -/
structure Assumption1 (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (m : ℕ → Ω → Vec d) (β : ℝ) :
    Prop where
  adapted : ∀ k, 1 ≤ k → StronglyMeasurable[ℱ k] (m k)
  integrable : ∀ k, 1 ≤ k → Integrable (m k) μ
  mds : ∀ k, 1 ≤ k → μ[m k | ℱ (k - 1)] =ᵐ[μ] 0
  moment : ∀ k, 1 ≤ k → Integrable (fun ω => ‖m k ω‖ ^ (2 + β)) μ

/-- `S_k = Σ_{j=1}^k m_j`, arXiv:2401.15719v5, p.4 (`S_0 = 0`). -/
def partialSum (m : ℕ → Ω → Vec d) (k : ℕ) (ω : Ω) : Vec d :=
  ∑ j ∈ Finset.Icc 1 k, m j ω

/-- The conditional covariance `Σ_k = E(m_k m_kᵀ | 𝓕_{k−1})`, arXiv:2401.15719v5, Assumption 1,
p.4, entrywise. -/
noncomputable def condCov (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (m : ℕ → Ω → Vec d) (k : ℕ)
    (ω : Ω) : Mat d :=
  Matrix.of fun i j => (μ[fun ω' => m k ω' i * m k ω' j | ℱ (k - 1)]) ω

/-- `E(Σ_k)`, the expectation of the conditional covariance, entrywise. -/
noncomputable def expCov (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (m : ℕ → Ω → Vec d) (k : ℕ) :
    Mat d :=
  Matrix.of fun i j => ∫ ω, condCov μ ℱ m k ω i j ∂μ

/-- `V_k = Σ_{j=k}^n E(Σ_j)`, arXiv:2401.15719v5, Theorem 1, p.6. The empty sum gives the
convention `V_{n+1} = 0`. -/
noncomputable def covSum (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (m : ℕ → Ω → Vec d) (n k : ℕ) :
    Mat d :=
  ∑ j ∈ Finset.Icc k n, expCov μ ℱ m j

/-- `D_k = V_k^{−1/2} E(Σ_k) V_k^{−1/2}`, arXiv:2401.15719v5, Theorem 1, p.6. -/
noncomputable def Dmat (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (m : ℕ → Ω → Vec d) (n k : ℕ) :
    Mat d :=
  minvSqrt (covSum μ ℱ m n k) * expCov μ ℱ m k * minvSqrt (covSum μ ℱ m n k)

/-- `Λ_k = V_k^{−1/2} V_{k+1} V_k^{−1/2}`, the covariance of `Z̃_k`, arXiv:2401.15719v5, pp.6–7. -/
noncomputable def lambdaMat (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (m : ℕ → Ω → Vec d)
    (n k : ℕ) : Mat d :=
  minvSqrt (covSum μ ℱ m n k) * covSum μ ℱ m n (k + 1) * minvSqrt (covSum μ ℱ m n k)

/-- The random matrix `A_{k,h}(𝓕_{k−1})` of Theorem 1, arXiv:2401.15719v5, p.6: `steinA` with
`Q_k = V_k^{1/2}`, `Λ_k`, evaluated at the shift `a = S_{k−1}(ω)`. -/
noncomputable def Akh (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (m : ℕ → Ω → Vec d) (n k : ℕ)
    (h : Vec d → ℝ) (ω : Ω) : Mat d :=
  steinA h (msqrt (covSum μ ℱ m n k)) (lambdaMat μ ℱ m n k) (partialSum m (k - 1) ω)

/-- `H_k = V_k^{−1/2} A_{k,h}(𝓕_{k−1}) V_k^{−1/2}`, arXiv:2401.15719v5, p.20 (and Lemma 3, p.11). -/
noncomputable def Hmat (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (m : ℕ → Ω → Vec d) (n k : ℕ)
    (h : Vec d → ℝ) (ω : Ω) : Mat d :=
  minvSqrt (covSum μ ℱ m n k) * Akh μ ℱ m n k h ω * minvSqrt (covSum μ ℱ m n k)

/-- The two Taylor-remainder terms of Theorem 1, arXiv:2401.15719v5, p.6:
`(1/√n) Σ_{k=1}^n [ C̃₁(d,β) ‖V_k^{1/2}‖_op E‖V_k^{−1/2} m_k‖^{2+β}
  + C̃₁(d,β) Tr(D_k) ‖V_k^{1/2}‖_op E‖V_k^{−1/2} m_k‖^β ]`. -/
noncomputable def taylorBound (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (m : ℕ → Ω → Vec d)
    (n : ℕ) (β : ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.Icc 1 n,
    (C1t d β * opNorm (msqrt (covSum μ ℱ m n k))
        * ∫ ω, ‖mApply (minvSqrt (covSum μ ℱ m n k)) (m k ω)‖ ^ (2 + β) ∂μ
      + C1t d β * Matrix.trace (Dmat μ ℱ m n k) * opNorm (msqrt (covSum μ ℱ m n k))
        * ∫ ω, ‖mApply (minvSqrt (covSum μ ℱ m n k)) (m k ω)‖ ^ β ∂μ)

/-- The covariance-interaction term of Theorem 1, arXiv:2401.15719v5, p.6:
`∆_n = sup_{h ∈ Lip_1} (1/√n) | Σ_{k=1}^n E[ Tr( A_{k,h}(𝓕_{k−1}) V_k^{−1/2} (E(Σ_k) − Σ_k)
V_k^{−1/2} ) ] |`.

**Formalization Note.** Valued in `[0, ∞]`, as a supremum over the unbounded family `Lip_1`. -/
noncomputable def deltaN (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (m : ℕ → Ω → Vec d) (n : ℕ) :
    ℝ≥0∞ :=
  ⨆ (h : Vec d → ℝ) (_ : LipschitzWith 1 h),
    ENNReal.ofReal ((Real.sqrt n)⁻¹ * |∑ k ∈ Finset.Icc 1 n,
      ∫ ω, Matrix.trace (Akh μ ℱ m n k h ω * minvSqrt (covSum μ ℱ m n k)
        * (expCov μ ℱ m k - condCov μ ℱ m k ω) * minvSqrt (covSum μ ℱ m n k)) ∂μ|)

end MarkovCLTRate


