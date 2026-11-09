-- Prove2me | Definitions.Def_UnknownCovDP_General_Model
-- name    : UnknownCovDP_General_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:51.761236+00:00
-- url     : https://prove2.me/theorems/bd532a9c-aec6-415e-b420-e038f078a6c0
-- title:
--   Eq. (5), Definition 1.2 — the prior $\mathcal P_{\mathrm{sub}}(d,k)$, the Gaussian experiment and the Bayes risk
-- statement:
--   Fix a dimension $d$, a rank parameter $k$ and a sample size $n$. This module sets up the random experiment of the mission.
--
--   1. **The covariance prior.** Let $G$ be a $d\times k$ matrix with i.i.d. $N(0,1)$ entries and put $\Sigma(G)=G(G^\top G)^{-1}G^\top$. When $k\le d$ the matrix $G$ has full column rank almost surely, $\Sigma(G)$ is the orthogonal projector onto its column span, and that span is uniformly distributed (Haar) among $k$-dimensional subspaces of $\mathbb R^d$. So $\Sigma(G)$ has the law of $DD^\top$ for $D$ uniform on $d\times k$ matrices with orthonormal columns.
--   2. **The prior.** Under $\mathcal P_{\mathrm{sub}}(d,k)$, the mean is $\mu\sim N(0,d^2 I_d)$ and, independently, $\Sigma$ has the law above:
--   $$(\mu,\Sigma)\sim\mathcal P_{\mathrm{sub}}(d,k)\iff \mu\sim N(0,d^2I_d),\quad \Sigma=DD^\top,\ D\sim\mathcal H_{d,k}.$$
--   3. **The data.** A dataset is $X=(x_1,\dots,x_n)$ with law $N(\mu,\Sigma)^{\otimes n}$, where the Gaussian may be singular.
--   4. **Algorithms.** A randomized algorithm is a Markov kernel from datasets to $\mathbb R^d$, and the experiment probability of an event $A$ is the iterated integral of the output probability of $A$ over $(\mu,\Sigma)$ and then over $X$.
--   5. **Bayes risk.** For a prior $\mathcal P$ on pairs $(\mu,\Sigma)$,
--   $$\mathfrak R_{\varepsilon,\delta}(\mathcal P,n)=\inf\Bigl\{\alpha\ge0:\ \exists\,\mathcal A\in A_{\varepsilon,\delta},\ \Pr_{(\mu,\Sigma)\sim\mathcal P,\ X\sim N(\mu,\Sigma)^{\otimes n}}\bigl[\|\mathcal A(X)-\mu\|_2\le\alpha\bigr]\ge\tfrac34\Bigr\},$$
--   where $A_{\varepsilon,\delta}$ is the class of $(\varepsilon,\delta)$-differentially private algorithms.
--
--   These are the objects every statement of the mission is written in.
--
--   **Formalization Note** The law $\mathcal H_{d,k}$ is realized through the Gaussian matrix, because the library has no uniform law on orthonormal frames; the file proves that the defining map is measurable, so the pushforward is a genuine probability measure. Mathlib's matrix inverse returns $0$ on the null event where $G^\top G$ is singular. For $k>d$, where $\mathcal H_{d,k}$ is empty, the law is the point mass at $0$. The Bayes risk takes values in $[0,\infty]$, so the infimum of the empty set is $+\infty$. Differential privacy is the published `PrivRobustStat.IsApproxDP`, whose neighbours differ in exactly one entry; identical datasets satisfy the inequality trivially when $\varepsilon\ge0,\delta\ge0$.
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Definition 1.2, printed p. 2 (PDF p. 3); eq. (5), printed p. 10 (PDF p. 11); Definition 1.1, printed p. 2 (PDF p. 3)

import Mathlib
import Definitions.Def_PrivRobustStat_Privacy

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General

/-!
# The random-subspace Gaussian experiment and the Bayes risk

Gaucher, Linder, Smith, Ullman, Zakynthinou, *Dimension-Free Private Mean Estimation is Impossible
Without the Covariance*, STOC 2027 submission #573 (October 2026), Definition 1.2 (printed p. 2,
PDF p. 3) and eq. (5) (printed p. 10, PDF p. 11).

**Formalization Note.**
* The uniform law on `d × k` matrices with orthonormal columns is not available in the library, so
  `covPrior d k` is the law of `G (GᵀG)⁻¹ Gᵀ` for a `d × k` matrix `G` with i.i.d. `N(0,1)` entries:
  the orthogonal projector onto the column span of `G`. For `k ≤ d` the matrix `G` has full column
  rank almost surely and the law of its column span is rotation invariant, so this is the law of
  `DDᵀ` with `D ∼ H_{d,k}`, the projector onto a Haar-uniform `k`-dimensional subspace (the paper's
  own remark after (5)). On the null event where `GᵀG` is singular, Lean's `⁻¹` returns `0`. For
  `k > d` the source's `H_{d,k}` is empty and this law is the Dirac mass at `0`.
* A randomized algorithm is a Markov kernel from datasets to outputs. All privacy is the published
  `PrivRobustStat.IsApproxDP`.
* `S` denotes the covariance matrix `Σ` (`Σ` is a reserved token in Lean).
-/

/-- The ambient space `ℝ^d` with the Euclidean norm. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Real `d × d` matrices. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The entrywise (product) σ-algebra on `d × d` matrices. -/
instance matMeasurableSpace (d : ℕ) : MeasurableSpace (Mat d) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

/-- The law of a `d × k` matrix with i.i.d. standard Gaussian entries. -/
noncomputable def gaussianMatrixLaw (d k : ℕ) : Measure (Fin d → Fin k → ℝ) :=
  Measure.pi fun _ : Fin d => Measure.pi fun _ : Fin k => gaussianReal 0 1

instance gaussianMatrixLaw_prob (d k : ℕ) : IsProbabilityMeasure (gaussianMatrixLaw d k) := by
  unfold gaussianMatrixLaw; infer_instance

/-- `G (GᵀG)⁻¹ Gᵀ`: the orthogonal projector onto the column span of `G` when `G` has full column
rank (and the zero matrix when `GᵀG` is singular). -/
noncomputable def spanProjOfMatrix {d k : ℕ} (G : Fin d → Fin k → ℝ) : Mat d :=
  let M : Matrix (Fin d) (Fin k) ℝ := Matrix.of G
  M * (M.transpose * M)⁻¹ * M.transpose

/-- The defining map of `covPrior` is measurable, so its pushforward is not the junk zero measure. -/
lemma measurable_spanProjOfMatrix (d k : ℕ) :
    Measurable (spanProjOfMatrix : (Fin d → Fin k → ℝ) → Mat d) := by
  have hcont : Continuous fun G : Fin d → Fin k → ℝ =>
      (Matrix.of G : Matrix (Fin d) (Fin k) ℝ) := continuous_id
  have hA : Continuous fun G : Fin d → Fin k → ℝ =>
      ((Matrix.of G : Matrix (Fin d) (Fin k) ℝ).transpose * Matrix.of G) :=
    hcont.matrix_transpose.matrix_mul hcont
  have hdet : Measurable fun G : Fin d → Fin k → ℝ =>
      Ring.inverse ((Matrix.of G : Matrix (Fin d) (Fin k) ℝ).transpose * Matrix.of G).det := by
    have : Measurable fun G : Fin d → Fin k → ℝ =>
        ((Matrix.of G : Matrix (Fin d) (Fin k) ℝ).transpose * Matrix.of G).det⁻¹ :=
      (hA.matrix_det.measurable).inv
    simpa only [Ring.inverse_eq_inv'] using this
  have hadj : Continuous fun G : Fin d → Fin k → ℝ =>
      ((Matrix.of G : Matrix (Fin d) (Fin k) ℝ).transpose * Matrix.of G).adjugate :=
    hA.matrix_adjugate
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have hexpr : (fun G : Fin d → Fin k → ℝ => spanProjOfMatrix G i j) = fun G =>
      Ring.inverse ((Matrix.of G : Matrix (Fin d) (Fin k) ℝ).transpose * Matrix.of G).det *
        ((Matrix.of G : Matrix (Fin d) (Fin k) ℝ) *
          ((Matrix.of G : Matrix (Fin d) (Fin k) ℝ).transpose * Matrix.of G).adjugate *
          (Matrix.of G : Matrix (Fin d) (Fin k) ℝ).transpose) i j := by
    funext G
    simp only [spanProjOfMatrix, Matrix.inv_def, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_apply, smul_eq_mul]
  rw [hexpr]
  refine hdet.mul ?_
  have : Continuous fun G : Fin d → Fin k → ℝ =>
      ((Matrix.of G : Matrix (Fin d) (Fin k) ℝ) *
        ((Matrix.of G : Matrix (Fin d) (Fin k) ℝ).transpose * Matrix.of G).adjugate *
        (Matrix.of G : Matrix (Fin d) (Fin k) ℝ).transpose) :=
    (hcont.matrix_mul hadj).matrix_mul hcont.matrix_transpose
  exact (this.matrix_elem i j).measurable

/-- The `Σ`-marginal of `P_sub(d,k)` (eq. (5)): the law of the orthogonal projector onto a
uniformly random `k`-dimensional subspace of `ℝ^d`, realized as the column span of a Gaussian
matrix. See the module note for `k > d` and for the singular null event. -/
noncomputable def covPrior (d k : ℕ) : Measure (Mat d) :=
  (gaussianMatrixLaw d k).map spanProjOfMatrix

instance covPrior_prob (d k : ℕ) : IsProbabilityMeasure (covPrior d k) :=
  Measure.isProbabilityMeasure_map (measurable_spanProjOfMatrix d k).aemeasurable

/-- The prior `P_sub(d,k)` of eq. (5): `μ ∼ N(0, d² I_d)` and, independently, `Σ ∼ covPrior d k`. -/
noncomputable def Psub (d k : ℕ) : Measure (Vec d × Mat d) :=
  (multivariateGaussian (0 : Vec d) (((d : ℝ) ^ 2) • (1 : Mat d))).prod (covPrior d k)

/-- The law `N(μ, S)^{⊗n}` of a dataset of `n` i.i.d. Gaussian samples. Mathlib's
`multivariateGaussian` allows a singular positive semidefinite `S`. -/
noncomputable def dataLaw {d : ℕ} (n : ℕ) (μ : Vec d) (S : Mat d) : Measure (Fin n → Vec d) :=
  Measure.pi fun _ : Fin n => multivariateGaussian μ S

/-- A randomized algorithm from `n`-point datasets in `ℝ^d` to `ℝ^d`; its coins are the kernel's
randomness. -/
abbrev Algorithm (d n : ℕ) := Kernel (Fin n → Vec d) (Vec d)

/-- `Pr_{(μ,Σ)∼P, X∼N(μ,Σ)^{⊗n}, coins of 𝒜}[𝒜(X) ∈ A(μ,Σ,X)]`. -/
noncomputable def experimentProb {d : ℕ} (P : Measure (Vec d × Mat d)) (n : ℕ)
    (κ : Algorithm d n) (A : Vec d → Mat d → (Fin n → Vec d) → Set (Vec d)) : ℝ≥0∞ :=
  ∫⁻ p, ∫⁻ X, κ X (A p.1 p.2 X) ∂(dataLaw n p.1 p.2) ∂P

/-- Definition 1.2: the unknown-covariance Bayes risk
`ℜ_{ε,δ}(P, n) = inf {α ≥ 0 : ∃ 𝒜 ∈ A_{ε,δ}, Pr[‖𝒜(X) − μ‖₂ ≤ α] ≥ 3/4}`, valued in `[0, ∞]`, so the
infimum of the empty set is `+∞`, never the junk real value `0`. -/
noncomputable def bayesRisk {d : ℕ} (P : Measure (Vec d × Mat d)) (n : ℕ) (ε δ : ℝ) : ℝ≥0∞ :=
  sInf {a : ℝ≥0∞ | ∃ α : ℝ≥0, a = α ∧ ∃ κ : Algorithm d n, IsMarkovKernel κ ∧
    PrivRobustStat.IsApproxDP (fun X => κ X) ε δ ∧
    3 / 4 ≤ experimentProb P n κ (fun μ _ _ => {y | ‖y - μ‖ ≤ (α : ℝ)})}

end UnknownCovDP.General


