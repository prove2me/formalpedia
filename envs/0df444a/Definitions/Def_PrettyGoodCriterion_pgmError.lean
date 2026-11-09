-- Prove2me | Definitions.Def_PrettyGoodCriterion_pgmError
-- name    : PrettyGoodCriterion_pgmError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:10.560204+00:00
-- url     : https://prove2.me/theorems/77ebe3b0-ade1-41be-876a-3af4f0f6265e
-- title:
--   Pretty good measurement and PGM error; the PGM bit error rate $p_e(\sigma_0,\sigma_1)$
-- statement:
--   Let $\mathcal E=\{(\pi_x,\sigma_x):x\in\mathcal X\}$ be a finite ensemble with average state $\bar\sigma$.
--
--   1. The **inverse square root over the support** $\bar\sigma^{-1/2}$ inverts $\sqrt{\bar\sigma}$ on the range $\operatorname{supp}(\bar\sigma)$ and is $0$ on the kernel of $\bar\sigma$.
--   2. The **pretty good measurement** (PGM) of $\mathcal E$ has the observables
--   $$M_{\hat x}:=\pi_{\hat x}\,\bar\sigma^{-1/2}\sigma_{\hat x}\bar\sigma^{-1/2},\qquad\hat x\in\mathcal X;$$
--   they sum to the projector onto $\operatorname{supp}(\bar\sigma)$, so the PGM is a measurement on that support.
--   3. The **PGM error** of $\mathcal E$ is the probability that the PGM outcome $\hat x$ differs from the label $x\sim\pi$ when applied to $\sigma_x$:
--   $$p_e(\mathcal E):=\Pr[\hat x\neq x]=\sum_{\hat x,x\in\mathcal X:\ \hat x\neq x}\pi_x\operatorname{Tr}(\sigma_xM_{\hat x}).$$
--   4. For the binary ensemble $\mathcal E_\alpha=\{(1-\alpha,\sigma_0),(\alpha,\sigma_1)\}$, $p_{e,\alpha}(\sigma_0,\sigma_1):=p_e(\mathcal E_\alpha)$, and the **PGM bit error rate** is $p_e(\sigma_0,\sigma_1):=p_{e,1/2}(\sigma_0,\sigma_1)$.
--
--   For commuting states the PGM is posterior sampling: given the classical observation it returns $\hat x$ with the posterior probability of $\hat x$. The bit error rate $p_e(\sigma_0,\sigma_1)$ is the second key quantity of the main theorem.
--
--   **Formalization Note** The ensemble is a prior `p : X → ℝ` and states `σ : X → Matrix ι ι ℂ` on a finite type; $\bar\sigma$ is the published `HolevoCQ.avgState σ p`. $\bar\sigma^{-1/2}$ is `cfc (fun t => (Real.sqrt t)⁻¹)`: Lean's $\sqrt0=0$ and $0^{-1}=0$ send the eigenvalue $0$ to $0$, which is the support convention (Mathlib's `Matrix.inv` would instead give $0$ for every singular matrix). Real parts of the traces are taken; they are real. The binary prior is `![1 - α, α]`.
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Definition 2.7 and footnote 18, p.17 (PDF 19); Definition 2.8, p.18 (PDF 20)

import Mathlib
import Definitions.Def_HolevoCQ_avgState

namespace PrettyGoodCriterion

/-- The inverse square root `A^{−1/2}` **over `supp(A)`**: on the range of the Hermitian matrix
`A` it is the inverse of `√A`, on its kernel it is `0`, Alrabiah–Guruswami, arXiv:2608.09347
(held version), Definition 2.7, p.17 (PDF 19) ("inverses are over supp(σ̄)").

**Formalization Note.** `cfc (fun t => (√t)⁻¹) A`: Lean's `(0 : ℝ)⁻¹ = 0` and `√0 = 0` send the
eigenvalue `0` to `0`, which is the paper's support convention. Every function is continuous on
the finite spectrum of a matrix, so the functional calculus applies. -/
noncomputable def invSqrt {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  cfc (fun t : ℝ => (Real.sqrt t)⁻¹) A

/-- The **pretty good measurement** of a finite ensemble `ℰ = {(π_x, σ_x) : x ∈ 𝒳}`: the
observables `M_x̂ := π_x̂ σ̄^{−1/2} σ_x̂ σ̄^{−1/2}`, inverses over `supp(σ̄)`,
arXiv:2608.09347 (held version), Definition 2.7, p.17 (PDF 19). They sum to the support
projector `Π_σ̄` (footnote 18), so the PGM is a POVM over `supp(σ̄)`.

**Formalization Note.** The ensemble is a prior `p : 𝒳 → ℝ` and states `σ : 𝒳 → Matrix ι ι ℂ`;
`σ̄ = ∑ π_x σ_x` is the published `HolevoCQ.avgState σ p`. -/
noncomputable def pgm {X ι : Type} [Fintype X] [Fintype ι] [DecidableEq ι] (p : X → ℝ)
    (σ : X → Matrix ι ι ℂ) (xh : X) : Matrix ι ι ℂ :=
  (p xh : ℂ) • (invSqrt (HolevoCQ.avgState σ p) * σ xh * invSqrt (HolevoCQ.avgState σ p))

/-- The **PGM error** `p_e(ℰ) := Pr[x̂ ≠ x] = ∑_{x̂, x ∈ 𝒳 : x̂ ≠ x} π_x Tr(σ_x M_x̂)`,
arXiv:2608.09347 (held version), Definition 2.8, p.18 (PDF 20).

**Formalization Note.** Traces of products of positive semidefinite matrices are real; the real
part of `Tr(σ_x M_x̂)` is taken. -/
noncomputable def pgmError {X ι : Type} [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (p : X → ℝ) (σ : X → Matrix ι ι ℂ) : ℝ :=
  ∑ x, ∑ xh ∈ Finset.univ.erase x, p x * (σ x * pgm p σ xh).trace.re

/-- The binary prior `(1 − α, α)` of the ensemble `ℰ_α = {(1 − α, σ₀), (α, σ₁)}`,
arXiv:2608.09347 (held version), Definition 2.8, p.18 (PDF 20). -/
def binPrior (α : ℝ) : Fin 2 → ℝ :=
  ![1 - α, α]

/-- `p_{e,α}(σ₀, σ₁) := p_e(ℰ_α)` for `ℰ_α = {(1 − α, σ₀), (α, σ₁)}`, arXiv:2608.09347 (held
version), Definition 2.8, p.18 (PDF 20). -/
noncomputable def pgmBitError {ι : Type} [Fintype ι] [DecidableEq ι] (α : ℝ)
    (σ : Fin 2 → Matrix ι ι ℂ) : ℝ :=
  pgmError (binPrior α) σ

/-- The **PGM bit error rate** `p_e(σ₀, σ₁) := p_{e,1/2}(σ₀, σ₁)` of the output pair
`(σ₀, σ₁)`, arXiv:2608.09347 (held version), Definition 2.8, p.18 (PDF 20). -/
noncomputable def pgmBitErrorUniform {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Fin 2 → Matrix ι ι ℂ) : ℝ :=
  pgmBitError (1 / 2) σ

end PrettyGoodCriterion


