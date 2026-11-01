-- Prove2me | Definitions.Def_GaussianGLOCC_Unilateral
-- name    : GaussianGLOCC_Unilateral
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:43.098494+00:00
-- url     : https://prove2.me/theorems/0e0fc7de-aa71-4f17-89eb-b06d43423886
-- title:
--   Unilateral Gaussian operation: the contraction and its covariance map (19)
-- statement:
--   A general Gaussian operation in system $A$ is described, via the isomorphism between completely positive maps and states, by a Gaussian state $\chi$ on (output modes) $\otimes$ (input modes of $A$) with CM
--
--   $$
--   \Gamma_A=\begin{pmatrix}\Gamma_{1A}&\Gamma_{12A}\\\Gamma_{12A}^T&\Gamma_{2A}\end{pmatrix}.
--   $$
--
--   Applied to a bipartite state $\rho$ it gives the unnormalized state $X=\operatorname{Tr}_{A_{\rm in}}[(\chi\otimes\mathbb 1_B)(\rho^{T_A}\otimes\mathbb 1)]$, i.e. $X_{(o,\beta),(o',\beta')}=\sum_{i,j}\chi_{(o,i),(o',j)}\rho_{(i,\beta),(j,\beta')}$. On covariance matrices $\gamma=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ the corresponding map is
--
--   $$
--   A'=\Gamma_{1A}-\tilde\Gamma_{12A}(\tilde\Gamma_{2A}+A)^{-1}\tilde\Gamma_{12A}^T,\quad B'=B-C^T(\tilde\Gamma_{2A}+A)^{-1}C,\quad C'=\tilde\Gamma_{12A}(\tilde\Gamma_{2A}+A)^{-1}C,
--   $$
--
--   with $\tilde\Gamma=(\mathbb 1\oplus\Lambda)\Gamma(\mathbb 1\oplus\Lambda)$, $\Lambda=\operatorname{diag}(1,-1,\dots,1,-1)$, so $\tilde\Gamma_{12A}=\Gamma_{12A}\Lambda$ and $\tilde\Gamma_{2A}=\Lambda\Gamma_{2A}\Lambda$.
--
--   **Formalization Note** The contraction transposes $\rho$ on the contracted factor, as the published `Claimed50.P37.contraction`; the output factor comes first, as in eq. (18). `unilateralCM` is the matrix expression only; Lemma 4 identifies it with the CM of the normalized output state. For Gaussian CMs $\tilde\Gamma_{2A}+A$ is positive definite, so the matrix inverse is the genuine one.
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, pp.3–4, eqs. (6)–(8); Lemma 4, eqs. (17)–(19c), p.6

import Mathlib
import Definitions.Def_GaussianGLOCC_PhaseSpace
import Definitions.Def_GaussianGLOCC_LocalSteps
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel)
open QAlgorithms.Papers.Independent.Claimed50.P37 (reflection)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, pp.3–4 and Lemma 4, p.6: the
unnormalized output of the general Gaussian local operation in system A whose
Choi–Jamiołkowski state is `χ` (output modes first, then input modes), applied to the
bipartite state `ρ`:
`X = Tr_{A_in}[(χ ⊗ 𝟙_B)(ρ^{T_A} ⊗ 𝟙_{A_out})]`, i.e.
`X_{(o,β),(o′,β′)} = Σ_{i,j} χ_{(o,i),(o′,j)} ρ_{(i,β),(j,β′)}`.

**Formalization Note.** p.3–4: "it is most convenient to employ the isomorphism between
completely positive maps and states [19], as explicitly analyzed and completely characterized
in Ref. [13]". This is the one-party, bipartite version of the published
`Claimed50.P37.contraction` (which transposes `ρ` on the contracted factor), with the output
factor first as in eq. (18). The CM of `ρ^{T}` is `ΛγΛ`, which is where the tilde of eq. (8)
comes from. Normalize with the published `successTrace`/`normalizeFockCoefficients`. -/
noncomputable def localContractionA {m nA nB : ℕ} (χ : DensityKernel (m + nA))
    (ρ : DensityKernel (nA + nB)) : DensityKernel (m + nB) :=
  fun a b => ∑' i : FockIndex nA, ∑' j : FockIndex nA,
    χ (joinAB (splitA a) i) (joinAB (splitA b) j) * ρ (joinAB i (splitB a)) (joinAB j (splitB b))

/-- arXiv:quant-ph/0301038v1, eqs. (18)–(19c) and (8), pp.4, 6: the covariance matrix
`γ′ = [[A′, C′], [C′ᵀ, B′]]` after the Gaussian local operation in A with CM
`Γ_A = [[Γ₁A, Γ₁₂A], [Γ₁₂Aᵀ, Γ₂A]]` (output block first) applied to `γ = [[A, C], [Cᵀ, B]]`:

* `A′ = Γ₁A − Γ̃₁₂A (Γ̃₂A + A)⁻¹ Γ̃₁₂Aᵀ` (19a),
* `B′ = B − Cᵀ (Γ̃₂A + A)⁻¹ C` (19b),
* `C′ = Γ̃₁₂A (Γ̃₂A + A)⁻¹ C` (19c),

with `Γ̃ = (𝟙 ⊕ Λ) Γ (𝟙 ⊕ Λ)` (8), `Λ = diag(1, −1, …, 1, −1)`, `𝟙` on the output block, i.e.
`Γ̃₁₂A = Γ₁₂A Λ` and `Γ̃₂A = Λ Γ₂A Λ`.

**Formalization Note.** `Λ` is the published `Claimed50.P37.reflection`. `⁻¹` is Mathlib's
matrix inverse; for Gaussian CMs `Γ̃₂A + A` is positive definite, hence invertible. This is a
matrix expression only; Lemma 4 (`unilateral_transformation`) identifies it with the CM of the
actual output state. -/
noncomputable def unilateralCM {m nA nB : ℕ} (ΓA : Cov (m + nA)) (γ : Cov (nA + nB)) :
    Cov (m + nB) :=
  let Γ12t := blockC ΓA * reflection nA
  let Γ2t := reflection nA * blockB ΓA * reflection nA
  blockCov (blockA ΓA - Γ12t * (Γ2t + blockA γ)⁻¹ * Γ12t.transpose)
    (Γ12t * (Γ2t + blockA γ)⁻¹ * blockC γ)
    (blockB γ - (blockC γ).transpose * (Γ2t + blockA γ)⁻¹ * blockC γ)

end GaussianGLOCC


