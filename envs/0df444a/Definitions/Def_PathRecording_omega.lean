-- Prove2me | Definitions.Def_PathRecording_omega
-- name    : PathRecording_omega
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:05:31.908976+00:00
-- url     : https://prove2.me/theorems/12de10c8-f208-44c2-967d-e9cff6ccf1b3
-- title:
--   Double Schur transform, block projectors $\Pi^{\otimes2}_{\lambda,t}$ and the commutant EPR projector $\Omega_{\mathcal A_t}$
-- statement:
--   Fix Schur–Weyl data for $\rho^{\otimes t}$. The **double Schur transform** $\mathrm{Schur}_t\otimes\overline{\mathrm{Schur}_t}$ maps $\mathrm{Path}_t=V^{\otimes t}\otimes\overline V^{\otimes t}$ to the space with basis $|\lambda,X,T\rangle\otimes|\lambda',Y,R\rangle$; its inverse is $\mathrm{Schur}_t^\dagger\otimes\mathrm{Schur}_t^\top$.
--
--   1. $\widehat\Pi_{\lambda,t}$ is the projector onto the Schur block $V^\lambda_G\otimes V^\lambda_{\mathcal A_t}$, and
--   $$\Pi^{\otimes2}_{\lambda,t}=(\mathrm{Schur}_t^\dagger\otimes\mathrm{Schur}_t^\top)\,(\widehat\Pi_{\lambda,t}\otimes\overline{\widehat\Pi_{\lambda,t}})\,(\mathrm{Schur}_t\otimes\overline{\mathrm{Schur}_t})$$
--   is the path-basis projector onto the $(\lambda,\lambda)$ block.
--   2. The **commutant EPR projector** in the double Schur basis acts by
--   $$\widehat\Pi^{\mathcal A_t}_{\mathrm{EPR},t}\big(|\lambda,X,T\rangle\otimes|\lambda',Y,R\rangle\big)=\begin{cases}\dfrac{\delta_{T,R}}{\dim V^\lambda_{\mathcal A_t}}\displaystyle\sum_{S}|\lambda,X,S\rangle\otimes|\lambda,Y,S\rangle,&\lambda=\lambda',\\0,&\lambda\ne\lambda',\end{cases}$$
--   i.e. it projects the two multiplicity registers onto the normalized EPR state and acts as the identity on the two $G$-registers.
--   3. On the path space,
--   $$\Omega_{\mathcal A_t}=(\mathrm{Schur}_t^\dagger\otimes\mathrm{Schur}_t^\top)\,\widehat\Pi^{\mathcal A_t}_{\mathrm{EPR},t}\,(\mathrm{Schur}_t\otimes\overline{\mathrm{Schur}_t}).\qquad(5.5)$$
--
--   $\Omega_{\mathcal A_t}$ is the "symmetrize" step of the path-recording update: its image is the legal path subspace.
--
--   **Formalization Note** The conjugate factor $\overline V^{\otimes t}$ uses the same coordinates as $V^{\otimes t}$, and a map on it is the entrywise-conjugate matrix, so the double Schur transform is the Kronecker product of the Schur matrix with its entrywise conjugate. Basis indices of the same label are compared through their numerical values.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, §5.1, pp.60–61, Eqs. (5.4)–(5.5)

import Mathlib
import Definitions.Def_PathRecording_SchurWeylData

set_option autoImplicit false

namespace PathRecording

/-!
# The double Schur transform, block projectors and the commutant EPR projector `Ω_{𝒜_t}`

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, §5.1, pp.60–61.

* Double Schur transform (p.60): `Schur_t ⊗ \overline{Schur_t} : V^{⊗t} ⊗ \overline{V}^{⊗t} →
  ⨁_{λ,λ'} (V^λ_G ⊗ V^λ_{𝒜_t}) ⊗ \overline{(V^{λ'}_G ⊗ V^{λ'}_{𝒜_t})}`, with basis
  `|λ, X, T⟩ ⊗ |λ', Y, R⟩`.
* `Π̂_{λ,t}` is the projector onto the Schur block `λ`, and `Π̂^{⊗2}_{λ,t} = Π̂_{λ,t} ⊗ \overline{Π̂_{λ,t}}`
  projects onto the `(λ, λ)` block; its path-basis version is
  `Π^{⊗2}_{λ,t} := (Schur_t† ⊗ Schur_tᵀ) Π̂^{⊗2}_{λ,t} (Schur_t ⊗ \overline{Schur_t})` (p.61).
* `Π̂^{𝒜_t}_{EPR,t}(|λ,X,T⟩ ⊗ |λ',Y,R⟩) = δ_{T,R}/dim(V^λ_{𝒜_t}) Σ_S |λ,X,S⟩ ⊗ |λ,Y,S⟩` if `λ = λ'`,
  and `0` if `λ ≠ λ'` (p.61).
* `Ω_{𝒜_t} := (Schur_t† ⊗ Schur_tᵀ) Π̂^{𝒜_t}_{EPR,t} (Schur_t ⊗ \overline{Schur_t})` (Eq. (5.5), p.61).

**Formalization Note.**
* `Path_t` is `ℂ^{PathIdx N t}` with basis `|x⃗, y⃗⟩`; the second factor `\overline{V}^{⊗t}` uses the
  same coordinates, and a linear map on it is represented by the entrywise conjugate matrix, so the
  double Schur transform is the Kronecker product `schur ⊗ₖ conj(schur)`. Its conjugate transpose is
  `Schur_t† ⊗ Schur_tᵀ`.
* All operators are matrices over `ℂ`; `Π̂_{λ,t}` and the EPR projector are written entrywise in the
  (double) Schur basis. Indices of `V^λ_G`, `V^λ_{𝒜_t}` of the same label are compared through their
  values in `ℕ`.
-/

open Matrix Kronecker

variable {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ} {ρ : UnitaryRep G N} {t : ℕ}

namespace SchurWeylData

variable (S : SchurWeylData ρ t)

/-- The double Schur transform `Schur_t ⊗ \overline{Schur_t}` from the path basis `|x⃗, y⃗⟩` to the
double Schur basis `|λ,X,T⟩ ⊗ |λ',Y,R⟩` (arXiv:2606.30281v2, p.60). -/
noncomputable def doubleSchur : Matrix (S.SchurIdx × S.SchurIdx) (PathIdx N t) ℂ :=
  S.schur ⊗ₖ S.schur.map star

/-- The Schur-basis projector `Π̂_{λ,t}` onto the block `V^λ_G ⊗ V^λ_{𝒜_t}` (p.61). -/
noncomputable def blockProjHat (l : S.ι) : Matrix S.SchurIdx S.SchurIdx ℂ :=
  Matrix.diagonal fun a => if a.1 = l then 1 else 0

/-- The path-basis projector `Π^{⊗2}_{λ,t} = (Schur_t† ⊗ Schur_tᵀ) (Π̂_{λ,t} ⊗ \overline{Π̂_{λ,t}})
(Schur_t ⊗ \overline{Schur_t})` onto the `(λ, λ)` block (p.61). -/
noncomputable def blockProj2 (l : S.ι) : Matrix (PathIdx N t) (PathIdx N t) ℂ :=
  S.doubleSchurᴴ * (S.blockProjHat l ⊗ₖ S.blockProjHat l) * S.doubleSchur

/-- The commutant EPR projector in the double Schur basis, `Π̂^{𝒜_t}_{EPR,t}`: the entry from
`|λ,X,T⟩ ⊗ |λ',Y,R⟩` to `|μ,X',S⟩ ⊗ |μ',Y',S'⟩` is `1/dim(V^λ_{𝒜_t})` when `λ = λ' = μ = μ'`,
`X' = X`, `Y' = Y`, `T = R` and `S = S'`, and `0` otherwise (p.61). -/
noncomputable def eprProjHat : Matrix (S.SchurIdx × S.SchurIdx) (S.SchurIdx × S.SchurIdx) ℂ :=
  Matrix.of fun a b =>
    if a.1.1 = a.2.1 ∧ b.1.1 = b.2.1 ∧ a.1.1 = b.1.1 ∧
        (a.1.2.1 : ℕ) = b.1.2.1 ∧ (a.2.2.1 : ℕ) = b.2.2.1 ∧
        (a.1.2.2 : ℕ) = a.2.2.2 ∧ (b.1.2.2 : ℕ) = b.2.2.2 then
      ((S.dA a.1.1 : ℂ))⁻¹
    else 0

/-- The commutant EPR projector on the path space,
`Ω_{𝒜_t} = (Schur_t† ⊗ Schur_tᵀ) Π̂^{𝒜_t}_{EPR,t} (Schur_t ⊗ \overline{Schur_t})`
(arXiv:2606.30281v2, Eq. (5.5), p.61). -/
noncomputable def omega : Matrix (PathIdx N t) (PathIdx N t) ℂ :=
  S.doubleSchurᴴ * S.eprProjHat * S.doubleSchur

end SchurWeylData

end PathRecording


