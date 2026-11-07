-- Prove2me | Definitions.Def_PathRecording_Gamma
-- name    : PathRecording_Gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:06:56.65922+00:00
-- url     : https://prove2.me/theorems/21a9f314-8e0e-444d-b72d-cc918609bc5c
-- title:
--   The EPR isometry $E_t$ and the partial isometry $\Gamma_t$
-- statement:
--   The **$\mathcal A_t$ EPR isometry** $E_t$ maps the tableau basis vector $|\lambda,X,Y\rangle$ of $\mathrm{Tab}_t$ to
--   $$E_t|\lambda,X,Y\rangle=\frac{1}{\sqrt{\dim V^\lambda_{\mathcal A_t}}}\sum_{R}|\lambda,X,R\rangle\otimes|\lambda,Y,R\rangle,$$
--   tensoring with a normalized EPR state on the two multiplicity registers. The map from tableau space to path space is
--   $$\Gamma_t=(\mathrm{Schur}_t^\dagger\otimes\mathrm{Schur}_t^\top)\,E_t:\ \mathrm{Tab}_t\to\mathrm{Path}_t .$$
--
--   $\Gamma_t$ composed with the Fourier transform is the isometry relating the uncompressed recording register $L^2(G)$ to the path-recording register.
--
--   **Formalization Note** The paper defines $\Gamma_t$ on $\bigoplus_{\lambda\in\widehat G}V^\lambda_G\otimes\overline{V^\lambda_G}$ with $E_t|\lambda,X,Y\rangle=0$ for $\lambda\notin\widehat G_t$; the Lean map is its restriction to $\mathrm{Tab}_t$, where it is supported.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, §5.3, pp.63–64

import Mathlib
import Definitions.Def_PathRecording_omega

set_option autoImplicit false

namespace PathRecording

/-!
# The EPR isometry `E_t` and the partial isometry `Γ_t`

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, §5.3, pp.63–64:

* `E_t |λ, X, Y⟩ := (1/√dim(V^λ_{𝒜_t})) Σ_{R ∈ B(V^λ_{𝒜_t})} |λ, X, R⟩ ⊗ |λ, Y, R⟩` for `λ ∈ Ĝ_t`
  (and `0` otherwise);
* `Γ_t := (Schur_t† ⊗ Schur_tᵀ) E_t : ⨁_λ V^λ_G ⊗ \overline{V^λ_G} → Path_t`.

**Formalization Note.** The domain is the reachable tableau space
`Tab_t = ⨁_{λ∈Ĝ_t} V^λ_G ⊗ \overline{V^λ_G}` with basis `|λ, X, Y⟩` (`TabIdx`). The paper's `Γ_t` is
defined on `⨁_{λ∈Ĝ}` and is zero on the blocks `λ ∉ Ĝ_t` (`E_t|λ,X,Y⟩ = 0` there), so restricting
the domain to `Tab_t` loses nothing.
-/

open Matrix

variable {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ} {ρ : UnitaryRep G N} {t : ℕ}

namespace SchurWeylData

variable (S : SchurWeylData ρ t)

/-- The `𝒜_t` EPR isometry `E_t : Tab_t → ⨁_λ (V^λ_G ⊗ V^λ_{𝒜_t}) ⊗ \overline{(V^λ_G ⊗ V^λ_{𝒜_t})}`:
the entry from `|λ, X, Y⟩` to `|λ', X', T⟩ ⊗ |λ'', Y', R⟩` is `1/√dim(V^λ_{𝒜_t})` when
`λ' = λ'' = λ`, `X' = X`, `Y' = Y` and `T = R`, and `0` otherwise
(arXiv:2606.30281v2, p.63). -/
noncomputable def eprIsometry : Matrix (S.SchurIdx × S.SchurIdx) S.TabIdx ℂ :=
  Matrix.of fun a b =>
    if a.1.1 = b.1 ∧ a.2.1 = b.1 ∧ (a.1.2.1 : ℕ) = b.2.1 ∧ (a.2.2.1 : ℕ) = b.2.2 ∧
        (a.1.2.2 : ℕ) = a.2.2.2 then
      ((Real.sqrt (S.dA b.1 : ℝ) : ℝ) : ℂ)⁻¹
    else 0

/-- The partial isometry `Γ_t = (Schur_t† ⊗ Schur_tᵀ) E_t : Tab_t → Path_t`
(arXiv:2606.30281v2, p.64). -/
noncomputable def Gamma : Matrix (PathIdx N t) S.TabIdx ℂ :=
  S.doubleSchurᴴ * S.eprIsometry

end SchurWeylData

end PathRecording


