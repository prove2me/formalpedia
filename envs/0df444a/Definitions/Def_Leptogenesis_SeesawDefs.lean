-- Prove2me | Definitions.Def_Leptogenesis_SeesawDefs
-- name    : Leptogenesis_SeesawDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T14:27:37.859494+00:00
-- url     : https://prove2.me/theorems/7f469355-471d-4272-bfa3-019324429ac2
-- title:
--   Type I seesaw: light mass matrix, its diagonalization, Casas–Ibarra $R$, $N_1$ decay rates and CP asymmetry
-- statement:
--   Definitions for the type I seesaw with three heavy singlet neutrinos $N_1,N_2,N_3$ (masses $M_k$) and three lepton flavours, in the mass basis of the charged leptons and of the $N_k$. The Yukawa matrix $\lambda$ is a complex $3\times3$ matrix ($\alpha$ = flavour row, $k$ = singlet column) and $v=v_u$ is the Higgs vev.
--
--   * **Light neutrino mass matrix** (Eq. (2.5)): $[m]_{\alpha\beta}=\sum_k\lambda_{\alpha k}M_k^{-1}\lambda_{\beta k}v^2$.
--   * **Diagonalization** (Eq. (2.6)): $U$, $D_m=\operatorname{diag}(m_1,m_2,m_3)$ diagonalize $m$ if $U$ is unitary, $m_i\ge0$, and $m=U^*D_mU^\dagger$.
--   * **Casas–Ibarra matrix** (Eq. (2.11)): $R=D_m^{-1/2}U^T\lambda D_M^{-1/2}v$.
--   * **Tree-level decay rates of $N_1$** (Eq. (4.5)): $\Gamma_{\alpha\alpha}=\Gamma(N_1\to\phi\ell_\alpha,\bar\phi\bar\ell_\alpha)=|\lambda_{\alpha1}|^2M_1/(8\pi)$ and $\Gamma_D=\sum_\alpha\Gamma_{\alpha\alpha}=[\lambda^\dagger\lambda]_{11}M_1/(8\pi)$; hence $B^{N_1}_{\phi\ell_\alpha}+B^{N_1}_{\bar\phi\bar\ell_\alpha}=\Gamma_{\alpha\alpha}/\Gamma_D$.
--   * **Flavoured CP asymmetry for hierarchical $N_k$** (Eq. (5.9)): $\varepsilon_{\alpha\alpha}=\dfrac{3M_1}{16\pi v^2[\lambda^\dagger\lambda]_{11}}\operatorname{Im}\{[\lambda]_{\alpha1}[m^*\lambda]_{\alpha1}\}$ (no sum on $\alpha$).
--
--   Conventions: indices run over $\{0,1,2\}$ in Lean, with $N_1$ = index $0$. $m^*$ is the entrywise complex conjugate. Division by zero returns $0$ (relevant only when the first column of $\lambda$ vanishes, or when some $m_i=0$ in $R$).
-- source:
--   S. Davidson, E. Nardi, Y. Nir, Leptogenesis, Physics Reports 466 (2008) 105–177, https://doi.org/10.1016/j.physrep.2008.06.002, Sec. 2.1 Eqs. (2.5), (2.6); Sec. 2.1.1 Eq. (2.11); Sec. 4.2 Eq. (4.5); Sec. 5.2 Eq. (5.9)

import Mathlib

open Matrix

namespace Leptogenesis

/-- Eq. (2.5): the light-neutrino Majorana mass matrix of the type I seesaw, in the mass basis
of the charged leptons and of the singlet fermions,
`[m]_{αβ} = ∑_k [λ]_{αk} M_k⁻¹ [λ]_{βk} v_u²`. -/
noncomputable def lightMassMatrix (v : ℝ) (M : Fin 3 → ℝ) (lam : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun α β => ∑ k, lam α k * ((M k : ℂ))⁻¹ * lam β k * (v : ℂ) ^ 2

/-- Eq. (2.6): `U`, `D_m = diag(m₁, m₂, m₃)` diagonalize the light-neutrino mass matrix `m`:
`U` is unitary, the masses are real and nonnegative, and `m = U^* D_m U^†`. -/
def IsLightMassDiagonalization (m : Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ)
    (masses : Fin 3 → ℝ) : Prop :=
  U ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧ (∀ i, 0 ≤ masses i) ∧
    m = U.map (starRingEnd ℂ) * Matrix.diagonal (fun i => (masses i : ℂ)) * Uᴴ

/-- Eq. (2.11): the Casas–Ibarra matrix `R = D_m^{-1/2} Uᵀ λ D_M^{-1/2} v_u`. -/
noncomputable def casasIbarraR (v : ℝ) (M : Fin 3 → ℝ) (lam : Matrix (Fin 3) (Fin 3) ℂ)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (masses : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (v : ℂ) • (Matrix.diagonal (fun i => ((Real.sqrt (masses i) : ℂ))⁻¹) * Uᵀ * lam *
    Matrix.diagonal (fun k => ((Real.sqrt (M k) : ℂ))⁻¹))

/-- Eq. (4.5): tree-level partial decay rate of `N₁` (index `0`) into lepton flavour `α`,
`Γ_{αα} = Γ(N₁ → φ ℓ_α, φ̄ ℓ̄_α) = |λ_{α1}|² M₁ / (8π)`. -/
noncomputable def partialDecayRate (M : Fin 3 → ℝ) (lam : Matrix (Fin 3) (Fin 3) ℂ)
    (α : Fin 3) : ℝ :=
  ‖lam α 0‖ ^ 2 * M 0 / (8 * Real.pi)

/-- Eq. (4.5): total tree-level decay rate `Γ_D = ∑_α Γ_{αα} = [λ^†λ]_{11} M₁ / (8π)`. -/
noncomputable def totalDecayRate (M : Fin 3 → ℝ) (lam : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  ∑ α, partialDecayRate M lam α

/-- Eq. (5.9): the flavoured CP asymmetry in `N₁` decays for hierarchical singlets,
`ε_{αα} = 3 M₁ / (16 π v_u²) · Im{[λ]_{α1} [m^* λ]_{α1}} / [λ^†λ]_{11}`
(no sum on `α`), where `m` is the light-neutrino mass matrix of Eq. (2.5) and `m^*` its
entrywise complex conjugate. -/
noncomputable def cpAsymmetry (v : ℝ) (M : Fin 3 → ℝ) (lam : Matrix (Fin 3) (Fin 3) ℂ)
    (α : Fin 3) : ℝ :=
  3 * M 0 / (16 * Real.pi * v ^ 2) *
    ((lam α 0 * ((lightMassMatrix v M lam).map (starRingEnd ℂ) * lam) α 0).im /
      ∑ β, ‖lam β 0‖ ^ 2)

end Leptogenesis


