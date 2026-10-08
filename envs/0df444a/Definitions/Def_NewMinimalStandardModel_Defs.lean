-- Prove2me | Definitions.Def_NewMinimalStandardModel_Defs
-- name    : NewMinimalStandardModel_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T11:57:26.463705+00:00
-- url     : https://prove2.me/theorems/8e853321-5933-4b7c-b6a8-cb8dd147abf1
-- title:
--   New Minimal Standard Model: neutrino mass matrices and slow-roll observables
-- statement:
--   Shared definitions for the new Minimal Standard Model (NMSM) of Davoudiasl–Kitano–Li–Murayama.
--
--   **Neutrino sector (Eq. (4), p. 119).** For a real Higgs vacuum expectation value parameter $v$ (with $\langle H\rangle = v/\sqrt2$), a complex $2\times3$ Yukawa matrix $h_\nu$ and real right-handed masses $M_1, M_2$:
--
--   1. the Dirac mass matrix $m_D = \dfrac{v}{\sqrt2}\,h_\nu$;
--   2. the right-handed Majorana mass matrix $\operatorname{diag}(M_1, M_2)$;
--   3. the $5\times5$ neutral-lepton mass matrix in the basis $(\nu_1,\nu_2,\nu_3,N_1,N_2)$,
--   $$\mathcal M(v,h_\nu,M) = \begin{pmatrix} 0_{3\times3} & m_D^{\mathsf T} \\ m_D & \operatorname{diag}(M_1,M_2)\end{pmatrix};$$
--   4. the seesaw light-neutrino mass matrix $m_\nu = -\,m_D^{\mathsf T}\operatorname{diag}(M_1,M_2)^{-1} m_D$;
--   5. the physical (Majorana) masses $\sigma_i(A) = \sqrt{\lambda_i(A^\dagger A)}$ of a square complex matrix $A$, where $\lambda_i$ are the eigenvalues of the Hermitian matrix $A^\dagger A$.
--
--   **Inflaton sector (Eq. (5), p. 119; p. 122).** For the quadratic potential $V(\varphi)=\tfrac12 m^2\varphi^2$ and reduced Planck mass $M_{\rm Pl}$:
--   $$\epsilon=\frac{M_{\rm Pl}^2}{2}\Big(\frac{V'}{V}\Big)^2,\quad \eta=M_{\rm Pl}^2\frac{V''}{V},\quad N(\varphi_{\rm end},\varphi)=\frac1{M_{\rm Pl}^2}\int_{\varphi_{\rm end}}^{\varphi}\frac{V}{V'}\,d\psi,\quad n_s=1-6\epsilon+2\eta,\quad r=16\epsilon.$$
--
--   These definitions are used by every theorem in the mission.
--
--   **Formalization Note** The matrix inverse is Mathlib's `Matrix.inv` (the zero matrix for a singular argument); all theorems that use $m_\nu$ assume $M_1,M_2>0$. Derivatives are Mathlib's `deriv` and the integral is the interval integral.
-- source:
--   H. Davoudiasl, R. Kitano, T. Li, H. Murayama, The new Minimal Standard Model, Phys. Lett. B 609 (2005) 117-123, https://doi.org/10.1016/j.physletb.2005.01.026, Eqs. (4)-(5), p. 119; p. 122

import Mathlib

/-!
# The new Minimal Standard Model — shared definitions

Source: H. Davoudiasl, R. Kitano, T. Li, H. Murayama, *The new Minimal Standard Model*,
Phys. Lett. B 609 (2005) 117–123, doi:10.1016/j.physletb.2005.01.026.

* Neutrino sector: Eq. (4) (p. 119) with two right-handed neutrinos `N_α`, `α = 1, 2`,
  in the basis where the right-handed-neutrino mass matrix is real and diagonal.
* Inflaton sector: Eq. (5) (p. 119), quadratic chaotic inflation, with the standard
  slow-roll observables used on p. 122.
-/

namespace NewMinimalStandardModel

open Matrix

/-! ## Neutrino sector (Eq. (4)) -/

/-- Dirac mass matrix `m_D = h_ν v / √2` (a `2 × 3` complex matrix, rows indexed by the
right-handed neutrinos `α`, columns by the lepton doublets `i`), obtained from the Yukawa
coupling `h_ν^{αi} N_α L_i H̃` of Eq. (4) with Higgs vacuum expectation value `⟨H⟩ = v / √2`. -/
noncomputable def diracMass (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ) :
    Matrix (Fin 2) (Fin 3) ℂ :=
  ((v : ℂ) / (Real.sqrt 2 : ℂ)) • hν

/-- Majorana mass matrix of the two right-handed neutrinos, `diag(M_1, M_2)`, in the basis
where it is real and diagonal (Eq. (4), p. 119). -/
noncomputable def rhNeutrinoMass (M : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun α => (M α : ℂ)

/-- The full `5 × 5` complex symmetric Majorana mass matrix of the neutral leptons after
electroweak symmetry breaking, in the basis `(ν_1, ν_2, ν_3, N_1, N_2)`:
`[[0, m_Dᵀ], [m_D, diag(M_1, M_2)]]`. -/
noncomputable def neutralLeptonMassMatrix (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ)
    (M : Fin 2 → ℝ) : Matrix (Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 0 (diracMass v hν)ᵀ (diracMass v hν) (rhNeutrinoMass M)

/-- The seesaw light-neutrino (left-handed) Majorana mass matrix
`m_ν = - m_Dᵀ diag(M_1, M_2)⁻¹ m_D` (a `3 × 3` complex symmetric matrix). -/
noncomputable def seesawMassMatrix (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ)
    (M : Fin 2 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  -((diracMass v hν)ᵀ * (rhNeutrinoMass M)⁻¹ * diracMass v hν)

/-- The physical masses of the Majorana mass eigenstates described by a square complex mass
matrix `A`: its singular values, i.e. the square roots of the eigenvalues of the Hermitian
positive semidefinite matrix `Aᴴ A` (listed in the order chosen by Mathlib's spectral
theorem). -/
noncomputable def majoranaMasses {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : n → ℝ :=
  fun i => Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-! ## Inflaton sector (Eq. (5)) and slow-roll observables -/

/-- The quadratic inflaton potential `V(φ) = m² φ² / 2` driving chaotic inflation
(the mass term of Eq. (5); the cubic and quartic terms are neglected, p. 119). -/
noncomputable def quadraticPotential (m : ℝ) : ℝ → ℝ :=
  fun φ => m ^ 2 * φ ^ 2 / 2

/-- First slow-roll parameter `ε(φ) = (M_Pl² / 2) (V'(φ) / V(φ))²`, with `M_Pl` the reduced
Planck mass. -/
noncomputable def slowRollEpsilon (V : ℝ → ℝ) (Mpl φ : ℝ) : ℝ :=
  Mpl ^ 2 / 2 * (deriv V φ / V φ) ^ 2

/-- Second slow-roll parameter `η(φ) = M_Pl² V''(φ) / V(φ)`. -/
noncomputable def slowRollEta (V : ℝ → ℝ) (Mpl φ : ℝ) : ℝ :=
  Mpl ^ 2 * deriv (deriv V) φ / V φ

/-- Number of e-folds of slow-roll inflation between field values `φ_end` and `φ`:
`N = (1 / M_Pl²) ∫_{φ_end}^{φ} V(ψ) / V'(ψ) dψ`. -/
noncomputable def efolds (V : ℝ → ℝ) (Mpl φend φ : ℝ) : ℝ :=
  (1 / Mpl ^ 2) * ∫ ψ in φend..φ, V ψ / deriv V ψ

/-- Slow-roll scalar spectral index `n_s = 1 - 6 ε + 2 η`. -/
noncomputable def spectralIndex (V : ℝ → ℝ) (Mpl φ : ℝ) : ℝ :=
  1 - 6 * slowRollEpsilon V Mpl φ + 2 * slowRollEta V Mpl φ

/-- Slow-roll tensor-to-scalar ratio `r = 16 ε`. -/
noncomputable def tensorToScalarRatio (V : ℝ → ℝ) (Mpl φ : ℝ) : ℝ :=
  16 * slowRollEpsilon V Mpl φ

end NewMinimalStandardModel


