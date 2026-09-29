-- Prove2me | Definitions.Def_LipariNeutrino_MixingMatrices
-- name    : LipariNeutrino_MixingMatrices
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T04:57:25.227896+00:00
-- url     : https://prove2.me/theorems/23c3b97c-c044-48a6-b057-abb8bbfccd95
-- title:
--   Two-flavour mixing matrix and standard PMNS parametrization
-- statement:
--   1. **Two-flavour mixing matrix** (Eq. (49)): for a mixing angle $\theta$,
--   $$U(\theta)=\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix},$$
--   rows indexed by $\nu_e,\nu_\mu$ and columns by $\nu_1,\nu_2$.
--
--   2. **Standard three-flavour parametrization** (Eq. (57)): with $c_{jk}=\cos\theta_{jk}$, $s_{jk}=\sin\theta_{jk}$ and CP phase $\delta$,
--   $$U(\theta_{12},\theta_{13},\theta_{23},\delta)=\begin{pmatrix}1&0&0\\0&c_{23}&s_{23}\\0&-s_{23}&c_{23}\end{pmatrix}\begin{pmatrix}c_{13}&0&s_{13}e^{-i\delta}\\0&1&0\\-s_{13}e^{i\delta}&0&c_{13}\end{pmatrix}\begin{pmatrix}c_{12}&s_{12}&0\\-s_{12}&c_{12}&0\\0&0&1\end{pmatrix},$$
--   rows indexed by $e,\mu,\tau$ and columns by $1,2,3$.
--
--   **Formalization Note** Rows and columns are indexed by $0,1$ (resp. $0,1,2$) in Lean. The matrices are defined as complex matrices; the two Majorana phases, which do not affect oscillations, are not included.
-- source:
--   P. Lipari, *Introduction to Neutrino Physics* (lecture notes, uploaded PDF), Section 4, §4.1 Eq. (49) and §4.2 Eq. (57).

import Mathlib

namespace LipariNeutrino

/-- Two-flavour mixing matrix (Lipari, Eq. (49)): with `c = cos θ`, `s = sin θ`,
`U = [[c, s], [-s, c]]` (rows: flavours `e, μ`; columns: mass states `1, 2`). -/
noncomputable def twoFlavorMix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), (Real.sin θ : ℂ); -(Real.sin θ : ℂ), (Real.cos θ : ℂ)]

/-- Standard three-flavour parametrization of the PMNS matrix (Lipari, Eq. (57)):
`U = R₂₃ · U₁₃(δ) · R₁₂` with mixing angles `θ₁₂, θ₁₃, θ₂₃` and CP phase `δ`.
Rows are indexed by the flavours `e, μ, τ` (as `0, 1, 2`) and columns by the mass
eigenstates `1, 2, 3` (as `0, 1, 2`). -/
noncomputable def pmns (θ12 θ13 θ23 δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
     0, (Real.cos θ23 : ℂ), (Real.sin θ23 : ℂ);
     0, -(Real.sin θ23 : ℂ), (Real.cos θ23 : ℂ)] *
  !![(Real.cos θ13 : ℂ), 0, (Real.sin θ13 : ℂ) * Complex.exp (-(Complex.I * (δ : ℂ)));
     0, 1, 0;
     -((Real.sin θ13 : ℂ) * Complex.exp (Complex.I * (δ : ℂ))), 0, (Real.cos θ13 : ℂ)] *
  !![(Real.cos θ12 : ℂ), (Real.sin θ12 : ℂ), 0;
     -(Real.sin θ12 : ℂ), (Real.cos θ12 : ℂ), 0;
     0, 0, 1]

end LipariNeutrino


