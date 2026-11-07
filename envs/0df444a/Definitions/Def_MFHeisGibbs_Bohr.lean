-- Prove2me | Definitions.Def_MFHeisGibbs_Bohr
-- name    : MFHeisGibbs_Bohr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:55:34.760189+00:00
-- url     : https://prove2.me/theorems/1aa4dc4d-5832-4d90-849c-c2f416ef4eb7
-- title:
--   Bohr frequencies $B(H)$, spectral projections $P_E$ and Bohr components $A_\nu$
-- statement:
--   For a Hermitian matrix $H$ with spectral projections $P_E$, the Bohr frequencies are $B(H)=\mathrm{spec}(H)-\mathrm{spec}(H)$, and the Bohr component of an operator $A$ at $\nu$ is
--
--   $$A_\nu=\sum_{E'-E=\nu}P_{E'}AP_E .$$
--
--   It satisfies $[H,A_\nu]=\nu A_\nu$, so $\nu<0$ lowers the energy. A function $h$ on frequencies acts by $h(\mathrm{ad}_H)(A)=\sum_{\nu\in B(H)}h(\nu)A_\nu$.
--
--   Every generator in the paper is built from the components $\sigma^{(i,\alpha)}_\nu$ for $H=H_n$.
--
--   **Formalization Note** $P_E$ is read off Mathlib's eigendecomposition; it does not depend on the eigenbasis chosen. $B(H)$ contains every difference, including those with $A_\nu=0$.
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), (6), p.4 (PDF 5); nomenclature, p.42 (PDF 43)

import Definitions.Def_MFHeisGibbs_Model

open Matrix

namespace MFHeisGibbs

/-!
# Bohr frequencies and Bohr components of a Hermitian matrix

Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…),
(6), p.4; nomenclature, p.42.

**Formalization Note.** The eigenvalues and the projections `P_E` are read off Mathlib's
eigendecomposition of the Hermitian `H`; the projection `P_E` onto an eigenspace does not depend on
the chosen eigenbasis. The set `B(H) = spec(H) − spec(H)` contains every difference, including the
frequencies with `A_ν = 0`, as on the page.
-/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

/-- The spectrum of a Hermitian matrix, as a finite set of reals. -/
noncomputable def specFinset (hH : H.IsHermitian) : Finset ℝ :=
  Finset.univ.image hH.eigenvalues

/-- The spectral projection `P_E` of a Hermitian matrix onto the eigenvalue `E`. -/
noncomputable def specProj (hH : H.IsHermitian) (E : ℝ) : Matrix ι ι ℂ :=
  (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
    Matrix.diagonal (fun k => if hH.eigenvalues k = E then (1 : ℂ) else 0) *
    (hH.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ

/-- The Bohr frequencies `B(H) := spec(H) − spec(H)`. -/
noncomputable def bohrFreqs (hH : H.IsHermitian) : Finset ℝ :=
  (specFinset hH ×ˢ specFinset hH).image fun p => p.1 - p.2

/-- The Bohr component `A_ν = ∑_{E′−E=ν} P_{E′} A P_E`, (6). -/
noncomputable def bohrComp (hH : H.IsHermitian) (A : Matrix ι ι ℂ) (ν : ℝ) : Matrix ι ι ℂ :=
  ∑ E' ∈ specFinset hH, ∑ E ∈ specFinset hH,
    if E' - E = ν then specProj hH E' * A * specProj hH E else 0

/-- The reweighting `h(ad_H)(A) = ∑_{ν ∈ B(H)} h(ν) A_ν`, p.11. -/
noncomputable def bohrFilter (hH : H.IsHermitian) (h : ℝ → ℂ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ ν ∈ bohrFreqs hH, h ν • bohrComp hH A ν

/-- The Bohr frequencies `B(H_n)`. -/
noncomputable def bohr (n : ℕ) : Finset ℝ := bohrFreqs (Hn_isHermitian n)

/-- The Bohr component `σ^(i,α)_ν` of a single-site Pauli for `H_n`. -/
noncomputable def sig {n : ℕ} (i : Fin n) (α : Fin 3) (ν : ℝ) : Op n :=
  bohrComp (Hn_isHermitian n) (pauliAt i α) ν

/-- The filtered Pauli `h(ad_{H_n})(σ^(i,α)) = ∑_ν h(ν) σ^(i,α)_ν`. -/
noncomputable def sigFilter {n : ℕ} (h : ℝ → ℂ) (i : Fin n) (α : Fin 3) : Op n :=
  bohrFilter (Hn_isHermitian n) h (pauliAt i α)

end MFHeisGibbs


