-- Prove2me | Definitions.Def_SpectrumLB_powSum
-- name    : SpectrumLB_powSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:17.380959+00:00
-- url     : https://prove2.me/theorems/4a4a62b8-4141-4fa2-b749-df0ba5f6a659
-- title:
--   Definition 2.4 — normalized power sum $\mathrm{pow}_L(\alpha)=d^{L-1}\sum_i\alpha_i^L$
-- statement:
--   For $L\in\mathbb N$ and $\alpha\in\mathbb R^d$, the normalized $L$-th power sum is
--
--   $$
--   \mathrm{pow}_L(\alpha)=d^{\,L-1}\sum_{i=1}^d\alpha_i^L .
--   $$
--
--   For a probability vector it is at least $1$, with equality for the uniform distribution; for a density matrix, $\mathrm{pow}_L(\mathrm{spec}\,\rho)$ is a normalized moment of the spectrum. Power sums are the statistics through which the spectra of the two hard ensembles are separated (Lemma 7.3, Proposition 5.8).
--
--   **Formalization Note** The factor $d^{L-1}$ uses an integer exponent, so $L=0$ gives $d^{-1}\cdot d=1$ without natural-number truncation.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 2.4, Eq. (2.1), p. 11

import Mathlib

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Normalized power sum `pow_L(α)`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 2.4, Eq. (2.1), p. 11: "pow_L(α) = d^{L−1} · Σ_{i=1}^d α_i^L".

**Formalization Note.** The exponent `L − 1` is an integer exponent (`zpow`), so `pow_0(α) = d^{−1} · d = 1`
for `d ≥ 1` with no natural-number truncation. -/
noncomputable def powSum {d : ℕ} (L : ℕ) (α : Fin d → ℝ) : ℝ :=
  (d : ℝ) ^ ((L : ℤ) - 1) * ∑ i, α i ^ L

end SpectrumLB


