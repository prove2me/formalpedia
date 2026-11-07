-- Prove2me | Definitions.Def_SpectrumLB_specError
-- name    : SpectrumLB_specError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:32.09828+00:00
-- url     : https://prove2.me/theorems/fe1b0ae6-c31b-4a90-8d9c-5d68d54ea6db
-- title:
--   Output error $d^{\downarrow}_{\mathrm{TV}}(\widehat\alpha,\mathrm{spec}\,\rho)$ of a spectrum estimate $\widehat\alpha\in\mathbb C^d$
-- statement:
--   For an output vector $\widehat\alpha\in\mathbb C^d$ and a $d\times d$ matrix $\rho$ with sorted spectrum $\lambda^{\downarrow}(\rho)=(\lambda_1\ge\cdots\ge\lambda_d)$, the output error is
--
--   $$
--   d^{\downarrow}_{\mathrm{TV}}(\widehat\alpha,\mathrm{spec}\,\rho)=\frac12\min_{\sigma\in S_d}\sum_{i=1}^d\big|\widehat\alpha_{\sigma(i)}-\lambda_i\big| .
--   $$
--
--   It is the precision measure of Definition 1.1: an estimate is good when some matching of its entries to the eigenvalues has small total deviation. When $\widehat\alpha$ is a probability vector it equals the sorted total-variation distance of Definition 2.1, since for real vectors the monotone matching is optimal.
--
--   **Formalization Note** Definition 1.1 allows outputs in $\mathbb C^d$, while Definition 2.1 defines $d^{\downarrow}_{\mathrm{TV}}$ only between probability distributions; this optimal-matching form is defined on all outputs and agrees with Definition 2.1 where both apply. The spectrum is the platform's sorted spectrum `OptimalSpectrum.Entangled.spec`.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 1.1, Eq. (1.1), p. 3; Definition 2.1, p. 11

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_spec

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Output error `d↓TV(α̂, spec ρ)` of a spectrum estimate.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 1.1, Eq. (1.1), p. 3, with Definition 2.1, p. 11.

For an output `α̂ ∈ ℂ^d` and a matrix `ρ`, `specError α̂ ρ = ½ · min_σ Σ_i |α̂_{σ(i)} − λ↓_i(ρ)|`, the minimum
over all permutations `σ` of `{1, …, d}`, where `λ↓(ρ)` is the sorted spectrum (nonincreasing).

**Formalization Note.** Definition 1.1 lets the algorithm output `α̂ ∈ ℂ^d`, but Definition 2.1 defines `d↓TV`
only between probability vectors (paper.md reading R1). This optimal-matching distance is defined on all of
`ℂ^d` and equals `d↓TV(α̂, spec ρ)` whenever `α̂` is a probability vector (for real vectors the monotone
matching is optimal). The spectrum is the platform's `OptimalSpectrum.Entangled.spec` (sorted, nonincreasing). -/
noncomputable def specError {d : ℕ} (α : Fin d → ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (1 / 2 : ℝ) * Finset.univ.inf' Finset.univ_nonempty
    (fun σ : Equiv.Perm (Fin d) => ∑ i, ‖α (σ i) - (OptimalSpectrum.Entangled.spec ρ i : ℂ)‖)

end SpectrumLB


