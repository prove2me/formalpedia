-- Prove2me | Definitions.Def_SpectrumLB_psi
-- name    : SpectrumLB_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:42.623185+00:00
-- url     : https://prove2.me/theorems/c01658ff-9b19-4f70-bb27-54260c3faf6e
-- title:
--   Normalized expected moment $\Psi_j(e)=\mathbf E[\mathrm{tr}\,X^j]/\mathbf E[\mathrm{tr}\,X]^j$, Eq. (7.1)
-- statement:
--   For $X\sim\mathrm{PRP}_d(e)$ and the normalized trace $\mathrm{tr}=\frac1d\mathrm{Tr}$,
--
--   $$
--   \Psi_j(e)=\frac{\mathbf E\big[\mathrm{tr}(X^j)\big]}{\mathbf E\big[\mathrm{tr}(X)\big]^j}.
--   $$
--
--   These deterministic quantities are the typical values of the normalized power sums of the random state's spectrum (Lemma 7.3); the two ensembles agree on $\Psi_j$ up to $O(1/d)$ for $j\le k$ and differ at $j=k+1$ (Lemma 7.1).
--
--   **Formalization Note** Real parts of the traces, which are real because $X$ is positive semidefinite; the dependence on $d$ is explicit.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §7.1, Eq. (7.1), p. 34

import Mathlib
import Definitions.Def_SpectrumLB_haarK
import Definitions.Def_SpectrumLB_prpMatrix

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Normalized expected moment `Ψ_j(e) = E[tr X^j] / E[tr X]^j`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, §7.1, Eq. (7.1), p. 34, with `tr = d⁻¹ Tr` (p. 12) and `X = X_e ∼ PRP_d(e)` (untilted).

**Formalization Note.** Real parts of the traces (they are real: `X` is PSD); the dependence on `d` is
explicit. -/
noncomputable def psi (d : ℕ) {K : ℕ} (e : Fin K → ℕ) (j : ℕ) : ℝ :=
  (∫ U, ((prpMatrix (d := d) e U) ^ j).trace.re / d ∂haarK d K) /
    (∫ U, (prpMatrix (d := d) e U).trace.re / d ∂haarK d K) ^ j

end SpectrumLB


