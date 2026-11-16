-- Prove2me | Definitions.Def_SpectrumLB_Supplement_projAvg
-- name    : SpectrumLB_Supplement_projAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:58:01.641209+00:00
-- url     : https://prove2.me/theorems/0f6cf421-a110-4ba9-be85-ea1e7c2edbef
-- title:
--   Average $n$-copy state $\overline\rho^{(n)}_{\mathrm{proj}}=\mathbf E[\rho_{\mathrm{proj}}^{\otimes n}]$, $\rho_{\mathrm{proj}}=\frac2d\Pi$
-- statement:
--   Let $\Pi$ be a Haar-random projection of rank $d/2$ on $\mathbb C^d$, i.e. $\Pi=URU^\dagger$ with $U$ Haar-distributed on the unitary group $U(d)$ and $R=\mathrm{diag}(1,\dots,1,0,\dots,0)$ of rank $d/2$. The first ensemble of §4 is the random state $\rho_{\mathrm{proj}}=\frac2d\Pi$, and its average $n$-copy state is
--
--   $$
--   \overline\rho^{(n)}_{\mathrm{proj}}=\mathbf E\big[\rho_{\mathrm{proj}}^{\otimes n}\big].
--   $$
--
--   It is the state an observer sees when given $n$ copies of a uniformly random maximally mixed state on a random half-dimensional subspace, and it is one of the two states compared in Theorem 4.4.
--
--   **Formalization Note** $\Pi$ is the published `SpectrumLB.haarProj (d/2) U`, $U$ is distributed by the platform's probability Haar measure `QAlgorithms.Schur.unitaryHaar d`, and the expectation is taken entrywise (`WildeQIT.Covering.expectation`). §4 takes $d$ even, so $d/2$ is an integer. The Jucys–Murphy closed form (4.17) is a consequence of Proposition 3.2 and is not used as the definition.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §4, Eq. (4.1), p. 15; Eq. (4.16), p. 17

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_WildeQIT_Covering_expectation
import Definitions.Def_SpectrumLB_haarProj

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB.Supplement

/-- **The average `n`-copy state `ρ̄^{(n)}_proj = E[ρ_proj^{⊗n}]` of the first warm-up ensemble.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680,
§4, Eq. (4.1), p. 15 ("Draw a Haar-random rank-d/2 projection Π on C^d and set ρ_proj := (2/d)Π")
and Eq. (4.16), p. 17 ("ρ̄^{(n)}_proj := E[ρ_proj^{⊗n}]").

`projAvg d n` is the entrywise expectation, over `U ∼ Haar` on `U(d)`, of
`((2/d) · U R U†)^{⊗n}` with `R = diag(1, …, 1, 0, …, 0)` of rank `d/2`.

**Formalization Note.** The Haar-random rank-`d/2` projection is the published `SpectrumLB.haarProj
(d / 2) U` with `U` distributed by the platform's probability Haar measure
`QAlgorithms.Schur.unitaryHaar d`; the expectation is the published entrywise
`WildeQIT.Covering.expectation` (the entries are continuous functions on the compact group, hence
integrable). `ρ^{⊗n}` is `QAlgorithms.piKron n` on `Fin n → Fin d`. §4 takes `d` even, so `d / 2`
(natural division) is exact there. The closed form (4.17) is Proposition 3.2, not this definition. -/
noncomputable def projAvg (d n : ℕ) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  WildeQIT.Covering.expectation (QAlgorithms.Schur.unitaryHaar d) fun U =>
    QAlgorithms.piKron n ((2 / (d : ℂ)) • SpectrumLB.haarProj (d / 2) U)

end SpectrumLB.Supplement


