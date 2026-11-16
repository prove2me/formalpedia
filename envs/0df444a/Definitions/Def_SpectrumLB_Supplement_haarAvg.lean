-- Prove2me | Definitions.Def_SpectrumLB_Supplement_haarAvg
-- name    : SpectrumLB_Supplement_haarAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:58:51.062206+00:00
-- url     : https://prove2.me/theorems/8ee142d6-c431-4259-90da-2ee3a27dd650
-- title:
--   Average $n$-copy state $\overline\rho^{(n)}_{\mathrm{Haar}}=\mathbf E[\rho_{\mathrm{Haar}}^{\otimes n}]$
-- statement:
--   Let $|\psi\rangle$ be a Haar-random unit vector of $\mathbb C^d\otimes\mathbb C^d$ and $\rho_{\mathrm{Haar}}=\mathrm{Tr}_2[|\psi\rangle\langle\psi|]$. The average $n$-copy state of this second ensemble of §4 is
--
--   $$
--   \overline\rho^{(n)}_{\mathrm{Haar}}=\mathbf E\big[\rho_{\mathrm{Haar}}^{\otimes n}\big].
--   $$
--
--   Together with $\overline\rho^{(n)}_{\mathrm{proj}}$ it is one of the two states whose relative entropy Theorem 4.4 bounds.
--
--   **Formalization Note** $|\psi\rangle$ is realized as the column $Ve_c$ of a unitary $V$ distributed by the platform's probability Haar measure on $U(d^2)$ (`QAlgorithms.Schur.unitaryHaar (d*d)`); every column of a Haar unitary is uniform on the unit sphere, so the average does not depend on $c$, which is kept as a parameter only because there is no canonical index when $d=0$. The expectation is entrywise (`WildeQIT.Covering.expectation`). The closed form (4.18) is Lemma 4.2 and is not used as the definition.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §4, Eq. (4.2), p. 15; Lemma 4.2, Eq. (4.18), p. 17

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_WildeQIT_Covering_expectation
import Definitions.Def_SpectrumLB_Supplement_haarInduced

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB.Supplement

/-- **The average `n`-copy state `ρ̄^{(n)}_Haar = E[ρ_Haar^{⊗n}]` of the second warm-up ensemble.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680,
§4, Eq. (4.2), p. 15 and Lemma 4.2, Eq. (4.18), p. 17 ("ρ̄^{(n)}_Haar := E[ρ_Haar^{⊗n}]").

`haarAvg d n c` is the entrywise expectation, over `V ∼ Haar` on `U(d²)`, of
`(haarInduced d c V)^{⊗n}`, where `haarInduced d c V = Tr₂[|ψ⟩⟨ψ|]` for `|ψ⟩ = V e_c`.

**Formalization Note.** `V e_c` is uniform on the unit sphere of `ℂ^d ⊗ ℂ^d` for every fixed `c`, so
the value does not depend on `c`; the column index is a parameter only because `Fin (d * d)` has no
canonical element when `d = 0`. The Haar measure is the platform's probability Haar measure
`QAlgorithms.Schur.unitaryHaar (d * d)`, the expectation the published entrywise
`WildeQIT.Covering.expectation`. The closed form `d^n/(d²)_n ∏_t (1 + J̃_t)` of (4.18) is Lemma 4.2
(a proof step), not this definition. -/
noncomputable def haarAvg (d n : ℕ) (c : Fin (d * d)) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  WildeQIT.Covering.expectation (QAlgorithms.Schur.unitaryHaar (d * d)) fun V =>
    QAlgorithms.piKron n (haarInduced d c V)

end SpectrumLB.Supplement


