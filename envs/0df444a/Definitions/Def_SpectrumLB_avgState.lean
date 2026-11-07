-- Prove2me | Definitions.Def_SpectrumLB_avgState
-- name    : SpectrumLB_avgState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:56.417915+00:00
-- url     : https://prove2.me/theorems/751c2e5a-2f20-4980-b3ac-c0c4ef5fd7ec
-- title:
--   Definition 5.4 — average $n$-copy state $\overline\rho^{(n)}=\mathbf E[\rho^{\otimes n}]$
-- statement:
--   For the random state $\rho$ drawn from the $n$-tilted law of $\mathrm{PRP}_d(a)$, the average $n$-copy state is
--
--   $$
--   \overline\rho^{(n)}_a=\mathbf E\big[\rho^{\otimes n}\big],
--   $$
--
--   a density matrix on $(\mathbb C^d)^{\otimes n}$. It is the state an algorithm faces when it is given $n$ copies of a state drawn from the ensemble; the lower bound shows $\overline\rho^{(n)}_a$ and $\overline\rho^{(n)}_b$ are close in trace distance (Theorem 5.7).
--
--   **Formalization Note** Defined literally as the tilted average of $\rho^{\otimes n}$; the identity $\overline\rho^{(n)}=\mathbf E[X^{\otimes n}]/\mathbf E[\mathrm{Tr}(X)^n]$ (Eq. (6.61)) is a provable consequence, not part of the definition.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 5.4, Eq. (5.5), p. 21

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_WildeQIT_Covering_expectation
import Definitions.Def_SpectrumLB_tiltedHaar
import Definitions.Def_SpectrumLB_prpState

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **The average `n`-copy state `ρ̄^{(n)} = E[ρ^{⊗n}]`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 5.4, Eq. (5.5), p. 21: "ρ̄^{(n)} := E[ρ^{⊗n}]".

`avgState d n a` is the entrywise expectation (the platform's `WildeQIT.Covering.expectation`) of `ρ^{⊗n}` for `ρ = prpState a U` and `U ∼ tiltedHaar d n a`.

**Formalization Note.** Defined literally as the tilted average; the identity
`ρ̄^{(n)} = E[X^{⊗n}]/E[Tr(X)^n]` ((6.61)) is a proof step, not part of the definition. `ρ^{⊗n}` is
`QAlgorithms.piKron n ρ` on `Fin n → Fin d`. -/
noncomputable def avgState (d n : ℕ) {K : ℕ} (a : Fin K → ℕ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  WildeQIT.Covering.expectation (tiltedHaar d n a) fun U => QAlgorithms.piKron n (prpState a U)

end SpectrumLB


