-- Prove2me | Definitions.Def_SpectrumLB_SpectrumEstimates
-- name    : SpectrumLB_SpectrumEstimates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:35.399783+00:00
-- url     : https://prove2.me/theorems/4a384f64-356f-49a5-a55c-a5659334c683
-- title:
--   Definition 1.1 — a measurement on $n$ copies estimates the spectrum to precision $\epsilon$
-- statement:
--   Let $E$ be a POVM on $(\mathbb C^d)^{\otimes n}$ whose outcomes are vectors $\widehat\alpha\in\mathbb C^d$: a countably additive map from Borel sets of $\mathbb C^d$ to positive semidefinite operators with $E(\mathbb C^d)=I$. The measurement **estimates the spectrum to within precision $\epsilon$** when, for every $d$-dimensional density matrix $\rho$,
--
--   $$
--   \mathrm{Tr}\Big(E\big(\{\widehat\alpha:\ d^{\downarrow}_{\mathrm{TV}}(\widehat\alpha,\mathrm{spec}\,\rho)\le\epsilon\}\big)\,\rho^{\otimes n}\Big)\ \ge\ \frac23 .
--   $$
--
--   Any algorithm that measures $n$ copies of $\rho$ (adaptively, with any classical post-processing) and outputs $\widehat\alpha$ is such a POVM, so this is the success criterion of Definition 1.1 for an arbitrary algorithm. The copy-complexity lower bound of Theorem 1.2 is stated against this predicate.
--
--   **Formalization Note** The POVM is the platform's `OperatorPOVM` on the index type `Fin n → Fin d` (copy $i$ is coordinate $i$), with Borel outcome space `Fin d → ℂ`; $\rho^{\otimes n}$ is `piKron n ρ` and the Born probability is the real part of the trace (`effectProb`). The success event is closed, hence Borel.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 1.1, p. 3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_SpectrumLB_specError

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **A measurement on `n` copies estimates the spectrum to precision `ε`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 1.1, p. 3: "Given n copies of an unknown state ρ ∈ C^{d×d}, we say an algorithm estimates
its spectrum to within precision ϵ if it outputs a vector α̂ ∈ C^d such that, with probability at least 2/3,
d↓TV(α̂, spec(ρ)) ≤ ϵ."

`SpectrumEstimates d n ε E` holds when the POVM `E` on `(ℂ^d)^{⊗n}` with outcomes `α̂ ∈ ℂ^d` satisfies, for
**every** density matrix `ρ`, `Tr(E({α̂ : d↓TV(α̂, spec ρ) ≤ ε}) ρ^{⊗n}) ≥ 2/3`.

**Formalization Note.** An algorithm on `n` copies is an arbitrary measurement of `ρ^{⊗n}`: the platform's
`OperatorPOVM` (countably additive, PSD on measurable sets, total mass `1`) on the index type `Fin n → Fin d`
(copy `i` is coordinate `i`) with outcome space `Fin d → ℂ` (product Borel σ-algebra); any other outcome space
with measurable post-processing yields such a POVM. `ρ^{⊗n}` is `QAlgorithms.piKron n ρ`, the Born probability
is `QAlgorithms.effectProb` (real part of the trace). The success event is closed, hence Borel, so
`E.operator` is evaluated on a measurable set. The error is `specError` (reading R1). -/
def SpectrumEstimates (d n : ℕ) (ε : ℝ)
    (E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) (Fin d → ℂ)) : Prop :=
  ∀ ρ : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix ρ →
    (2 / 3 : ℝ) ≤
      QAlgorithms.effectProb (E.operator {α | specError α ρ ≤ ε}) (QAlgorithms.piKron n ρ)

end SpectrumLB


