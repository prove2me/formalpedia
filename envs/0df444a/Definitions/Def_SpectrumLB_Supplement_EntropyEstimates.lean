-- Prove2me | Definitions.Def_SpectrumLB_Supplement_EntropyEstimates
-- name    : SpectrumLB_Supplement_EntropyEstimates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:56:42.165504+00:00
-- url     : https://prove2.me/theorems/4b2aed03-dd29-4d74-af14-cd3e2512d646
-- title:
--   A measurement on $n$ copies estimates the von Neumann entropy to precision $\epsilon$
-- statement:
--   Let $E$ be a POVM on $(\mathbb C^d)^{\otimes n}$ with real outcomes $\widehat S$: a countably additive map from Borel subsets of $\mathbb R$ to positive semidefinite operators with $E(\mathbb R)=I$. The measurement **estimates the von Neumann entropy to within precision $\epsilon$** when, for every $d$-dimensional density matrix $\rho$,
--
--   $$
--   \mathrm{Tr}\Big(E\big(\{\widehat S\in\mathbb R:\ |\widehat S-S(\rho)|\le\epsilon\}\big)\,\rho^{\otimes n}\Big)\ \ge\ \frac23,
--   \qquad S(\rho)=-\mathrm{Tr}(\rho\ln\rho).
--   $$
--
--   Any algorithm that measures $n$ copies of $\rho$, adaptively and with arbitrary classical post-processing, and outputs a real number is such a POVM. This is the success criterion of Definition 1.1 with the spectrum replaced by the entropy, and it is the predicate against which the lower bound of Theorem 1.3 is stated.
--
--   **Formalization Note** The POVM is the platform's `OperatorPOVM` on the index type `Fin n → Fin d` with outcome space $\mathbb R$; $\rho^{\otimes n}$ is `piKron n ρ` and the Born probability is the real part of the trace (`effectProb`). $S$ is the platform's `MomentPolytopes.QuantumFunctionals.vnEntropy`: the Shannon entropy of the spectrum with the natural logarithm and $0\ln 0=0$, which equals $-\mathrm{Tr}(\rho\ln\rho)$ on density matrices. The success event is closed, hence Borel.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Theorem 1.3, p. 3 (task and S(ρ) := −Tr(ρ ln ρ)); Definition 1.1, p. 3 (success probability 2/3)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB.Supplement

/-- **A measurement on `n` copies estimates the von Neumann entropy to precision `ε`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680,
Theorem 1.3, p. 3 (the task of "estimating a d-dimensional state's von Neumann entropy to within
precision ϵ", with `S(ρ) := −Tr(ρ ln(ρ))`, p. 3), in the shape of Definition 1.1, p. 3 (success
"with probability at least 2/3").

`EntropyEstimates d n ε E` holds when the POVM `E` on `(ℂ^d)^{⊗n}` with real outcomes `Ŝ` satisfies,
for **every** density matrix `ρ`, `Tr(E({Ŝ : |Ŝ − S(ρ)| ≤ ε}) ρ^{⊗n}) ≥ 2/3`.

**Formalization Note.** The paper defines this task only by analogy with Definition 1.1; this is
Definition 1.1 with a real output and the error `|Ŝ − S(ρ)|`. An algorithm on `n` copies (adaptive,
with any classical post-processing) is a POVM: the platform's `OperatorPOVM` on the index type
`Fin n → Fin d` (copy `i` is coordinate `i`) with outcome space `ℝ` (Borel). `ρ^{⊗n}` is
`QAlgorithms.piKron n ρ`; the Born probability is `QAlgorithms.effectProb` (real part of the trace).
`S(ρ)` is the platform's `MomentPolytopes.QuantumFunctionals.vnEntropy`, the Shannon entropy of the
spectrum with the **natural** logarithm and `0 log 0 = 0`, which is `−Tr(ρ ln ρ)` for a density
matrix. The success event is closed, hence Borel. The output is any real number. -/
def EntropyEstimates (d n : ℕ) (ε : ℝ)
    (E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) ℝ) : Prop :=
  ∀ ρ : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix ρ →
    (2 / 3 : ℝ) ≤
      QAlgorithms.effectProb
        (E.operator {s | |s - MomentPolytopes.QuantumFunctionals.vnEntropy ρ| ≤ ε})
        (QAlgorithms.piKron n ρ)

end SpectrumLB.Supplement


