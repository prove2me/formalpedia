-- Prove2me | Definitions.Def_SpectrumLB_Supplement_RankTests
-- name    : SpectrumLB_Supplement_RankTests
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:57:18.426426+00:00
-- url     : https://prove2.me/theorems/feca0991-2771-40dd-a744-5b1d9dfb12cf
-- title:
--   A two-outcome measurement on $n$ copies tests rank $\le\beta d$ against $\epsilon$-far, with two-sided error
-- statement:
--   Let $M$ be an operator on $(\mathbb C^d)^{\otimes n}$ with $0\preceq M\preceq I$, the "accept" outcome of the two-outcome measurement $\{M,\,I-M\}$. It **tests whether a state has rank at most $\beta d$ or is $\epsilon$-far from all such states** when
--
--   1. every density matrix $\rho$ with $\operatorname{rank}\rho\le\beta d$ is accepted with probability $\mathrm{Tr}(M\rho^{\otimes n})\ge 2/3$, and
--   2. every density matrix $\rho$ with $D_{\mathrm{tr}}(\rho,\sigma)\ge\epsilon$ for all density matrices $\sigma$ of rank at most $\beta d$ is rejected with probability $\mathrm{Tr}((I-M)\rho^{\otimes n})\ge 2/3$,
--
--   where $D_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$ is the trace distance (Definition 2.3).
--
--   Both kinds of error are allowed (two-sided error); the one-sided variant, which must accept every low-rank state with certainty, is a different task. Theorem 1.4 lower-bounds the number of copies any such tester needs.
--
--   **Formalization Note** The effect condition is the platform's `QAlgorithms.IsEffect`; a general two-outcome POVM on $n$ copies, including adaptive strategies, is of this form. The rank is `Matrix.rank` over $\mathbb C$ and the comparison with the real number $\beta d$ is real (equivalently $\operatorname{rank}\le\lfloor\beta d\rfloor$). The trace distance is the platform's `QAlgorithms.traceDistance`.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Theorem 1.4, p. 3 (task, two-sided error, footnote 1); Definition 1.1, p. 3 (success probability 2/3); Definition 2.3, p. 11 (trace distance)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB.Supplement

/-- **A two-outcome measurement on `n` copies tests rank `≤ β·d` against `ε`-far.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680,
Theorem 1.4, p. 3: "testing whether a state has rank at most β·d or is ϵ-far in trace distance from
all such states", with two-sided error (p. 3, footnote 1 contrasts it with one-sided error), success
probability `2/3` as in Definition 1.1, p. 3, and `D_tr(ρ, σ) = ½‖ρ − σ‖₁` (Definition 2.3, p. 11).

`RankTests d n β ε M` holds when `M` is an effect (`0 ⪯ M ⪯ 1`) on `(ℂ^d)^{⊗n}` (the "accept"
outcome of the two-outcome POVM `{M, 1 − M}`) and
1. (completeness) every density matrix `ρ` with `rank ρ ≤ β·d` is accepted with probability
   `Tr(M ρ^{⊗n}) ≥ 2/3`;
2. (soundness) every density matrix `ρ` with `D_tr(ρ, σ) ≥ ε` for every density matrix `σ` of
   `rank σ ≤ β·d` is rejected with probability `Tr((1 − M) ρ^{⊗n}) ≥ 2/3`.

**Formalization Note.** A tester on `n` copies (adaptive, with any post-processing) is a two-outcome
POVM on `(ℂ^d)^{⊗n}`, i.e. an effect `M` (`QAlgorithms.IsEffect`), indexed by `Fin n → Fin d`.
`ρ^{⊗n}` is `QAlgorithms.piKron n ρ`, probabilities are `QAlgorithms.effectProb`. `rank` is
`Matrix.rank` over `ℂ`; `β·d` is real, so "rank at most β·d" is the real comparison
(`rank ≤ ⌊β·d⌋`). "ε-far from all such states" ranges over density matrices `σ` only; the distance
is the platform's `QAlgorithms.traceDistance`. -/
def RankTests (d n : ℕ) (β ε : ℝ) (M : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Prop :=
  QAlgorithms.IsEffect M ∧
  (∀ ρ : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix ρ → (ρ.rank : ℝ) ≤ β * d →
    (2 / 3 : ℝ) ≤ QAlgorithms.effectProb M (QAlgorithms.piKron n ρ)) ∧
  (∀ ρ : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix ρ →
    (∀ σ : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix σ → (σ.rank : ℝ) ≤ β * d →
      ε ≤ QAlgorithms.traceDistance ρ σ) →
    (2 / 3 : ℝ) ≤ QAlgorithms.effectProb (1 - M) (QAlgorithms.piKron n ρ))

end SpectrumLB.Supplement


