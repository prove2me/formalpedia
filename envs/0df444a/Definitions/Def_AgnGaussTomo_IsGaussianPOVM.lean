-- Prove2me | Definitions.Def_AgnGaussTomo_IsGaussianPOVM
-- name    : AgnGaussTomo_IsGaussianPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:54.994437+00:00
-- url     : https://prove2.me/theorems/fa946c1c-f3ab-4bd4-841b-5eb77617b532
-- title:
--   Gaussian measurements and Gaussian measurement schemes
-- statement:
--   A **Gaussian measurement** of $n$ modes is a POVM with outcomes $y\in\mathbb R^{2n}$ of the form
--
--   $$
--   M(d^{2n}y)=\frac{1}{(2\pi)^n}\,D(y)\,\tau\,D(y)^\dagger\,d^{2n}y ,
--   $$
--
--   where the **seed** $\tau$ is a mean-zero Gaussian state. Heterodyne detection is the case $\tau=|0\rangle\langle0|$; a Gaussian unitary followed by heterodyne is again of this form after an affine relabelling of the outcomes. Here each outcome also carries an independent uniform random number $u\in[0,1]$ (classical randomness available to the learner): for every density $\rho$ and measurable $B\subseteq\mathbb R^{2n}$, $B'\subseteq\mathbb R$,
--
--   $$
--   \Pr[(y,u)\in B\times B']=\mathrm{Leb}(B'\cap[0,1])\cdot\frac1{(2\pi)^n}\int_B\operatorname{tr}\big(D(y)\tau D(y)^\dagger\rho\big)\,d^{2n}y .
--   $$
--
--   A measurement scheme **uses exclusively Gaussian measurements** if the POVM of every round, after every history of earlier outcomes, is a Gaussian measurement.
--
--   **Formalization Note** The density $\operatorname{tr}(D(y)\tau D(y)^\dagger\rho)$ is an iterated series over the Fock basis; the integral is a lower Lebesgue integral, so no integrability side condition can make it vanish. Rectangles $B\times B'$ determine the outcome law.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), §2.2, printed p. 10 (PDF p. 13); Theorems 3.4, 3.6, pp. 16–17 (PDF pp. 19–20)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_BosonicLearn_AdaptiveScheme
import Definitions.Def_AgnGaussTomo_dispOp

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (GaussianAt OscillatorCovariance)
open MeasureTheory

namespace AgnGaussTomo

/-- **A Gaussian measurement (with an independent uniform seed).** Arulandu, Chen, Chen, Li, Ma,
*Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), §2.2,
printed p. 10 (PDF p. 13): "Gaussian measurements … are POVMs of the form
M(d^{2n}y) = 1/(2π)^n D(y) τ D(y)† d^{2n}y, where τ is a mean-zero Gaussian state known as the seed
state, and its covariance W is known as the seed covariance."

A POVM `M` with outcomes `(y, u) ∈ ℝ^{2n} × ℝ` is Gaussian if there is a mean-zero Gaussian seed
state `τ` such that, for every density operator `ρ` and all measurable `B ⊆ ℝ^{2n}`, `B' ⊆ ℝ`,

  `P[(y, u) ∈ B × B'] = Leb(B' ∩ [0, 1]) · (2π)^{-n} ∫_B tr(D(y) τ D(y)† ρ) d^{2n}y`,

i.e. `y` is the outcome of the Gaussian measurement with seed `τ` and `u` is an independent uniform
random number in `[0, 1]`.

**Formalization Note.** `y` is indexed in the grouped order (`inl j` = `q_j`, `inr j` = `p_j`);
`D(y)` is `dispOp y`. The second coordinate is classical randomness, free in the paper's
algorithm model (Proposition 2.9's and Lemma 2.10's estimators are randomized); it carries no
quantum information. Heterodyne (`τ = |0⟩⟨0|`) and a Gaussian unitary followed by heterodyne (seed
`U†|0⟩⟨0|U`, outcomes relabelled by the affine map of `U`, p. 10) are in this class. The
probability density `tr(D(y)τD(y)†ρ)` is the iterated Fock-basis series below (real part, since it
is real for densities); the integral is a lower Lebesgue integral of its `ENNReal.ofReal`, so no
integrability side condition can make it vanish. Rectangles determine the law. -/
def IsGaussianPOVM {n : ℕ}
    (M : BosonicLearn.FockPOVM (Occupation (Fin n)) ((Fin n ⊕ Fin n → ℝ) × ℝ)) : Prop :=
  ∃ (τ : State (Occupation (Fin n))) (W : OscillatorCovariance (Fin n)),
    GaussianAt τ.coefficients 0 W ∧
    ∀ ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ, IsDensity ρ →
      ∀ (B : Set (Fin n ⊕ Fin n → ℝ)) (B' : Set ℝ), MeasurableSet B → MeasurableSet B' →
        M.law ρ (B ×ˢ B') = volume (B' ∩ Set.Icc 0 1) *
          ∫⁻ y in B, ENNReal.ofReal (((2 * Real.pi) ^ n)⁻¹ *
            (∑' u, ∑' v, (∑' a, ∑' b, dispOp y u a * τ.coefficients a b *
              star (dispOp y v b)) * ρ v u).re)

/-- **A scheme that uses exclusively Gaussian measurements** (Theorems 3.4 and 3.6, printed
pp. 16–17: "uses exclusively Gaussian measurements"): every round's POVM, after every record of
earlier outcomes, is a Gaussian measurement in the sense of `IsGaussianPOVM`. -/
def IsGaussianScheme {n N : ℕ}
    (S : BosonicLearn.AdaptiveScheme n N ((Fin n ⊕ Fin n → ℝ) × ℝ)) : Prop :=
  ∀ (t : Fin N) (x : Fin t → (Fin n ⊕ Fin n → ℝ) × ℝ), IsGaussianPOVM (S.povm t x)

end AgnGaussTomo


