-- Prove2me | Definitions.Def_BosonicResources_IsGaussianMeasurement
-- name    : BosonicResources_IsGaussianMeasurement
-- status  : Definition
-- author  : @Senrui Chen
-- created : 2026-11-27T05:37:22.237455+00:00
-- url     : https://prove2.me/theorems/551b5ebe-5876-4d0f-ad45-f0055d28299b
-- title:
--   Gaussian (general-dyne) measurements with seed covariance $V$, and adaptive Gaussian schemes
-- statement:
--   Let $\rho(\mu,\Sigma)$ denote the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$ (quadratures ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$, vacuum covariance $\tfrac12 I$), and let $V$ be a real $2n\times 2n$ matrix. A POVM $E$ on the $n$-mode system with outcomes $\xi\in\mathbb R^{2n}$ is a *Gaussian (general-dyne) measurement with seed covariance $V$* if its elements are $(2\pi)^{-n}\rho(\xi,V)\,d\xi$: for every measurable $B\subseteq\mathbb R^{2n}$ and all Fock states $\lvert u\rangle,\lvert v\rangle$,
--
--   $$
--   \langle u\rvert E(B)\lvert v\rangle=\frac{1}{(2\pi)^{n}}\int_{B}\langle u\rvert\rho(\xi,V)\lvert v\rangle\,d\xi ,
--   $$
--
--   where $\rho(\xi,V)$ is the Gaussian state with mean $\xi$ and covariance $V$ and $d\xi$ is Lebesgue measure.
--
--   An adaptive single-copy scheme on $N$ copies with outcomes in $\mathbb R^{2n}$ (the POVM of round $t$ may depend on the record $x$ of the earlier outcomes) is called a *Gaussian scheme* if every one of its POVMs is a Gaussian measurement with some seed covariance $V$, which may depend on $t$ and on $x$.
--
--   This is the paper's family $\{(2\pi)^{-n}D(\xi)\rho(0,V)D(\xi)^\dagger\}_{\xi\in\mathbb R^{2n}}$ with seed $\rho(0,V)$; heterodyne detection is the case $V=\tfrac12 I$. Gaussian measurements are the main examples of classical measurements; the definition is used in Theorem 1 and Theorem 5 (adaptive Gaussian schemes), Theorem 4 (heterodyne) and Theorem 7 (non-adaptive schemes).
--
--   **Formalization Note** The displaced seed $D(\xi)\rho(0,V)D(\xi)^\dagger$ is the Gaussian state with covariance $V$ and mean $\pm\xi$ (the sign depends on the convention for $\hat D$); outcomes are labelled so that the element at $\xi$ is $\rho(\xi,V)$, the labelling for which the outcome law on $\rho(\mu,\Sigma)$ is $\mathcal N(\mu,\Sigma+V)$ as the paper states. A Gaussian state is determined by its mean and covariance, so the family $\xi\mapsto\rho(\xi,V)$ is unique. Existence of a Gaussian state with covariance $V$ is the condition $V+\tfrac i2\Omega\succeq0$; if $V$ is not a valid covariance, no POVM satisfies the predicate. Homodyne detection is the limit of such seeds and is not itself of this form. The file contains two predicates: `IsGaussianMeasurement E V` on a `BosonicLearn.FockPOVM`, and `IsGaussianScheme S` on a `BosonicLearn.AdaptiveScheme`.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 2 (Gaussian / general-dyne measurements, heterodyne and homodyne); Sec. 3.3, Theorem 5; Sec. 3.4; App. D.1, Theorem S8

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicLearn_AdaptiveScheme

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn (FockPOVM IsGaussianState AdaptiveScheme)

open MeasureTheory

namespace BosonicResources

/-- **Gaussian (general-dyne) measurement with seed covariance `V`.**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, §2: "The most well-known example of classical measurements are Gaussian
measurements (or, general-dyne measurements), which is of the form {(2π)^{-n} D(ξ) ρ(0,V) D(ξ)†}_{ξ∈ℝ^{2n}} where
ρ(0,V) is a Gaussian state (thus V + (i/2)Ω ≥ 0) called the seed of this measurement. The outcome distribution
obtained by applying a Gaussian measurement with seed covariance matrix V on a Gaussian state ρ(µ,Σ) is given by
N(µ, Σ+V). Two examples … are heterodyne measurements (V = ½ I_{2n}) and homodyne measurements".

`IsGaussianMeasurement E V` says the POVM `E` on the `n`-mode Fock space, with outcomes `ξ ∈ ℝ²ⁿ` (grouped order),
has the elements `(2π)^{-n} ρ(ξ, V) dξ`: there is a family of density operators `ρ(ξ, V)`, the Gaussian state with
mean `ξ` and covariance `V` for every `ξ`, and for every measurable `B ⊆ ℝ²ⁿ`

`E(B)_{uv} = (2π)^{-n} ∫_B ρ(ξ, V)_{uv} dξ` (Lebesgue measure).

**Formalization Note.** The displaced seed `D(ξ) ρ(0,V) D(ξ)†` is the Gaussian state with covariance `V` and mean
`±ξ` (the sign depends on the convention for `D̂`); outcomes are labelled so that the element at `ξ` is `ρ(ξ, V)`, the
labelling for which the outcome law on `ρ(µ, Σ)` is `N(µ, Σ + V)` as the paper states. A Gaussian state is determined
by its mean and covariance, so the family is unique. Existence of a Gaussian state with covariance `V` is the
condition `V + (i/2)Ω ⪰ 0`; if `V` is not a valid covariance no POVM satisfies the predicate. Homodyne detection is
the limit of such seeds and is not itself of this form. -/
def IsGaussianMeasurement {n : ℕ}
    (E : FockPOVM (Occupation (Fin n)) (EuclideanSpace ℝ (Fin n ⊕ Fin n)))
    (V : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) : Prop :=
  ∃ seed : EuclideanSpace ℝ (Fin n ⊕ Fin n) → State (Occupation (Fin n)),
    (∀ ξ, IsGaussianState (seed ξ) (WithLp.ofLp ξ) V) ∧
    ∀ B : Set (EuclideanSpace ℝ (Fin n ⊕ Fin n)), MeasurableSet B → ∀ u v : Occupation (Fin n),
      E.effect B u v =
        ((1 / (2 * Real.pi) ^ n : ℝ) : ℂ) * ∫ ξ in B, (seed ξ).coefficients u v

/-- **Adaptive single-copy Gaussian measurement schemes.**
arXiv:2603.18136, Theorem 5 ("this can be achieved by Gaussian measurements"), Theorem S8 ("a protocol using adaptive
general-dyne measurements"), §3.4 ("non-entangling (i.e., single-copy) Gaussian measurements").

`IsGaussianScheme S` says every measurement of the adaptive single-copy scheme `S` (round `t`, after earlier outcomes
`x`) is a Gaussian measurement with some seed covariance `V`, which may depend on `t` and on `x`. -/
def IsGaussianScheme {n N : ℕ} (S : AdaptiveScheme n N (EuclideanSpace ℝ (Fin n ⊕ Fin n))) : Prop :=
  ∀ (t : Fin N) (x : Fin t → EuclideanSpace ℝ (Fin n ⊕ Fin n)),
    ∃ V : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, IsGaussianMeasurement (S.povm t x) V

end BosonicResources


