-- Prove2me | Definitions.Def_GaussOptCVQKD_MeasurementModel
-- name    : GaussOptCVQKD_MeasurementModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:22.561571+00:00
-- url     : https://prove2.me/theorems/ea829b0e-019c-426f-9aad-739f8be55618
-- title:
--   Homodyne and heterodyne measurements on oscillator modes, the joint outcome law $p(a,b)$ and the Shannon mutual information $S(a{:}b)$
-- statement:
--   **Setting (pp.1–2).** Alice and Bob share a state $\rho_{AB}$ of finitely many bosonic modes; each mode belongs to Alice or to Bob. Each party applies one measurement to all of its modes: **homodyne $x$**, **homodyne $p$** (one real outcome per mode) or **heterodyne** (the coherent-state POVM $\pi^{-1}|\alpha\rangle\langle\alpha|$, two real outcomes per mode). Alice's outcome is $a$, Bob's is $b$.
--
--   **Outcome law ((2), p.2).** The joint law $p(a,b)$ of the outcomes is the probability measure $\mu$ on Alice's outcomes $\times$ Bob's outcomes whose characteristic function is given by the Born rule:
--   $$
--   \int e^{i(\eta_A\cdot a+\eta_B\cdot b)}\,d\mu(a,b)=\operatorname{Tr}\bigl(\rho\,W(\xi_{\eta_A,\eta_B})\bigr)\prod_{\text{heterodyne parties}}e^{-|\eta|^2/4},
--   $$
--   where $W(\xi)=e^{i\xi\cdot R}$ is the Weyl operator and $\xi_{\eta_A,\eta_B}$ places the frequencies on the measured quadratures and $0$ elsewhere. For homodyne detection this is the law of the measured (commuting) quadratures; for heterodyne the Husimi law of $(x,p)$.
--
--   **Mutual information (p.2).** $S(a{:}b)=I_{ab}=D\bigl(\mu\,\|\,\mu_a\otimes\mu_b\bigr)$, the Kullback–Leibler divergence of the joint law from the product of its marginals, in nats, valued in $[0,\infty]$.
--
--   **Formalization Note** Quadratures follow the published oscillator layer (Support50.P14): $x=(a+a^\dagger)/\sqrt2$, vacuum covariance $I$, interleaved coordinates $(j,0)=x_j$, $(j,1)=p_j$. A heterodyne outcome $\alpha$ is recorded as $(\sqrt2\,\mathrm{Re}\,\alpha,\sqrt2\,\mathrm{Im}\,\alpha)$, an invertible linear relabelling. The law is characterized by its characteristic function rather than by a pointwise Born series (which need not converge absolutely for trace-class $\rho$). The mutual information is an infimum over all laws satisfying the relation (there is exactly one for a density); when none does, its value is $+\infty$, never $0$.
-- source:
--   García-Patrón, Cerf, Unconditional optimality of Gaussian attacks against continuous-variable QKD, arXiv:quant-ph/0608032v1, 'Physical model of measurement' p.1, (2) p.2 and 'Entanglement-based version of CV-QKD' p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open MeasureTheory
open scoped ENNReal
open QAlgorithms.Papers.Independent.Support50.P14 (OscillatorKernel InterleavedQuadrature oscillatorCharacteristic)

namespace GaussOptCVQKD

/-- **The measurement a party performs on its modes**, García-Patrón, Cerf, *Unconditional
optimality of Gaussian attacks against continuous-variable QKD*, arXiv:quant-ph/0608032v1,
"Entanglement-based version of CV-QKD", p.2: "homodyne measurements, corresponding to the
preparation of squeezed states, or heterodyne measurements, corresponding to the preparation of
coherent states (a then collectively denotes two real numbers)".

`homodyneX` reads the `x` quadrature, `homodyneP` the `p` quadrature, `heterodyne` both (the
coherent-state POVM `(1/π)|α⟩⟨α|`).

**Formalization Note** A party applies one choice to every mode it owns (p.3, under (7): "Alice
(Bob) do the same measurement on her (his) N modes"). -/
inductive Measurement
  | homodyneX
  | homodyneP
  | heterodyne
  deriving DecidableEq

/-- Which canonical coordinate a measurement reads out: coordinate `0` is `x`, coordinate `1` is
`p` (the interleaved convention of the published oscillator layer Support50.P14). -/
def Measurement.reads : Measurement → Fin 2 → Bool
  | .homodyneX, k => decide (k = 0)
  | .homodyneP, k => decide (k = 1)
  | .heterodyne, _ => true

/-- **Reconciliation direction**, arXiv:quant-ph/0608032v1, p.1: "either direct reconciliation
(DR), where Bob corrects his data to Alice's ones, or reverse reconciliation (RR), where Alice's
and Bob's roles are interchanged". -/
inductive Reconciliation
  | direct
  | reverse
  deriving DecidableEq

/-- The canonical coordinates `(j, k)` (mode `j`, quadrature `k`) read out by party `p`
(`0` = Alice, `1` = Bob) when party `p'` uses `choice p'`. -/
def measuredCoords {I : Type} [Fintype I] (owner : I → Fin 2) (choice : Fin 2 → Measurement)
    (p : Fin 2) : Finset (I × Fin 2) :=
  Finset.univ.filter (fun q => owner q.1 = p ∧ (choice p).reads q.2 = true)

/-- **The outcome of party `p`**: one real number per measured coordinate. Homodyne gives one
real number per mode, heterodyne two ("a then collectively denotes two real numbers", p.2).

**Formalization Note** A heterodyne outcome `α ∈ ℂ` is recorded as `(√2 Re α, √2 Im α)`, the
coherent-state quadrature means in the convention `x = (a + a†)/√2`; this is an invertible linear
relabelling of the outcome, which changes neither mutual informations nor Holevo quantities. -/
abbrev PartyOutcome {I : Type} [Fintype I] (owner : I → Fin 2) (choice : Fin 2 → Measurement)
    (p : Fin 2) : Type :=
  measuredCoords owner choice p → ℝ

open Classical in
/-- The Weyl argument `ξ ∈ ℝ^{I × {x,p}}` that places a frequency vector `η` of party `p`'s
outcome on the measured coordinates and `0` elsewhere. -/
noncomputable def embedOutcome {I : Type} [Fintype I] (owner : I → Fin 2)
    (choice : Fin 2 → Measurement) (p : Fin 2) (η : PartyOutcome owner choice p) :
    InterleavedQuadrature I → ℝ :=
  fun q => if h : q ∈ measuredCoords owner choice p then η ⟨q, h⟩ else 0

/-- The Euclidean pairing `η · a` of a frequency vector and an outcome. -/
def pairing {I : Type} [Fintype I] {owner : I → Fin 2} {choice : Fin 2 → Measurement}
    {p : Fin 2} (η a : PartyOutcome owner choice p) : ℝ :=
  ∑ q, η q * a q

/-- The vacuum-noise factor of heterodyne detection: `exp(−|η|²/4)` when party `p` measures
heterodyne, `1` for homodyne. It is the factor by which the characteristic function of the
heterodyne outcome `(x_Q, p_Q)` differs from the Weyl characteristic function of the state
(antinormal versus symmetric ordering, vacuum covariance `I`). -/
noncomputable def heterodyneFactor {I : Type} [Fintype I] {owner : I → Fin 2}
    (choice : Fin 2 → Measurement) (p : Fin 2) (η : PartyOutcome owner choice p) : ℝ :=
  if choice p = .heterodyne then Real.exp (-(∑ q, η q ^ 2) / 4) else 1

/-- **The joint outcome law `p(a, b)` of Alice's and Bob's measurements on `ρ_AB`**,
arXiv:quant-ph/0608032v1, (2), p.2: `ρ_ab = ∫ da db p(a,b) |a⟩⟨a| ⊗ |b⟩⟨b|`.

`μ` is a probability measure on Alice's outcomes × Bob's outcomes whose characteristic function is
the Born-rule one: for all frequency vectors `η_A`, `η_B`,
`∫ exp(i(η_A·a + η_B·b)) dμ = Tr(ρ W(ξ)) · (heterodyne factors)`, where `W(ξ)` is the Weyl
operator at the embedded frequencies. For homodyne detection this is the joint law of the commuting
measured quadratures; for heterodyne the Husimi law of `(x, p)`.

**Formalization Note** The law is characterized through its characteristic function (Lévy
uniqueness makes it unique), not through a pointwise Born density: a pointwise series
`Σ_{u,v} ⟨a|u⟩ρ_{uv}⟨v|a⟩` need not converge absolutely for a trace-class `ρ`. -/
def IsOutcomeLaw {I : Type} [Fintype I] (owner : I → Fin 2) (choice : Fin 2 → Measurement)
    (ρ : OscillatorKernel I)
    (μ : Measure (PartyOutcome owner choice 0 × PartyOutcome owner choice 1)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (ηA : PartyOutcome owner choice 0) (ηB : PartyOutcome owner choice 1),
      ∫ ω, Complex.exp (Complex.I * ((pairing ηA ω.1 + pairing ηB ω.2 : ℝ) : ℂ)) ∂μ =
        oscillatorCharacteristic ρ (embedOutcome owner choice 0 ηA + embedOutcome owner choice 1 ηB) *
          ((heterodyneFactor choice 0 ηA * heterodyneFactor choice 1 ηB : ℝ) : ℂ)

/-- **The Shannon mutual information `I_ab = S(a:b)` of the outcomes**, arXiv:quant-ph/0608032v1,
p.2: "The quantum mutual entropy S(a:b) then simply reduces to the Shannon mutual information I_ab
between the preparer's and the measurer's internal states."

`I(a:b) = D(μ ‖ μ_a ⊗ μ_b)` in nats, for the outcome law `μ` of `IsOutcomeLaw`.

**Formalization Note** Written as an infimum over all laws satisfying `IsOutcomeLaw` (there is
exactly one when `ρ` is a density), valued in `[0, ∞]`. If no law satisfies it (e.g. `ρ` is not a
density) the value is `⊤`, never a junk `0`; a finiteness conclusion therefore also asserts that
the outcome law exists. -/
noncomputable def mutualInfo {I : Type} [Fintype I] (owner : I → Fin 2)
    (choice : Fin 2 → Measurement) (ρ : OscillatorKernel I) : ℝ≥0∞ :=
  ⨅ (μ : Measure (PartyOutcome owner choice 0 × PartyOutcome owner choice 1))
    (_ : IsOutcomeLaw owner choice ρ μ),
    InformationTheory.klDiv μ ((μ.map Prod.fst).prod (μ.map Prod.snd))

end GaussOptCVQKD


