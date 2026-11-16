-- Prove2me | Definitions.Def_ProdMixedTomo_Supplement_NonAdaptiveAlg
-- name    : ProdMixedTomo_Supplement_NonAdaptiveAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:31:53.135198+00:00
-- url     : https://prove2.me/theorems/893ca8cb-b7a7-401d-9093-ba39aeacd745
-- title:
--   Non-adaptive single-copy measurement algorithms and their success probability
-- statement:
--   A **non-adaptive single-copy measurement algorithm** on $n$ qubits using $N$ copies consists of:
--   1. a probability space $(\Omega,P)$ of random seeds;
--   2. for each copy $i<N$ and seed $\omega$, a POVM $\bigl(M_i(\omega)(o)\bigr)_{o<K}$ on $\mathbb C^{2^n}$: positive semidefinite effects summing to the identity, measurable in $\omega$;
--   3. a decoder that, from $\omega$ and the outcomes $o=(o_0,\dots,o_{N-1})$, outputs Bloch vectors $c_1,\dots,c_n$ with $\|c_j\|\le1$, measurable in $\omega$; the output is the product mixed state $\hat\pi=\bigotimes_j\tfrac12(I+c_j\cdot\sigma)\in\mathcal M_n$.
--
--   Run on $\rho^{\otimes N}$, the seed is drawn first; given $\omega$ the outcomes are independent with $\Pr[o_i]=\operatorname{Re}\operatorname{tr}(\rho\,M_i(\omega)(o_i))$. The success probability for a threshold $\eta$ is
--   $$
--   \Pr[d_{\mathrm{tr}}(\rho,\hat\pi)\le\eta]=\int_\Omega\sum_{o}\prod_{i<N}\operatorname{Re}\operatorname{tr}\bigl(\rho\,M_i(\omega)(o_i)\bigr)\,\mathbf 1\bigl[d_{\mathrm{tr}}(\rho,\hat\pi(\omega,o))\le\eta\bigr]\,dP(\omega).
--   $$
--   The measurement on each copy is chosen before any outcome is seen (non-adaptive), may be any POVM on the whole $n$-qubit copy (entangled across qubits, any number of outcomes), and no running-time bound is imposed.
--
--   This is the algorithm class of the lower bound, Theorem 5.1.
--
--   **Formalization Note** One outcome alphabet $\{0,\dots,K-1\}$ for all copies loses nothing (pad with zero effects). A finite-dimensional POVM with an arbitrary outcome space is a randomization of finite-outcome POVMs followed by classical post-processing; this randomization and every random choice of the decoder are part of the seed, drawn in advance. Elements of $\mathcal M_n$ are exactly the products of $\tfrac12(I+c_j\cdot\sigma)$ with $\|c_j\|\le1$.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 5.1, p.34 (PDF p.36); proof of Theorem 5.1, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_ProdMixedTomo_States
import Definitions.Def_ProdMixedTomo_TraceDistance

open MeasureTheory
open scoped ComplexOrder

namespace ProdMixedTomo.Supplement

/-- A **non-adaptive single-copy measurement algorithm** on `n` qubits using `N` copies (the
algorithm class of Theorem 5.1). It draws a random seed `ω` from a probability space, then measures
copy `i` of `ρ^{⊗N}` with a POVM `(Mᵢ(ω)(o))_{o < K}` on `ℂ^{2ⁿ}` that depends on `ω` only, and
finally outputs a product mixed state `π̂ = ⨂ⱼ ½(I + cⱼ·σ)`, `‖cⱼ‖ ≤ 1`, computed from the seed and
the `N` outcomes.

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 5.1, p.34 (PDF p.36): "any algorithm using only non-adaptive single-copy measurements
… outputs π̂ ∈ M_n"; proof, p.38 (PDF p.40): "if the non-adaptive algorithm makes N measurements
and the distribution over outputs when given copies of ρ_b is denoted Q_b".

**Formalization Note.**
* The POVMs are arbitrary on the whole `n`-qubit space of one copy (entangled across qubits
  allowed, any number of outcomes): each effect is positive semidefinite and the effects sum to the
  identity. A common outcome alphabet `Fin K` loses nothing (pad with zero effects).
* A finite-dimensional POVM with any outcome space is a randomization of finite-outcome POVMs
  followed by classical post-processing; that randomization, and all randomness of the decoder, is
  part of the seed, drawn before any measurement. This is the whole class.
* Measurability in `ω` of the effects and of the decoder makes the success probability a genuine
  probability.
* The output is given by Bloch vectors in the closed unit ball, i.e. any element of `M_n`. -/
structure NonAdaptiveAlg (n N : ℕ) where
  /-- The seed space. -/
  Ω : Type
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- The seed law. -/
  seed : Measure Ω
  /-- The seed law is a probability measure. -/
  [isProb : IsProbabilityMeasure seed]
  /-- Size of the outcome alphabet. -/
  K : ℕ
  /-- The effect `Mᵢ(ω)(o)` applied to copy `i` given the seed `ω`. -/
  povm : Fin N → Ω → Fin K → QMat n
  /-- Effects are positive semidefinite. -/
  psd : ∀ i ω o, (povm i ω o).PosSemidef
  /-- Effects sum to the identity. -/
  complete : ∀ i ω, ∑ o, povm i ω o = 1
  /-- Effects are measurable in the seed. -/
  measurable_povm : ∀ i o x y, Measurable fun ω => povm i ω o x y
  /-- The Bloch vectors `cⱼ` of the output, from the seed and the outcomes. -/
  decoder : Ω → (Fin N → Fin K) → Fin n → Fin 3 → ℝ
  /-- The decoder is measurable in the seed. -/
  measurable_decoder : ∀ o, Measurable fun ω => decoder ω o
  /-- Every output Bloch vector has length at most `1`. -/
  ball : ∀ ω o j, ∑ k, decoder ω o j k ^ 2 ≤ 1

attribute [instance] NonAdaptiveAlg.mΩ NonAdaptiveAlg.isProb

/-- The output `π̂ = ⨂ⱼ ½(I + cⱼ·σ) ∈ M_n` of `A` on seed `ω` and outcomes `o`. -/
noncomputable def NonAdaptiveAlg.output {n N : ℕ} (A : NonAdaptiveAlg n N) (ω : A.Ω)
    (o : Fin N → Fin A.K) : QMat n :=
  prodMat fun j => qubitOf (A.decoder ω o j)

open Classical in
/-- `Pr[d_tr(ρ, π̂) ≤ η]` for `A` run on `N` copies of `ρ`: over the seed `ω`, then the outcomes
`o = (o₀, …, o_{N−1})`, independent given `ω` with `Pr[oᵢ] = Re tr(ρ Mᵢ(ω)(oᵢ))` (Born rule on
`ρ^{⊗N}`, one measurement per copy), then the output `π̂ = A.output ω o`. -/
noncomputable def succProb {n N : ℕ} (A : NonAdaptiveAlg n N) (ρ : QMat n) (η : ℝ) : ENNReal :=
  ∫⁻ ω, ∑ o : Fin N → Fin A.K, ENNReal.ofReal (∏ i, (ρ * A.povm i ω (o i)).trace.re) *
    (if dtr ρ (A.output ω o) ≤ η then 1 else 0) ∂A.seed

end ProdMixedTomo.Supplement


