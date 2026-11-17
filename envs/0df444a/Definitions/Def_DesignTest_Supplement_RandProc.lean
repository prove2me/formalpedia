-- Prove2me | Definitions.Def_DesignTest_Supplement_RandProc
-- name    : DesignTest_Supplement_RandProc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:03:20.666014+00:00
-- url     : https://prove2.me/theorems/ffff12ae-1839-43c5-83a3-a65f16034331
-- title:
--   Randomized testers and estimators with sample access
-- statement:
--   A **randomized procedure** with $m$ samples from an unknown law $\nu$ on $X$ first draws an internal seed $\omega$ from a probability space, independent of the samples. The seed selects a deterministic procedure of a given algorithm class, whose finite classical transcript $h$ has probability $p(h\mid\omega,x)$ given the sampled family $x=(x_1,\dots,x_m)$, $x_i\sim\nu$ i.i.d., and then the output $\mathrm{out}(\omega,h)$ is produced.
--
--   1. A **tester** has outputs in $[0,1]$ (acceptance probabilities) and accepts $\nu$ with probability $\mathbb E_{x\sim\nu^{\otimes m}}\mathbb E_\omega\sum_h p(h\mid\omega,x)\,\mathrm{out}(\omega,h)$.
--   2. An **estimator** of a quantity $F$ succeeds with accuracy $\varepsilon$ with probability $\mathbb E_{x}\mathbb E_\omega\sum_h p(h\mid\omega,x)\,\mathbf 1\{|\mathrm{out}(\omega,h)-F|\le\varepsilon\}$.
--
--   This is the guarantee of §3.2.4: for each fixed input law, probability over samples, internal randomness and measurement outcomes.
--
--   **Formalization Note.** Seeds and finite-outcome measurements: the randomized wrapper `RandProc` draws an internal seed from an arbitrary probability space before any sample, and every measurement has finitely many outcomes; by Chiribella–D'Ariano–Schlingemann (PRL 98, 190403, 2007) a measurement with a continuum of outcomes on a finite-dimensional system is a randomization of finite-outcome ones followed by classical post-processing. Measurability of $p$ in $(\omega,x)$ and of the output in $\omega$ is required.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), §3.2, p.14; §3.2.4, p.16; Problem 6.1, p.77

import Mathlib

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory

/-- **A randomized testing/estimation procedure** with sample access to `m` independent draws from an
unknown law on `X` (A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027
submission (sha256 e2f0a429…), §3.2, p.14; §3.2.4, p.16).

Before any sample is seen, an internal random seed `ω ∈ Ω` is drawn from the probability measure `P`
("Choices fixed in advance may depend on initial classical randomness independent of the sampled
processes", p.15). The seed selects a deterministic procedure `alg ω : D` of some algorithm class, whose
classical transcript `h ∈ H` (a finite set) has probability `prob (alg ω) x h` given the sampled family
`x : Fin m → X`. The procedure then outputs `out ω h`: an acceptance probability in `[0, 1]` for a tester,
an estimate for an estimator. Final randomized post-processing is a function of the seed, which may be
drawn in advance.

**Formalization Note.** The seed space is an arbitrary probability space; measurability of the
transcript probabilities in `(ω, x)` and of the outputs in `ω` is required so that the averaged
probabilities below are genuine integrals. Measurements have finitely many outcomes per step; a
measurement with a continuum of outcomes on a finite-dimensional system is a randomization of
finite-outcome measurements followed by classical post-processing (Chiribella–D'Ariano–Schlingemann,
PRL 98, 190403, 2007), which the seed and `out` provide. -/
structure RandProc (X : Type) [MeasurableSpace X] (m : ℕ) (D : Type) (H : Type) [Fintype H]
    (prob : D → (Fin m → X) → H → ℝ) where
  /-- the seed space -/
  Ω : Type
  /-- its σ-algebra -/
  [mΩ : MeasurableSpace Ω]
  /-- the law of the seed -/
  P : Measure Ω
  /-- the law of the seed is a probability measure -/
  [isProb : IsProbabilityMeasure P]
  /-- the deterministic procedure selected by the seed -/
  alg : Ω → D
  /-- the output on seed `ω` and transcript `h` -/
  out : Ω → H → ℝ
  /-- transcript probabilities are jointly measurable in the seed and the samples -/
  meas_prob : ∀ h, Measurable fun z : Ω × (Fin m → X) => prob (alg z.1) z.2 h
  /-- outputs are measurable in the seed -/
  meas_out : ∀ h, Measurable fun ω => out ω h

attribute [instance] RandProc.mΩ RandProc.isProb

namespace RandProc

variable {X : Type} [MeasurableSpace X] {m : ℕ} {D H : Type} [Fintype H]
  {prob : D → (Fin m → X) → H → ℝ}

/-- A **tester**: every output is an acceptance probability in `[0, 1]`. -/
def IsTester (T : RandProc X m D H prob) : Prop := ∀ ω h, 0 ≤ T.out ω h ∧ T.out ω h ≤ 1

/-- The **acceptance probability** on the input law `ν`: the samples `x_1, …, x_m` are independent draws
from `ν`, then the seed, the transcript and the output decide
(`E_{x∼ν^{⊗m}} E_ω Σ_h prob(h | ω, x) · out(ω, h)`). -/
noncomputable def acceptProb (T : RandProc X m D H prob) (ν : Measure X) : ℝ :=
  ∫ x, ∫ ω, ∑ h, prob (T.alg ω) x h * T.out ω h ∂T.P ∂(Measure.pi fun _ : Fin m => ν)

/-- The **success probability of an estimator** for the target value `F` with accuracy `ε`: the
probability that the output `F̂` satisfies `|F̂ − F| ≤ ε` (STOC 2027 submission (sha256 e2f0a429…),
Problem 6.1, p.77). -/
noncomputable def successProb (T : RandProc X m D H prob) (ν : Measure X) (F ε : ℝ) : ℝ :=
  ∫ x, ∫ ω, ∑ h, prob (T.alg ω) x h * (if |T.out ω h - F| ≤ ε then 1 else 0) ∂T.P
    ∂(Measure.pi fun _ : Fin m => ν)

end RandProc

end DesignTest.Supplement


