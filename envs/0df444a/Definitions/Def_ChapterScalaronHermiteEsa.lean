-- Prove2me | Definitions.Def_ChapterScalaronHermiteEsa
-- name    : ChapterScalaronHermiteEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:47:42.599552+00:00
-- url     : https://prove2.me/theorems/f67757e6-0203-4919-81f2-706118093632
-- title:
--   Chapter ScalaronHermiteEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterScalaronHermiteEsa.lean`): generated def bundle for ChapterScalaronHermiteEsa. See BookProof/ChapterScalaronHermiteEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronHermiteEsa.lean

import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Mathlib


/-!
# The exponentially growing scalaron potential is essentially self-adjoint on the
Gauss–polynomial (Hermite) core

`CONSOLIDATED_PLAN.md` §10.6.1 target 4 asks for **essential** self-adjointness on the
Gauss–polynomial core of `L²(ℝᵈ)` for the potentials of the gauge-fixed `R + αR²`
Hamiltonian.  `BookProof.ChapterQgHermiteOscillatorEsa` settles the conformal-mode
(harmonic) potential `‖x‖²/4`, and, by Kato–Rellich, harmonic-plus-*bounded*; the
Starobinsky scalaron potential

`V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²`

is neither, since it grows **exponentially** as `φ → −∞`.  On the compactly supported
smooth core the exponential wall was already shown to be harmless
(`BookProof.ChapterScalaronCoreEsa`), but that core is not the core the Hermite/SIRK
numerics work in.

This module removes the restriction for the **potential term** on the *Hermite* core: for
every continuous, exponentially bounded real potential `W` on `ℝᵈ` — in particular for the
scalaron potential and for the full two-variable sector potential `V₃(R_c) + V(φ)` —
multiplication by `W` is essentially self-adjoint on the Gauss–polynomial core.

## The argument

A deficiency vector `w ∈ L²` at a non-real `z` satisfies `∫ p e^{−‖x‖²/4} (W − z) w = 0`
for every polynomial `p`.  The function `u = (W − z)w` is *not* in `L²` (it is only in
`L²_loc`, `W` being unbounded), so the moment lemma of
`BookProof.ChapterHermiteProductCore` does not apply verbatim.  What does survive — and is
all the Fourier argument ever needed — is `GaussExpDecay u`: `e^{c‖x‖}e^{−‖x‖²/4}u` is
integrable for *every* `c`, because `|u| ≤ C e^{c‖x‖}|w|` and the Gaussian beats every
exponential while `w ∈ L²`.  Under that hypothesis the Fourier transform of `e^{−‖x‖²/4}u`
is given by an everywhere convergent power series whose coefficients are the (vanishing)
moments, hence is identically zero, hence `u = 0` a.e.; and `W − z ≠ 0` pointwise because
`W` is real and `z` is not, so `w = 0`.

## What is proved

* `GaussExpDecay`, `gaussExpDecay_of_memLp_mul`, `integrable_pgFun_mul_of_gaussExpDecay` —
  the growth class replacing `MemLp _ 2` in the moment argument;
* `fourier_gaussD_mul_eq_zero_of_gaussExpDecay`, `ae_eq_zero_of_moments_of_gaussExpDecay` —
  the generalized moment/Fourier uniqueness lemma;
* `potCore_deficiencyTrivialAt`, `potCore_essentiallySelfAdjoint` — the headline statement,
  for an arbitrary continuous exponentially bounded real potential;
* `scalaronPot_essentiallySelfAdjoint`, `scalaronSector_essentiallySelfAdjoint` — the two
  instances the plan asks for (the one-variable scalaron potential and the reduced
  `(R_c, φ)` sector potential `V₃ + V`);
* `potCore_stone_flow`, `scalaronPot_stone_flow`, `scalaronSector_stone_flow` — the
  self-adjoint realization and the unitary group it generates, obtained from essential
  self-adjointness rather than from a choice of extension.

**Honest boundary.**  What is proved here is essential self-adjointness of the *potential*
term on the Hermite core, for exponentially growing potentials.  The sum `−Δ + V` on the
Hermite core with the exponential scalaron potential is *not* claimed: §10.6.1 target 4 for
the full Hamiltonian remains open (the Friedrichs extension of
`BookProof.ChapterQgHermiteFriedrichs` continues to be what is available there).
-/

namespace BookProof.ScalaronHermiteEsa

open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

/-! ## 1. The growth class -/

/-- `u` has **Gaussian exponential decay**: multiplied by the Gaussian `e^{−‖x‖²/4}` it stays
integrable against every exponential `e^{c‖x‖}`.  This is the hypothesis under which the
moment/Fourier argument of `BookProof.ChapterHermiteProductCore` works; it is strictly
weaker than `MemLp u 2` in the direction that matters here — `u` may grow exponentially. -/
def GaussExpDecay (u : Vd d → ℂ) : Prop :=
  ∀ c : ℝ, Integrable (fun x : Vd d => ((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) * u x)











/-! ## 2. The generalized moment lemma -/





/-! ## 3. Essential self-adjointness of the potential term -/















/-! ## 4. The scalaron instances -/

/-- The scalaron potential as a potential on `ℝ¹`. -/
def scalaronPot (M alpha : ℝ) (x : Vd 1) : ℝ := starobinskyV M alpha (x 0)















end

end BookProof.ScalaronHermiteEsa


