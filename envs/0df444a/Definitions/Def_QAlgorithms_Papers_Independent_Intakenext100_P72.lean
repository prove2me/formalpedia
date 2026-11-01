-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P72
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P72
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:43:30.042628+00:00
-- url     : https://prove2.me/theorems/fd9a1ed2-3d10-47cd-a844-36fb8158e808
-- title:
--   Definitions for Reverse reconciliation protocols for quantum cryptography with continuous variables
-- statement:
--   The objects the formalized statements of *Reverse reconciliation protocols for quantum cryptography with continuous variables* (arXiv:quant-ph/0204127) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `aliceVarianceExpression`: PDF p.3, (22)--(23): the explicit Alice residual-variance expression. This is a formula, not a replacement definition of the regression minimum.
--   - `eveVarianceExpression`: PDF pp.3--4, (26)--(27), (38)--(39): the crossed-quadrature Eve bound expression; G and chi belong to the conjugate quadrature.
--   - `varianceProduct`: PDF p.4, (44): the dimensionless symmetric variance-product expression.
--   - `balanceExpression`: PDF p.4, (48): the signed Gaussian-model expression, in bits per compatible-basis measurement. Its identification with measured information is a separate deferred result; this definition makes no extraction claim.
--   - `eprExpression`: PDF p.5, (54): half of the compatible-basis expression at s=1/V, accounting for the EPR protocol's independent random basis choices.
--   - `coherentExpression`: PDF p.5, (56): the coherent expression at s=1, with no basis penalty.
--   - `lossExpression`: PDF p.5, (55): the common signed pure-loss expression.
--   - `noiseThreshold`: PDF p.4, (52): the positive root bounding the added output noise G*chi.
--   - `strongLossCoefficient`: PDF p.5, (59): the strong-loss coefficient at finite modulation, prior to the large-modulation limit.
--   - `coherentExcessThreshold`: PDF p.5, IV.B: the sufficient coherent-state excess-noise threshold.
--   - `eprExcessThreshold`: PDF p.5, IV.B: the sufficient EPR excess-noise threshold.
-- source:
--   Reverse reconciliation protocols for quantum cryptography with continuous variables, arXiv:quant-ph/0204127v1, https://arxiv.org/abs/quant-ph/0204127v1

import Mathlib

/-!
Grosshans--Grangier, arXiv:quant-ph/0204127v1, PDF pp.4--5.
Only the independently pinned algebraic and asymptotic results are stated here.
The named balance functions are explicitly the signed ANALYTIC EXPRESSIONS in
(48), (54), and (56), not definitions of mutual information, security, or
achievable key rates. The missing identification with actual measured laws is
recorded under #eq45-48 in HARD.md. No quantum or operational conclusion is
asserted by assigning these expressions names. Shot noise cancels from them.
Compilation is pending the requested batch handoff.
-/

noncomputable section

open Filter
open scoped Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P72

/-- PDF p.3, (22)--(23): the explicit Alice residual-variance expression.
This is a formula, not a replacement definition of the regression minimum. -/
def aliceVarianceExpression (G chi s N0 : ℝ) : ℝ :=
  G * (chi + s) * N0

/-- PDF pp.3--4, (26)--(27), (38)--(39): the crossed-quadrature Eve
bound expression; G and chi belong to the conjugate quadrature. -/
def eveVarianceExpression (G chi V N0 : ℝ) : ℝ :=
  N0 / (G * (chi + 1 / V))

/-- PDF p.4, (44): the dimensionless symmetric variance-product expression. -/
def varianceProduct (G chi V s : ℝ) : ℝ :=
  (G * chi + G * s) * (G * chi + G / V)

/-- PDF p.4, (48): the signed Gaussian-model expression, in bits per
compatible-basis measurement. Its identification with measured information
is a separate deferred result; this definition makes no extraction claim. -/
def balanceExpression (G chi V s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (1 / varianceProduct G chi V s)

/-- PDF p.5, (54): half of the compatible-basis expression at s=1/V,
accounting for the EPR protocol's independent random basis choices. -/
def eprExpression (G chi V : ℝ) : ℝ :=
  (1 / 2 : ℝ) * balanceExpression G chi V (1 / V)

/-- PDF p.5, (56): the coherent expression at s=1, with no basis penalty. -/
def coherentExpression (G chi V : ℝ) : ℝ :=
  balanceExpression G chi V 1

/-- PDF p.5, (55): the common signed pure-loss expression. -/
def lossExpression (G V : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (1 / (1 - G * (1 - 1 / V)))

/-- PDF p.4, (52): the positive root bounding the added output noise G*chi. -/
def noiseThreshold (G s : ℝ) : ℝ :=
  (Real.sqrt (G ^ 2 * s ^ 2 + 4) - G * s) / 2

/-- PDF p.5, (59): the strong-loss coefficient at finite modulation,
prior to the large-modulation limit. -/
def strongLossCoefficient (V : ℝ) : ℝ :=
  (1 - 1 / V) / (2 * Real.log 2)

/-- PDF p.5, IV.B: the sufficient coherent-state excess-noise threshold. -/
def coherentExcessThreshold (V : ℝ) : ℝ :=
  (V - 1) / (2 * V)

/-- PDF p.5, IV.B: the sufficient EPR excess-noise threshold. -/
def eprExcessThreshold (V : ℝ) : ℝ :=
  (V - 1) / V

example (N0 : ℝ) : aliceVarianceExpression 1 0 1 N0 = N0 := by
  simp [aliceVarianceExpression]

example (N0 : ℝ) : eveVarianceExpression 1 0 1 N0 = N0 := by
  simp [eveVarianceExpression]

example : varianceProduct 1 0 1 1 = 1 := by
  norm_num [varianceProduct]

example : balanceExpression 1 0 1 1 = 0 := by
  norm_num [balanceExpression, varianceProduct]

example (G chi V : ℝ) :
    eprExpression G chi V = (1 / 2 : ℝ) * balanceExpression G chi V (1 / V) := by
  rfl

example (G chi V : ℝ) : coherentExpression G chi V = balanceExpression G chi V 1 := by
  rfl

example (V : ℝ) : lossExpression 0 V = 0 := by
  simp [lossExpression]

example (s : ℝ) : noiseThreshold 0 s = 1 := by
  norm_num [noiseThreshold]

example : strongLossCoefficient 1 = 0 := by
  simp [strongLossCoefficient]

example : coherentExcessThreshold 1 = 0 := by
  norm_num [coherentExcessThreshold]

example : eprExcessThreshold 1 = 0 := by
  norm_num [eprExcessThreshold]

end QAlgorithms.Papers.Independent.Intakenext100.P72


