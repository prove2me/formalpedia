-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
-- name    : Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:50:18.215063+00:00
-- url     : https://prove2.me/theorems/4bf23b2a-1f6c-4d71-9247-a2b4875cc760
-- title:
--   Quotient Param Nonneg
-- statement:
--   Definitions and structural lemmas for Quotient Param Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.Gaps.T0
structure SumDat (ι : Type*) where

  s : Finset ι

  l : ι → ℝ

  I : ι → ℝ

  N : ι → ℝ

  cD : ι → ℝ

  vQ : ι → ℝ

  be : ι → ℝ

  (R δ d D T c i g₀ rw : ℝ)

  (G PH Prw Pη Pd PD PQ DivisibilityWeightConstant RR γ₀ : ℝ)

  (L κ F' f r : ℝ)

  (aδ aF HF Hδ SS Λ' : ℝ)

  (ρ ρ' : ℝ)
namespace SumDat
variable {ι : Type*} (X : SumDat ι)
def rr (la : ι) : ℝ :=
  X.R * (X.I la + X.T * (X.c / (2 * X.i)) * X.N la) + X.cD la + (X.vQ la + X.ρ' * X.be la)
def P1 : ℝ := 60 * X.G + 180 * X.PH + 40 * X.PD
def P2 : ℝ := 5 * X.G * (X.f * X.r ^ 2) + X.Pd
def P3 : ℝ := X.Pη / 2
def P4 : ℝ := X.DivisibilityWeightConstant * (X.PD + X.PQ)
def lev : ℝ :=
  (X.D + 4) * (X.D + 1) * (3 * X.G + 9 * X.PH) * X.L + 5 * X.G * (X.f * X.r ^ 2) * X.T + Real.log X.δ
    + 1 / 2 * X.T * X.c * X.Pη
def totalNamed : ℝ :=
  X.d * (X.P1 * X.D ^ 2 * X.κ / X.T + X.P2 * X.T + X.P3 * X.T * X.c
    + X.P4 * (1 / X.T + X.RR ^ 2 * X.c) * X.κ / X.γ₀)
def total (PP : ℝ) : ℝ :=
  X.d * PP ^ 2 * (X.D ^ 3 * X.κ / X.T + X.T * X.c + (X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀)
    + X.d * PP ^ 3 * X.T
structure Ok : Prop where

  R0 : 0 ≤ X.R
  δ1 : 1 ≤ X.δ
  D1 : 1 ≤ X.D
  T1 : 1 ≤ X.T
  c0 : 0 ≤ X.c
  g0 : 0 ≤ X.g₀
  rw1 : 1 ≤ X.rw
  G0 : 0 ≤ X.G
  height_param_nonneg : 0 ≤ X.PH
  Pη0 : 0 ≤ X.Pη
  BaseRankDimension : 0 ≤ X.PD
  quotient_param_nonneg : 0 ≤ X.PQ
  f0 : 0 ≤ X.f
  L0 : 0 ≤ X.L
  κ0 : 0 ≤ X.κ
  γ0 : 0 < X.γ₀

  Rδ : X.R * X.δ ≤ X.d

  Tcg : X.T * X.c * X.g₀ ≤ 1

  PrwPH : X.Prw ≤ X.PH

  lrw : Real.log X.rw + 1 / 2 ≤ X.Prw * X.L

  lev1 : 2 * ∑ la ∈ X.s, X.I la * X.l la ≤
    X.δ * Real.log X.δ + 2 * X.SS + 2 * X.D * X.aF * (Real.log X.rw + 1 / 2) + 2 * X.HF

  lev2 : X.T * (X.c / X.i) * ∑ la ∈ X.s, X.N la * X.l la ≤
    X.T * X.c * X.g₀ * (X.Hδ + X.D * X.aδ * (Real.log X.rw + 1 / 2)) + X.T * X.c * X.δ * X.Pη

  SSle : X.SS ≤ X.δ * X.Λ'

  S4 : X.Λ' ≤ X.G * X.F'

  S3 : X.F' ≤ (X.D + 2) * X.L + 5 * (X.f * X.r ^ 2) * X.T

  S2 : X.T * X.L ≤ 2 * X.κ

  lδ : Real.log X.δ ≤ X.Pd

  aδle : X.aδ ≤ 4 / 3 * X.δ

  aFle : X.aF ≤ 4 / 3 * (X.D + 4) * X.δ

  HFle : X.HF ≤ (X.D + 4) * (X.D + 1) * X.δ * (2 * X.G + 6 * X.PH) * X.L

  Hδle : X.Hδ ≤ (X.D + 1) * X.δ * (2 * X.G + 6 * X.PH) * X.L

  deep : ∑ la ∈ X.s, X.cD la * X.l la ≤ X.ρ * X.PD * X.κ

  quot : ∑ la ∈ X.s, (X.vQ la + X.ρ' * X.be la) * X.l la ≤ X.ρ' * X.PQ * X.κ

  shρ : X.ρ ≤ X.ρ' + 22 * X.D ^ 2 * X.d / X.T

  shρ' : X.ρ' ≤ X.d * (X.DivisibilityWeightConstant * (X.RR ^ 2 * X.c + 1 / X.T) / X.γ₀)
structure Rel (PP : ℝ) : Prop where
  r1 : X.P1 * X.D ^ 2 ≤ PP ^ 2 * X.D ^ 3
  r2 : X.P2 ≤ PP ^ 3
  r3 : X.P3 ≤ PP ^ 2
  r4 : X.P4 ≤ PP ^ 2
structure Page (PP C k b m δ₂ q DF : ℝ) : Prop where
  tableDegreeThreeBase : 0 < PP
  one_le_radius_alt : 1 ≤ X.RR
  q0 : 0 < q
  C0 : 0 ≤ C
  k0 : 0 ≤ k
  b0 : 0 ≤ b
  m0 : 0 < m
  δ₂0 : 0 < δ₂

  Tγ : X.T ≤ X.γ₀

  S1 : X.κ ≤ C * k * X.f * b

  ps0 : PP ^ 3 * X.T ≤ X.f * m * b * δ₂ / 4

  ps1 : 4 * C * PP ^ 2 * X.D ^ 3 * k / (m * δ₂) ≤ X.T

  cdef : X.c = X.RR * PP * DF ^ 2 / q
  g1 : 1 ≤ X.g₀

  qlow : X.RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q

  TPP : PP ^ 2 ≤ X.T

  primeSetTwoBounds : 2 ≤ PP ^ 2
variable {X}
end SumDat
end Formalism.MainNotions.Gaps.T0


