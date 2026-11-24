-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementN
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementN
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:25.973803+00:00
-- url     : https://prove2.me/theorems/b9c5d4b0-008c-4790-bb2e-965c9ad23c2a
-- title:
--   Statement N
-- statement:
--   Definitions and structural lemmas for Statement N, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/StatementN.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_PlacesAddClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp jetPair)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
structure PlaceData (K : Type) (r0 r1 : ℕ) where

  ν : ℕ

  hν : NeZero ν

  u : ZMod (2 * ν) → K

  TT : Finset (ZMod (2 * ν))

  ξ : ZMod (2 * ν) → Fin r0 → K

  e : TpV ν r1 → ℕ

  C : ℕ

  l : Fin C → ℕ

  sf : Fin C → ZMod (2 * ν)

  T : ∀ c, Fin (l c) → Fin r0 → K

  I : ∀ c, Fin (l c) → Fin r1

  J : Finset (Fin r1)

  kind : Fin 3
attribute [instance] PlaceData.hν
namespace PlaceData
variable {K : Type} {r0 r1 : ℕ}
def op [Field K] (D : PlaceData K r0 r1) : MvPolynomial (ZV D.ν r0 r1) K :=
  entryOp D.ξ D.e D.l D.sf D.T D.I
def pay (D : PlaceData K r0 r1) : ℕ :=
  if D.kind = 2 then
    ∑ x : TpV D.ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ D.J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ D.J)
      then D.e x else 0) +
    ∑ c, (if (D.sf c).val % 2 = 1 then ((univ.image (D.I c)) ∩ D.J).card else 0)
  else 0
def bound (D : PlaceData K r0 r1) (p : ℕ) : ℝ :=
  (if D.kind = 0 then
    excessGain (p : ℝ) D.TT (dSet D.TT) (fun s => (alN D.e s : ℝ)) (fun s => (capN D.sf s : ℝ))
      (deLoss p r0 r1 D.TT (alN D.e) (lsN D.l D.sf))
  else if D.kind = 1 then
    gainG (p : ℝ) D.TT (oddT D.TT) (fun s => (alN D.e s : ℝ)) (fun s => (capN D.sf s : ℝ))
      (deLoss p r0 r1 D.TT (alN D.e) (lsN D.l D.sf)) - ∑ s ∈ D.TT \ oddT D.TT, (alN D.e s : ℝ)
  else
    gainG (p : ℝ) D.TT (oddT D.TT) (fun s => (alN D.e s : ℝ)) (fun s => (capN D.sf s : ℝ))
      (deLoss p r0 r1 D.TT (alN D.e) (lsN D.l D.sf))) +
  rhoP p * ∑ s, ((alN D.e s : ℝ) + lsN D.l D.sf s)
def OK [NormedField K] (D : PlaceData K r0 r1) : Prop :=
  (∀ s, ‖D.u s‖ ≤ 1) ∧ (∀ s a, ‖D.ξ s a‖ ≤ 1) ∧ (∀ c i a, ‖D.T c i a‖ ≤ 1) ∧
    ∀ x : TpV D.ν r1, x.1 ∉ D.TT → D.e x = 0
end PlaceData
def EntryMulti : Prop :=
  ∀ (K Pl : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [Fintype Pl] [DecidableEq Pl]
    (p r0 r1 : ℕ) (ϖ : K) (D : Pl → PlaceData K r0 r1), p.Prime → 2 < p →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) → (∀ v, (D v).OK) →
    ∀ U : MvPowerSeries (Σ v, ZV (D v).ν r0 r1) K, Integral U →
      ‖(p : K) ^ (∑ v, (D v).pay) *
        jetPair (∏ v, MvPolynomial.rename (Sigma.mk v) (D v).op)
          ((∏ v, atPlace (ι := fun v => ZV (D v).ν r0 r1) v
            (mvExp (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hhS p (D v).u)))) * U)‖ ≤
        (p : ℝ) ^ (-(∑ v, (D v).bound p))
end Formalism.InvariantFactorPaths.G7


