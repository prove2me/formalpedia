-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MiracleFlatness_MiracleFlatOfRegSeqDepth
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MiracleFlatness_MiracleFlatOfRegSeqDepth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:23.138865+00:00
-- url     : https://prove2.me/theorems/d404c500-4a54-4821-aeed-388f2edcdedd
-- title:
--   Miracle Flat Of Reg Seq Depth
-- statement:
--   Definitions and structural lemmas for Miracle Flat Of Reg Seq Depth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MiracleFlatness/MiracleFlatOfRegSeqDepth.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MiracleFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace PI.UnitaryGroupMassFormula.MF
open RingTheory.Sequence IsLocalRing
def RegSeqGen : Prop :=
  ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A],
    ∃ xs : List A, IsRegular A xs ∧ Ideal.ofList xs = maximalIdeal A ∧ (xs.length : WithBot ℕ∞) = ringKrullDim A
def AssDim : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R), IsRegular M rs → ∀ p ∈ associatedPrimes R M, (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)
def DepthDrop : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (x : R), IsRegular M rs → rs ≠ [] → x ∈ maximalIdeal R → IsSMulRegular M x →
      ∃ zs : List R, zs.length + 1 = rs.length ∧ IsRegular (QuotSMulTop x M) zs
def CMSop : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B],
    (∃ rs : List B, IsRegular B rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal B) ∧ (rs.length : WithBot ℕ∞) = ringKrullDim B) →
    ∀ xs : List B, (∀ x ∈ xs, x ∈ maximalIdeal B) →
      ringKrullDim B = (xs.length : WithBot ℕ∞) + ringKrullDim (B ⧸ Ideal.ofList xs) → IsRegular B xs
def CMSopOf : Prop := AssDim.{u} → DepthDrop.{u} → CMSop.{u}
def LocCrit : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B] (x : A),
    IsSMulRegular A x → IsSMulRegular B (algebraMap A B x) → algebraMap A B x ∈ maximalIdeal B →
    Module.Flat (A ⧸ Ideal.span {x}) (B ⧸ (Ideal.span {x}).map (algebraMap A B)) → Module.Flat A B
def FlatOfReg : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] (xs : List A), IsRegular A xs → Ideal.ofList xs = maximalIdeal A →
    IsRegular B (xs.map (algebraMap A B)) → Module.Flat A B
def FlatOfRegOf : Prop := LocCrit.{u} → FlatOfReg.{u}
def Assembly : Prop := RegSeqGen.{u} → CMSop.{u} → FlatOfReg.{u} → PI.MiracleFlat.{u}
end PI.UnitaryGroupMassFormula.MF


