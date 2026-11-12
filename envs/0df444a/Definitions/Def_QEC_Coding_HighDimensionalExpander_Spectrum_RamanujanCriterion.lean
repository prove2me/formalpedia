-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
-- name    : QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:49:19.05282+00:00
-- url     : https://prove2.me/theorems/0907661a-2f87-4ad6-a308-247433e80366
-- title:
--   Ramanujan Criterion
-- statement:
--   Definitions and structural lemmas for Ramanujan Criterion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u
def IsLSVSphericalConstituent
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V) : Prop :=
  OccursInLSVAutomorphicL2 P r level sigma ∧
    IsIrreducibleUnitarySpherical sigma
def IsLSVTrivialSphericalConstituent
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V) : Prop :=
  IsLSVSphericalConstituent P r level sigma ∧ Module.Finite ℂ V
def IsLSVInfiniteDimensionalSphericalConstituent
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V) : Prop :=
  IsLSVSphericalConstituent P r level sigma ∧ ¬ Module.Finite ℂ V
def lsvNontrivialJointSpectrum
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set (Fin (r.matrixRank - 1) → ℂ) :=
  lsvFiniteDetCandidateNontrivialJointSpectrum P r level
def IsLSVRamanujanQuotient
    (P : BasePrime) (r : Rank) (level : Nat) : Prop :=
  lsvNontrivialJointSpectrum P r level ⊆
    lsvUniversalBuildingJointSpectrum P r
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


