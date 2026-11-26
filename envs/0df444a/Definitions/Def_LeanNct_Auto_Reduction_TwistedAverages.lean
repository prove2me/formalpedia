-- Prove2me | Definitions.Def_LeanNct_Auto_Reduction_TwistedAverages
-- name    : LeanNct_Auto_Reduction_TwistedAverages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:00:38.874551+00:00
-- url     : https://prove2.me/theorems/327702fc-331f-508d-adf2-5dcd4e09a208
-- title:
--   Twisted Averages
-- statement:
--   Definitions and structural lemmas for Twisted Averages, from Floris van Doorn, Polona Durcik, Joris Roos, Lenka Slavíková, Christoph Thiele (roos-j/lean-nct; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Norm-variation of multiple ergodic averages for commuting transformations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/TwistedAverages.lean

module
public import Definitions.Def_LeanNct_Auto_Preliminaries_Notation
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
noncomputable def aux_twistedAverage {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x ↦ ∫ s : ℝ, chi s * ∏ i,
    f i (x + s • WithLp.toLp 2 (Pi.single i (1 : ℝ)))
noncomputable def aux_twistedAverageAtScale {n : ℕ} (t : ℝ) (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  aux_twistedAverage (fun s ↦ t⁻¹ * chi (t⁻¹ * s)) f
noncomputable abbrev twistedAverage {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  aux_twistedAverage chi f
noncomputable abbrev twistedAverageAtScale {n : ℕ} (t : ℝ) (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  aux_twistedAverageAtScale t chi f
def TwistedScaleChain (J : ℕ) :=
  {t : Fin (J + 1) → ℝ // StrictMono t ∧ ∀ j, 0 < t j}
noncomputable def twistedJumpEnergy {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (J : ℕ)
    (t : TwistedScaleChain J) : ℝ≥0∞ :=
  ∑ j : Fin J,
    eLpNorm
      (fun x ↦ twistedAverageAtScale (t.1 j.succ) chi f x -
        twistedAverageAtScale (t.1 j.castSucc) chi f x)
      2 volume ^ 2
noncomputable def twistedVariationEnergy {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (J : ℕ) : ℝ≥0∞ :=
  ⨆ t : TwistedScaleChain J, twistedJumpEnergy chi f J t
def TwistedDyadicChain (J : ℕ) :=
  {k : Fin (J + 1) → ℤ // StrictMono k}
noncomputable def twistedDyadicJumpEnergy {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (J : ℕ)
    (k : TwistedDyadicChain J) : ℝ≥0∞ :=
  ∑ j : Fin J,
    eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) chi f x -
        twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) chi f x)
      2 volume ^ 2
noncomputable def twistedDyadicVariationEnergy {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (J : ℕ) : ℝ≥0∞ :=
  ⨆ k : TwistedDyadicChain J, twistedDyadicJumpEnergy chi f J k
end
end Auto


