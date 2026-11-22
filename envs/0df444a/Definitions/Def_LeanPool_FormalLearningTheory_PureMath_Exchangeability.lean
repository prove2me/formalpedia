-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_PureMath_Exchangeability
-- name    : LeanPool_FormalLearningTheory_PureMath_Exchangeability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:31.465662+00:00
-- url     : https://prove2.me/theorems/853ad8ef-b1d4-4664-b331-d67cc8fdc2a7
-- title:
--   Exchangeability
-- statement:
--   Definitions and structural lemmas for Exchangeability, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/Exchangeability.lean

module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open MeasureTheory ENNReal
structure ExchangeableSample {X : Type*} [MeasurableSpace X] where
  /-- Sample size. -/
  m : ℕ
  /-- Underlying sample distribution. -/
  μ : MeasureTheory.Measure X
  hμ : MeasureTheory.IsProbabilityMeasure μ
noncomputable def DoubleSampleMeasure {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) (m : ℕ) : MeasureTheory.Measure ((Fin m → X) × (Fin m → X)) :=
  (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
    (MeasureTheory.Measure.pi (fun _ : Fin m => D))
abbrev MergedSample (X : Type u) (m : ℕ) := Fin (2 * m) → X
noncomputable def mergeSamples {X : Type u} {m : ℕ}
    (p : (Fin m → X) × (Fin m → X)) : MergedSample X m :=
  fun i =>
    let j : Fin (m + m) := i.cast (two_mul m)
    if h : j.val < m
    then p.1 ⟨j.val, h⟩
    else p.2 ⟨j.val - m, by omega⟩
noncomputable def splitMergedSample {X : Type u} {m : ℕ}
    (z : MergedSample X m) : (Fin m → X) × (Fin m → X) :=
  (fun i => z (Fin.castAdd m i |>.cast (two_mul m).symm),
   fun i => z (Fin.natAdd m i |>.cast (two_mul m).symm))
structure ValidSplit (m : ℕ) where
  /-- Assignment of each of 2m indices to one of two groups -/
  assign : Fin (2 * m) → Bool
  /-- Exactly m indices are assigned to the first group -/
  card_true : (Finset.univ.filter (fun i => assign i = true)).card = m
  deriving DecidableEq
noncomputable instance (m : ℕ) : Fintype (ValidSplit m) :=
  Fintype.ofInjective (fun vs => vs.assign)
    (fun a b h => by cases a; cases b; simp_all)
instance (m : ℕ) : MeasurableSpace (ValidSplit m) := ⊤
noncomputable def SplitMeasure (m : ℕ) : MeasureTheory.Measure (ValidSplit m) :=
  if _h : Fintype.card (ValidSplit m) = 0 then 0
  else (Fintype.card (ValidSplit m) : ENNReal)⁻¹ •
    ∑ vs : ValidSplit m, MeasureTheory.Measure.dirac vs
def splitFirst {X : Type u} {m : ℕ} (z : MergedSample X m) (vs : ValidSplit m) :
    Fin m → X := by
  let _validSplit := vs.card_true
  exact fun i => z (Fin.castAdd m i |>.cast (two_mul m).symm)
def splitSecond {X : Type u} {m : ℕ} (z : MergedSample X m) (vs : ValidSplit m) :
    Fin m → X := by
  let _validSplit := vs.card_true
  exact fun i => z (Fin.natAdd m i |>.cast (two_mul m).symm)


