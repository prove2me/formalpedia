-- Prove2me | solution 1 for Auto.aux_discreteJumpEnergy_orbitFunction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:06.420648+00:00
-- url     : https://prove2.me/submissions/f9da6b85-b5bd-4cd4-a543-2d7e4d41bbd6

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_discreteAverage_orbitFunction

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {n J : ℕ}
    (S : ErgodicSystem X μ n) (N : Fin (J + 1) → ℕ)
    (f : Fin n → X → ℝ) (x : X) :
    aux_discreteJumpEnergy N (aux_orbitFunction S f x) =
      ∑ j : Fin J, eLpNorm
        (fun k ↦ realErgodicAverage S (N j.succ) f
            (aux_orbit S.transformation k x) -
          realErgodicAverage S (N j.castSucc) f
            (aux_orbit S.transformation k x)) 2 Measure.count ^ 2 := by
  unfold aux_discreteJumpEnergy
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply congrArg (fun h ↦ eLpNorm h 2 Measure.count)
  funext k
  rw [aux_discreteAverage_orbitFunction]
  rw [aux_discreteAverage_orbitFunction]
end Auto
