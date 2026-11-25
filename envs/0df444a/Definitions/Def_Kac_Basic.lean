-- Prove2me | Definitions.Def_Kac_Basic
-- name    : Kac_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T13:00:55.585702+00:00
-- url     : https://prove2.me/theorems/09350f07-6e3d-48b2-917f-4f14e18cff08
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Zayn Blore (zblore/kac-lean; see pinned Apache-2.0 LICENSE and source headers)'s pinned Kac's return-time formula for measure-preserving maps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
namespace Kac
section Sets
variable {α : Type*} {f : α → α} {A : Set α}
def notYet (f : α → α) (A : Set α) : ℕ → Set α
  | 0 => univ
  | n + 1 => Aᶜ ∩ f ⁻¹' notYet f A n
def firstHit (f : α → α) (A : Set α) (n : ℕ) : Set α :=
  notYet f A n ∩ f^[n] ⁻¹' A
end Sets
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {A : Set α}
section Finite
variable [IsFiniteMeasure μ]
end Finite
section Probability
variable [IsProbabilityMeasure μ]
end Probability
end Kac


