-- Prove2me | Definitions.Def_PricingWithTips_ThreeDM
-- name    : PricingWithTips_ThreeDM
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-21T19:35:07.333877+00:00
-- url     : https://prove2.me/theorems/32fc1178-227a-41c8-8391-b13ee914210e
-- title:
--   Three-dimensional matching reduction for pricing with tips
-- statement:
--   Defines finite 3-dimensional matching instances, the paper’s unit-value zero-one-cost market construction, exact optimal-welfare and equilibrium-welfare decision predicates, and a binary encoding for polynomial-time reductions.
-- source:
--   Pricing with Tips in Three-Sided Delivery Platforms, arXiv:2507.10872v1, Theorems 4.1–4.2 and their shared 3DM reduction

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

/-- A three-dimensional matching instance with three vertex classes of size `n`. -/
def HasPerfect3DMatching (n : ℕ) (edge : Fin n → Fin n → Fin n → Bool) : Prop :=
  ∃ A : Allocation (Fin n) (Fin n) (Fin n),
    (∀ b, ∃ s d, A.Trades b s d) ∧
    (∀ b s d, A.Trades b s d → edge b s d = true)

/-- The zero-one-cost market constructed in Theorems 4.1 and 4.2. -/
def marketOf3DM (n : ℕ) (edge : Fin n → Fin n → Fin n → Bool) :
    Market (Fin n) (Fin n) (Fin n) where
  value := fun _ _ => 1
  cost := fun d b s => if edge b s d then 0 else 1
  value_nonneg := by intros; norm_num
  cost_nonneg := by intros; split_ifs <;> norm_num

def HasWelfareAtLeastCard (n : ℕ) (edge : Fin n → Fin n → Fin n → Bool) : Prop :=
  ∃ A : Allocation (Fin n) (Fin n) (Fin n),
    (n : ℝ) ≤ welfare (marketOf3DM n edge) A

def HasEquilibriumWelfareAtLeastCard (n : ℕ)
    (edge : Fin n → Fin n → Fin n → Bool) : Prop :=
  ∃ A : Allocation (Fin n) (Fin n) (Fin n),
    HasWithTipEquilibriumAt (marketOf3DM n edge) A ∧
    (n : ℝ) ≤ welfare (marketOf3DM n edge) A

def HasWelfareEqualCard (n : ℕ) (edge : Fin n → Fin n → Fin n → Bool) : Prop :=
  ∃ A : Allocation (Fin n) (Fin n) (Fin n),
    welfare (marketOf3DM n edge) A = (n : ℝ)

def HasEquilibriumWelfareEqualCard (n : ℕ)
    (edge : Fin n → Fin n → Fin n → Bool) : Prop :=
  ∃ A : Allocation (Fin n) (Fin n) (Fin n),
    HasWithTipEquilibriumAt (marketOf3DM n edge) A ∧
    welfare (marketOf3DM n edge) A = (n : ℝ)

/-- Finite 3DM instances with a uniform, size-indexed representation. -/
abbrev ThreeDMInstance := Σ n : ℕ, Fin n → Fin n → Fin n → Bool

/-- Unary size prefix followed by the cubic incidence table. -/
def encodeThreeDMInstance (I : ThreeDMInstance) : List Bool :=
  List.replicate I.1 true ++ [false] ++
    (List.finRange I.1).flatMap (fun b =>
      (List.finRange I.1).flatMap (fun s =>
        (List.finRange I.1).map (fun d => I.2 b s d)))

def ThreeDMYes (I : ThreeDMInstance) : Prop :=
  HasPerfect3DMatching I.1 I.2

def WelfareYes (I : ThreeDMInstance) : Prop :=
  HasWelfareEqualCard I.1 I.2

def EquilibriumWelfareYes (I : ThreeDMInstance) : Prop :=
  HasEquilibriumWelfareEqualCard I.1 I.2

/-- Many-one reduction whose map is computed by a polynomial-time TM2 machine. -/
def PolyManyOneReduces (L₁ L₂ : ThreeDMInstance → Prop) : Prop :=
  ∃ f : ThreeDMInstance → ThreeDMInstance,
    Nonempty (Turing.TM2ComputableInPolyTime
      encodeThreeDMInstance encodeThreeDMInstance f) ∧
    ∀ I, L₁ I ↔ L₂ (f I)

def HardFor (sourceClass : Set (ThreeDMInstance → Prop))
    (target : ThreeDMInstance → Prop) : Prop :=
  ∀ source ∈ sourceClass, PolyManyOneReduces source target

end PricingWithTips


