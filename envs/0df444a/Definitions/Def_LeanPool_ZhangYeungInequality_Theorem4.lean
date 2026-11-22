-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
-- name    : LeanPool_ZhangYeungInequality_Theorem4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:53:26.628199+00:00
-- url     : https://prove2.me/theorems/a5bf9092-2c1d-4b2e-9cdc-7d036597b858
-- title:
--   Theorem4
-- statement:
--   Definitions and structural lemmas for Theorem4, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR
universe u
def IF (F : Finset (Fin 4) → ℝ) (α β : Finset (Fin 4)) : ℝ :=
  F α + F β - F (α ∪ β)
def condIF (F : Finset (Fin 4) → ℝ) (α β γ : Finset (Fin 4)) : ℝ :=
  F (α ∪ γ) + F (β ∪ γ) - F (α ∪ β ∪ γ) - F γ
def deltaF (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) : ℝ :=
  IF F {i} {j} - condIF F {i} {j} {k} - condIF F {i} {j} {l}
def shannonCone (F : Finset (Fin 4) → ℝ) : Prop :=
  F ∅ = 0 ∧
  (∀ α β : Finset (Fin 4), α ⊆ β → F α ≤ F β) ∧
  (∀ α β : Finset (Fin 4), F (α ∪ β) + F (α ∩ β) ≤ F α + F β)
def zhangYeungAt (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) : Prop :=
  deltaF F i j k l ≤ (1 / 2) * (IF F {k} {l} + IF F {k} ({i} ∪ {j})
    + condIF F {i} {j} {k} - condIF F {i} {j} {l})
def zhangYeungHolds (F : Finset (Fin 4) → ℝ) : Prop :=
  ∀ π : Equiv.Perm (Fin 4), zhangYeungAt F (π 0) (π 1) (π 2) (π 3)
def FWitnessℚ : Finset (Fin 4) → ℚ := fun S =>
  if S.card = 0 then 0
  else if S.card = 1 then 2
  else if S = ({0, 1} : Finset (Fin 4)) then 4
  else if S.card = 2 then 3
  else 4
noncomputable def FWitness : Finset (Fin 4) → ℝ := fun S => (FWitnessℚ S : ℝ)
def pair01 : Finset (Fin 4) := {0, 1}
def nonemptyBonus (S : Finset (Fin 4)) : ℚ := if S.Nonempty then 1 else 0
def fullBonus (S : Finset (Fin 4)) : ℚ := if S = Finset.univ then 1 else 0
def pairBonus (S : Finset (Fin 4)) : ℚ := if S = pair01 then 1 else 0
def baseWitness (S : Finset (Fin 4)) : ℚ := (S.card : ℚ) + nonemptyBonus S - fullBonus S
abbrev PairBonusExceptional (α β : Finset (Fin 4)) : Prop :=
  (α = ({0} : Finset (Fin 4)) ∧ β = ({1} : Finset (Fin 4))) ∨
    (α = ({1} : Finset (Fin 4)) ∧ β = ({0} : Finset (Fin 4))) ∨
    (α = ({0, 1, 2} : Finset (Fin 4)) ∧ β = ({0, 1, 3} : Finset (Fin 4))) ∨
    (α = ({0, 1, 3} : Finset (Fin 4)) ∧ β = ({0, 1, 2} : Finset (Fin 4)))
section EntropyFnEvaluation
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Fin 4 → Type u}
  [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
  [∀ i, MeasurableSingletonClass (S i)]
  (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) [IsProbabilityMeasure μ]
end EntropyFnEvaluation
def zhangYeungRegion_4 : Set (Finset (Fin 4) → ℝ) :=
  {F | zhangYeungHolds F}
noncomputable def _root_.ZhangYeung.FWitnessN
    {n : ℕ} (hn : 4 ≤ n) (α : Finset (Fin n)) : ℝ :=
  FWitness (α.preimage (Fin.castLE hn) (Fin.castLE_injective hn).injOn)
end ZhangYeung


