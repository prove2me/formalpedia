-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
-- name    : LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:44:27.691221+00:00
-- url     : https://prove2.me/theorems/6b950dbf-e66b-499d-b5dd-3b30e95430d8
-- title:
--   Asymmetric
-- statement:
--   Definitions and structural lemmas for Asymmetric, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
def nbr (supp : I → Finset A) (i : I) : Finset I :=
  Finset.univ.filter fun j ↦ j ≠ i ∧ ¬ Disjoint (supp i) (supp j)
def avoid (Ev : I → Finset (Cfg β)) (S : Finset I) : Finset (Cfg β) :=
  Finset.univ.filter fun ω ↦ ∀ i ∈ S, ω ∉ Ev i
section AvoidBasic
end AvoidBasic
section Telescope
end Telescope
section Main
variable (Ev : I → Finset (Cfg β)) (supp : I → Finset A) (x : I → ℝ)
end Main
section TwoType
end TwoType
section Fibre
variable {G : Finset A}
def fibre (G : Finset A) (c : (a : A) → a ∈ G → β a) : Finset (Cfg β) :=
  Finset.univ.filter fun ω : Cfg β ↦ ∀ a, ∀ ha : a ∈ G, ω a = c a ha
end Fibre
section Pinned
end Pinned
end BSLambda.LLL


