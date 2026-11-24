-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
-- name    : LeanPool_BlockSpectralSensitivity_LLL_Prob
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:44:06.552064+00:00
-- url     : https://prove2.me/theorems/78ccb0a8-e730-471a-b2c0-62b90c1857bb
-- title:
--   Prob
-- statement:
--   Definitions and structural lemmas for Prob, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
abbrev Cfg (β : A → Type*) : Type _ := ∀ a, β a
noncomputable def pr (E : Finset (Cfg β)) : ℝ := E.dens
section Basic
omit [(a : A) → DecidableEq (β a)]
variable [∀ a, Nonempty (β a)]
end Basic
section Additivity
variable [∀ a, Nonempty (β a)]
end Additivity
def Determined (S : Finset A) (E : Finset (Cfg β)) : Prop :=
  ∀ ω ω' : Cfg β, (∀ a ∈ S, ω a = ω' a) → (ω ∈ E ↔ ω' ∈ E)
section Determined
end Determined
section Independence
section Glue
omit [Fintype A] [(a : A) → Fintype (β a)] [(a : A) → DecidableEq (β a)]
def glue (S : Finset A) (u v : Cfg β) : Cfg β := fun a ↦ if a ∈ S then u a else v a
def swapGlue (S : Finset A) (p : Cfg β × Cfg β) : Cfg β × Cfg β :=
  (glue S p.1 p.2, glue S p.2 p.1)
end Glue
variable [∀ a, Nonempty (β a)]
end Independence
section Pinning
variable [∀ a, Nonempty (β a)]
end Pinning
end BSLambda.LLL


