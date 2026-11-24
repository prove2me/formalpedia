-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
-- name    : LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:44:45.446319+00:00
-- url     : https://prove2.me/theorems/6b37a6cb-6643-4523-95db-644519758871
-- title:
--   Sensitivity
-- statement:
--   Definitions and structural lemmas for Sensitivity, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
def SensitiveCoord (f : Input V → Bool) (x : Input V) (v : V) : Prop :=
  f (flipSet x {v}) ≠ f x
instance (f : Input V → Bool) (x : Input V) (v : V) : Decidable (SensitiveCoord f x v) :=
  inferInstanceAs (Decidable (f (flipSet x {v}) ≠ f x))
def sensCoords (f : Input V → Bool) (x : Input V) : Finset V :=
  Finset.univ.filter fun v ↦ SensitiveCoord f x v
def sensAt (f : Input V → Bool) (x : Input V) : ℕ := (sensCoords f x).card
def sens (f : Input V → Bool) : ℕ := Finset.univ.sup (sensAt f)
structure IsSensitiveBlock (f : Input V → Bool) (x : Input V) (A : Finset V) : Prop where
  nonempty : A.Nonempty
  flips : f (flipSet x A) ≠ f x
structure IsBlockFamily (f : Input V → Bool) (x : Input V) (𝓑 : Finset (Finset V)) : Prop where
  sensitive : ∀ A ∈ 𝓑, IsSensitiveBlock f x A
  disjoint : (𝓑 : Set (Finset V)).PairwiseDisjoint id
def blockFamilyCards (f : Input V → Bool) (x : Input V) : Set ℕ :=
  {n | ∃ 𝓑 : Finset (Finset V), IsBlockFamily f x 𝓑 ∧ 𝓑.card = n}
noncomputable def bsAt (f : Input V → Bool) (x : Input V) : ℕ := sSup (blockFamilyCards f x)
noncomputable def bs (f : Input V → Bool) : ℕ := Finset.univ.sup (bsAt f)
end BSLambda


