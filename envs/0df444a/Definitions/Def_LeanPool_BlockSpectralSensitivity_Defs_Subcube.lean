-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
-- name    : LeanPool_BlockSpectralSensitivity_Defs_Subcube
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:44:42.575725+00:00
-- url     : https://prove2.me/theorems/fcb90dbe-37f3-4a78-baa8-6727edfa6618
-- title:
--   Subcube
-- statement:
--   Definitions and structural lemmas for Subcube, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
abbrev PartialAssign (V : Type*) : Type _ := V → Option Bool
namespace PartialAssign
variable {V : Type*}
def Sat (P : PartialAssign V) (x : Input V) : Prop := ∀ v b, P v = some b → x v = b
def proj (P : PartialAssign V) (x : Input V) : Input V := fun v => (P v).getD (x v)
def Conflict (P Q : PartialAssign V) (v : V) : Prop := ∃ b, P v = some b ∧ Q v = some (!b)
instance (P Q : PartialAssign V) (v : V) : Decidable (P.Conflict Q v) :=
  inferInstanceAs (Decidable (∃ b, P v = some b ∧ Q v = some (!b)))
section Fintype
variable [Fintype V]
instance (P : PartialAssign V) (x : Input V) : Decidable (P.Sat x) :=
  inferInstanceAs (Decidable (∀ v b, P v = some b → x v = b))
def fixedSet (P : PartialAssign V) : Finset V := Finset.univ.filter fun v => (P v).isSome
def codim (P : PartialAssign V) : ℕ := P.fixedSet.card
def violSet (P : PartialAssign V) (x : Input V) : Finset V :=
  Finset.univ.filter fun v => P v ≠ none ∧ P v ≠ some (x v)
def dist (P : PartialAssign V) (x : Input V) : ℕ := (P.violSet x).card
section IndUnion
variable {ι : Type*} [Fintype ι]
def indUnion (P : ι → PartialAssign V) : Input V → Bool := fun x => decide (∃ i, (P i).Sat x)
variable {P : ι → PartialAssign V} {x : Input V}
end IndUnion
end Fintype
section Cube
variable [Fintype V] [DecidableEq V]
def cube (P : PartialAssign V) : Finset (Input V) := Finset.univ.filter fun x => P.Sat x
end Cube
end PartialAssign
end BSLambda


