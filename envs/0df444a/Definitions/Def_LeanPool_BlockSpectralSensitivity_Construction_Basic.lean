-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
-- name    : LeanPool_BlockSpectralSensitivity_Construction_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:44:59.749485+00:00
-- url     : https://prove2.me/theorems/3aec92ae-55b7-4efc-8957-52fbdcf36d52
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
namespace Construction
variable {ι : Type*} {r : ℕ}
abbrev Coord (ι : Type*) (r : ℕ) : Type _ := ι × Fin r
def block (i : ι) : Finset (Coord ι r) := {i} ×ˢ Finset.univ
def gateCoord (γ : ι → ι → Fin r) (i j : ι) : Coord ι r := (j, γ i j)
section Cert
variable [DecidableEq ι]
def cert (Arc : ι → ι → Bool) (γ : ι → ι → Fin r) (i : ι) : PartialAssign (Coord ι r) :=
  fun v ↦ if v.1 = i then some true
    else if Arc i v.1 ∧ v.2 = γ i v.1 then some false else none
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι} {v : Coord ι r} {b : Bool}
end Cert
section Fintype
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i : ι}
def ind (Arc : ι → ι → Bool) (γ : ι → ι → Fin r) : Input (Coord ι r) → Bool :=
  PartialAssign.indUnion (cert Arc γ)
variable {x : Input (Coord ι r)}
end Fintype
end Construction
end BSLambda


