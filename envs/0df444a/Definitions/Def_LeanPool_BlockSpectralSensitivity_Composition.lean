-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
-- name    : LeanPool_BlockSpectralSensitivity_Composition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:45:23.177102+00:00
-- url     : https://prove2.me/theorems/779a9b32-6219-4e8b-a62d-6bab5e5cbee2
-- title:
--   Composition
-- statement:
--   Definitions and structural lemmas for Composition, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
open Function
universe u
def comp {W V : Type*} (f : Input W → Bool) (g : Input V → Bool) :
    Input (W × V) → Bool := fun x => f fun w => g fun v => x (w, v)
def IterCoord (V : Type u) : ℕ → Type u
  | 0 => PUnit
  | m + 1 => V × IterCoord V m
instance instFintypeIterCoord {V : Type*} [Fintype V] : ∀ m, Fintype (IterCoord V m)
  | 0 => inferInstanceAs (Fintype PUnit)
  | m + 1 =>
      letI := instFintypeIterCoord (V := V) m
      inferInstanceAs (Fintype (V × IterCoord V m))
instance instDecidableEqIterCoord {V : Type*} [DecidableEq V] : ∀ m, DecidableEq (IterCoord V m)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | m + 1 =>
      letI := instDecidableEqIterCoord (V := V) m
      inferInstanceAs (DecidableEq (V × IterCoord V m))
def iterBlock {V ι : Type*} [DecidableEq V] (blk : ι → Finset V) :
    (m : ℕ) → IterCoord ι m → Finset (IterCoord V m)
  | 0 => fun _ => (Finset.univ : Finset PUnit)
  | m + 1 => fun t => (blk t.1) ×ˢ iterBlock blk m t.2
def iterFun {V : Type*} (f : Input V → Bool) : (m : ℕ) → Input (IterCoord V m) → Bool
  | 0 => fun x => x PUnit.unit
  | m + 1 => comp f (iterFun f m)
section Seed
variable {V ι : Type*} [DecidableEq V] {f : Input V → Bool} {blk : ι → Finset V}
end Seed
section Blocks
variable {V ι : Type*} [DecidableEq V] {blk : ι → Finset V}
end Blocks
end BSLambda


