-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
-- name    : ReciprocityTheory_DualLattices_ProdEraseUpdate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:31.779883+00:00
-- url     : https://prove2.me/theorems/421c86c0-6ada-473a-b7b5-21a04c5830e8
-- title:
--   Prod Erase Update
-- statement:
--   Definitions and structural lemmas for Prod Erase Update, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.PGsh.Up
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] {ι : Type} [Fintype ι]
  [DecidableEq ι]
def xc (k : Type) [Field k] [CharP k p] (i : ι) (x : ι → ZMod p) : k :=
  ZMod.castHom (dvd_refl p) k (x i)
def lam (Cm : Matrix ι ι k) (j : ι) (x : ι → ZMod p) : k := ∑ i, Cm j i * xc k i x
def monF (Cm : Matrix ι ι k) (α : ι → ZMod p) (x : ι → ZMod p) : k :=
  ∏ j, lam Cm j x ^ (α j).val
def MulStable (S : Submodule k ((ι → ZMod p) → k)) (h : (ι → ZMod p) → k) : Prop :=
  ∀ f ∈ S, h * f ∈ S
def delta (k : Type) [Field k] [CharP k p] (y : ι → ZMod p) : (ι → ZMod p) → k :=
  ∏ i, ((fun _ => (1 : k)) + (fun _ => (-1 : k)) *
    ((fun x => xc k i x) + (fun _ => -ZMod.castHom (dvd_refl p) k (y i))) ^ (p - 1))
end ReciprocityTheory.PGsh.Up


