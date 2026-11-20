-- Prove2me | Definitions.Def_ChandraFurstLipton_NOFModel
-- name    : ChandraFurstLipton_NOFModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T18:13:48.206107+00:00
-- url     : https://prove2.me/theorems/45007ced-0a24-4df6-8142-9b263e9dacdb
-- title:
--   NOFModel
-- statement:
--   Definitions and structural lemmas for NOFModel, from Yaël Dillies and Isabel Dahlgren's pinned Chandra–Furst–Lipton: number-on-the-forehead protocols development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/NOFModel.lean

module
public import Definitions.Def_ChandraFurstLipton_MultidimCorners
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ZMod.Defs
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace NOF
variable {ι G : Type*} {d : ℕ} [Fintype ι]
variable (G d) in
structure Protocol where
  nextBit (i : ZMod d) : ({j : ZMod d // j ≠ i} → G) → List Bool → Bool
  guess (i : ZMod d) : ({j : ZMod d // j ≠ i} → G) → List Bool → Bool
variable {F : (ZMod d → G) → Bool} {P : Protocol G d} {a : ZMod d → ZMod d → G} {v : ZMod d → G}
  {B : List Bool} {t : ℕ}
namespace Protocol
def broadcast (P : Protocol G d) (x : ZMod d → G) : ℕ → List Bool
  | 0 => []
  | t + 1 => P.nextBit t (forget (t : ZMod d) x) (broadcast P x t) :: broadcast P x t
def IsValid (P : Protocol G d) (F : (ZMod d → G) → Bool) (t : ℕ) : Prop :=
  ∀ x i, P.guess i (forget i x) (broadcast P x t) = F x
noncomputable def complexity (P : Protocol G d) (F : (ZMod d → G) → Bool) : ENat :=
  ⨅ (t : ℕ) (_ : IsValid P F t), t
end Protocol
noncomputable def funComplexity (F : (ZMod d → G) → Bool) := ⨅ P : Protocol G d, P.complexity F
end NOF


