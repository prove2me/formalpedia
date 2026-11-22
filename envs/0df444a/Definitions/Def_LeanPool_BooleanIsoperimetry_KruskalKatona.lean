-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
-- name    : LeanPool_BooleanIsoperimetry_KruskalKatona
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:07.206672+00:00
-- url     : https://prove2.me/theorems/cc3b2253-3129-43e1-93fa-901dc7f62a7c
-- title:
--   Kruskal Katona
-- statement:
--   Definitions and structural lemmas for Kruskal Katona, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
namespace BooleanIsoperimetry
def layer (N r : ℕ) : Finset (Cube N) :=
  Finset.univ.filter (fun x => x.card = r)
noncomputable def upperShadowVal (N r t : ℕ) : ℕ :=
  H N (binomPrefix N r + t) - binomPrefix N (r + 1)
noncomputable def layerInitSeg (N r t : ℕ) : Finset (Cube N) :=
  (simplicialInitSeg N (binomPrefix N r + t)).filter (fun x => x.card = r)
noncomputable def upperLayerShadow (N r : ℕ) (A : Finset (Cube N)) : Finset (Cube N) :=
  (Finset.upShadow A).filter (fun x => x.card = r + 1)
end BooleanIsoperimetry


