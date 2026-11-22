-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
-- name    : LeanPool_BooleanIsoperimetry_LayerWindows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:32.441872+00:00
-- url     : https://prove2.me/theorems/7650909d-bb1c-419b-a514-d2e0c2c01e0b
-- title:
--   Layer Windows
-- statement:
--   Definitions and structural lemmas for Layer Windows, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BooleanIsoperimetry
open Finset
noncomputable def layerPart (N r : ℕ) (A : Finset (Cube N)) : Finset (Cube N) :=
  A.filter (fun x => x.card = r)
noncomputable def layerCount (N r : ℕ) (A : Finset (Cube N)) : ℕ :=
  (layerPart N r A).card
noncomputable def neighborhoodLayerCost (N a : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (N + 2), layerCount N r (neighborhood 1 (simplicialInitSeg N a))
noncomputable def initSegPairLayerWindowCost (N a b : ℕ) : ℕ :=
  max (neighborhoodLayerCost N a) b + max (neighborhoodLayerCost N b) a
noncomputable def layerWindowRemainder (N r a : ℕ) : ℕ :=
  layerCount N r (simplicialInitSeg N a)
noncomputable def layerWindowShadowCost (N r a : ℕ) : ℕ :=
  layerCount N r (neighborhood 1 (simplicialInitSeg N a))
noncomputable def PairLayerWindowCost (N r a b : ℕ) : ℕ :=
  max (layerWindowShadowCost N r a) (layerWindowRemainder N r b) +
  max (layerWindowShadowCost N r b) (layerWindowRemainder N r a)
end BooleanIsoperimetry


