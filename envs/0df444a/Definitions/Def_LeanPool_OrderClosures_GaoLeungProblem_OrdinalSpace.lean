-- Prove2me | Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
-- name    : LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:58:13.347238+00:00
-- url     : https://prove2.me/theorems/c0dcd39e-dba7-4e8c-835a-b7fb37277fce
-- title:
--   Ordinal Space
-- statement:
--   Definitions and structural lemmas for Ordinal Space, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace OrderClosures
open Set
universe u v
section OrdinalConstruction
abbrev GaoIndex (ξ : Ordinal.{u}) := Set.Iic (Ordinal.omega0 ^ ξ + 1)
def GaoCompactSpace (ξ : Ordinal.{u}) :=
  {x : GaoIndex ξ → Bool |
    ∀ a b : GaoIndex ξ, cnfExtensionLT a.1 b.1 → x a ≤ x b}
noncomputable def ordinalProjection (ξ : Ordinal.{u}) (ζ : GaoIndex ξ) :
    C(GaoCompactSpace ξ, ℝ) where
  toFun := fun x ↦ if x.1 ζ then 1 else 0
  continuous_toFun := by
    exact (continuous_of_discreteTopology :
      Continuous (fun b : Bool ↦ if b then (1 : ℝ) else 0)).comp
        ((continuous_apply ζ).comp continuous_subtype_val)
noncomputable def leastCNFExponent (ζ : Ordinal.{u}) : Ordinal.{u} :=
  ((Ordinal.CNF Ordinal.omega0 ζ).getLast?.map Prod.fst).getD 0
def GaoStageIndices (ξ β : Ordinal.{u}) : Set (GaoIndex ξ) :=
  {ζ | ζ.1 ≤ Ordinal.omega0 ^ ξ ∧ leastCNFExponent ζ.1 < β}
def GaoStageSet (ξ β : Ordinal.{u}) : Set C(GaoCompactSpace ξ, ℝ) :=
  {f | ∃ ζ ∈ GaoStageIndices ξ β, |f| ≤ ordinalProjection ξ ζ}
noncomputable def leadingCNFTerm (a : Ordinal.{u}) : Ordinal.{u} :=
  Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a *
    (a / Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a)
end OrdinalConstruction
end OrderClosures


