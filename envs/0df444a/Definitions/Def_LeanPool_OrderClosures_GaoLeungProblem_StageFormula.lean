-- Prove2me | Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
-- name    : LeanPool_OrderClosures_GaoLeungProblem_StageFormula
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:00:07.532342+00:00
-- url     : https://prove2.me/theorems/11ddfd36-6539-43ad-ab06-cb01e73b5179
-- title:
--   Stage Formula
-- statement:
--   Definitions and structural lemmas for Stage Formula, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace OrderClosures
open Set
universe u v
section OrdinalConstruction
def gaoDominators (ξ γ : Ordinal.{u})
    (b : C(GaoCompactSpace ξ, ℝ)) : Set (GaoIndex ξ) :=
  {ζ | ζ ∈ GaoStageIndices ξ γ ∧ b ≤ ordinalProjection ξ ζ}
def gaoMinimalDominators (ξ γ : Ordinal.{u})
    (b : C(GaoCompactSpace ξ, ℝ)) : Set (GaoIndex ξ) :=
  {μ | μ ∈ gaoDominators ξ γ b ∧
    ∀ η ∈ gaoDominators ξ γ b, cnfExtensionLE η.1 μ.1 → η = μ}
def singletonCNFBelow (γ : Ordinal.{u}) : Set (Ordinal.{u}) :=
  {q | ∃ δ d, Ordinal.CNF Ordinal.omega0 q = [(δ, d)] ∧
    q < Ordinal.omega0 ^ γ}
end OrdinalConstruction
end OrderClosures


