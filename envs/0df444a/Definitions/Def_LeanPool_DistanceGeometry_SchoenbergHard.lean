-- Prove2me | Definitions.Def_LeanPool_DistanceGeometry_SchoenbergHard
-- name    : LeanPool_DistanceGeometry_SchoenbergHard
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:45:44.453432+00:00
-- url     : https://prove2.me/theorems/38ee83a4-0c3b-421c-a081-01cfab962c84
-- title:
--   Schoenberg Hard
-- statement:
--   Definitions and structural lemmas for Schoenberg Hard, from Egor Lyfar; LeanPool contributors's pinned Euclidean distance geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/SchoenbergHard.lean

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Mathlib.Analysis.Matrix.PosDef
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Matrix
open scoped RealInnerProductSpace
namespace Matrix
variable {n k : ℕ}
section Factorization
variable {G : Matrix (Fin n) (Fin n) ℝ}
end Factorization
section Scatter
variable {p : Fin n → Prop} [DecidablePred p]
noncomputable def scatter (ι : {r : Fin n // p r} ↪ Fin k) :
    Matrix (Fin k) (Fin n) ℝ :=
  fun t r => if h : p r then (if ι ⟨r, h⟩ = t then (1 : ℝ) else 0) else 0
end Scatter
namespace PosSemidef
variable {G : Matrix (Fin n) (Fin n) ℝ}
end PosSemidef
end Matrix
namespace DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n k : ℕ} [NeZero n]
end DistanceGeometry


