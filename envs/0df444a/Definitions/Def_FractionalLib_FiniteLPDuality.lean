-- Prove2me | Definitions.Def_FractionalLib_FiniteLPDuality
-- name    : FractionalLib_FiniteLPDuality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:26:28.546589+00:00
-- url     : https://prove2.me/theorems/e4b464ae-f408-4f5e-a025-57d06ebefeb8
-- title:
--   Finite LPDuality
-- statement:
--   Definitions and structural lemmas for Finite LPDuality, from Juan Pablo Traverso Gianini (jtraverso/erdos-girth-chromatic; see pinned Apache-2.0 LICENSE and source headers)'s pinned Graphs of large girth and large chromatic number: Erdos, Mycielski and Tutte development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/FiniteLPDuality.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators InnerProductSpace
open Finset
namespace FiniteLP
noncomputable def col {ι κ : Type*} [Fintype ι] (N : ι → κ → ℝ) (j : κ) :
    EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm (fun i => N i j)
noncomputable def toE {ι : Type*} [Fintype ι] (f : ι → ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm f
end FiniteLP


