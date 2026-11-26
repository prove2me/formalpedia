-- Prove2me | Definitions.Def_AlonTarsiLib_GraphPolynomial
-- name    : AlonTarsiLib_GraphPolynomial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:12:00.793056+00:00
-- url     : https://prove2.me/theorems/b2efb497-4f2f-492a-b1aa-6d3eb9632e3d
-- title:
--   Graph Polynomial
-- statement:
--   Definitions and structural lemmas for Graph Polynomial, from Juan Pablo Traverso Gianini (jtraverso/alon-tarsi-choosability; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Alon-Tarsi theorem and 3-choosability of planar bipartite graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/GraphPolynomial.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset MvPolynomial
namespace AlonTarsi
variable {V : Type*}
noncomputable def graphPoly (A : Finset (V × V)) : MvPolynomial V ℤ :=
  ∏ a ∈ A, (X a.1 - X a.2)
noncomputable def outExp (A : Finset (V × V)) : V →₀ ℕ :=
  ∑ a ∈ A, Finsupp.single a.1 1
end AlonTarsi


