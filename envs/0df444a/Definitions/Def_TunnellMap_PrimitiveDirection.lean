-- Prove2me | Definitions.Def_TunnellMap_PrimitiveDirection
-- name    : TunnellMap_PrimitiveDirection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:53:59.530016+00:00
-- url     : https://prove2.me/theorems/a40b4233-140a-5650-b7d9-1c7422445c3a
-- title:
--   Primitive Direction
-- statement:
--   Definitions and structural lemmas for Primitive Direction, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
set_option autoImplicit true
namespace TunnellMap
open Polynomial
noncomputable def triplePolynomial (v : Triple) : ℤ[X] :=
  C v.x + C v.y * X + C v.z * X ^ 2
def polynomialTriple (f : ℤ[X]) : Triple :=
  ⟨f.coeff 0, f.coeff 1, f.coeff 2⟩
noncomputable def tripleContent (v : Triple) : ℤ :=
  (triplePolynomial v).content
noncomputable def primitivePartTriple (v : Triple) : Triple :=
  polynomialTriple (triplePolynomial v).primPart
def FirstNonzeroPositive (v : Triple) : Prop :=
  0 < v.x ∨ (v.x = 0 ∧ 0 < v.y) ∨ (v.x = 0 ∧ v.y = 0 ∧ 0 < v.z)
instance firstNonzeroPositiveDecidable (v : Triple) : Decidable (FirstNonzeroPositive v) :=
  by
    unfold FirstNonzeroPositive
    infer_instance
def orientDirection (v : Triple) : Triple :=
  if FirstNonzeroPositive v then v else negTriple v
noncomputable def primitiveDirection (v : Triple) : Triple :=
  orientDirection (primitivePartTriple v)
noncomputable def directionScale (v : Triple) : ℤ :=
  if FirstNonzeroPositive (primitivePartTriple v) then
    tripleContent v
  else
    -tripleContent v
end TunnellMap


