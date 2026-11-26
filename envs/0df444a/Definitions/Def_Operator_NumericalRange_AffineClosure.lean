-- Prove2me | Definitions.Def_Operator_NumericalRange_AffineClosure
-- name    : Operator_NumericalRange_AffineClosure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:20:17.652113+00:00
-- url     : https://prove2.me/theorems/368e2a58-5a30-4cd1-a950-70a413ac97cd
-- title:
--   Affine Closure
-- statement:
--   Definitions and structural lemmas for Affine Closure, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/AffineClosure.lean

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Definitions.Def_Operator_NumericalRange_Affine
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


