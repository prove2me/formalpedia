-- Prove2me | Definitions.Def_Operator_SpectralSet_Normal
-- name    : Operator_SpectralSet_Normal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:42:15.938314+00:00
-- url     : https://prove2.me/theorems/09c33571-92b6-4db1-b9cf-11389ea37f88
-- title:
--   Normal
-- statement:
--   Definitions and structural lemmas for Normal, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/Normal.lean

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann
set_option autoImplicit false
open Polynomial


