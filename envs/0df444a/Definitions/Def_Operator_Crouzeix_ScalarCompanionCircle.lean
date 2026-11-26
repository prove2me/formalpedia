-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
-- name    : Operator_Crouzeix_ScalarCompanionCircle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:10:33.233944+00:00
-- url     : https://prove2.me/theorems/69592fea-3b5a-5ca3-820c-04a85c977d5a
-- title:
--   Scalar Companion Circle
-- statement:
--   Definitions and structural lemmas for Scalar Companion Circle, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionCircle.lean

import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Definitions.Def_Operator_Crouzeix_VonNeumann
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real


