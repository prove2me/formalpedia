-- Prove2me | Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
-- name    : Operator_Crouzeix_ResolventCauchyKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:51:31.607015+00:00
-- url     : https://prove2.me/theorems/8e87409f-d696-5073-8f36-bda4674486e2
-- title:
--   Resolvent Cauchy Kernel
-- statement:
--   Definitions and structural lemmas for Resolvent Cauchy Kernel, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


