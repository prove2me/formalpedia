-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalKaehlerCyclic
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_LocalKaehlerCyclic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:01:27.051233+00:00
-- url     : https://prove2.me/theorems/30a931be-b7f9-4393-bca8-589dda520c94
-- title:
--   Local Kaehler Cyclic
-- statement:
--   Definitions and structural lemmas for Local Kaehler Cyclic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalKaehlerCyclic.lean

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.Module
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [CommRing k] [CommRing V] [Algebra k V]
variable [IsLocalRing V] [Algebra.EssFiniteType k V]
variable (K : Type*) [Field K] [Algebra k K] [Algebra V K]
variable [IsScalarTower k V K] [SMulCommClass k V K]
end
end QEC.Coding.AlgebraicGeometry


