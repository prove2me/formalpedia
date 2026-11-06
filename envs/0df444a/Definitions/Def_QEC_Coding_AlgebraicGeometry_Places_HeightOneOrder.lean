-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
-- name    : QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:11:53.614199+00:00
-- url     : https://prove2.me/theorems/7d637b8d-0c53-4aaf-a70e-8902ad3ac543
-- title:
--   Height One Order
-- statement:
--   Definitions and structural lemmas for Height One Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]
noncomputable def heightOnePlace
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra k K] [Algebra R K] [IsFractionRing R K]
    (H : IsDedekindDomain.HeightOneSpectrum R) : GlobalPlace k K where
  valuation := H.valuation K
  normalized := H.valuation_surjective K
end
end QEC.Coding.AlgebraicGeometry


