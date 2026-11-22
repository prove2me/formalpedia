-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:02.231787+00:00
-- url     : https://prove2.me/theorems/1520f304-7850-4c04-9323-a2486e278424
-- title:
--   Twisted Is Real Order Lattice
-- statement:
--   Definitions and structural lemmas for Twisted Is Real Order Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwistedIsRealOrderLattice.lean

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.S6x5
open Module MeasureTheory
section General
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
noncomputable abbrev scal (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ) : V →ₗ[ℤ] V :=
  (c • (LinearMap.id : V →ₗ[ℝ] V)).restrictScalars ℤ
noncomputable def scalInv (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ) (hc : c ≠ 0) :
    V ≃L[ℝ] V :=
  ContinuousLinearEquiv.equivOfInverse (c⁻¹ • ContinuousLinearMap.id ℝ V)
    (c • ContinuousLinearMap.id ℝ V) (fun x => by simp [smul_smul, hc])
    (fun x => by simp [smul_smul, hc])
end General
end Formalism.FourierDecayAlt.P.S6x5
namespace Formalism.FourierDecayAlt.P.S6x5
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
noncomputable abbrev emb (E : Type) [Field E] [NumberField E] : E →ₗ[ℤ] mixedEmbedding.mixedSpace E :=
  (mixedEmbedding E).toAddMonoidHom.toIntLinearMap
end Formalism.FourierDecayAlt.P.S6x5
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x5
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
end Formalism.FourierDecayAlt.P


