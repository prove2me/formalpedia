-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:18.078263+00:00
-- url     : https://prove2.me/theorems/70601982-26e6-4734-80a3-84c55c51e0d7
-- title:
--   Fin Theta
-- statement:
--   Definitions and structural lemmas for Fin Theta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
section Coord
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
def crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k
end Coord
section Bounds
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
end Bounds
section Places
variable (F : Type) [Field F] [NumberField F]
def piV (v : HeightOneSpectrum (𝓞 F)) : AF F →ₐ[F] Fv F v := (evalV F v).comp (sndA F)
def piW (w : InfinitePlace F) : AF F →ₐ[F] w.Completion :=
  (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w).comp (fstA F)
end Places
section Finite
variable {F : Type} [Field F] [NumberField F]
end Finite
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
end Main
end PI.VolStabSW.FiniteThetaCoordinates
namespace PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
end PI.VolStabSW


