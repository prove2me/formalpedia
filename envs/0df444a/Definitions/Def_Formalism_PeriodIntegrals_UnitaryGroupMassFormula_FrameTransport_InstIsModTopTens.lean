-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:00.178783+00:00
-- url     : https://prove2.me/theorems/117dc81e-1744-47b9-acb2-2db25090fee9
-- title:
--   Inst Is Mod Top Tens
-- statement:
--   Definitions and structural lemmas for Inst Is Mod Top Tens, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/InstIsModTopTens.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
section Mat
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
  {R : Type} [CommRing R] [Algebra F R]
abbrev mt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : HA R σ J) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
abbrev mtI {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : HA R σ J) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (((HA.mat R σ J g)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
end Mat
section Cont
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
instance instIsModTopTens : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
instance instContAddTens : ContinuousAdd (R ⊗[F] E) :=
  IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
end Cont
section Frame
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
local notation "ι" => inclR (F := F) (E := E) (AF F)
instance instNontrivialAF : Nontrivial (AF F) :=
  inferInstanceAs (Nontrivial (NumberField.InfiniteAdeleRing F ×
    IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))
end Frame
end PI.FT


