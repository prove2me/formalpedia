-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:19.709804+00:00
-- url     : https://prove2.me/theorems/2c57f2dd-3163-4d9e-a802-f346fd5d1fc3
-- title:
--   Mem HFin In Iff
-- statement:
--   Definitions and structural lemmas for Mem HFin In Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
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
section Lin
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
def Lm (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (B : Matrix (Fin (M + 1)) (Fin M) E) : Matrix (Fin M) (Fin (M + 1)) E :=
  J'⁻¹ * Formalism.UG.cT (σ : E →+* E) B * J
def Xc (x : Fin 1 → Fin (M + 1) → E) : Matrix (Fin (M + 1)) (Fin 1) E := (Matrix.of x)ᵀ
def qm (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (b : E) :
    Matrix (Fin 1) (Fin (M + 1)) E :=
  b⁻¹ • ((Matrix.of x).map σ * J)
def Rm (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (x : Fin 1 → Fin (M + 1) → E) (b : E) :
    Matrix (Fin M) (Fin (M + 1)) E :=
  Lm σ J J' B - (Lm σ J J' B * Xc x) * qm σ J x b
variable {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
  {B : Matrix (Fin (M + 1)) (Fin M) E} {x : Fin 1 → Fin (M + 1) → E} {b : E}
end Lin
section Tens
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
variable (R : Type) [CommRing R] [Algebra F R]
end Tens
end PI.FT


