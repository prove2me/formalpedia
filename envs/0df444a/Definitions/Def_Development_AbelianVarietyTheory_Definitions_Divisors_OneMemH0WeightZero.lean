-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneMemH0WeightZero
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_OneMemH0WeightZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:59.898731+00:00
-- url     : https://prove2.me/theorems/a360c142-4865-4ec7-bf51-4b0a4f460ca9
-- title:
--   One Mem H0 Weight Zero
-- statement:
--   Definitions and structural lemmas for One Mem H0 Weight Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneMemH0WeightZero.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Quaternion
namespace GlobalTheory.QSA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
def nrm {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : R :=
  x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2
def coords {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : Fin 4 → R :=
  ![x.re, x.imI, x.imJ, x.imK]
scoped instance top {R : Type*} [CommRing R] [TopologicalSpace R] {a b : R} : TopologicalSpace ℍ[R, a, b] :=
  TopologicalSpace.induced coords inferInstance
variable (F : Type) [Field F] [NumberField F]
abbrev DA (a b : F) : Type := ℍ[AF F, algebraMap F (AF F) a, algebraMap F (AF F) b]
variable {F}
def rat {a b : F} (x : ℍ[F, a, b]) : DA F a b :=
  ⟨algebraMap F (AF F) x.re, algebraMap F (AF F) x.imI, algebraMap F (AF F) x.imJ, algebraMap F (AF F) x.imK⟩
def H0 {a b : F} (ε : AF F) : Set (DA F a b) :=
  {x | ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ x = rat γ * h}
end GlobalTheory.QSA


