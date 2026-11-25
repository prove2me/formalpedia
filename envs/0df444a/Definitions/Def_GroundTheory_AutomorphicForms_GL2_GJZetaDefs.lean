-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
-- name    : GroundTheory_AutomorphicForms_GL2_GJZetaDefs
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:30.491997+00:00
-- url     : https://prove2.me/theorems/8979c4c3-09e4-424a-aa25-b5d57fb413bf
-- title:
--   GJZeta Defs
-- statement:
--   Definitions and structural lemmas for GJZeta Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJZetaDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleFiniteLength
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
def IsSchwartzBruhat (Φ : Matrix (Fin n) (Fin n) F → ℂ) : Prop :=
  IsLocallyConstant Φ ∧ HasCompactSupport Φ
def absDet (g : GL (Fin n) F) : ℝ :=
  (LocalField.modulus ((g : Matrix (Fin n) (Fin n) F).det) : ℝ)
def detPow (g : GL (Fin n) F) (s : ℂ) : ℂ :=
  (absDet g : ℂ) ^ s
variable (F) in

def qs (s : ℂ) : ℂ :=
  (LocalField.residueCard F : ℂ) ^ (-s)
def ordDet (g : GL (Fin n) F) : ℤ :=
  LocalField.ord ((g : Matrix (Fin n) (Fin n) F).det)
def IsLeviSchwartz {α : Type*} (β : Fin n → α) (Ψ : Matrix (Fin n) (Fin n) F → ℂ) : Prop :=
  ∃ r A : ℕ,
    (∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      (∀ i j, β i ≠ β j → Y i j = 0) →
      (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) → Ψ (X + Y) = Ψ X) ∧
    (∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) → Ψ X ≠ 0 →
      ∀ i j, (uniformizer F : F) ^ A * X i j ∈ 𝒪[F])
end GodementJacquet
end GroundTheory.Automorphic


