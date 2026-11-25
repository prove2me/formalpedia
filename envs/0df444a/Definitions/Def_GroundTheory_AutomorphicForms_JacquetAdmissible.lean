-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
-- name    : GroundTheory_AutomorphicForms_JacquetAdmissible
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T11:39:01.94825+00:00
-- url     : https://prove2.me/theorems/6dffdacd-d7ed-4f80-86fd-c8758c3fcb98
-- title:
--   Jacquet Admissible
-- statement:
--   Definitions and structural lemmas for Jacquet Admissible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
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
namespace Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
section Quotient
variable {G : Type*} [Group G] {U : Type*} [AddCommGroup U] [Module ℂ U]
  {τ : Representation ℂ G U}
def quotientMk (Y : Submodule ℂ U) (hY : ∀ g, Y ≤ Y.comap (τ g)) :
    Representation.IntertwiningMap τ (Representation.quotient τ Y hY) :=
  ⟨Y.mkQ, fun _ => LinearMap.ext fun _ => rfl⟩
end Quotient
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
section Transitivity
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
end Transitivity
section Generators
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
end Generators
section Jacquet
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
def refineFun (β γ : Fin n → ℕ) : Fin n → ℕ :=
  fun i => (Finset.univ.sup γ + 1) * β i + γ i
end Jacquet
end Parabolic
end GroundTheory.Automorphic


