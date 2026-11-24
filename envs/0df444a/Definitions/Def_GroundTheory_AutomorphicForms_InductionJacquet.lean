-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
-- name    : GroundTheory_AutomorphicForms_InductionJacquet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:07.822957+00:00
-- url     : https://prove2.me/theorems/b5eb93e2-96cd-470e-9f32-edea6515d991
-- title:
--   Induction Jacquet
-- statement:
--   Definitions and structural lemmas for Induction Jacquet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
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
open Set Filter Topology
section Exactness
variable {N : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [LocallyCompactSpace N] [T2Space N] [TotallyDisconnectedSpace N]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ N V)
variable {W X : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
  {ρ} {σ : Representation ℂ N W} {τ : Representation ℂ N X}
end Exactness
section Translate
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (N : Subgroup G)
theorem mk_apply_of_mem {n : G} (hn : n ∈ N) (u : V) :
    Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ n u) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) u :=
  Representation.Coinvariants.mk_self_apply (ρ := ρ.comp N.subtype) ⟨n, hn⟩ u
def coinvariantsTranslate (a : G) (ha : ∀ n ∈ N, a * n * a⁻¹ ∈ N) :
    Representation.Coinvariants (ρ.comp N.subtype) →ₗ[ℂ]
      Representation.Coinvariants (ρ.comp N.subtype) :=
  Representation.Coinvariants.lift _ (Representation.Coinvariants.mk _ ∘ₗ ρ a) fun n =>
    LinearMap.ext fun u => by
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
        Subgroup.coe_subtype]
      have : ρ a (ρ n u) = ρ (a * n * a⁻¹) (ρ a u) := by
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
      rw [this]
      exact mk_apply_of_mem ρ N (ha n n.2) (ρ a u)
variable {ρ N}
end Translate
section JacquetLemma
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {N M Nbar K : Subgroup G}
end JacquetLemma
end GroundTheory.Automorphic


