-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoB
-- name    : ReciprocityTheory_GroupCohomology_InfIsoB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:12.809673+00:00
-- url     : https://prove2.me/theorems/a1d8eddf-da9d-469b-ac7c-91a1d9ef1b48
-- title:
--   Inf Iso B
-- statement:
--   Definitions and structural lemmas for Inf Iso B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfIsoB.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function Topology
noncomputable section
universe u
namespace InflationIsomorphism
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
section Inv
variable {N : Subgroup G} [N.Normal]
theorem inv_disc {A : TRep R G} [DiscreteTopology A.V] {Q : TRep R (G ⧸ N)} {P : Pair Q A}
    (hP : IsInvRep A N Q P) : DiscreteTopology Q.V := hP.2.1.discreteTopology
theorem inv_mem {A : TRep R G} {Q : TRep R (G ⧸ N)} {P : Pair Q A} (hP : IsInvRep A N Q P) (q : Q.V) :
    ∀ g ∈ N, A.rho g (P.u q) = P.u q := (hP.2.2 _).1 ⟨q, rfl⟩
theorem inv_equiv {A : TRep R G} {Q : TRep R (G ⧸ N)} {P : Pair Q A} (hP : IsInvRep A N Q P) (g : G)
    (q : Q.V) : P.u (Q.rho (g : G ⧸ N) q) = A.rho g (P.u q) := by
  have h := P.equiv g q
  rw [hP.1] at h
  exact h
def invLin {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)} {PB : Pair QB B}
    (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB) (a : A.V →ₗ[R] B.V)
    (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) : QA.V →ₗ[R] QB.V :=
  (LinearEquiv.ofInjective PB.u hB.2.1.injective).symm.toLinearMap.comp
    ((a.comp PA.u).codRestrict (LinearMap.range PB.u) fun q => (hB.2.2 _).2 fun g hg => by
      rw [LinearMap.comp_apply, ← ha, inv_mem hA q g hg])
theorem invLin_spec {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)}
    {PB : Pair QB B} (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB) (a : A.V →ₗ[R] B.V)
    (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) (q : QA.V) : PB.u (invLin hA hB a ha q) = a (PA.u q) := by
  unfold invLin
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofInjective_symm_apply]
  rfl
def invPair {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)} {PB : Pair QB B}
    [DiscreteTopology A.V] (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB) (a : A.V →ₗ[R] B.V)
    (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) : Pair QA QB :=
  have := inv_disc hA
  Pair.ofMap (invLin hA hB a ha) continuous_of_discreteTopology fun y q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    apply hB.2.1.injective
    rw [inv_equiv hB, invLin_spec, invLin_spec, inv_equiv hA, ha]
end Inv
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G] {N : Subgroup G} [N.Normal]
abbrev Mbot (M : TRep R G) : TRep R (⊥ : Subgroup (G ⧸ N)) := M.res 1 continuous_const
def evC (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) : Pair QC (Mbot (N := N) M) :=
  have := inv_disc hC
  { φ := (⊥ : Subgroup (G ⧸ N)).subtype
    u := (coindEv (⊥ : Subgroup G) (M.resSub ⊥)).u.comp PC.u
    φ_cont := continuous_subtype_val
    u_cont := continuous_of_discreteTopology
    equiv := fun g m => by
      have hg : g = 1 := Subtype.ext (Subgroup.mem_bot.1 g.2)
      subst hg
      show _ = M.rho 1 _
      rw [map_one, map_one, map_one]
      rfl }
end InflationIsomorphism
end
end ReciprocityTheory.Coh


