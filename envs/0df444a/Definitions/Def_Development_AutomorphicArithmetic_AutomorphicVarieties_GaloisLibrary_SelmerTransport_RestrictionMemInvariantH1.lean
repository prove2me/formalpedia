-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:18.803093+00:00
-- url     : https://prove2.me/theorems/319e54b7-4f0c-4359-b78c-c8a194b86403
-- title:
--   Restriction Mem Invariant H1
-- statement:
--   Definitions and structural lemmas for Restriction Mem Invariant H1, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/RestrictionMemInvariantH1.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.Gal
namespace UpperTheory.V.Base
section Eig
variable {R Q N : Type} [CommRing R] [Group Q] [AddCommGroup N] [Module R N]
def eig (π : Representation R Q N) (ψ : Q →* Rˣ) : Submodule R N :=
  ⨅ g, LinearMap.ker (π g - ((ψ g : Rˣ) : R) • LinearMap.id)
def coeig (π : Representation R Q N) (ψ : Q →* Rˣ) : Submodule R N :=
  ⨆ g, LinearMap.range (π g - ((ψ g : Rˣ) : R) • LinearMap.id)
end Eig
variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
abbrev H1U (ρ : Representation R G M) (U : Subgroup G) : Type := H1 (ρ.comp U.subtype : Representation R U M)
abbrev Z1U (ρ : Representation R G M) (U : Subgroup G) : Submodule R (U → M) :=
  Z1 (ρ.comp U.subtype : Representation R U M)
abbrev H0U (ρ : Representation R G M) (U : Subgroup G) : Submodule R M :=
  H0 (ρ.comp U.subtype : Representation R U M)
def resU (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) : H1U ρ U →ₗ[R] H1U ρ U' :=
  pairH1DecompositionMap _ _ (Subgroup.inclusion h) (continuous_inclusion h) LinearMap.id continuous_id fun _ _ => rfl
theorem resU_mk (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) (z : Z1U ρ U) :
    ∃ z' : Z1U ρ U', resU ρ h (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ u : U', z'.1 u = z.1 ⟨u.1, h u.2⟩ := ⟨_, rfl, fun _ => rfl⟩
theorem resU_mk_eq_zero (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) (z : Z1U ρ U) :
    resU ρ h (Submodule.Quotient.mk z) = 0 ↔ ∃ m, ∀ u : U', z.1 ⟨u.1, h u.2⟩ = ρ u m - m := by
  obtain ⟨z', e, f⟩ := resU_mk ρ h z
  rw [e, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
  exact exists_congr fun m => forall_congr' fun u => by rw [f u]; rfl
theorem resU_resU (ρ : Representation R G M) {U'' U' U : Subgroup G} (h' : U'' ≤ U') (h : U' ≤ U) (x : H1U ρ U) :
    resU ρ h' (resU ρ h x) = resU ρ (h'.trans h) x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := resU_mk ρ h z
  obtain ⟨z₂, e₂, f₂⟩ := resU_mk ρ h' z₁
  obtain ⟨z₃, e₃, f₃⟩ := resU_mk ρ (h'.trans h) z
  rw [e₁, e₂, e₃]
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  rw [f₂, f₁, f₃]
def LocSel (ρ : Representation R G M) (U : Subgroup G) (𝒟 : Set (Subgroup G)) : Submodule R (H1U ρ U) :=
  ⨅ D ∈ 𝒟, LinearMap.ker (resU ρ (inf_le_left : U ⊓ D ≤ U))
theorem mem_locSel {ρ : Representation R G M} {U : Subgroup G} {𝒟 : Set (Subgroup G)} {x : H1U ρ U} :
    x ∈ LocSel ρ U 𝒟 ↔ ∀ D ∈ 𝒟, resU ρ (inf_le_left : U ⊓ D ≤ U) x = 0 := by
  simp only [LocSel, Submodule.mem_iInf, LinearMap.mem_ker]
theorem mk_mem_locSel {ρ : Representation R G M} {U : Subgroup G} {𝒟 : Set (Subgroup G)} {z : Z1U ρ U} :
    Submodule.Quotient.mk z ∈ LocSel ρ U 𝒟 ↔ ∀ D ∈ 𝒟, ∃ m, ∀ u : U, u.1 ∈ D → z.1 u = ρ u m - m := by
  rw [mem_locSel]
  refine forall₂_congr fun D _ => ?_
  rw [resU_mk_eq_zero]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, fun u hu => hm ⟨u.1, Subgroup.mem_inf.mpr ⟨u.2, hu⟩⟩⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, fun u => hm ⟨u.1, (Subgroup.mem_inf.mp u.2).1⟩ (Subgroup.mem_inf.mp u.2).2⟩
theorem resU_mem_locSel {ρ : Representation R G M} {U' U : Subgroup G} (h : U' ≤ U) {𝒟 : Set (Subgroup G)}
    {x : H1U ρ U} (hx : x ∈ LocSel ρ U 𝒟) : resU ρ h x ∈ LocSel ρ U' 𝒟 := by
  rw [mem_locSel] at hx ⊢
  intro D hD
  have hle : U' ⊓ D ≤ U ⊓ D := inf_le_inf_right D h
  calc resU ρ (inf_le_left : U' ⊓ D ≤ U') (resU ρ h x)
      = resU ρ ((inf_le_left : U' ⊓ D ≤ U').trans h) x := resU_resU ρ _ h x
    _ = resU ρ hle (resU ρ (inf_le_left : U ⊓ D ≤ U) x) := (resU_resU ρ hle inf_le_left x).symm
    _ = 0 := by rw [hx D hD, map_zero]
def selRes (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) (𝒟 : Set (Subgroup G)) :
    LocSel ρ U 𝒟 →ₗ[R] LocSel ρ U' 𝒟 :=
  (resU ρ h).restrict fun _ hx => resU_mem_locSel h hx
def ConjStable (𝒟 : Set (Subgroup G)) : Prop :=
  ∀ D ∈ 𝒟, ∀ g : G, ∃ D' ∈ 𝒟, ∀ x, x ∈ D ↔ g⁻¹ * x * g ∈ D'
abbrev quotRep (ρ : Representation R G M) (U U' : Subgroup G) [(U'.subgroupOf U).Normal] :=
  Representation.quotientToInvariants (ρ.comp U.subtype : Representation R U M) (U'.subgroupOf U)
section Conj
variable [IsTopologicalGroup G] [DiscreteTopology M]
def conjHom (U : Subgroup G) [hU : U.Normal] (g : G) : U →* U where
  toFun u := ⟨g⁻¹ * u * g, by simpa using hU.conj_mem u u.2 g⁻¹⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])
theorem continuous_conjHom (U : Subgroup G) [U.Normal] (g : G) : Continuous (conjHom U g) := by
  refine continuous_induced_rng.2 ?_
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const
def conjU (ρ : Representation R G M) (U : Subgroup G) [U.Normal] (g : G) : H1U ρ U →ₗ[R] H1U ρ U :=
  pairH1DecompositionMap _ _ (conjHom U g) (continuous_conjHom U g) (ρ g) continuous_of_discreteTopology fun u m => by
    show ρ g (ρ (g⁻¹ * u * g) m) = ρ u (ρ g m)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
theorem conjU_mk (ρ : Representation R G M) (U : Subgroup G) [U.Normal] (g : G) (z : Z1U ρ U) :
    ∃ z' : Z1U ρ U, conjU ρ U g (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ u : U, z'.1 u = ρ g (z.1 (conjHom U g u)) := ⟨_, rfl, fun _ => rfl⟩
def conjRep (ρ : Representation R G M) (U : Subgroup G) [U.Normal] : Representation R G (H1U ρ U) where
  toFun := conjU ρ U
  map_one' := LinearMap.ext fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨z', e, f⟩ := conjU_mk ρ U 1 z
    rw [e, Module.End.one_apply]
    congr 1
    refine Subtype.ext (funext fun u => ?_)
    rw [f, map_one, Module.End.one_apply]
    exact congrArg z.1 (Subtype.ext (by simp [conjHom]))
  map_mul' g h := LinearMap.ext fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨z₁, e₁, f₁⟩ := conjU_mk ρ U h z
    obtain ⟨z₂, e₂, f₂⟩ := conjU_mk ρ U g z₁
    obtain ⟨z₃, e₃, f₃⟩ := conjU_mk ρ U (g * h) z
    rw [Module.End.mul_apply, e₁, e₂, e₃]
    congr 1
    refine Subtype.ext (funext fun u => ?_)
    rw [f₃, f₂, f₁, map_mul, Module.End.mul_apply]
    exact congrArg (fun t => ρ g (ρ h (z.1 t))) (Subtype.ext (by simp [conjHom, mul_assoc]))
theorem conjRep_apply (ρ : Representation R G M) (U : Subgroup G) [U.Normal] (g : G) :
    conjRep ρ U g = conjU ρ U g := rfl
theorem conjRep_mem_locSel (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)}
    (h𝒟 : ConjStable 𝒟) (g : G) {x : H1U ρ U} (hx : x ∈ LocSel ρ U 𝒟) : conjRep ρ U g x ∈ LocSel ρ U 𝒟 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z', e, f⟩ := conjU_mk ρ U g z
  rw [conjRep_apply, e, mk_mem_locSel]
  rw [mk_mem_locSel] at hx
  intro D hD
  obtain ⟨D', hD', hiff⟩ := h𝒟 D hD g
  obtain ⟨m, hm⟩ := hx D' hD'
  refine ⟨ρ g m, fun u hu => ?_⟩
  rw [f u, hm (conjHom U g u) ((hiff u).mp hu), map_sub]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  simp [conjHom, mul_assoc]
def selRep (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟) :
    Representation R G (LocSel ρ U 𝒟) :=
  (conjRep ρ U).subrepresentation (LocSel ρ U 𝒟) fun g _ hx => conjRep_mem_locSel ρ U h𝒟 g hx
abbrev invariantsUnderSubgroupH1 (ρ : Representation R G M) (U U' : Subgroup G) [U'.Normal] : Submodule R (H1U ρ U') :=
  Representation.invariants ((conjRep ρ U').comp U.subtype : Representation R U (H1U ρ U'))
abbrev selEig (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟)
    (W : Subgroup G) (ψ : W →* Rˣ) : Submodule R (LocSel ρ U 𝒟) :=
  eig ((selRep ρ U h𝒟).comp W.subtype : Representation R W (LocSel ρ U 𝒟)) ψ
abbrev resCoker (ρ : Representation R G M) {U' U : Subgroup G} [U'.Normal] (h : U' ≤ U) : Type :=
  invariantsUnderSubgroupH1 ρ U U' ⧸ (LinearMap.range (resU ρ h)).comap (invariantsUnderSubgroupH1 ρ U U').subtype
end Conj
end UpperTheory.V.Base
end


