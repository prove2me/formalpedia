-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
-- name    : GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:24.023221+00:00
-- url     : https://prove2.me/theorems/6ccce425-889c-4cc4-b6ec-67135dfd9297
-- title:
--   Mem Invariants Comp Subtype Iff
-- statement:
--   Definitions and structural lemmas for Mem Invariants Comp Subtype Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Polynomial
open scoped Pointwise
namespace GroundTheory.Global
section Average
variable {G : Type*} [Group G]
def cosetAverage (I : Subgroup G) (f : G → ℂ) (g : G) : ℂ :=
  (Nat.card I : ℂ)⁻¹ * ∑ᶠ i : I, f (g * i)
end Average
section Inertia
variable {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S]
theorem mem_inertia_smul_iff (P : Ideal S) (h σ : G) :
    σ ∈ (h • P).inertia G ↔ h⁻¹ * σ * h ∈ P.inertia G := by
  constructor
  · intro hσ x
    have := hσ (h • x)
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem] at this
    simpa [mul_smul, smul_sub] using this
  · intro hσ x
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [mul_smul, smul_sub] using hσ (h⁻¹ • x)
theorem mul_mul_inv_mem_inertia {P : Ideal S} {s i : G} (hs : s ∈ MulAction.stabilizer G P)
    (hi : i ∈ P.inertia G) : s * i * s⁻¹ ∈ P.inertia G := by
  have hsP : s • P = P := hs
  rw [← hsP, mem_inertia_smul_iff, show s⁻¹ * (s * i * s⁻¹) * s = i by group]
  exact hi
end Inertia
section Place
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
omit [NumberField L] [IsGalois K L] in
theorem exists_liesOver : ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal := by
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  refine ⟨⟨Q, hQmax.isPrime, fun h => v.ne_bot ?_⟩, hQ⟩
  rw [hQ.over, h]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
def placeAbove : HeightOneSpectrum (𝓞 L) :=
  (exists_liesOver (L := L) v).choose
instance liesOver_placeAbove : (placeAbove (L := L) v).asIdeal.LiesOver v.asIdeal :=
  (exists_liesOver (L := L) v).choose_spec
variable (L) in

def localAverage (f : Gal(L/K) → ℂ) (m : ℕ) : ℂ :=
  cosetAverage ((placeAbove (L := L) v).asIdeal.inertia Gal(L/K)) f
    (arithFrobAt (𝓞 K) Gal(L/K) (placeAbove (L := L) v).asIdeal ^ m)
end Place
section Representation
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
abbrev subgroupInvariants (I : Subgroup G) : Submodule ℂ V :=
  Representation.invariants (ρ.comp I.subtype)
omit [Finite G] [FiniteDimensional ℂ V] in
theorem mem_invariants_comp_subtype_iff (I : Subgroup G) (x : V) :
    x ∈ subgroupInvariants ρ I ↔ ∀ i ∈ I, ρ i x = x :=
  ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩
omit [Finite G] [FiniteDimensional ℂ V] in

theorem mapsTo_invariants (I : Subgroup G) {g : G} (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) (x : V)
    (hx : x ∈ subgroupInvariants ρ I) : ρ g x ∈ subgroupInvariants ρ I := by
  rw [mem_invariants_comp_subtype_iff] at hx ⊢
  intro i hi
  rw [← Module.End.mul_apply, ← map_mul, show i * g = g * (g⁻¹ * i * g) by group, map_mul,
    Module.End.mul_apply, hx _ (hg i hi)]
def invariantsEnd (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) :
    Module.End ℂ (subgroupInvariants ρ I) :=
  (ρ g).restrict (mapsTo_invariants ρ I hg)
end Representation
section GaloisRepresentation
variable {K L V : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : Representation ℂ Gal(L/K) V)
omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem inv_mul_mul_mem_inertia (w : HeightOneSpectrum (𝓞 L)) {φ : Gal(L/K)}
    (hφ : φ ∈ MulAction.stabilizer Gal(L/K) w.asIdeal) :
    ∀ i ∈ w.asIdeal.inertia Gal(L/K), φ⁻¹ * i * φ ∈ w.asIdeal.inertia Gal(L/K) :=
  fun _ hi => by simpa using mul_mul_inv_mem_inertia (inv_mem hφ) hi
def inertiaFactor (w : HeightOneSpectrum (𝓞 L)) (φ : Gal(L/K))
    (hφ : φ ∈ MulAction.stabilizer Gal(L/K) w.asIdeal) : ℂ[X] :=
  (invariantsEnd ρ (w.asIdeal.inertia Gal(L/K)) φ (inv_mul_mul_mem_inertia w hφ)).charpoly.reverse
def localFactor : ℂ[X] :=
  inertiaFactor ρ (placeAbove v) (arithFrobAt (𝓞 K) Gal(L/K) (placeAbove (L := L) v).asIdeal)
    (IsArithFrobAt.arithFrobAt_mem_stabilizer _ _ _)
end GaloisRepresentation
end GroundTheory.Global


