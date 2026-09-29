-- Prove2me | solution 1 for AlgebraicGeometry.isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/97beb7e3-aba3-5f4a-b78b-cf534b36d70d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace NoethDesc

theorem isNoetherianRing_of_faithfullyFlat (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [IsNoetherianRing B] : IsNoetherianRing A := by
  have hmono : StrictMono (Ideal.map (algebraMap A B)) :=
    Monotone.strictMono_of_injective (fun I J h => Ideal.map_mono h) Ideal.map_injective_of_faithfullyFlat
  haveI : WellFoundedGT (Ideal B) := isNoetherian_iff'.mp (isNoetherianRing_iff.mp inferInstance)
  haveI : WellFoundedGT (Ideal A) := hmono.wellFoundedGT
  exact isNoetherianRing_iff.mpr (isNoetherian_iff'.mpr inferInstance)

theorem flat_pi {R : Type*} [CommRing R] {ι : Type*} [Finite ι] (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Flat R (S i)] : Module.Flat R (Π i, S i) := by
  classical
  haveI := Fintype.ofFinite ι
  haveI : Module.Flat R (DirectSum ι S) := Module.Flat.directSum_iff.mpr inferInstance
  exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι S).symm

end NoethDesc

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f] [IsLocallyNoetherian X] :
    IsLocallyNoetherian Y := by
  classical
  refine ⟨fun V => ?_⟩

  have hc : IsCompact ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) := f.isCompact_preimage V.2.isCompact
  obtain ⟨s, hs, hsU⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hc
  haveI : Finite s := hs.to_subtype
  have hle : ∀ i : s, ((i : X.affineOpens) : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens) := by
    intro i
    rw [hsU]
    exact le_iSup₂ (f := fun (j : X.affineOpens) (_ : j ∈ s) => (j : X.Opens)) i.1 i.2

  let R := Γ(Y, (V : Y.Opens))
  let S : s → Type _ := fun i => Γ(X, ((i : X.affineOpens) : X.Opens))
  let φ : ∀ i : s, R →+* S i := fun i => (f.appLE (V : Y.Opens) ((i : X.affineOpens) : X.Opens) (hle i)).hom
  letI : ∀ i : s, Algebra R (S i) := fun i => (φ i).toAlgebra

  haveI : ∀ i : s, Module.Flat R (S i) := fun i => by
    have hflat : (φ i).Flat :=
      HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat) f (inferInstance : AlgebraicGeometry.Flat f) V i.1 (hle i)
    exact hflat
  haveI : ∀ i : s, IsNoetherianRing (S i) := fun i => IsLocallyNoetherian.component_noetherian (i : X.affineOpens)

  haveI : Module.Flat R (Π i : s, S i) := NoethDesc.flat_pi S
  haveI : IsNoetherianRing (Π i : s, S i) := inferInstance

  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R (Π i : s, S i))) := by
    intro 𝔭

    let y : Y := V.2.fromSpec.base 𝔭
    obtain ⟨x, hx⟩ := (‹Surjective f›).surj y
    have hxV : x ∈ (f ⁻¹ᵁ (V : Y.Opens) : X.Opens) := by
      show f.base x ∈ (V : Y.Opens)
      rw [hx]
      have hy : y ∈ Set.range V.2.fromSpec.base := ⟨𝔭, rfl⟩
      rw [V.2.range_fromSpec] at hy
      exact hy
    rw [hsU] at hxV
    obtain ⟨i, hi, hxi⟩ : ∃ i ∈ s, x ∈ ((i : X.affineOpens) : X.Opens) := by
      simpa only [TopologicalSpace.Opens.mem_iSup, exists_prop] using hxV
    obtain ⟨𝔮, h𝔮⟩ : ∃ 𝔮, (i : X.affineOpens).2.fromSpec.base 𝔮 = x := by
      have : x ∈ Set.range (i : X.affineOpens).2.fromSpec.base := by rw [(i : X.affineOpens).2.range_fromSpec]; exact hxi
      exact this

    have hcomap : PrimeSpectrum.comap (φ ⟨i, hi⟩) 𝔮 = 𝔭 := by
      have hnat := IsAffineOpen.SpecMap_appLE_fromSpec f V.2 (i : X.affineOpens).2 (hle ⟨i, hi⟩)
      have h1 : V.2.fromSpec.base ((Spec.map (f.appLE (V : Y.Opens) ((i : X.affineOpens) : X.Opens) (hle ⟨i, hi⟩))).base 𝔮) =
          V.2.fromSpec.base 𝔭 := by
        have h2 : (Spec.map (f.appLE (V : Y.Opens) ((i : X.affineOpens) : X.Opens) (hle ⟨i, hi⟩)) ≫ V.2.fromSpec) 𝔮 =
            ((i : X.affineOpens).2.fromSpec ≫ f) 𝔮 := by rw [hnat]
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h2
        show V.2.fromSpec ((Spec.map (f.appLE (V : Y.Opens) ((i : X.affineOpens) : X.Opens) (hle ⟨i, hi⟩))) 𝔮) = V.2.fromSpec 𝔭
        rw [h2]
        show f.base ((i : X.affineOpens).2.fromSpec.base 𝔮) = V.2.fromSpec.base 𝔭
        rw [h𝔮, hx]
      exact V.2.fromSpec.isOpenEmbedding.injective h1
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun i : s => S i) ⟨i, hi⟩) 𝔮, ?_⟩
    rw [← hcomap, ← PrimeSpectrum.comap_comp_apply]
    rfl
  haveI : Module.FaithfullyFlat R (Π i : s, S i) := Module.FaithfullyFlat.of_comap_surjective hsurj
  exact NoethDesc.isNoetherianRing_of_faithfullyFlat R (Π i : s, S i)

end S_AlgebraicGeometry_isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact
end P2MW
export P2MW.S_AlgebraicGeometry_isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact (solution)
