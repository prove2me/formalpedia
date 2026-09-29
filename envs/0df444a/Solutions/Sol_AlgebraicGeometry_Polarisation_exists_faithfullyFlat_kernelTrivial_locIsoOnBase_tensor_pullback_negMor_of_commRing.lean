-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_faithfullyFlat_kernelTrivial_locIsoOnBase_tensor_pullback_negMor_of_commRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5a87f5f2-b594-5d80-8601-e5f6dc6430e7

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_pullback_fst_of_kernelTrivial
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_tensor_pullback_negMor_of_commRing

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace SqrtHelpers

theorem inv_natural {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (G : RelativeGroupLaw R₀ f) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R₀)) (t' : T' ⟶ Spec (CommRingCat.of R₀))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h : GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) * GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := by
    show G.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x)) (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = G.one t'
    rw [← G.mul_natural t t' ψ hψ, G.inv_mul_cancel, G.one_natural t t' ψ hψ]
  show GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) = (GoodReductionJacobian.schemeHomOverComp ψ hψ x)⁻¹
  exact (inv_eq_of_mul_eq_one_left h).symm

end SqrtHelpers

theorem solution
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛₀ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∀ (L' : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₁ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
          Scheme.Modules.IsInvertible 𝓛₁ ∧ KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L' 𝓛₁ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj
              (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀))
            (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L')).obj 𝓛₁) := by
  refine ⟨S, inferInstance, inferInstance, inferInstance, fun L' hL' => ?_⟩

  let g := Spec.map (CommRingCat.ofHom (algebraMap S S))
  let X := pullback f g
  let p₁ : X ⟶ A := pullback.fst f g
  let p₂ := pullback.snd f g
  let N := negMor f L
  let N' := negMor p₂ L'
  refine ⟨(Scheme.Modules.pullback p₁).obj 𝓛₀, h₀.pullback p₁,
    kernelTrivial_pullback_fst_of_kernelTrivial f L 𝓛₀ h₀ hK S L' hL', ?_⟩

  have hbase : p₁ ≫ f = p₂ ≫ g := pullback.condition

  have hone : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S)),
      (L'.one t').1 ≫ p₁ = (L.one (t' ≫ g)).1 := by
    intro T t'
    letI := L.pointGroup (t' ≫ g)
    let e' : SchemeHomOver (t' ≫ g) f := ⟨(L'.one t').1 ≫ p₁, by rw [Category.assoc, pullback.condition, ← Category.assoc, (L'.one t').2]⟩
    have h := hL' T t' (L'.one t') (L'.one t')
    rw [L'.one_mul] at h

    have h2 : e' * e' = e' := Subtype.ext h.symm
    have h3 : e' = 1 := by
      have := congrArg (· * e'⁻¹) h2
      simpa [mul_assoc] using this
    exact congrArg Subtype.val h3

  have hinv : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t' p₂),
      (L'.inv t' P).1 ≫ p₁ = (L.inv (t' ≫ g) ⟨P.1 ≫ p₁, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩).1 := by
    intro T t' P
    letI := L.pointGroup (t' ≫ g)
    let Pb : SchemeHomOver (t' ≫ g) f := ⟨P.1 ≫ p₁, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
    let Q : SchemeHomOver (t' ≫ g) f := ⟨(L'.inv t' P).1 ≫ p₁, by rw [Category.assoc, pullback.condition, ← Category.assoc, (L'.inv t' P).2]⟩
    have h := hL' T t' (L'.inv t' P) P
    rw [L'.inv_mul_cancel, hone] at h

    have h2 : Q * Pb = 1 := Subtype.ext h.symm
    have h3 : Q = Pb⁻¹ := eq_inv_of_mul_eq_one_left h2
    exact congrArg Subtype.val h3

  have hN : N' ≫ p₁ = p₁ ≫ N := by
    have h1 := hinv X p₂ (idPt p₂)

    have h2 : p₁ ≫ N = (L.inv (p₂ ≫ g) ⟨(idPt p₂).1 ≫ p₁, by rw [Category.assoc, pullback.condition, ← Category.assoc, (idPt p₂).2]⟩).1 := by
      have hn := SqrtHelpers.inv_natural L f (p₂ ≫ g) p₁ hbase (idPt f)
      have hc' : GoodReductionJacobian.schemeHomOverComp p₁ hbase (idPt f) =
          ⟨(idPt p₂).1 ≫ p₁, by rw [Category.assoc, pullback.condition, ← Category.assoc, (idPt p₂).2]⟩ := by
        apply Subtype.ext
        show p₁ ≫ 𝟙 A = 𝟙 X ≫ p₁
        rw [Category.comp_id, Category.id_comp]
      rw [hc'] at hn
      exact (congrArg Subtype.val hn)
    rw [h2]
    exact h1

  let e₁ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback N).obj 𝓛₀) ≅
      (Scheme.Modules.pullback N').obj ((Scheme.Modules.pullback p₁).obj 𝓛₀) :=
    (Scheme.Modules.pullbackComp p₁ N).app 𝓛₀ ≪≫ (Scheme.Modules.pullbackCongr hN.symm).app 𝓛₀ ≪≫
      ((Scheme.Modules.pullbackComp N' p₁).app 𝓛₀).symm
  let eG : (Scheme.Modules.pullback p₁).obj (𝓛₀ ⊗ (Scheme.Modules.pullback N).obj 𝓛₀) ≅
      (Scheme.Modules.pullback p₁).obj 𝓛₀ ⊗ (Scheme.Modules.pullback N').obj ((Scheme.Modules.pullback p₁).obj 𝓛₀) :=
    Scheme.Modules.pullbackTensorObjIso p₁ _ _ ≪≫ (Iso.refl _ ⊗ᵢ e₁)
  intro s
  exact ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (p₂ ⁻¹ᵁ ⊤).ι).mapIso eG⟩⟩

end S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_tensor_pullback_negMor_of_commRing
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_tensor_pullback_negMor_of_commRing (solution)
