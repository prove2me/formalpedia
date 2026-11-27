-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.bijective_etale_constant_cohomology_on_finite_projectiveLine_cover
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-27T06:21:30.622926+00:00
-- url     : https://prove2.me/submissions/1af20fc2-ec3b-481d-9c10-a21e5aba4b1b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleAdditiveCohomologyBaseChangeMap
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjectiveLineFiniteOverlap
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Finite
import Theorems.Thm_AlgebraicGeometry_Scheme_bijective_etale_cyclic_cohomology_prime_to_characteristic_on_finite_projectiveLine_cover
import Theorems.Thm_AlgebraicGeometry_Scheme_etale_additive_isBaseChange_on_finite_projectiveLine_cover
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_and_subsingleton_additive_etale_cohomology_of_two_affine_opens

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 950000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAdditiveStructureSheaf (sheaf frobenius cohomologyModule frobenius_cohomology_smul)
open PhilipponArtinSchreierBaseChange
open PhilipponArtinSchreierCohomology (artinSchreier_surjective mem_artinSchreierKernel_iff)
open PhilipponArtinSchreierKernel (constantIsoKernel)
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtalePrimeTorsionComparison (restrict)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleCharacteristicComparison

open scoped TensorProduct

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev primeCoefficients (p : ℕ) := AddCommGrpCat.of (ULift.{u} (ZMod p))

private def artinSchreierSequence {K : Type u} [Field K] {X : Scheme.{u}}
    (r : X ⟶ Spec (.of K)) {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0) :
    ShortComplex (Ab X) :=
  ShortComplex.mk (PhilipponArtinSchreierKernel.inclusion r hp hK)
    (frobenius r hp hK - 𝟙 (sheaf X))
    (by simp only [PhilipponArtinSchreierKernel.inclusion, Category.assoc, kernel.condition, comp_zero])

private theorem artinSchreierSequence_shortExact {K : Type u} [Field K] {X : Scheme.{u}}
    (r : X ⟶ Spec (.of K)) {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0) :
    (artinSchreierSequence r hp hK).ShortExact := by
  let g := frobenius r hp hK - 𝟙 (sheaf X)
  let T := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  let : Sheaf.IsLocallySurjective g := PhilipponArtinSchreierEtaleCover.locally_surjective r hp hK
  have hT : T.ShortExact := { exact := ShortComplex.exact_kernel g }
  let e := constantIsoKernel r hp hK
  let i : T ≅ artinSchreierSequence r hp hK := ShortComplex.isoMk e.symm
    (Iso.refl _) (Iso.refl _)
    (by change e.inv ≫ (e.hom ≫ kernel.ι g) = kernel.ι g ≫ 𝟙 _; simp)
    (by simp [T, g, artinSchreierSequence])
  exact ShortComplex.shortExact_of_iso i hT

private def artinSchreierMap {K E : Type u} [Field K] [Field E] [Algebra K E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    (h : a ≫ r = s ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)))
    {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0) (hE : (p : E) = 0) :
    (artinSchreierSequence r hp hK).map (pullbackSheaves a) ⟶ artinSchreierSequence s hp hE where
  τ₁ := (pullbackConstantIso a).hom.app (primeCoefficients p)
  τ₂ := structureComparison a
  τ₃ := structureComparison a
  comm₁₂ := (inclusion_baseChange a r s (algebraMap K E) h hp hK hE).symm
  comm₂₃ := by
    let L := pullbackSheaves a
    let : L.Additive := (pullbackAdjunction a).left_adjoint_additive
    change structureComparison a ≫ (frobenius s hp hE - 𝟙 (sheaf Y)) =
      L.map (frobenius r hp hK - 𝟙 (sheaf X)) ≫ structureComparison a
    rw [L.map_sub, L.map_id, Preadditive.comp_sub, Preadditive.sub_comp,
      structureComparison_frobenius a r s hp hK hE, Category.comp_id, Category.id_comp]

/-- In characteristic `p`, finite-dimensional additive cohomology and flat
base change imply field-extension comparison for constant prime coefficients. -/
theorem restrict_bijective_of_additiveBaseChange {K E : Type u}
    [Field K] [IsAlgClosed K] [Field E] [IsSepClosed E] [Algebra K E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    (h : a ≫ r = s ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)))
    {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0)
    (hFinite : ∀ q : ℕ, @Module.Finite K ((sheaf X).H q) _ _ (cohomologyModule r q))
    (hBase : IsAdditiveCohomologyBaseChange a r s h) (q : ℕ) :
    Function.Bijective (restrict a
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (primeCoefficients p)) q) := by
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hK
  have hE : (p : E) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap K E) hK
  let : CharP E p := (CharP.charP_iff_prime_eq_zero hp).mpr hE
  let S := artinSchreierSequence r hp hK
  let T := artinSchreierSequence s hp hE
  let m := artinSchreierMap a r s h hp hK hE
  let : IsIso m.τ₁ := inferInstanceAs (IsIso ((pullbackConstantIso a).hom.app (primeCoefficients p)))
  have hS (n : ℕ) : Function.Surjective (Sheaf.H.map S.g n) := by
    let := cohomologyModule r n
    let := hFinite n
    exact artinSchreier_surjective (frobenius r hp hK) n (frobenius_cohomology_smul r hp hK n)
  have hT (n : ℕ) : Function.Surjective (Sheaf.H.map T.g n) := by
    let := cohomologyModule r n
    let := cohomologyModule s n
    let := restrictedModule (K := K) s n
    let := restrictedModule_isScalarTower (K := K) s n
    let := hFinite n
    have hn : IsBaseChange E (linearComparison a r s h n) := hBase n
    let : Module.Finite E ((sheaf Y).H n) := Module.Finite.equiv hn.equiv
    exact artinSchreier_surjective (frobenius s hp hE) n (frobenius_cohomology_smul s hp hE n)
  apply restrict_bijective_of_kernel_comparison a S T (artinSchreierSequence_shortExact r hp hK)
    (artinSchreierSequence_shortExact s hp hE) m hS hT q
  let := cohomologyModule r q
  let := cohomologyModule s q
  let := restrictedModule (K := K) s q
  let := restrictedModule_isScalarTower (K := K) s q
  let := hFinite q
  have hb : IsBaseChange E (linearComparison a r s h q) := hBase q
  have hf := PhilipponArtinSchreierFieldExtension.bijOn_fixed_of_isBaseChange p
    (linearComparison a r s h q) hb (Sheaf.H.map (frobenius r hp hK) q)
    (Sheaf.H.map (frobenius s hp hE) q) (frobenius_cohomology_smul r hp hK q)
    (frobenius_cohomology_smul s hp hE q) (structureCohomologyComparison_frobenius a r s hp hK hE q)
  let FS := frobenius r hp hK
  let FT := frobenius s hp hE
  have hx : ((Sheaf.H.map (FS - 𝟙 _) q).ker : Set ((sheaf X).H q)) =
      {x | Sheaf.H.map (frobenius r hp hK) q x = x} :=
    Set.ext (mem_artinSchreierKernel_iff FS q)
  have hy : ((Sheaf.H.map (FT - 𝟙 _) q).ker : Set ((sheaf Y).H q)) =
      {x | Sheaf.H.map (frobenius s hp hE) q x = x} :=
    Set.ext (mem_artinSchreierKernel_iff FT q)
  change Set.BijOn (linearComparison a r s h q) ((Sheaf.H.map (FS - 𝟙 _) q).ker : Set ((sheaf X).H q))
    ((Sheaf.H.map (FT - 𝟙 _) q).ker : Set ((sheaf Y).H q))
  rwa [hx, hy]

end PhilipponEtaleCharacteristicComparison

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor (whiskerLeft)
open PhilipponEtalePrimeTorsionComparison (restrict)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleCyclicConstantComparison

universe u

/-- In a fixed degree, comparison for the constant cyclic group of order `l`
implies comparison for every finite constant abelian group killed by `l`. -/
theorem restrict_bijective_of_cyclic {X Y : Scheme.{u}} (f : Y ⟶ X)
    (l : ℕ) (hl : l.Prime) (q : ℕ)
    (h : Function.Bijective (restrict f
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod l)))) q))
    (M : AddCommGrpCat.{u}) [Finite M] (hM : l • 𝟙 M = 0) :
    Function.Bijective (restrict f
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M) q) := by
  classical
  let : Fact l.Prime := ⟨hl⟩
  let : Module (ZMod l) M := AddCommGroup.zmodModule fun x =>
    congrArg (fun a : M ⟶ M => a x) hM
  let I := Module.Basis.ofVectorSpaceIndex (ZMod l) (↑M : Type u)
  let : Finite I := inferInstanceAs (Finite {m : M // m ∈ I})
  let A := AddCommGrpCat.of (ULift.{u} (ZMod l))
  let b : Module.Basis I (ZMod l) M := Module.Basis.ofVectorSpace (ZMod l) (↑M : Type u)
  let e : M ≅ AddCommGrpCat.of (I → A) :=
    (b.equivFun.toAddEquiv.trans
      (AddEquiv.piCongrRight fun _ : I => (AddEquiv.ulift : A ≃+ ZMod l).symm)).toAddCommGrpIso
  let G : I → AddCommGrpCat.{u} := fun _ => A
  let d : (∐ G) ≅ AddCommGrpCat.of (I → A) :=
    (biproduct.isoCoproduct G).symm ≪≫ biproduct.isoProduct G ≪≫
      (productIsProduct G).conePointUniqueUpToIso
        (AddCommGrpCat.HasLimit.productLimitCone G).isLimit
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let L := pullbackSheaves f
  let F := C ⋙ Sheaf.functorH X.smallEtaleTopology q
  let F' := C ⋙ L ⋙ Sheaf.functorH Y.smallEtaleTopology q
  let : C.Additive := inferInstanceAs
    (Functor.const _ ⋙ presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).Additive
  let : L.Additive := (pullbackAdjunction f).left_adjoint_additive
  let : F.Additive := inferInstanceAs
    (C ⋙ Sheaf.functorH X.smallEtaleTopology q).Additive
  let : F'.Additive := inferInstanceAs
    (C ⋙ L ⋙ Sheaf.functorH Y.smallEtaleTopology q).Additive
  let α : F ⟶ F' :=
    { app B := AddCommGrpCat.ofHom (restrict f (C.obj B) q)
      naturality {B D} a := by
        ext x
        exact PhilipponExtComparison.comparison_post L _ (C.map a) q x }
  let : ∀ i : Discrete I, IsIso ((whiskerLeft (Discrete.functor G) α).app i) :=
    fun _ => (ConcreteCategory.isIso_iff_bijective _).mpr h
  let : IsIso (whiskerLeft (Discrete.functor G) α) := NatIso.isIso_of_isIso_app _
  let : PreservesFiniteCoproducts F := Functor.preservesFiniteCoproductsOfAdditive F
  let : PreservesFiniteCoproducts F' := Functor.preservesFiniteCoproductsOfAdditive F'
  have hsum : IsIso (α.app (∐ G)) :=
    isIso_app_coconePt_of_preservesColimit (Discrete.functor G) α _
      (colimit.isColimit (Discrete.functor G))
  exact (ConcreteCategory.isIso_iff_bijective (α.app M)).mp
    ((NatTrans.isIso_app_iff_of_iso α (e ≪≫ d.symm)).mpr hsum)

end PhilipponEtaleCyclicConstantComparison

end

section

attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (R L E : Type u) [CommRing R] [Field L] [IsAlgClosed L] [Field E] [IsAlgClosed E]
    (φ : L →+* E) (v : Spec (.of L) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of L)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
    (hP : IsPullback r d v (ProjSpace.π R 1)) (j : T ⟶ Spec (.of E)) (a : T ⟶ P)
    (hT : IsPullback j a (Spec.map (CommRingCat.ofHom φ)) r)
    {Y : Scheme.{u}} (p : Y ⟶ P) [IsFinite p] (N : ℕ) (hN : N.Prime)
    (M : AddCommGrpCat.{u}) [Finite M] (hM : N • 𝟙 M = 0) (q : ℕ) :
    Function.Bijective (PhilipponEtalePrimeTorsionComparison.restrict (pullback.snd a p)
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M) (q + 1)) := by
  apply PhilipponEtaleCyclicConstantComparison.restrict_bijective_of_cyclic
    (pullback.snd a p) N hN (q + 1) ?_ M hM
  by_cases hchar : (N : L) = 0
  · let : Algebra L E := φ.toAlgebra
    let b := pullback.snd a p
    let t := pullback.fst a p ≫ j
    have hY : IsPullback t b (Spec.map (CommRingCat.ofHom (algebraMap L E))) (p ≫ r) :=
      ((IsPullback.of_hasPullback a p).flip.paste_vert hT.flip).flip
    have h : b ≫ (p ≫ r) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap L E)) := hY.w.symm
    let : IsProper r := MorphismProperty.of_isPullback hP.flip (inferInstance : IsProper (ProjSpace.π R 1))
    let : IsProper (p ≫ r) := inferInstance
    let : IsProper t := MorphismProperty.of_isPullback hY.flip (inferInstance : IsProper (p ≫ r))
    let : IsAffineHom b := MorphismProperty.of_isPullback hY
      (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap L E))))
    obtain ⟨U, V, hU, hV, hUV⟩ := PhilipponEtaleProjectiveLineTwoAffine.exists_two_affine_opens v r d hP
    have hcover : p ⁻¹ᵁ U ⊔ p ⁻¹ᵁ V = ⊤ := by rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]
    have hcover' : b ⁻¹ᵁ (p ⁻¹ᵁ U) ⊔ b ⁻¹ᵁ (p ⁻¹ᵁ V) = ⊤ := by
      rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
    have sBounds := AlgebraicGeometry.Scheme.finite_and_subsingleton_additive_etale_cohomology_of_two_affine_opens L (p ≫ r) (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) (hU.preimage p) (hV.preimage p) hcover
    have tBounds := AlgebraicGeometry.Scheme.finite_and_subsingleton_additive_etale_cohomology_of_two_affine_opens E t (b ⁻¹ᵁ (p ⁻¹ᵁ U)) (b ⁻¹ᵁ (p ⁻¹ᵁ V))
      ((hU.preimage p).preimage b) ((hV.preimage p).preimage b) hcover'
    have low := AlgebraicGeometry.Scheme.etale_additive_isBaseChange_on_finite_projectiveLine_cover R L E v r d hP j a hT p h
    have allDegrees : PhilipponEtaleCharacteristicComparison.IsAdditiveCohomologyBaseChange b (p ≫ r) t h := by
      intro n
      cases n with
      | zero => exact low.1
      | succ n =>
        cases n with
        | zero => exact low.2
        | succ n =>
          let := sBounds.2 n
          let := tBounds.2 n
          exact PhilipponEtaleCharacteristicComparison.isBaseChange_of_subsingleton b (p ≫ r) t h (n + 2)
    exact PhilipponEtaleCharacteristicComparison.restrict_bijective_of_additiveBaseChange
      b (p ≫ r) t h hN hchar sBounds.1 allDegrees (q + 1)
  · exact AlgebraicGeometry.Scheme.bijective_etale_cyclic_cohomology_prime_to_characteristic_on_finite_projectiveLine_cover R L E φ v r d hP j a hT p N hN hchar q

end

end
