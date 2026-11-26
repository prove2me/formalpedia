-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleClosedFiberOverlapPreimages
-- name    : AlgebraicGeometry_EtaleClosedFiberOverlapPreimages
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T02:44:17.505266+00:00
-- url     : https://prove2.me/theorems/92990173-fb67-5060-a67e-1db503794694
-- title:
--   Finite models of first cohomology classes on the closed fiber
-- statement:
--   For the two affine charts on the closed fiber, use Mayer–Vietoris and lift the resulting section on the affine overlap.
-- source:
--   Mayer–Vietoris and the finite model method for étale cohomology.

import Definitions.Def_AlgebraicGeometry_EtaleOpenFiniteCoefficientModels
import Definitions.Def_AlgebraicGeometry_ProjectiveLineFiniteOverlap
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleExtensionByZero (restrict)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleMayerVietoris

universe u

variable {X : Scheme.{u}} (U V : X.Opens)

private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)
private abbrev openChart (U : X.Opens) : X.Etale := Scheme.Etale.mk U.ι

private def inclusion (U : X.Opens) : openChart U ⟶ terminal X :=
  MorphismProperty.Over.homMk U.ι (Category.comp_id _) trivial

private def intersectionMap {U V : X.Opens} (h : U ≤ V) : openChart U ⟶ openChart V :=
  MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι h) trivial

private def square : Square X.Etale where
  X₁ := openChart (U ⊓ V)
  X₂ := openChart U
  X₃ := openChart V
  X₄ := terminal X
  f₁₂ := intersectionMap inf_le_left
  f₁₃ := intersectionMap inf_le_right
  f₂₄ := inclusion U
  f₃₄ := inclusion V
  fac := MorphismProperty.Over.Hom.ext
    ((X.homOfLE_ι inf_le_left).trans (X.homOfLE_ι inf_le_right).symm)

private abbrev underlying (X : Scheme.{u}) : X.Etale ⥤ Scheme.{u} :=
  Scheme.Etale.forget X ⋙ Over.forget X

private instance (U : X.Opens) : Mono (inclusion U) :=
  Functor.mono_of_mono_map (underlying X) (inferInstanceAs (Mono U.ι))

private theorem isPullback_square : (square U V).IsPullback :=
  IsPullback.of_map (underlying X) (square U V).fac (isPullback_opens_inf U V)

private theorem opens_cover (h : U ⊔ V = ⊤) :
    Sieve.ofTwoArrows (inclusion U) (inclusion V) ∈ X.smallEtaleTopology (terminal X) := by
  rw [Sieve.ofTwoArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff]
  refine Set.eq_univ_of_forall ?_
  intro x
  have hx : x ∈ U ⊔ V := h.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
  rcases hx with hx | hx
  · exact Set.mem_iUnion.mpr ⟨WalkingPair.left, ⟨⟨x, hx⟩, rfl⟩⟩
  · exact Set.mem_iUnion.mpr ⟨WalkingPair.right, ⟨⟨x, hx⟩, rfl⟩⟩

/-- Two open subschemes covering a scheme give a Mayer–Vietoris square in
the small étale site. -/
def mayerVietoris (h : U ⊔ V = ⊤) : X.smallEtaleTopology.MayerVietorisSquare := by
  let : Mono (square U V).f₂₄ := inferInstanceAs (Mono (inclusion U))
  let : Mono (square U V).f₃₄ := inferInstanceAs (Mono (inclusion V))
  exact GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    (J := X.smallEtaleTopology) (square U V) (isPullback_square U V) (opens_cover U V h)

private def terminalChartIsTerminal (X : Scheme.{u}) : IsTerminal (terminal X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

/-- The connecting map from degree-zero cohomology of the overlap to degree-one
cohomology of the whole scheme. -/
def overlapBoundary (h : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    F.H' 0 (openChart (U ⊓ V)) →+ F.H 1 :=
  ((PhilipponSheafCohomology.terminalComparison X.smallEtaleTopology
    (terminalChartIsTerminal X) F 1).symm.toAddMonoidHom).comp
      (((mayerVietoris U V h).δ F 0 1 rfl).hom)

/-- The overlap boundary commutes with a change of coefficient sheaf. -/
theorem overlapBoundary_naturality (h : U ⊔ V = ⊤)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (a : F ⟶ G)
    (t : F.H' 0 (openChart (U ⊓ V))) :
    overlapBoundary U V h G (t.comp (Ext.mk₀ a) rfl) =
      Sheaf.H.map a 1 (overlapBoundary U V h F t) := by
  let S := mayerVietoris U V h
  let e := PhilipponSheafCohomology.freeTerminalIso X.smallEtaleTopology (terminalChartIsTerminal X)
  let d := S.shortComplex_shortExact.extClass
  change (Ext.mk₀ e.inv).comp (d.comp (t.comp (Ext.mk₀ a) rfl) rfl) rfl =
    ((Ext.mk₀ e.inv).comp (d.comp t rfl) rfl).comp (Ext.mk₀ a) rfl
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero]

/-- If degree-one cohomology vanishes on both members of the cover, every
degree-one class is the boundary of a section on the overlap. -/
theorem overlapBoundary_surjective (h : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (hU : Subsingleton (((restrict U.ι).obj F).H 1))
    (hV : Subsingleton (((restrict V.ι).obj F).H 1)) :
    Function.Surjective (overlapBoundary U V h F) := by
  let S := mayerVietoris U V h
  let e := PhilipponSheafCohomology.terminalComparison X.smallEtaleTopology
    (terminalChartIsTerminal X) F 1
  let _ := hU
  let _ := hV
  have z₂ : IsZero (F.H' 1 S.X₂) := AddCommGrpCat.isZero_iff_subsingleton.mpr
    ((PhilipponEtaleOpenCohomology.openComparison U.ι F 1).injective.subsingleton)
  have z₃ : IsZero (F.H' 1 S.X₃) := AddCommGrpCat.isZero_iff_subsingleton.mpr
    ((PhilipponEtaleOpenCohomology.openComparison V.ι F 1).injective.subsingleton)
  have hTo : S.toBiprod F 1 = 0 := by
    apply biprod.hom_ext
    · exact z₂.eq_of_tgt _ _
    · exact z₃.eq_of_tgt _ _
  have hexact : Function.Exact (S.δ F 0 1 rfl) (S.toBiprod F 1) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp ((S.sequence_exact F 0 1 rfl).exact 2)
  intro x
  obtain ⟨t, ht⟩ := (hexact (e x)).mp (by rw [hTo]; rfl)
  exact ⟨t, e.symm_apply_eq.mpr ht⟩

end PhilipponEtaleMayerVietoris

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleClosedFiberDegreeOne (finiteConstantModel)
open PhilipponEtaleExtensionByZero (restrict)
open PhilipponEtaleMayerVietoris (overlapBoundary overlapBoundary_naturality overlapBoundary_surjective)
open PhilipponEtaleModuleSkyscrapers (underlying)
open PhilipponEtaleNeighborhoodRestriction (restrictionIso)
open PhilipponEtaleOpenCohomology (openComparison openComparison_map)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleClosedFiberOverlap

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Modules (X : Scheme.{u}) (N : ℕ) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))

variable {S X : Scheme.{u}} (j : S ⟶ X) (W : X.Opens)

/-- Restricting an inverse image to the preimage of an open is the inverse
image of the restricted coefficient sheaf. -/
def restrictPullbackIso :
    pullbackSheaves j ⋙ restrict (j ⁻¹ᵁ W).ι ≅ restrict W.ι ⋙ pullbackSheaves (j ∣_ W) :=
  Functor.isoWhiskerLeft (pullbackSheaves j) (restrictionIso (j ⁻¹ᵁ W).ι) ≪≫
    pullbackCompIso j (j ⁻¹ᵁ W).ι ≪≫
    eqToIso (congrArg pullbackSheaves (morphismRestrict_ι j W).symm) ≪≫
    (pullbackCompIso W.ι (j ∣_ W)).symm ≪≫
    Functor.isoWhiskerRight (restrictionIso W.ι).symm (pullbackSheaves (j ∣_ W))

private def preimageSectionsIso (O : S.Opens) (hO : O = j ⁻¹ᵁ W) (F : Ab X) :
    ((pullbackSheaves j).obj F).H' 0 (Scheme.Etale.mk O.ι) ≃+
      ((pullbackSheaves (j ∣_ W)).obj ((restrict W.ι).obj F)).H 0 := by
  subst O
  exact (openComparison (j ⁻¹ᵁ W).ι ((pullbackSheaves j).obj F) 0).trans
    (((Sheaf.functorH _ 0).mapIso ((restrictPullbackIso j W).app F)).addCommGroupIsoToAddEquiv)

private theorem naturality_apply {C D : Type*} [Category* C] [Category* D] {L R : C ⥤ D}
    (E : L ≅ R) (H : D ⥤ AddCommGrpCat.{u}) {F G : C} (a : F ⟶ G)
    (x : H.obj (L.obj F)) :
    H.map (E.hom.app G) (H.map (L.map a) x) = H.map (R.map a) (H.map (E.hom.app F) x) := by
  have h := congrArg H.map (E.hom.naturality a)
  rw [H.map_comp, H.map_comp] at h
  exact ConcreteCategory.congr_hom h x

private theorem preimageSectionsIso_map (O : S.Opens) (hO : O = j ⁻¹ᵁ W)
    {F G : Ab X} (a : F ⟶ G)
    (t : ((pullbackSheaves j).obj F).H' 0 (Scheme.Etale.mk O.ι)) :
    preimageSectionsIso j W O hO G (t.comp (Ext.mk₀ ((pullbackSheaves j).map a)) rfl) =
      Sheaf.H.map ((pullbackSheaves (j ∣_ W)).map ((restrict W.ι).map a)) 0
        (preimageSectionsIso j W O hO F t) := by
  subst O
  let Z := (j ⁻¹ᵁ W).toScheme
  let E := restrictPullbackIso j W
  let L := pullbackSheaves j ⋙ restrict (j ⁻¹ᵁ W).ι
  let R := restrict W.ι ⋙ pullbackSheaves (j ∣_ W)
  let H := Sheaf.functorH Z.smallEtaleTopology 0
  let e (F : Ab X) := openComparison (j ⁻¹ᵁ W).ι ((pullbackSheaves j).obj F) 0
  change H.map (E.hom.app G) (e G (t.comp (Ext.mk₀ ((pullbackSheaves j).map a)) rfl)) =
    H.map (R.map a) (H.map (E.hom.app F) (e F t))
  rw [openComparison_map]
  exact naturality_apply (L := L) (R := R) E H a (e F t)

private theorem vanishing_on_preimage (F : Ab X) (n : ℕ)
    (h : Subsingleton (((pullbackSheaves (j ∣_ W)).obj ((restrict W.ι).obj F)).H n)) :
    Subsingleton (((restrict (j ⁻¹ᵁ W).ι).obj ((pullbackSheaves j).obj F)).H n) := by
  let e := ((Sheaf.functorH _ n).mapIso ((restrictPullbackIso j W).app F)).addCommGroupIsoToAddEquiv
  exact ⟨fun a b => e.injective (h.elim (e a) (e b))⟩

/-- Lifting sections of a closed restriction on an affine base by bounded
finite models of the ambient coefficient sheaf. -/
def AffineModelSections (N : ℕ) : Prop :=
  ∀ {W S : Scheme.{u}} [IsAffine W] (i : S ⟶ W) [IsClosedImmersion i]
    (F : Ab W), N • 𝟙 F = 0 → ∀ x : ((pullbackSheaves i).obj F).H 0,
      ∃ (B : Ab W) (b : B ⟶ F) (y : ((pullbackSheaves i).obj B).H 0),
        Sheaf.H.map ((pullbackSheaves i).map b) 0 y = x ∧ boundedFiniteModel W N B

/-- The affine lifting follows by pulling a filtered bounded presentation
back to the affine closed subscheme and lifting in degree zero. -/
theorem affineModelSections_of_ind (N : ℕ)
    (hModels : ∀ (W : Scheme.{u}) [IsAffine W] (F : Ab W), N • 𝟙 F = 0 →
      ObjectProperty.ind.{u} (boundedFiniteModel W N) F)
    (hZero : ∀ {I : Type u} [Category.{u} I] [IsFiltered I] (S : Scheme.{u}) [IsAffine S]
      (D : I ⥤ Ab S) (c : Cocone D), IsColimit c → ∀ x : c.pt.H 0,
        ∃ (i : I) (y : (D.obj i).H 0), Sheaf.H.map (c.ι.app i) 0 y = x) :
    AffineModelSections.{u} N := by
  intro W S _ i _ F hF x
  let : IsAffine S := isAffine_of_isAffineHom i
  obtain ⟨I, _, _, p, hp⟩ := hModels W F hF
  let L := pullbackSheaves i
  let : L.IsLeftAdjoint := (pullbackAdjunction i).isLeftAdjoint
  let c := L.mapCocone (Cocone.mk F p.ι)
  obtain ⟨k, y, hy⟩ := hZero S _ c (isColimitOfPreserves L p.isColimit) x
  exact ⟨p.diag.obj k, p.ι.app k, y, hy, hp k⟩

/-- A degree-one class on the closed subscheme lifts through a finite model
when degree one vanishes on both charts and finite covers of the overlap extend. -/
theorem exists_finite_constant_preimage [IsClosedImmersion j] (U V : X.Opens)
    (hCover : U ⊔ V = ⊤) (hW : IsAffineOpen (U ⊓ V))
    {N : ℕ} (hN : N.Prime) (J : Modules X N) [Injective J]
    (hModelSections : AffineModelSections.{u} N)
    (hU : Subsingleton (((pullbackSheaves (j ∣_ U)).obj
      ((restrict U.ι).obj (underlying.obj J))).H 1))
    (hV : Subsingleton (((pullbackSheaves (j ∣_ V)).obj
      ((restrict V.ι).obj (underlying.obj J))).H 1))
    (hExtend : ∀ {T : Scheme.{u}} (q : T ⟶ (U ⊓ V).toScheme) [IsFinite q],
      ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (k : T ⟶ Y),
        IsPullback q k (U ⊓ V).ι p)
    (x : ((pullbackSheaves j).obj (underlying.obj J)).H 1) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p)
      (a : finiteConstantModel p N ⟶ underlying.obj J)
      (y : ((pullbackSheaves j).obj (finiteConstantModel p N)).H 1),
      Sheaf.H.map ((pullbackSheaves j).map a) 1 y = x := by
  let G : Ab X := underlying.obj J
  let L := pullbackSheaves j
  let W := U ⊓ V
  let U₀ := j ⁻¹ᵁ U
  let V₀ := j ⁻¹ᵁ V
  have hCover₀ : U₀ ⊔ V₀ = ⊤ := by
    change j ⁻¹ᵁ U ⊔ j ⁻¹ᵁ V = ⊤
    rw [← Scheme.Hom.preimage_sup, hCover, Scheme.Hom.preimage_top]
  have hOverlap : U₀ ⊓ V₀ = j ⁻¹ᵁ W := (Scheme.Hom.preimage_inf j (U := U) (V := V)).symm
  let s (F : Ab X) := preimageSectionsIso j W (U₀ ⊓ V₀) hOverlap F
  have hU₀ := vanishing_on_preimage j U G 1 hU
  have hV₀ := vanishing_on_preimage j V G 1 hV
  obtain ⟨t, ht⟩ := overlapBoundary_surjective U₀ V₀ hCover₀ (L.obj G) hU₀ hV₀ x
  let : IsAffine W.toScheme := hW
  let R := restrict W.ι
  let P := pullbackSheaves (j ∣_ W)
  have hG : N • 𝟙 (R.obj G) = 0 := by
    have h := PhilipponEtalePrimeTorsionComparison.underlying_killed J
    simpa only [R.map_nsmul, R.map_id, R.map_zero] using congrArg (fun a => R.map a) h
  obtain ⟨F, f, z, hz, hF⟩ := hModelSections (j ∣_ W) (R.obj G) hG (s G t)
  obtain ⟨Y, p, hp, a, b, hab⟩ :=
    PhilipponEtaleFiniteConstantApproximation.exists_factorization_on_open W.ι hN
      (J := J) hExtend hF f
  let B := finiteConstantModel p N
  let z' := Sheaf.H.map (P.map b) 0 z
  let t' := (s B).symm z'
  have ht' : t'.comp (Ext.mk₀ (L.map a)) rfl = t := by
    apply (s G).injective
    change s G (t'.comp (Ext.mk₀ (L.map a)) rfl) = s G t
    rw [show s G (t'.comp (Ext.mk₀ (L.map a)) rfl) =
        Sheaf.H.map (P.map (R.map a)) 0 (s B t') from
      preimageSectionsIso_map j W _ hOverlap a t']
    rw [show s B t' = z' from (s B).apply_symm_apply z']
    change Sheaf.H.map (P.map (R.map a)) 0 (Sheaf.H.map (P.map b) 0 z) = s G t
    rw [← Sheaf.H.map_comp_apply, ← P.map_comp, hab]
    exact hz
  let y := overlapBoundary U₀ V₀ hCover₀ (L.obj B) t'
  refine ⟨Y, p, hp, a, y, ?_⟩
  change Sheaf.H.map (L.map a) 1 (overlapBoundary U₀ V₀ hCover₀ (L.obj B) t') = x
  rw [← overlapBoundary_naturality, ht', ht]

end PhilipponEtaleClosedFiberOverlap

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedFiberDegreeOne (finiteConstantModel)
open PhilipponEtaleExtensionByZero (restrict)
open PhilipponEtaleModuleSkyscrapers (underlying)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleProjectiveLineFinitePreimage

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev Line (R : Type u) [CommRing R] := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)
private abbrev Coeff (N : ℕ) := ModuleCat.{u} (ULift.{u} (ZMod N))
private abbrev Modules (X : Scheme.{u}) (N : ℕ) := Sheaf X.smallEtaleTopology (Coeff N)

/-- On a relative projective line, affine closed-restriction acyclicity
and finite models of sections give finite models of closed-fiber classes. -/
theorem exists_finite_constant_preimage {R A : Type u} [CommRing R] [CommRing A]
    (v : Spec (.of A) ⟶ Spec (.of R)) {P S : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) (d : P ⟶ Line R) (hr : IsPullback r d v (ProjSpace.π R 1))
    (j : S ⟶ P) [IsClosedImmersion j]
    {N : ℕ} (hN : N.Prime) (J : Modules P N) [Injective J]
    (hSections : PhilipponEtaleClosedFiberOverlap.AffineModelSections.{u} N)
    (hAffine : ∀ {X Y : Scheme.{u}} [IsAffine X] (i : Y ⟶ X) [IsClosedImmersion i]
      (I : Modules X N), Injective I → Subsingleton (((pullbackSheaves i).obj (underlying.obj I)).H 1))
    (x : ((pullbackSheaves j).obj (underlying.obj J)).H 1) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ P) (_ : IsFinite p)
      (a : finiteConstantModel p N ⟶ underlying.obj J)
      (y : ((pullbackSheaves j).obj (finiteConstantModel p N)).H 1),
      Sheaf.H.map ((pullbackSheaves j).map a) 1 y = x := by
  let : IsProper r := MorphismProperty.of_isPullback hr.flip (inferInstance : IsProper (ProjSpace.π R 1))
  have hTerminal : terminal.from P = r ≫ terminal.from (Spec (.of A)) := terminal.hom_ext _ _
  let : P.IsSeparated := ⟨hTerminal.symm ▸ inferInstanceAs
    (IsSeparated (r ≫ terminal.from (Spec (.of A))))⟩
  obtain ⟨U, V, hU, hV, hCover, ⟨s, hs⟩, ⟨t, ht⟩⟩ :=
    PhilipponEtaleProjectiveLineTwoAffine.exists_two_affine_opens_with_principal_intersection v r d hr
  have hLocal (W : P.Opens) (hW : IsAffineOpen W) :
      Subsingleton (((pullbackSheaves (j ∣_ W)).obj
        ((restrict W.ι).obj (underlying.obj J))).H 1) := by
    let L := (PhilipponSmallEtaleOpenImmersion.along W.ι).sheafPushforwardContinuous (Coeff N)
      W.toScheme.smallEtaleTopology P.smallEtaleTopology
    let : L.PreservesInjectiveObjects :=
      PhilipponEtaleExtensionByZero.restriction_preservesInjectiveObjects W.ι (Coeff N)
    let : IsAffine W.toScheme := hW
    let I := L.obj J
    have hI : Injective I := L.injective_obj_of_injective (inferInstance : Injective J)
    exact hAffine (j ∣_ W) I hI
  refine PhilipponEtaleClosedFiberOverlap.exists_finite_constant_preimage j U V hCover (hU.inf hV)
    hN J hSections (hLocal U hU) (hLocal V hV) ?_ x
  intro T q hq
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  let a : (U ⊓ V).toScheme ⟶ U.toScheme := P.homOfLE inf_le_left
  let b : (U ⊓ V).toScheme ⟶ V.toScheme := P.homOfLE inf_le_right
  let U' := (U : Scheme).basicOpen s
  let V' := (V : Scheme).basicOpen t
  have hRangeU : Set.range a = Set.range U'.ι :=
    congrArg (fun O : (U : Scheme).Opens => (O : Set (U : Scheme))) (hs.trans U'.opensRange_ι.symm)
  have hRangeV : Set.range b = Set.range V'.ι :=
    congrArg (fun O : (V : Scheme).Opens => (O : Set (V : Scheme))) (ht.trans V'.opensRange_ι.symm)
  let eu := IsOpenImmersion.isoOfRangeEq a U'.ι hRangeU
  let ev := IsOpenImmersion.isoOfRangeEq b V'.ι hRangeV
  exact PhilipponFiniteMorphismTwoOpenGluing.extend_from_intersection U V hCover s t eu ev
    (IsOpenImmersion.isoOfRangeEq_hom_fac a U'.ι hRangeU)
    (IsOpenImmersion.isoOfRangeEq_hom_fac b V'.ι hRangeV) q

end PhilipponEtaleProjectiveLineFinitePreimage

end

end


