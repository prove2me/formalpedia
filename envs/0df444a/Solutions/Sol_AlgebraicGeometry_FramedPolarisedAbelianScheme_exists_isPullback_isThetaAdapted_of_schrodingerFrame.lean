-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isPullback_isThetaAdapted_of_schrodingerFrame
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ade820e9-ae39-58a5-88b2-8c5070348e82

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq_of_isPullback_of_iso
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_monoidHom_pt_comp_eq_act_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_sigma_eq_isClosedImmersion_of_isSectionBasis
import Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isPullback_isThetaAdapted_of_schrodingerFrame
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation GoodReductionJacobian.RelativeGroupLaw

open scoped BigOperators TensorProduct

universe u

noncomputable section

namespace C10PasBc

def castPt {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s f) : SchemeHomOver s' f :=
  ⟨P.1, P.2.trans h⟩

@[scoped simp] theorem castPt_coe {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s f) : (castPt h P).1 = P.1 := rfl

theorem castPt_injective {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') : Function.Injective (castPt (f := f) h) := by
  intro P Q hPQ
  exact Subtype.ext (by simpa [castPt] using congrArg Subtype.val hPQ)

theorem nsmul_castPt {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (m : ℕ) (P : SchemeHomOver s f) :
    L.nsmul s' m (castPt h P) = castPt h (L.nsmul s m P) := by
  subst h; rfl

theorem one_castPt {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') :
    L.one s' = castPt h (L.one s) := by
  subst h; rfl

theorem finComb_castPt {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') {m : ℕ} (x : Fin m → SchemeHomOver s f) (c : Fin m → ℕ) :
    L.finComb s' (fun i => castPt h (x i)) c = castPt h (L.finComb s x c) := by
  subst h; rfl

section PointBijection

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

def toBaseHom {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    letI := (G.baseChange ι).pointGroup t'; letI := G.pointGroup (t' ≫ ι);
    SchemeHomOver t' (baseChangeStr ι f) →* SchemeHomOver (t' ≫ ι) f :=
  letI := (G.baseChange ι).pointGroup t'; letI := G.pointGroup (t' ≫ ι)
  { toFun := baseChangePointToBase ι
    map_one' := baseChangePointToBase_one ι G t'
    map_mul' := fun x y => baseChangePointToBase_mul ι G t' x y }

theorem toBase_nsmul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (m : ℕ) (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((G.baseChange ι).nsmul t' m x) = G.nsmul (t' ≫ ι) m (baseChangePointToBase ι x) := by
  induction m with
  | zero => exact baseChangePointToBase_one ι G t'
  | succ m ih => rw [nsmul_succ, nsmul_succ, baseChangePointToBase_mul, ih]

theorem toBase_finComb {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) {m : ℕ}
    (x : Fin m → SchemeHomOver t' (baseChangeStr ι f)) (c : Fin m → ℕ) :
    baseChangePointToBase ι ((G.baseChange ι).finComb t' x c) = G.finComb (t' ≫ ι) (fun i => baseChangePointToBase ι (x i)) c := by
  letI := (G.baseChange ι).pointGroup t'; letI := G.pointGroup (t' ≫ ι)
  have hpow : ∀ i, baseChangePointToBase ι (x i ^ c i) = baseChangePointToBase ι (x i) ^ c i :=
    fun i => map_pow (toBaseHom ι G t') (x i) (c i)
  have := map_list_prod (toBaseHom ι G t') (List.ofFn fun i => x i ^ c i)
  rw [List.map_ofFn] at this
  simpa [RelativeGroupLaw.finComb, toBaseHom, Function.comp_def, hpow] using this

end PointBijection

section Main

variable {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') {g d n : ℕ} (X : PolarisedAbelianScheme g d n S)

abbrev ι : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom φ)

abbrev f' : baseChangeScheme (ι φ) X.f ⟶ Spec (CommRingCat.of S') := baseChangeStr (ι φ) X.f

abbrev gA : baseChangeScheme (ι φ) X.f ⟶ X.A := pullback.fst X.f (ι φ)

def QP (i : Fin (2 * g)) : SchemeHomOver (𝟙 _ ≫ ι φ) X.f :=
  GoodReductionJacobian.schemeHomOverComp (ι φ) (by simp) (X.P i)

@[scoped simp] theorem QP_coe (i : Fin (2 * g)) : (QP φ X i).1 = ι φ ≫ (X.P i).1 := rfl

def P' (i : Fin (2 * g)) : SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) (f' φ X) :=
  baseChangePointOfBase (ι φ) (QP φ X i)

@[scoped simp] theorem toBase_P' (i : Fin (2 * g)) : baseChangePointToBase (ι φ) (P' φ X i) = QP φ X i :=
  baseChangePointToBase_ofBase _ _

theorem P'_gA (i : Fin (2 * g)) : (P' φ X i).1 ≫ gA φ X = ι φ ≫ (X.P i).1 :=
  congrArg Subtype.val (toBase_P' φ X i)

theorem geom_base_eq {k : Type u} [Field k] (sk : S' →+* k) :
    Spec.map (CommRingCat.ofHom sk) ≫ ι φ = Spec.map (CommRingCat.ofHom (sk.comp φ)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem geom_P' {k : Type u} [Field k] (sk : S' →+* k) (i : Fin (2 * g)) :
    castPt (geom_base_eq φ sk) (baseChangePointToBase (ι φ)
      (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P' φ X i))) =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (sk.comp φ))) (Category.comp_id _) (X.P i) := by
  apply Subtype.ext
  simp only [castPt_coe, baseChangePointToBase_coe, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
  rw [P'_gA, ← Category.assoc, geom_base_eq]

theorem h0_baseChange (k : Type u) [Field k] [IsAlgClosed k] (sk : S' →+* k) :
    Scheme.Modules.geomFibreH0Finrank (f' φ X) ((Scheme.Modules.pullback (gA φ X)).obj X.pol) k sk =
      Scheme.Modules.geomFibreH0Finrank X.f X.pol k (sk.comp φ) :=
  (Scheme.Modules.geomFibreH0Finrank_comp_eq_of_isPullback_of_iso φ X.f (f' φ X) (gA φ X)
    (IsPullback.of_hasPullback X.f (ι φ)) X.pol _ ⟨Iso.refl _⟩ k sk).symm

private def _root_.C10PasBc.baseChange : PolarisedAbelianScheme g d n S' where
  A := baseChangeScheme (ι φ) X.f
  f := f' φ X
  L := X.L.baseChange (ι φ)
  comm := RelativeGroupLaw.IsCommutative.baseChange (ι φ) X.comm
  bundle := AbelianSchemePropertyBundle.of_isPullback X.bundle (IsPullback.of_hasPullback X.f (ι φ))
  dim_fibre := by
    haveI : Smooth X.f := X.bundle.smooth
    exact topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected φ X.f X.bundle.connectedFibres g X.dim_fibre
  P := P' φ X
  P_torsion := fun i => by
    apply (baseChangePointEquiv (ι φ) (𝟙 _)).injective
    change baseChangePointToBase (ι φ) _ = baseChangePointToBase (ι φ) _
    rw [toBase_nsmul, baseChangePointToBase_one, toBase_P']
    have h := congrArg (GoodReductionJacobian.schemeHomOverComp (ι φ) (by simp : ι φ ≫ 𝟙 _ = 𝟙 _ ≫ ι φ)) (X.P_torsion i)
    rw [X.L.nsmul_natural, X.L.one_natural] at h
    exact h
  P_indep := fun k _ _ sk c c' hcc' => by
    apply X.P_indep k (sk.comp φ) c c'
    have h := congrArg (fun Q => castPt (geom_base_eq φ sk) (baseChangePointToBase (ι φ) Q)) hcc'
    simp only [toBase_finComb, ← finComb_castPt, geom_P'] at h
    exact h
  P_span := fun k _ _ sk Q hQ => by

    have hQ' : X.L.nsmul (Spec.map (CommRingCat.ofHom (sk.comp φ))) n
        (castPt (geom_base_eq φ sk) (baseChangePointToBase (ι φ) Q)) =
        X.L.one (Spec.map (CommRingCat.ofHom (sk.comp φ))) := by
      rw [nsmul_castPt, ← toBase_nsmul, hQ, baseChangePointToBase_one, ← one_castPt]
    obtain ⟨c, hc⟩ := X.P_span k (sk.comp φ) _ hQ'
    refine ⟨c, ?_⟩
    apply (baseChangePointEquiv (ι φ) _).injective
    apply castPt_injective (geom_base_eq φ sk)
    change castPt _ (baseChangePointToBase (ι φ) _) = castPt _ (baseChangePointToBase (ι φ) _)
    rw [← hc, toBase_finComb, ← finComb_castPt]
    simp only [geom_P']
  pol := (Scheme.Modules.pullback (gA φ X)).obj X.pol
  pol_isInvertible := X.pol_isInvertible.pullback (gA φ X)
  pol_veryAmple := by
    obtain ⟨N, 𝔓, h𝔓⟩ := X.pol_veryAmple
    letI : Algebra S S' := φ.toAlgebra
    have sq : IsPullback (gA φ X) (f' φ X) X.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) :=
      IsPullback.of_hasPullback X.f (ι φ)
    obtain ⟨𝔓', -, -, hsq⟩ := Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback sq 𝔓
    exact ⟨N, 𝔓', MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq h𝔓⟩
  pol_finrank := fun k _ _ sk => by
    rw [h0_baseChange φ X k sk]
    exact X.pol_finrank k (sk.comp φ)

p2m_export "C10PasBc" "baseChange"

theorem exists_isPullback_exposed :
    ∃ (X' : PolarisedAbelianScheme g d n S') (gA : X'.A ⟶ X.A)
      (hg : IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' X'.f),
        (X'.L.mul t' x y).1 ≫ gA =
          (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
      (∀ i, (X'.P i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (X.P i).1) ∧
      Nonempty ((Scheme.Modules.pullback gA).obj X.pol ≅ X'.pol) ∧
      PolarisedAbelianScheme.IsPullback φ X X' := by
  refine ⟨baseChange φ X, gA φ X, IsPullback.of_hasPullback X.f (ι φ), ?_, P'_gA φ X, ⟨Iso.refl _⟩, ?_⟩
  · intro T t' x y
    exact congrArg Subtype.val (baseChangePointToBase_mul (ι φ) X.L t' x y)
  · refine ⟨gA φ X, IsPullback.of_hasPullback X.f (ι φ), ?_, P'_gA φ X, ⟨Iso.refl _⟩⟩
    intro T t' x y
    exact congrArg Subtype.val (baseChangePointToBase_mul (ι φ) X.L t' x y)

theorem isPullback_baseChange : PolarisedAbelianScheme.IsPullback φ X (baseChange φ X) := by
  refine ⟨gA φ X, IsPullback.of_hasPullback X.f (ι φ), ?_, P'_gA φ X, ⟨Iso.refl _⟩⟩
  intro T t' x y
  exact congrArg Subtype.val (baseChangePointToBase_mul (ι φ) X.L t' x y)

theorem baseChange_hmul (hg : IsPullback (gA φ X) (baseChange φ X).f X.f (Spec.map (CommRingCat.ofHom φ)))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' (baseChange φ X).f) :
    ((baseChange φ X).L.mul t' x y).1 ≫ gA φ X =
      (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨x.1 ≫ gA φ X, (baseChangePointToBase (ι φ) x).2⟩
        ⟨y.1 ≫ gA φ X, (baseChangePointToBase (ι φ) y).2⟩).1 :=
  congrArg Subtype.val (baseChangePointToBase_mul (ι φ) X.L t' x y)

end Main

end C10PasBc
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isPullback_isThetaAdapted_of_schrodingerFrame.C10PasBc"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isPullback_isThetaAdapted_of_schrodingerFrame.C10PasBc"

noncomputable section

namespace C10

variable {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
  {R : Type} [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
  (u : PolarisedAbelianScheme g (N + 1) n R)
  (F : Polarisation.SchrodingerFrame u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap R R'))) δ)

abbrev t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R R'))

abbrev ub : PolarisedAbelianScheme g (N + 1) n R' := C10PasBc.baseChange (algebraMap R R') u

def σf : Fin (N + 1) → Γ((ub R' u).pol, ⊤) := fun i => F.σ (e i)

theorem σf_apply (i : Fin (N + 1)) : σf δ e R' u F i = F.σ (e i) := rfl

theorem appLE_top_eq : ((ub R' u).f.appLE ⊤ ⊤ le_top) = (ub R' u).f.appTop := by
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]

theorem isSectionBasis_σf : Scheme.Modules.IsSectionBasis (ub R' u).f (ub R' u).pol (σf δ e R' u F) := by
  change Function.Bijective _
  have hre : (fun c : Fin (N + 1) → R' =>
      ∑ i, (((ub R' u).f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (c i))) • σf δ e R' u F i) =
      (fun c : ((i : Fin g) → ZMod (δ i)) → R' =>
        ∑ h, Polarisation.baseScalar u.f (t R') (c h) • F.σ h) ∘ (fun c => c ∘ e.symm) := by
    funext c
    simp only [Function.comp_apply, σf_apply, appLE_top_eq]
    rw [← e.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rfl
  rw [hre]
  exact F.basis.comp (e.symm.arrowCongr (Equiv.refl R')).symm.bijective

def X' (𝔓 : Scheme.Modules.ProjPresentation (ub R' u).pol (ub R' u).f N) (h𝔓σ : 𝔓.σ = σf δ e R' u F)
    (h𝔓c : IsClosedImmersion 𝔓.toProj) : FramedPolarisedAbelianScheme g N n R' where
  toPolarisedAbelianScheme := ub R' u
  frame := 𝔓
  frame_isClosedImmersion := h𝔓c
  frame_basis := by rw [h𝔓σ]; exact isSectionBasis_σf δ e R' u F

abbrev b : pullback (ub R' u).f (𝟙 (Spec (CommRingCat.of R'))) ⟶ pullback u.f (t R') :=
  pullback.fst (ub R' u).f (𝟙 (Spec (CommRingCat.of R')))

theorem specMap_id : Spec.map (CommRingCat.ofHom (RingHom.id R')) = 𝟙 (Spec (CommRingCat.of R')) := by
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

theorem hb₂ : b R' u ≫ pullback.snd u.f (t R') =
    pullback.snd (ub R' u).f (𝟙 _) ≫ Spec.map (CommRingCat.ofHom (RingHom.id R')) := by
  rw [specMap_id]
  exact pullback.condition

theorem hr : Spec.map (CommRingCat.ofHom (RingHom.id R')) ≫ t R' = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
  rw [specMap_id]

theorem b_app_baseScalar (r : R') :
    (b R' u).app ⊤ (Polarisation.baseScalar u.f (t R') r) = Polarisation.baseScalar (ub R' u).f (𝟙 _) r := by
  simp only [Polarisation.baseScalar]
  change ((pullback.snd u.f (t R')).appTop ≫ (b R' u).appTop) _ = _
  rw [← Scheme.Hom.comp_appTop, hb₂, specMap_id, Category.comp_id]

theorem isThetaAdapted (𝔓 : Scheme.Modules.ProjPresentation (ub R' u).pol (ub R' u).f N) (h𝔓σ : 𝔓.σ = σf δ e R' u F)
    (h𝔓c : IsClosedImmersion 𝔓.toProj) : (X' δ e R' u F 𝔓 h𝔓σ h𝔓c).IsThetaAdapted δ e := by

  obtain ⟨β, -, hβact, -, -⟩ :=
    AlgebraicGeometry.Polarisation.ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback (algebraMap R R')
      u.L (ub R' u).L (pullback.fst u.f (t R')) (IsPullback.of_hasPullback u.f (t R'))
      (fun t'' x y => C10PasBc.baseChange_hmul (algebraMap R R') u (IsPullback.of_hasPullback u.f (t R')) t'' x y)
      u.pol (ub R' u).pol (t R') (𝟙 _) (RingHom.id R') (hr R') (b R' u) rfl (hb₂ R' u) (Iso.refl _)

  let σ' : ((i : Fin g) → ZMod (δ i)) → Γ((Scheme.Modules.pullback (b R' u)).obj (ub R' u).pol, ⊤) :=
    fun h => Scheme.Modules.pullbackLocalSection (b R' u) (F.σ h)
  have hσ' : ∀ i : Fin (N + 1), σ' (e i) =
      (Scheme.Modules.pullbackLocalSection (pullback.fst (X' δ e R' u F 𝔓 h𝔓σ h𝔓c).f (𝟙 (Spec (CommRingCat.of R'))))
        ((X' δ e R' u F 𝔓 h𝔓σ h𝔓c).frame.σ i) :
          Γ((Scheme.Modules.pullback (pullback.fst (X' δ e R' u F 𝔓 h𝔓σ h𝔓c).f (𝟙 (Spec (CommRingCat.of R'))))).obj
            (X' δ e R' u F 𝔓 h𝔓σ h𝔓c).pol, (pullback.fst (X' δ e R' u F 𝔓 h𝔓σ h𝔓c).f (𝟙 (Spec (CommRingCat.of R')))) ⁻¹ᵁ ⊤)) := by
    intro i
    change σ' (e i) = Scheme.Modules.pullbackLocalSection (b R' u) (𝔓.σ i)
    rw [h𝔓σ]
    rfl
  have hact : ∀ (θ : ThetaPt u.f u.L u.pol (t R')) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f (t R'))).obj u.pol, ⊤)),
      (β θ).act (Scheme.Modules.pullbackLocalSection (b R' u) s) = Scheme.Modules.pullbackLocalSection (b R' u) (θ.act s) := by
    intro θ s
    have h := hβact θ s
    simp at h
    exact h
  refine ⟨{ σ := σ'
            basis := ?_
            lift := fun h => β (F.lift h)
            dualLift := fun χ => β (F.dualLift χ)
            lift_act := ?_
            dualLift_act := ?_ }, hσ'⟩
  · exact AlgebraicGeometry.FramedPolarisedAbelianScheme.bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame
      δ e (X' δ e R' u F 𝔓 h𝔓σ h𝔓c) σ' hσ'
  · intro h h'
    change (β (F.lift h)).act (Scheme.Modules.pullbackLocalSection (b R' u) (F.σ h')) =
      Scheme.Modules.pullbackLocalSection (b R' u) (F.σ (h + h'))
    rw [hact, F.lift_act]
  · intro χ h
    change (β (F.dualLift χ)).act (Scheme.Modules.pullbackLocalSection (b R' u) (F.σ h)) = _
    rw [hact, F.dualLift_act, Scheme.Modules.pullbackLocalSection_smul, b_app_baseScalar]
    try rfl

include F in

theorem main : ∃ X' : FramedPolarisedAbelianScheme g N n R',
    PolarisedAbelianScheme.IsPullback (algebraMap R R') u X'.toPolarisedAbelianScheme ∧ X'.IsThetaAdapted δ e := by
  obtain ⟨𝔓, h𝔓σ, h𝔓c⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_projPresentation_sigma_eq_isClosedImmersion_of_isSectionBasis
      (ub R' u).f (ub R' u).pol (ub R' u).pol_isInvertible (ub R' u).pol_veryAmple (σf δ e R' u F) (isSectionBasis_σf δ e R' u F)
  exact ⟨X' δ e R' u F 𝔓 h𝔓σ h𝔓c, C10PasBc.isPullback_baseChange (algebraMap R R') u, isThetaAdapted δ e R' u F 𝔓 h𝔓σ h𝔓c⟩

end C10
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isPullback_isThetaAdapted_of_schrodingerFrame.C10PasBc"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isPullback_isThetaAdapted_of_schrodingerFrame.C10PasBc"

theorem solution
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    {R : Type} [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    (u : PolarisedAbelianScheme g (N + 1) n R)
    (F : Polarisation.SchrodingerFrame u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap R R'))) δ) :
    ∃ X' : FramedPolarisedAbelianScheme g N n R',
      PolarisedAbelianScheme.IsPullback (algebraMap R R') u X'.toPolarisedAbelianScheme ∧ X'.IsThetaAdapted δ e :=
  C10.main δ e R' u F

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isPullback_isThetaAdapted_of_schrodingerFrame
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isPullback_isThetaAdapted_of_schrodingerFrame (solution)
