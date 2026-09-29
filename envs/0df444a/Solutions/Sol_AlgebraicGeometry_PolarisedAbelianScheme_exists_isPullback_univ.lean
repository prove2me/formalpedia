-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a6ec20bf-d294-5585-aeb9-6d0c12b07b7f

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq_of_isPullback_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_univ
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw

universe u

noncomputable section

namespace P2mKcPasBcUnivSol

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

private def _root_.P2mKcPasBcUnivSol.baseChange : PolarisedAbelianScheme g d n S' where
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

p2m_export "P2mKcPasBcUnivSol" "baseChange"

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

theorem exists_isPullback : ∃ X' : PolarisedAbelianScheme g d n S', PolarisedAbelianScheme.IsPullback φ X X' := by
  obtain ⟨X', -, -, -, -, -, h⟩ := exists_isPullback_exposed φ X
  exact ⟨X', h⟩

end Main

end P2mKcPasBcUnivSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_univ.P2mKcPasBcUnivSol"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_univ.P2mKcPasBcUnivSol"

open AlgebraicGeometry.PolarisedAbelianScheme in
theorem solution
    {g d n : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u₀ : AlgebraicGeometry.PolarisedAbelianScheme g d n S) :
    ∃ u' : AlgebraicGeometry.PolarisedAbelianScheme g d n S',
      AlgebraicGeometry.PolarisedAbelianScheme.IsPullback φ u₀ u' :=
  P2mKcPasBcUnivSol.exists_isPullback φ u₀

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_univ
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_univ (solution)
