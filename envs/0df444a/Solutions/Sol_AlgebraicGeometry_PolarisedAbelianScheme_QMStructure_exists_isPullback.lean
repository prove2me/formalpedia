-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6ce0091d-b3a3-531c-ad68-fc812765e706

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM"

noncomputable section

namespace P2mKcQmBcSol

def castPt {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{0}}
    {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s f) : SchemeHomOver s' f :=
  ⟨P.1, P.2.trans h⟩

@[scoped simp] theorem castPt_coe {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{0}}
    {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s f) : (castPt h P).1 = P.1 := rfl

theorem mul_castPt {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P Q : SchemeHomOver s f) :
    L.mul s' (castPt h P) (castPt h Q) = castPt h (L.mul s P Q) := by
  subst h; rfl

theorem one_castPt {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') :
    L.one s' = castPt h (L.one s) := by
  subst h; rfl

theorem pushPt_castPt {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (e : A ⟶ A) (he : e ≫ f = f) {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s')
    (P : SchemeHomOver s f) : pushPt e he (castPt h P) = castPt h (pushPt e he P) := by
  subst h; rfl

section Square

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}
  {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {X : PolarisedAbelianScheme 2 d m S} {X' : PolarisedAbelianScheme 2 d m S'}
  {gA : X'.A ⟶ X.A}

def gPt (hg : IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ)))
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' X'.f) :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) X.f :=
  ⟨P.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem gPt_coe (hg : IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ)))
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' X'.f) : (gPt hg P).1 = P.1 ≫ gA := rfl

theorem gPt_injective (hg : IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ)))
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} {P Q : SchemeHomOver t' X'.f}
    (h : gPt hg P = gPt hg Q) : P = Q := by
  apply Subtype.ext
  apply hg.hom_ext
  · exact congrArg Subtype.val h
  · rw [P.2, Q.2]

def liftPt (hg : IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ)))
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) X.f) :
    SchemeHomOver t' X'.f :=
  ⟨hg.lift Q.1 t' (by rw [Q.2]), hg.lift_snd _ _ _⟩

@[scoped simp] theorem gPt_liftPt (hg : IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ)))
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) X.f) :
    gPt hg (liftPt hg Q) = Q :=
  Subtype.ext (hg.lift_fst _ _ _)

def SqHom (hg : IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ))) : Prop :=
  ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' X'.f),
    (X'.L.mul t' x y).1 ≫ gA = (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (gPt hg x) (gPt hg y)).1

variable {hg : IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ))}

theorem SqHom.gPt_mul (h : SqHom hg) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' X'.f) :
    gPt hg (X'.L.mul t' x y) = X.L.mul _ (gPt hg x) (gPt hg y) :=
  Subtype.ext (h t' x y)

theorem SqHom.gPt_one (h : SqHom hg) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    gPt hg (X'.L.one t') = X.L.one _ := by
  letI := X.L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ))
  have hmul : gPt hg (X'.L.one t') = X.L.mul _ (gPt hg (X'.L.one t')) (gPt hg (X'.L.one t')) := by
    conv_lhs => rw [← X'.L.one_mul t' (X'.L.one t')]
    exact h.gPt_mul t' _ _
  have key : (gPt hg (X'.L.one t') : SchemeHomOver _ X.f) * gPt hg (X'.L.one t') = gPt hg (X'.L.one t') * 1 := by
    change X.L.mul _ _ _ = X.L.mul _ _ (X.L.one _)
    rw [X.L.mul_one]; exact hmul.symm
  exact mul_left_cancel key

def act' (hg : IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ))) (s : QMStructure Λ star β X) (x : ↥Λ) :
    X'.A ⟶ X'.A :=
  hg.lift (gA ≫ s.act x) X'.f (by rw [Category.assoc, s.act_over, hg.w])

@[reassoc (attr := simp)] theorem act'_gA (s : QMStructure Λ star β X) (x : ↥Λ) : act' hg s x ≫ gA = gA ≫ s.act x :=
  hg.lift_fst _ _ _

theorem act'_over (s : QMStructure Λ star β X) (x : ↥Λ) : act' hg s x ≫ X'.f = X'.f :=
  hg.lift_snd _ _ _

theorem gPt_pushPt (s : QMStructure Λ star β X) (x : ↥Λ) {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')}
    (P : SchemeHomOver t' X'.f) :
    gPt hg (pushPt (act' hg s x) (act'_over s x) P) = pushPt (s.act x) (s.act_over x) (gPt hg P) :=
  Subtype.ext (by simp [pushPt, mapPt])

theorem act'_hom (h : SqHom hg) (s : QMStructure Λ star β X) (x : ↥Λ) {T : Scheme.{0}}
    (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' X'.f) :
    pushPt (act' hg s x) (act'_over s x) (X'.L.mul t' P Q) =
      X'.L.mul t' (pushPt (act' hg s x) (act'_over s x) P) (pushPt (act' hg s x) (act'_over s x) Q) := by
  apply gPt_injective hg
  rw [gPt_pushPt, h.gPt_mul, h.gPt_mul, gPt_pushPt, gPt_pushPt]
  exact s.act_hom x _ _ _

theorem act'_one (s : QMStructure Λ star β X) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) : act' hg s ⟨1, h1⟩ = 𝟙 X'.A := by
  apply hg.hom_ext
  · rw [act'_gA, s.act_one h1, Category.id_comp, Category.comp_id]
  · rw [act'_over, Category.id_comp]

theorem act'_mul (s : QMStructure Λ star β X) (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    act' hg s ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = act' hg s y ≫ act' hg s x := by
  apply hg.hom_ext
  · simp only [Category.assoc, act'_gA, act'_gA_assoc, s.act_mul x y hxy]
  · rw [act'_over, Category.assoc, act'_over, act'_over]

theorem act'_add (h : SqHom hg) (s : QMStructure Λ star β X) (x y : ↥Λ) {T : Scheme.{0}}
    (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' X'.f) :
    pushPt (act' hg s (x + y)) (act'_over s (x + y)) P =
      X'.L.mul t' (pushPt (act' hg s x) (act'_over s x) P) (pushPt (act' hg s y) (act'_over s y) P) := by
  apply gPt_injective hg
  rw [gPt_pushPt, h.gPt_mul, gPt_pushPt, gPt_pushPt]
  exact s.act_add x y _ _

theorem tangentZero_tangentBase {k : Type} [Field k] (sk : S' →+* k) : tangentZero k ≫ tangentBase k sk = geomPoint k sk := by
  have h : (TrivSqZeroExt.fstHom k k k).toRingHom.comp ((algebraMap k (DualNumber k)).comp sk) = sk := by
    ext x
    simp
  unfold tangentZero tangentBase geomPoint
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem tangentBase_comp {k : Type} [Field k] (sk : S' →+* k) :
    tangentBase k sk ≫ Spec.map (CommRingCat.ofHom φ) = tangentBase k (sk.comp φ) := by
  unfold tangentBase
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc]

theorem geomPoint_comp {k : Type} [Field k] (sk : S' →+* k) :
    geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ) = geomPoint k (sk.comp φ) := by
  unfold geomPoint
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem SqHom.one_coe (h : SqHom hg) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S'))
    {t : T ⟶ Spec (CommRingCat.of S)} (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t) :
    (X'.L.one t').1 ≫ gA = (X.L.one t).1 := by
  subst ht
  exact congrArg Subtype.val (h.gPt_one t')

section Trace

variable (h : SqHom hg) (s : QMStructure Λ star β X)
  {k : Type} [Field k] [IsAlgClosed k] (sk : S' →+* k)
  {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) X'.f)

def sigma (v : V) : SchemeHomOver (tangentBase k (sk.comp φ)) X.f :=
  ⟨(τ v).1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, (τ v).2, tangentBase_comp]⟩

omit [IsAlgClosed k] [AddCommGroup V] [Module k V] [Module.Finite k V] in
@[scoped simp] theorem sigma_coe (v : V) : (sigma (hg := hg) sk τ v).1 = (τ v).1 ≫ gA := rfl

omit [IsAlgClosed k] [AddCommGroup V] [Module k V] [Module.Finite k V] in
theorem sigma_injective (hτinj : Function.Injective τ) : Function.Injective (sigma (hg := hg) sk τ) := by
  intro v w hvw
  apply hτinj
  apply gPt_injective hg
  apply Subtype.ext
  change (τ v).1 ≫ gA = (τ w).1 ≫ gA
  exact congrArg Subtype.val hvw

omit [IsAlgClosed k] [AddCommGroup V] [Module k V] [Module.Finite k V] in
include h in
theorem sigma_range_of (hτrange : ∀ P : SchemeHomOver (tangentBase k sk) X'.f, P ∈ Set.range τ ↔ IsTangentVector X'.L k sk P)
    (v : V) : IsTangentVector X.L k (sk.comp φ) (sigma (hg := hg) sk τ v) := by
  have hv : IsTangentVector X'.L k sk (τ v) := (hτrange (τ v)).mp ⟨v, rfl⟩
  unfold IsTangentVector at hv ⊢
  rw [sigma_coe, ← Category.assoc, hv]
  exact h.one_coe (geomPoint k sk) (geomPoint_comp sk)

omit [IsAlgClosed k] [AddCommGroup V] [Module k V] [Module.Finite k V] in
include h in
theorem sigma_range_to (hτrange : ∀ P : SchemeHomOver (tangentBase k sk) X'.f, P ∈ Set.range τ ↔ IsTangentVector X'.L k sk P)
    (P : SchemeHomOver (tangentBase k (sk.comp φ)) X.f) (hP : IsTangentVector X.L k (sk.comp φ) P) :
    P ∈ Set.range (sigma (hg := hg) sk τ) := by
  have hP2 : P.1 ≫ X.f = tangentBase k sk ≫ Spec.map (CommRingCat.ofHom φ) := by rw [P.2, tangentBase_comp]
  let Pt : SchemeHomOver (tangentBase k sk) X'.f := ⟨hg.lift P.1 (tangentBase k sk) hP2, hg.lift_snd _ _ _⟩
  have hPt : Pt.1 ≫ gA = P.1 := hg.lift_fst _ _ _
  have htv : IsTangentVector X'.L k sk Pt := by
    unfold IsTangentVector
    apply hg.hom_ext
    · rw [Category.assoc, hPt]
      unfold IsTangentVector at hP
      rw [hP]
      exact (h.one_coe (geomPoint k sk) (geomPoint_comp sk)).symm
    · rw [Category.assoc, Pt.2, (X'.L.one (geomPoint k sk)).2, tangentZero_tangentBase]
  obtain ⟨v, hv⟩ := (hτrange Pt).mpr htv
  refine ⟨v, Subtype.ext ?_⟩
  rw [sigma_coe, hv, hPt]

omit [IsAlgClosed k] [Module k V] [Module.Finite k V] in
include h in
theorem sigma_add (hτadd : ∀ v w : V, τ (v + w) = X'.L.mul (tangentBase k sk) (τ v) (τ w)) (v w : V) :
    sigma (hg := hg) sk τ (v + w) = X.L.mul (tangentBase k (sk.comp φ)) (sigma (hg := hg) sk τ v) (sigma (hg := hg) sk τ w) := by
  apply Subtype.ext
  rw [sigma_coe, hτadd, h (tangentBase k sk) (τ v) (τ w)]
  have := congrArg Subtype.val (mul_castPt X.L (tangentBase_comp (φ := φ) sk) (gPt hg (τ v)) (gPt hg (τ w)))
  rw [castPt_coe] at this
  exact this.symm

omit [IsAlgClosed k] [Module.Finite k V] in
theorem sigma_smul (hτsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) (c : k) (v : V) :
    (sigma (hg := hg) sk τ (c • v)).1 = tangentScale k c ≫ (sigma (hg := hg) sk τ v).1 := by
  rw [sigma_coe, hτsmul, Category.assoc, sigma_coe]

omit [IsAlgClosed k] [Module.Finite k V] in
theorem sigma_act (x : ↥Λ) (Φ : V →ₗ[k] V) (hΦ : ∀ v : V, τ (Φ v) = pushPt (act' hg s x) (act'_over s x) (τ v)) (v : V) :
    sigma (hg := hg) sk τ (Φ v) = pushPt (s.act x) (s.act_over x) (sigma (hg := hg) sk τ v) := by
  apply Subtype.ext
  rw [sigma_coe, hΦ]
  change ((τ v).1 ≫ act' hg s x) ≫ gA = ((τ v).1 ≫ gA) ≫ s.act x
  rw [Category.assoc, act'_gA, Category.assoc]

include h in

theorem act'_trace
    (hτinj : Function.Injective τ)
    (hτrange : ∀ P : SchemeHomOver (tangentBase k sk) X'.f, P ∈ Set.range τ ↔ IsTangentVector X'.L k sk P)
    (hτadd : ∀ v w : V, τ (v + w) = X'.L.mul (tangentBase k sk) (τ v) (τ w))
    (hτsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
    (x : ↥Λ) (Φ : V →ₗ[k] V) (hΦ : ∀ v : V, τ (Φ v) = pushPt (act' hg s x) (act'_over s x) (τ v))
    (n : ℤ) (hn : (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) :
    LinearMap.trace k V Φ = (n : k) :=
  s.act_trace k (sk.comp φ) V (sigma (hg := hg) sk τ) (sigma_injective sk τ hτinj)
    (fun P => ⟨by rintro ⟨v, rfl⟩; exact sigma_range_of h sk τ hτrange v, sigma_range_to h sk τ hτrange P⟩)
    (sigma_add h sk τ hτadd) (sigma_smul sk τ hτsmul) x Φ (sigma_act s sk τ x Φ hΦ) n hn

end Trace

def genP (hg : IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ))) (s : QMStructure Λ star β X) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) X'.f :=
  ⟨hg.lift (Spec.map (CommRingCat.ofHom φ) ≫ s.P.1) (𝟙 _) (by rw [Category.assoc, s.P.2, Category.comp_id, Category.id_comp]),
    hg.lift_snd _ _ _⟩

@[scoped simp] theorem genP_gA (s : QMStructure Λ star β X) : (genP hg s).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ s.P.1 :=
  hg.lift_fst _ _ _

theorem level_match' (s : QMStructure Λ star β X) (hgP : ∀ i, (X'.P i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (X.P i).1)
    (j : Fin (2 * 2)) : pushPt (act' hg s (β j)) (act'_over s (β j)) (genP hg s) = X'.P j := by
  apply Subtype.ext
  apply hg.hom_ext
  · have hj := congrArg Subtype.val (s.level_match j)
    simp only [pushPt, mapPt_coe] at hj
    simp only [pushPt, mapPt_coe, Category.assoc, act'_gA, hgP]
    rw [← Category.assoc, genP_gA, Category.assoc, hj]
  · simp only [pushPt, mapPt_coe, Category.assoc, act'_over]
    rw [(genP hg s).2, (X'.P j).2]

theorem locIsoOnBase_of_iso {R : Type} [CommRing R] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of R)) {M M' : Y.Modules}
    (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

def pullbackCubeIso (E : X.A.Modules) :
    (Scheme.Modules.pullback gA).obj (E ⊗ E ⊗ E) ≅
      (Scheme.Modules.pullback gA).obj E ⊗ (Scheme.Modules.pullback gA).obj E ⊗ (Scheme.Modules.pullback gA).obj E :=
  Scheme.Modules.pullbackTensorObjIso gA E (E ⊗ E) ≪≫
    whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso gA E E)

theorem pol_canonical' (h : SqHom hg) (s : QMStructure Λ star β X)
    (hgpol : Nonempty ((Scheme.Modules.pullback gA).obj X.pol ≅ X'.pol)) :
    ∃ polE' : X'.A.Modules,
      CerednikDrinfeld.QM.IsCanonicalPolData X'.f X'.L (act' hg s) (act'_over s) star polE' ∧
        LocIsoOnBase X'.f X'.pol (polE' ⊗ polE' ⊗ polE') := by
  obtain ⟨polE, hcan, hloc⟩ := s.pol_canonical
  obtain ⟨epol⟩ := hgpol
  refine ⟨(Scheme.Modules.pullback gA).obj polE, ?_, ?_⟩
  · exact CerednikDrinfeld.QM.IsCanonicalPolData.pullback_of_isPullback φ X.L X'.L s.act s.act_over (act' hg s)
      (act'_over s) star gA hg (fun t' x y => h t' x y) (act'_gA s) polE hcan
  · have h1 : LocIsoOnBase X'.f ((Scheme.Modules.pullback gA).obj X.pol)
        ((Scheme.Modules.pullback gA).obj (polE ⊗ polE ⊗ polE)) :=
      LocIsoOnBase.pullback_of_comp_eq X'.f gA (Spec.map (CommRingCat.ofHom φ)) hg.w hloc
    have h2 : LocIsoOnBase X'.f X'.pol ((Scheme.Modules.pullback gA).obj X.pol) := locIsoOnBase_of_iso X'.f epol.symm
    have h3 : LocIsoOnBase X'.f ((Scheme.Modules.pullback gA).obj (polE ⊗ polE ⊗ polE))
        ((Scheme.Modules.pullback gA).obj polE ⊗ (Scheme.Modules.pullback gA).obj polE ⊗
          (Scheme.Modules.pullback gA).obj polE) :=
      locIsoOnBase_of_iso X'.f (pullbackCubeIso polE)
    exact (LocIsoOnBase.equivalence X'.f).trans ((LocIsoOnBase.equivalence X'.f).trans h2 h1) h3

theorem exists_isPullback_of_square (h : SqHom hg) (s : QMStructure Λ star β X)
    (hgP : ∀ i, (X'.P i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (X.P i).1)
    (hgpol : Nonempty ((Scheme.Modules.pullback gA).obj X.pol ≅ X'.pol)) :
    ∃ s' : QMStructure Λ star β X', QMStructure.IsPullback φ s s' := by
  let s' : QMStructure Λ star β X' :=
    { act := act' hg s
      act_over := act'_over s
      act_hom := fun x _ t' P Q => act'_hom h s x t' P Q
      act_one := act'_one s
      act_mul := act'_mul s
      act_add := fun x y _ t' P => act'_add h s x y t' P
      act_trace := fun k _ _ sk V _ _ _ τ hτinj hτrange hτadd hτsmul x Φ hΦ n hn =>
        act'_trace h s sk τ hτinj hτrange hτadd hτsmul x Φ hΦ n hn
      P := genP hg s
      level_match := level_match' s hgP
      pol_canonical := pol_canonical' h s hgpol }
  refine ⟨s', gA, hg, ?_, hgP, hgpol, ?_, ?_⟩
  · intro T t' x y
    exact h t' x y
  · intro x
    exact act'_gA s x
  · exact genP_gA s

end Square

theorem exists_isPullback {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X : PolarisedAbelianScheme 2 d m S} {X' : PolarisedAbelianScheme 2 d m S'}
    (hX : PolarisedAbelianScheme.IsPullback φ X X') (s : QMStructure Λ star β X) :
    ∃ s' : QMStructure Λ star β X', QMStructure.IsPullback φ s s' := by
  obtain ⟨gA, hg, hmul, hP, hpol⟩ := hX
  exact exists_isPullback_of_square (gA := gA) (hg := hg) (fun t' x y => hmul t' x y) s hP hpol

end P2mKcQmBcSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback.P2mKcQmBcSol"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback.P2mKcQmBcSol"

open scoped Quaternion in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X : AlgebraicGeometry.PolarisedAbelianScheme 2 d m S} {X' : AlgebraicGeometry.PolarisedAbelianScheme 2 d m S'}
    (hX : AlgebraicGeometry.PolarisedAbelianScheme.IsPullback φ X X')
    (s : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure Λ star β X) :
    ∃ s' : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure Λ star β X',
      AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.IsPullback φ s s' :=
  P2mKcQmBcSol.exists_isPullback φ hX s

end S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback (solution)
