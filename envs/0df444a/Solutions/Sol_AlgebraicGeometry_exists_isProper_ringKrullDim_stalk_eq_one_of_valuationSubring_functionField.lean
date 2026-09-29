-- Prove2me | solution 1 for AlgebraicGeometry.exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/50e3d737-694e-53cc-8e6c-9e05255d176e

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
import Theorems.Thm_AlgebraicGeometry_exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper
import Theorems.Thm_Ideal_height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField.AlgebraicGeometry TopologicalSpace Topology IsLocalRing HomogeneousLocalization"

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.fromSpecStalk_app Scheme.Hom.map_appLE IsLocallyNoetherian Scheme.fromSpecStalk_closedPoint Spec.map_comp_assoc Spec.map_apply IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom IsAffineOpen.toSpecΓ_fromSpec Scheme.Hom.appLE_comp_appLE Spec_stalkClosedPointIso IsAffineOpen.fromSpec_top IsProper.eq_valuativeCriterion IsAffineOpen.isoSpec_inv_ι ext_of_isAffine stalkClosedPointIso IsAffineOpen.primeIdealOf_eq_map_closedPoint ValuativeCommSq QuasiCompact IsAffine IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Proj.awayι Scheme.Hom.appTop Scheme.isoSpec_Spec_inv IsOpenImmersion functionField_isFractionRing_of_isAffineOpen Scheme.Hom.appIso_inv_app_apply genericPoint_eq_of_isOpenImmersion Proj IsSeparated.valuativeCriterion IsSeparated exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE germ_stalkClosedPointIso_hom IsAffineOpen genericPoint_eq_bot_of_affine QuasiSeparated Scheme.Hom.app_eq_appLE ValuativeCriterion Scheme.ΓSpecIso_naturality Scheme.Hom.comp_apply Scheme.Hom.appLE Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio ProjSpace.adjoin_range_ratio ProjSpace.exists_algHom_away_apply_ratio_eq exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral"
namespace RosenlichtL3
p2m_open "AlgebraicGeometry"

section Eval

variable {R : CommRingCat.{u}} {Z : Scheme.{u}}

def ev (u : Spec R ⟶ Z) (V : Z.Opens) (h : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V) : Γ(Z, V) →+* R :=
  (Scheme.ΓSpecIso R).hom.hom.comp (u.appLE V ⊤ h).hom

lemma ev_apply (u : Spec R ⟶ Z) (V : Z.Opens) (h : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V) (x : Γ(Z, V)) :
    ev u V h x = (Scheme.ΓSpecIso R).hom (u.appLE V ⊤ h x) := rfl

lemma ev_map (u : Spec R ⟶ Z) {V V' : Z.Opens} (i : V ≤ V') (h : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V)
    (h' : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V') (x : Γ(Z, V')) :
    ev u V h (Z.presheaf.map (homOfLE i).op x) = ev u V' h' x := by
  simp only [ev_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

lemma appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ h = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

lemma appLE_congr_hom {X Y : Scheme.{u}} {u u' : X ⟶ Y} (e : u = u') (V : Y.Opens) (W : X.Opens)
    (h : W ≤ u ⁻¹ᵁ V) : u.appLE V W h = u'.appLE V W (e ▸ h) := by
  subst e; rfl

lemma ev_comp {Z' : Scheme.{u}} (v : Spec R ⟶ Z') (w : Z' ⟶ Z) (V : Z.Opens)
    (h : (⊤ : (Spec R).Opens) ≤ (v ≫ w) ⁻¹ᵁ V) (x : Γ(Z, V)) :
    ev (v ≫ w) V h x = ev v (w ⁻¹ᵁ V) h (w.app V x) := by
  rw [ev_apply, ev_apply, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply (w.appLE _ _ _),
    Scheme.Hom.appLE_comp_appLE]

lemma ev_specMap_top {A : CommRingCat.{u}} (φ : A ⟶ R) (a : A) :
    ev (Spec.map φ) ⊤ le_top ((Scheme.ΓSpecIso A).inv a) = φ a := by
  rw [ev_apply, appLE_top_top]
  change ((Scheme.ΓSpecIso A).inv ≫ (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso R).hom) a = φ a
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

lemma germ_stalkClosedPointIso_hom_assoc_helper (R : CommRingCat.{u}) [IsLocalRing R] :
    (Scheme.ΓSpecIso R).hom ≫ (stalkClosedPointIso R).inv =
      (Spec R).presheaf.germ ⊤ (closedPoint R) trivial := by
  rw [← germ_stalkClosedPointIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma primeIdealOf_eq_comap_ev [IsLocalRing R] (u : Spec R ⟶ Z) {V : Z.Opens} (hV : IsAffineOpen V)
    (h : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V) :
    (hV.primeIdealOf ⟨u (closedPoint R), h (Opens.mem_top _)⟩).asIdeal =
      Ideal.comap (ev u V h) (maximalIdeal R) := by
  have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := u) (x := closedPoint R) V hV ⊤
    (isAffineOpen_top (Spec R)) h (Opens.mem_top _)
  rw [← h1]
  have h2 : ((isAffineOpen_top (Spec R)).primeIdealOf ⟨closedPoint R, Opens.mem_top _⟩) =
      PrimeSpectrum.comap (Scheme.ΓSpecIso R).hom.hom (closedPoint R) := by
    rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint]
    change Spec.map ((Spec R).presheaf.germ ⊤ (closedPoint R) trivial) _ = _
    rw [← germ_stalkClosedPointIso_hom_assoc_helper R, Spec.map_comp, Scheme.Hom.comp_apply,
      Spec_stalkClosedPointIso, Scheme.fromSpecStalk_closedPoint, Spec.map_apply]
  rw [h2]
  simp only [PrimeSpectrum.comap_asIdeal, ev, Ideal.comap_comap]
  rfl

lemma top_le_of_closedPoint_mem [IsLocalRing R] (u : Spec R ⟶ Z) (V : Z.Opens)
    (h : u (closedPoint R) ∈ V) : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V := by
  have : closedPoint R ∈ u ⁻¹ᵁ V := h
  rw [(IsLocalRing.closedPoint_mem_iff _).mp this]
  exact le_top

end Eval

section Sections

variable {P : Scheme.{u}} [IsIntegral P]

lemma exists_affine_sections {d : ℕ} (f : Fin d → P.functionField) :
    ∃ (U : P.Opens) (hU : IsAffineOpen U) (hη : genericPoint P ∈ U) (g : Fin d → Γ(P, U)),
      ∀ i, P.presheaf.germ U (genericPoint P) hη (g i) = f i := by
  classical

  have hrep : ∀ i, ∃ (W : P.Opens) (hW : genericPoint P ∈ W) (t : Γ(P, W)),
      P.presheaf.germ W (genericPoint P) hW t = f i := fun i =>
    let ⟨W, hW, t, ht⟩ := P.presheaf.exists_germ_eq (x := genericPoint P) (f i)
    ⟨W, hW, t, ht⟩
  choose W hW t ht using hrep
  let W₀ : P.Opens := Finset.univ.inf W
  have hW₀ : genericPoint P ∈ W₀ := by
    show genericPoint P ∈ (Finset.univ.inf W : P.Opens)
    rw [← SetLike.mem_coe, Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    simpa using fun i => hW i
  have hle : ∀ i, W₀ ≤ W i := fun i => Finset.inf_le (Finset.mem_univ i)
  obtain ⟨U, hU, hηU, hUW⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint P) (U := W₀) hW₀
  refine ⟨U, hU, hηU, fun i => P.presheaf.map (homOfLE ((hUW.trans (hle i)) : U ≤ W i)).op (t i), fun i => ?_⟩
  show P.presheaf.germ U (genericPoint P) hηU (P.presheaf.map (homOfLE _).op (t i)) = f i
  rw [TopCat.Presheaf.germ_res_apply P.presheaf]
  exact ht i

end Sections

section Chart

variable (k : Type u) [Field k] (d : ℕ)

abbrev grading := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k

abbrev PP : Scheme.{u} := Proj (grading k d)

abbrev Ad : Type u := Away (grading k d) (MvPolynomial.X (0 : Fin (d + 1)))

abbrev awayι₀ : Spec (.of (Ad k d)) ⟶ PP k d :=
  Proj.awayι (grading k d) (MvPolynomial.X 0) (ProjSpace.X_mem_one k d 0) one_pos

abbrev πP : PP k d ⟶ Spec (.of k) := ProjSpace.π k d

variable {k d}
variable {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))

def φk (U : P.Opens) : CommRingCat.of k ⟶ Γ(P, U) := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ U le_top

lemma ι_comp_eq (U : P.Opens) (hU : IsAffineOpen U) :
    U.ι ≫ p = hU.isoSpec.hom ≫ Spec.map (φk p U) := by
  rw [φk, ← IsAffineOpen.toSpecΓ_fromSpec hU, Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, Spec.map_comp]
  rfl

abbrev algU (U : P.Opens) : Algebra k Γ(P, U) := (show k →+* Γ(P, U) from (φk p U).hom).toAlgebra

def chartMor (U : P.Opens) (hU : IsAffineOpen U)
    (φ : letI := algU p U; Ad k d →ₐ[k] Γ(P, U)) : (U : Scheme.{u}) ⟶ PP k d :=
  letI := algU p U
  hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ awayι₀ k d

lemma chartMor_comp_π (U : P.Opens) (hU : IsAffineOpen U)
    (φ : letI := algU p U; Ad k d →ₐ[k] Γ(P, U)) :
    chartMor p U hU φ ≫ πP k d = U.ι ≫ p := by
  letI := algU p U
  rw [chartMor, Category.assoc, Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp, ι_comp_eq p U hU]
  congr 2
  ext x
  change φ.toRingHom (algebraMap k (Ad k d) x) = (φk p U) x
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl

end Chart

section KPoint

variable {P : Scheme.{u}} [IsIntegral P]

def κ (U : P.Opens) (hU : IsAffineOpen U) (hη : genericPoint P ∈ U) :
    Spec P.functionField ⟶ (U : Scheme.{u}) :=
  Spec.map (P.presheaf.germ U (genericPoint P) hη) ≫ hU.isoSpec.inv

@[reassoc]
lemma κ_ι (U : P.Opens) (hU : IsAffineOpen U) (hη : genericPoint P ∈ U) :
    κ U hU hη ≫ U.ι = P.fromSpecStalk (genericPoint P) := by
  rw [κ, Category.assoc, IsAffineOpen.isoSpec_inv_ι, ← hU.fromSpecStalk_eq_fromSpecStalk hη]
  rfl

@[reassoc]
lemma κ_isoSpec_hom (U : P.Opens) (hU : IsAffineOpen U) (hη : genericPoint P ∈ U) :
    κ U hU hη ≫ hU.isoSpec.hom = Spec.map (P.presheaf.germ U (genericPoint P) hη) := by
  rw [κ, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable (O : ValuationSubring P.functionField)
  (ℓ₀ : Spec (CommRingCat.of O) ⟶ P)
  (hℓ₀ : Spec.map (CommRingCat.ofHom (algebraMap O P.functionField)) ≫ ℓ₀ =
    P.fromSpecStalk (genericPoint P))

include hℓ₀ in

lemma algebraMap_ev_ℓ₀ (V : P.Opens) (h : (⊤ : (Spec (CommRingCat.of O)).Opens) ≤ ℓ₀ ⁻¹ᵁ V)
    (hηV : genericPoint P ∈ V) (x : Γ(P, V)) :
    algebraMap O P.functionField (ev ℓ₀ V h x) = P.presheaf.germ V (genericPoint P) hηV x := by
  set ι : CommRingCat.of (O : Type u) ⟶ P.functionField := CommRingCat.ofHom (algebraMap O P.functionField)
  have hℓ₀' : Spec.map ι ≫ ℓ₀ = P.fromSpecStalk (genericPoint P) := hℓ₀
  have hK : (⊤ : (Spec P.functionField).Opens) ≤ (Spec.map ι ≫ ℓ₀) ⁻¹ᵁ V := by
    intro y _
    show ℓ₀ (Spec.map ι y) ∈ V
    exact h (Opens.mem_top _)

  have h1 : (Scheme.ΓSpecIso P.functionField).hom ((Spec.map ι ≫ ℓ₀).appLE V ⊤ hK x) =
      (Scheme.ΓSpecIso P.functionField).hom
        ((P.fromSpecStalk (genericPoint P)).appLE V ⊤ (hℓ₀' ▸ hK) x) := by
    rw [appLE_congr_hom hℓ₀']

  have h2 : (Spec.map ι ≫ ℓ₀).appLE V ⊤ hK x = (Spec.map ι).appTop (ℓ₀.appLE V ⊤ h x) := by
    rw [← appLE_top_top (Spec.map ι) le_top, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have h3 : (Scheme.ΓSpecIso P.functionField).hom ((Spec.map ι).appTop (ℓ₀.appLE V ⊤ h x)) =
      ι ((Scheme.ΓSpecIso (CommRingCat.of (O : Type u))).hom (ℓ₀.appLE V ⊤ h x)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
    rfl

  have h4 : (P.fromSpecStalk (genericPoint P)).appLE V ⊤ (hℓ₀' ▸ hK) x =
      (Scheme.ΓSpecIso P.functionField).inv (P.presheaf.germ V (genericPoint P) hηV x) := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hηV]
    simp only [Category.assoc, ← Functor.map_comp]
    have : (homOfLE (le_top : (P.fromSpecStalk (genericPoint P)) ⁻¹ᵁ V ≤ ⊤)).op ≫
        (homOfLE ((hℓ₀' ▸ hK) : (⊤ : (Spec P.functionField).Opens) ≤ (P.fromSpecStalk (genericPoint P)) ⁻¹ᵁ V)).op =
        𝟙 _ := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  rw [h2, h3, h4] at h1
  simp only [CategoryTheory.Iso.inv_hom_id_apply] at h1
  exact h1

end KPoint

section Constants

variable {k : Type u} [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsIntegral P]

def θ : k →+* P.functionField :=
  (P.presheaf.germ ⊤ (genericPoint P) trivial).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)

variable (O : ValuationSubring P.functionField) {d : ℕ} (f : Fin d → P.functionField)
  (hind : ∀ Q : MvPolynomial (Fin d) k,
    O.valuation (Q.eval₂ ((P.presheaf.germ ⊤ (genericPoint P) trivial).hom.comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) f) < 1 → Q = 0)

include hind in
lemma θ_mem (c : k) : θ p c ∈ O := by
  by_contra hc
  have h1 : ¬ O.valuation (θ p c) ≤ 1 := fun h => hc ((O.valuation_le_one_iff _).mp h)
  have h2 : 1 < O.valuation (θ p c) := lt_of_not_ge h1
  have hc0 : θ p c ≠ 0 := by
    intro h0; rw [h0, map_zero] at h2; exact not_lt_of_ge zero_le_one h2
  have h3 : O.valuation (θ p c⁻¹) < 1 := by
    rw [map_inv₀, map_inv₀]
    exact inv_lt_one_of_one_lt₀ h2
  have h4 : (MvPolynomial.C c⁻¹ : MvPolynomial (Fin d) k) = 0 := by
    apply hind
    rw [MvPolynomial.eval₂_C]
    exact h3
  rw [MvPolynomial.C_eq_zero, inv_eq_zero] at h4
  exact hc0 (by rw [h4, map_zero])

def θO : k →+* O := (θ p).codRestrict O.toSubring (θ_mem p O f hind)

lemma algebraMap_θO (c : k) : algebraMap O P.functionField (θO p O f hind c) = θ p c := rfl

end Constants

section Aux

variable {R : CommRingCat.{u}} {Z : Scheme.{u}}

lemma ev_congr {u u' : Spec R ⟶ Z} (e : u = u') (V : Z.Opens) (h : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V)
    (x : Γ(Z, V)) : ev u V h x = ev u' V (e ▸ h) x := by
  subst e; rfl

theorem ringKrullDim_stalk_eq_height {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) = (hU.primeIdealOf ⟨x, hx⟩).asIdeal.height := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (X.presheaf.stalk x)

theorem chart_finiteType {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := algU f U
    Algebra.FiniteType k Γ(X, U) := by
  have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) hU le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

end Aux

section Main

variable {k : Type u} [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
  [IsIntegral P] [LocallyOfFiniteType p]
  (O : ValuationSubring P.functionField) (hO : O ≠ ⊤)
  (ℓ₀ : Spec (CommRingCat.of O) ⟶ P)
  (hℓ₀ : Spec.map (CommRingCat.ofHom (algebraMap O P.functionField)) ≫ ℓ₀ =
    P.fromSpecStalk (genericPoint P))
  (d : ℕ) (hd : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim P)
  (f : Fin d → P.functionField) (hf : ∀ i, f i ∈ O)
  (hind : ∀ Q : MvPolynomial (Fin d) k,
    O.valuation (Q.eval₂ ((P.presheaf.germ ⊤ (genericPoint P) trivial).hom.comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) f) < 1 → Q = 0)

include hℓ₀ in

lemma ev_ℓ₀_p (h : (⊤ : (Spec (CommRingCat.of O)).Opens) ≤ (ℓ₀ ≫ p) ⁻¹ᵁ ⊤) (c : k) :
    ev (ℓ₀ ≫ p) ⊤ h ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) = θO p O f hind c := by
  apply Subtype.ext
  change algebraMap O P.functionField _ = θ p c
  rw [ev_comp, algebraMap_ev_ℓ₀ O ℓ₀ hℓ₀ (p ⁻¹ᵁ ⊤) h trivial]
  rfl

include hO hℓ₀ hd hf hind in
theorem main :
    ∃ (P' : Scheme.{u}) (β : P' ⟶ P) (U : P.Opens) (s : (U : Scheme.{u}) ⟶ P')
      (ℓ : Spec (CommRingCat.of O) ⟶ P') (y' : P'),
      IsIntegral P' ∧ IsProper β ∧ (U : Set P).Nonempty ∧ IsOpenImmersion s ∧ s ≫ β = U.ι ∧
      Set.range s.base = β.base ⁻¹' (U : Set P) ∧
      ℓ ≫ β = ℓ₀ ∧ ℓ.base (IsLocalRing.closedPoint O) = y' ∧
      ringKrullDim (P'.presheaf.stalk y') = 1 := by
  classical

  obtain ⟨U, hU, hη, g, hg⟩ := exists_affine_sections f
  haveI : Nonempty U := ⟨⟨_, hη⟩⟩
  have hUne : (U : Set P).Nonempty := ⟨_, hη⟩

  letI algKU : Algebra k Γ(P, U) := algU p U
  let bU : Fin (d + 1) → Γ(P, U) := Fin.cons 1 g
  obtain ⟨φU, hφU⟩ := ProjSpace.exists_algHom_away_apply_ratio_eq k d 0 bU (by simp [bU])
  let gU : (U : Scheme.{u}) ⟶ PP k d := chartMor p U hU φU
  have hgU : gU ≫ πP k d = U.ι ≫ p := chartMor_comp_π p U hU φU
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p

  obtain ⟨P', β, s, g', hP'int, hβ, hs, hsβ, hrange, hsg', hg'π⟩ :=
    AlgebraicGeometry.exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper
      p (πP k d) U hUne gU hgU

  let ιOK : CommRingCat.of (O : Type u) ⟶ P.functionField :=
    CommRingCat.ofHom (algebraMap O P.functionField)
  have hℓ₀' : Spec.map ιOK ≫ ℓ₀ = P.fromSpecStalk (genericPoint P) := hℓ₀
  have hprop : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) β := by
    rw [← IsProper.eq_valuativeCriterion]; exact hβ
  let sq : ValuativeCommSq β :=
    { R := O, K := P.functionField, i₁ := κ U hU hη ≫ s, i₂ := ℓ₀,
      commSq := ⟨by rw [Category.assoc, hsβ, κ_ι]; exact hℓ₀'.symm⟩ }
  obtain ⟨⟨⟨lift⟩, -⟩⟩ := hprop.1.1.1 sq
  let ℓ : Spec (CommRingCat.of O) ⟶ P' := lift.l
  have hℓK : Spec.map ιOK ≫ ℓ = κ U hU hη ≫ s := lift.fac_left
  have hℓβ : ℓ ≫ β = ℓ₀ := lift.fac_right

  letI algKO : Algebra k O := (θO p O f hind).toAlgebra
  let bO : Fin (d + 1) → O := Fin.cons 1 (fun i => ⟨f i, hf i⟩)
  obtain ⟨φO, hφO⟩ := ProjSpace.exists_algHom_away_apply_ratio_eq k d 0 bO (by simp [bO])
  let mO : Spec (CommRingCat.of O) ⟶ PP k d :=
    Spec.map (CommRingCat.ofHom φO.toRingHom) ≫ awayι₀ k d

  have hring : (algebraMap O P.functionField).comp φO.toRingHom =
      (P.presheaf.germ U (genericPoint P) hη).hom.comp φU.toRingHom := by
    letI algKK : Algebra k P.functionField := (θ p).toAlgebra
    let F1 : Ad k d →ₐ[k] P.functionField :=
      { toRingHom := (algebraMap O P.functionField).comp φO.toRingHom
        commutes' := fun c => by
          change algebraMap O P.functionField (φO (algebraMap k (Ad k d) c)) = θ p c
          rw [AlgHom.commutes]
          rfl }
    let F2 : Ad k d →ₐ[k] P.functionField :=
      { toRingHom := (P.presheaf.germ U (genericPoint P) hη).hom.comp φU.toRingHom
        commutes' := fun c => by
          change P.presheaf.germ U (genericPoint P) hη (φU (algebraMap k (Ad k d) c)) = θ p c
          rw [AlgHom.commutes]
          change P.presheaf.germ U (genericPoint P) hη
            (P.presheaf.map (homOfLE le_top).op (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) = _
          rw [TopCat.Presheaf.germ_res_apply P.presheaf]
          rfl }
    have hF : F1 = F2 := by
      refine AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio k d 0) ?_
      rintro _ ⟨j, rfl⟩
      change algebraMap O P.functionField (φO (ProjSpace.ratio k d 0 j)) =
        P.presheaf.germ U (genericPoint P) hη (φU (ProjSpace.ratio k d 0 j))
      rw [hφO, hφU]
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [bO, bU]
      · simp only [bO, bU, Fin.cons_succ]
        exact (hg i).symm
    exact congrArg AlgHom.toRingHom hF
  have hsqP : CommSq (κ U hU hη ≫ gU) (Spec.map ιOK) (πP k d) (ℓ₀ ≫ p) :=
    ⟨by rw [Category.assoc, hgU, ← Category.assoc, κ_ι, ← hℓ₀', Category.assoc]⟩
  have hmO_left : Spec.map ιOK ≫ mO = κ U hU hη ≫ gU := by
    change Spec.map ιOK ≫ Spec.map _ ≫ awayι₀ k d =
      κ U hU hη ≫ (hU.isoSpec.hom ≫ Spec.map _ ≫ awayι₀ k d)
    rw [κ_isoSpec_hom_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext1
    exact hring
  have hmO_right : mO ≫ πP k d = ℓ₀ ≫ p := by
    change (Spec.map _ ≫ awayι₀ k d) ≫ πP k d = ℓ₀ ≫ p
    rw [Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp]
    refine ext_of_isAffine ?_
    have key : ∀ c : k, (Scheme.ΓSpecIso (CommRingCat.of O)).hom
        ((ℓ₀ ≫ p).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) = θO p O f hind c := by
      intro c
      rw [← appLE_top_top (ℓ₀ ≫ p) le_top]
      exact ev_ℓ₀_p p O ℓ₀ hℓ₀ d f hind le_top c
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).inv,
      ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of O)).hom, Category.assoc, Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
    apply CommRingCat.hom_ext
    refine RingHom.ext fun c => ?_
    change φO.toRingHom (algebraMap k (Ad k d) c) =
      (Scheme.ΓSpecIso (CommRingCat.of O)).hom ((ℓ₀ ≫ p).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
    rw [key c, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rfl
  have hℓg' : ℓ ≫ g' = mO := by
    let sqP : ValuativeCommSq (πP k d) :=
      { R := O, K := P.functionField, i₁ := κ U hU hη ≫ gU, i₂ := ℓ₀ ≫ p, commSq := hsqP }
    have hsub : Subsingleton sqP.commSq.LiftStruct := IsSeparated.valuativeCriterion (πP k d) sqP
    let L1 : sqP.commSq.LiftStruct :=
      ⟨ℓ ≫ g', by
        change Spec.map ιOK ≫ ℓ ≫ g' = κ U hU hη ≫ gU
        rw [← Category.assoc, hℓK, Category.assoc, hsg'], by
        change (ℓ ≫ g') ≫ πP k d = ℓ₀ ≫ p
        rw [Category.assoc, hg'π, ← Category.assoc, hℓβ]⟩
    let L2 : sqP.commSq.LiftStruct := ⟨mO, hmO_left, hmO_right⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim L1 L2)

  let W0 : (PP k d).Opens := (awayι₀ k d) ''ᵁ ⊤
  let r : Fin (d + 1) → Γ(PP k d, W0) := fun j =>
    ((awayι₀ k d).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of (Ad k d))).inv (ProjSpace.ratio k d 0 j))
  let V0 : P'.Opens := g' ⁻¹ᵁ W0
  let t : Fin (d + 1) → Γ(P', V0) := fun j => g'.app W0 (r j)
  let y' : P' := ℓ (closedPoint O)
  have hy'V0 : y' ∈ V0 := by
    change g' (ℓ (closedPoint O)) ∈ W0
    rw [← Scheme.Hom.comp_apply, hℓg']
    change awayι₀ k d (Spec.map (CommRingCat.ofHom φO.toRingHom) (closedPoint O)) ∈ (awayι₀ k d) ''ᵁ ⊤
    exact ⟨_, trivial, rfl⟩
  have hV0top : (⊤ : (Spec (CommRingCat.of O)).Opens) ≤ ℓ ⁻¹ᵁ V0 := top_le_of_closedPoint_mem ℓ V0 hy'V0
  have ht : ∀ j, ev ℓ V0 hV0top (t j) = bO j := by
    intro j
    have e1 : ev ℓ V0 hV0top (t j) = ev (ℓ ≫ g') W0 hV0top (r j) := (ev_comp ℓ g' W0 hV0top (r j)).symm
    rw [e1, ev_congr hℓg', ev_comp]
    change ev (Spec.map (CommRingCat.ofHom φO.toRingHom)) ((awayι₀ k d) ⁻¹ᵁ W0) _
      ((awayι₀ k d).app ((awayι₀ k d) ''ᵁ ⊤) (((awayι₀ k d).appIso ⊤).inv _)) = _
    rw [Scheme.Hom.appIso_inv_app_apply]
    have hop : (eqToHom ((awayι₀ k d).preimage_image_eq ⊤)).op =
        (homOfLE ((awayι₀ k d).preimage_image_eq ⊤).le).op := Subsingleton.elim _ _
    rw [hop, ev_map (Spec.map (CommRingCat.ofHom φO.toRingHom)) ((awayι₀ k d).preimage_image_eq ⊤).le _ le_top,
      ev_specMap_top]
    exact hφO j

  obtain ⟨V, hV, hy'V, hVV0s⟩ := exists_isAffineOpen_mem_and_subset (x := y') (U := V0) hy'V0
  have hVV0 : V ≤ V0 := hVV0s
  have hVtop : (⊤ : (Spec (CommRingCat.of O)).Opens) ≤ ℓ ⁻¹ᵁ V := top_le_of_closedPoint_mem ℓ V hy'V
  let tV : Fin (d + 1) → Γ(P', V) := fun j => P'.presheaf.map (homOfLE hVV0).op (t j)
  let χ : Γ(P', V) →+* O := ev ℓ V hVtop
  have hχt : ∀ j, χ (tV j) = bO j := fun j => by
    change ev ℓ V hVtop (P'.presheaf.map (homOfLE hVV0).op (t j)) = bO j
    rw [ev_map ℓ hVV0 hVtop hV0top]
    exact ht j
  let 𝔮 : PrimeSpectrum Γ(P', V) := hV.primeIdealOf ⟨y', hy'V⟩
  have h𝔮 : 𝔮.asIdeal = Ideal.comap χ (maximalIdeal O) := primeIdealOf_eq_comap_ev ℓ hV hVtop
  let p' : P' ⟶ Spec (CommRingCat.of k) := β ≫ p
  letI algB : Algebra k Γ(P', V) := algU p' V
  haveI : Algebra.FiniteType k Γ(P', V) := chart_finiteType p' hV
  haveI : Nonempty V := ⟨⟨y', hy'V⟩⟩
  have hχalg : ∀ c : k, χ (algebraMap k Γ(P', V) c) = θO p O f hind c := by
    intro c
    have e0 : χ (algebraMap k Γ(P', V) c) =
        ev (ℓ ≫ p') ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
      change (Scheme.ΓSpecIso (CommRingCat.of O)).hom (ℓ.appLE V ⊤ hVtop (p'.appLE ⊤ V le_top _)) =
        (Scheme.ΓSpecIso (CommRingCat.of O)).hom ((ℓ ≫ p').appLE ⊤ ⊤ le_top _)
      rw [← CommRingCat.comp_apply (p'.appLE _ _ _), Scheme.Hom.appLE_comp_appLE]
      rfl
    have e : ℓ ≫ p' = ℓ₀ ≫ p := by
      change ℓ ≫ β ≫ p = ℓ₀ ≫ p
      rw [← Category.assoc, hℓβ]
    rw [e0, ev_congr e]
    exact ev_ℓ₀_p p O ℓ₀ hℓ₀ d f hind _ c
  have hind' : ∀ Q : MvPolynomial (Fin d) k,
      MvPolynomial.aeval (fun i => tV i.succ) Q ∈ 𝔮.asIdeal → Q = 0 := by
    intro Q hQ
    rw [h𝔮, Ideal.mem_comap] at hQ
    apply hind Q
    have e1 : χ (MvPolynomial.aeval (fun i => tV i.succ) Q) =
        MvPolynomial.eval₂ (χ.comp (algebraMap k _)) (χ ∘ fun i => tV i.succ) Q := by
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
    have e2 : (χ ∘ fun i => tV i.succ) = fun i => (⟨f i, hf i⟩ : O) := by
      funext i
      change χ (tV i.succ) = _
      rw [hχt]
      simp [bO]
    have e3 : χ.comp (algebraMap k Γ(P', V)) = θO p O f hind := RingHom.ext hχalg
    have e4 : ((χ (MvPolynomial.aeval (fun i => tV i.succ) Q) : O) : P.functionField) =
        Q.eval₂ (θ p) f := by
      rw [e1, e3, e2]
      change algebraMap O P.functionField (MvPolynomial.eval₂ _ _ Q) = _
      rw [MvPolynomial.eval₂_comp_left (algebraMap O P.functionField)]
      rfl
    have e5 : O.valuation (Q.eval₂ (θ p) f) < 1 := by
      rw [← e4]
      exact (O.valuation_lt_one_iff _).mp hQ
    exact e5

  have h𝔮ne : 𝔮.asIdeal ≠ ⊥ := by
    intro hbot
    have hy'gen : y' = genericPoint P' := by
      have e1 : hV.fromSpec 𝔮 = y' := hV.fromSpec_primeIdealOf ⟨y', hy'V⟩
      have e2 : 𝔮 = genericPoint (Spec Γ(P', V)) := by
        rw [genericPoint_eq_bot_of_affine]
        exact PrimeSpectrum.ext hbot
      rw [← e1, e2]
      exact genericPoint_eq_of_isOpenImmersion hV.fromSpec
    have hβgen : β y' = genericPoint P := by
      rw [hy'gen, ← genericPoint_eq_of_isOpenImmersion s, ← Scheme.Hom.comp_apply, hsβ]
      exact genericPoint_eq_of_isOpenImmersion U.ι
    have hx₀ : ℓ₀ (closedPoint O) = genericPoint P := by
      rw [← hℓβ, Scheme.Hom.comp_apply]
      exact hβgen
    have hUtop : (⊤ : (Spec (CommRingCat.of O)).Opens) ≤ ℓ₀ ⁻¹ᵁ U :=
      top_le_of_closedPoint_mem ℓ₀ U (by rw [hx₀]; exact hη)
    have hχ₀ : Ideal.comap (ev ℓ₀ U hUtop) (maximalIdeal O) = ⊥ := by
      rw [← primeIdealOf_eq_comap_ev ℓ₀ hU hUtop]
      have e1 : hU.primeIdealOf ⟨ℓ₀ (closedPoint O), hUtop (Opens.mem_top _)⟩ =
          hU.primeIdealOf ⟨genericPoint P, hη⟩ := by
        congr 2
      rw [e1]
      have e2 := hU.primeIdealOf_genericPoint (X := P)
      rw [genericPoint_eq_bot_of_affine] at e2
      exact congrArg PrimeSpectrum.asIdeal e2
    apply hO
    haveI := functionField_isFractionRing_of_isAffineOpen P U hU
    rw [eq_top_iff]
    rintro z -
    obtain ⟨a, b, hbnz, rfl⟩ := IsFractionRing.div_surjective (A := Γ(P, U)) z
    have hb : b ≠ 0 := nonZeroDivisors.ne_zero hbnz
    have hbunit : IsUnit (ev ℓ₀ U hUtop b) := by
      by_contra hnu
      have : b ∈ Ideal.comap (ev ℓ₀ U hUtop) (maximalIdeal O) :=
        Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr hnu)
      rw [hχ₀] at this
      exact hb this
    have ha' : algebraMap Γ(P, U) P.functionField a = algebraMap O P.functionField (ev ℓ₀ U hUtop a) :=
      (algebraMap_ev_ℓ₀ O ℓ₀ hℓ₀ U hUtop hη a).symm
    have hb' : algebraMap Γ(P, U) P.functionField b = algebraMap O P.functionField (ev ℓ₀ U hUtop b) :=
      (algebraMap_ev_ℓ₀ O ℓ₀ hℓ₀ U hUtop hη b).symm
    obtain ⟨u, hu⟩ := hbunit
    rw [ha', hb', ← hu]
    have : algebraMap O P.functionField (ev ℓ₀ U hUtop a) / algebraMap O P.functionField (u : O) =
        algebraMap O P.functionField (ev ℓ₀ U hUtop a * ((u⁻¹ : Oˣ) : O)) := by
      rw [map_mul, div_eq_mul_inv]
      congr 1
      exact (map_units_inv (algebraMap O P.functionField) u).symm
    rw [this]
    exact (ev ℓ₀ U hUtop a * ((u⁻¹ : Oˣ) : O)).2

  have hdimU : topologicalKrullDim P = ringKrullDim Γ(P, U) :=
    topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral p hU hUne
  haveI : IsAffine (U : Scheme.{u}) := hU
  have hsU : IsAffineOpen (s ''ᵁ ⊤) := (isAffineOpen_top (U : Scheme.{u})).image_of_isOpenImmersion s
  have hsUne : ((s ''ᵁ ⊤ : P'.Opens) : Set P').Nonempty :=
    ⟨s ⟨genericPoint P, hη⟩, ⟨⟨genericPoint P, hη⟩, trivial, rfl⟩⟩
  haveI : LocallyOfFiniteType p' := inferInstance
  have hdimP'1 : topologicalKrullDim P' = ringKrullDim Γ(P', s ''ᵁ ⊤) :=
    topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral p' hsU hsUne
  have hdimP'2 : topologicalKrullDim P' = ringKrullDim Γ(P', V) :=
    topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral p' hV ⟨y', hy'V⟩
  have hiso : ringKrullDim Γ(P', s ''ᵁ ⊤) = ringKrullDim Γ(P, U) :=
    ringKrullDim_eq_of_ringEquiv ((s.appIso ⊤) ≪≫ U.topIso).commRingCatIsoToRingEquiv
  have hdimB : ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim Γ(P', V) := by
    rw [← hdimP'2, hdimP'1, hiso, ← hdimU]
    exact hd

  have hht : 𝔮.asIdeal.height = 1 :=
    Ideal.height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq k 𝔮.asIdeal h𝔮ne d
      hdimB (fun i => tV i.succ) hind'
  have hdim : ringKrullDim (P'.presheaf.stalk y') = 1 := by
    rw [ringKrullDim_stalk_eq_height hV y' hy'V]
    change ((𝔮.asIdeal.height : ℕ∞) : WithBot ℕ∞) = 1
    rw [hht]
    rfl
  exact ⟨P', β, U, s, ℓ, y', hP'int, hβ, hUne, hs, hsβ, hrange, hℓβ, rfl, hdim⟩

end Main

end AlgebraicGeometry.RosenlichtL3

end

theorem solution
    (k : Type u) [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsIntegral P] [LocallyOfFiniteType p]
    (O : ValuationSubring P.functionField) (hO : O ≠ ⊤)
    (ℓ₀ : Spec (CommRingCat.of O) ⟶ P)
    (hℓ₀ : Spec.map (CommRingCat.ofHom (algebraMap O P.functionField)) ≫ ℓ₀ =
      P.fromSpecStalk (genericPoint P))
    (d : ℕ) (hd : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim P)
    (f : Fin d → P.functionField) (hf : ∀ i, f i ∈ O)
    (hind : ∀ Q : MvPolynomial (Fin d) k,
      O.valuation (Q.eval₂ ((P.presheaf.germ ⊤ (genericPoint P) trivial).hom.comp
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) f) < 1 → Q = 0) :
    ∃ (P' : Scheme.{u}) (β : P' ⟶ P) (U : P.Opens) (s : (U : Scheme.{u}) ⟶ P')
      (ℓ : Spec (CommRingCat.of O) ⟶ P') (y' : P'),
      IsIntegral P' ∧ IsProper β ∧ (U : Set P).Nonempty ∧ IsOpenImmersion s ∧ s ≫ β = U.ι ∧
      Set.range s.base = β.base ⁻¹' (U : Set P) ∧
      ℓ ≫ β = ℓ₀ ∧ ℓ.base (IsLocalRing.closedPoint O) = y' ∧
      ringKrullDim (P'.presheaf.stalk y') = 1 :=
  AlgebraicGeometry.RosenlichtL3.main p O hO ℓ₀ hℓ₀ d hd f hf hind

end S_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField (solution)
