-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/87250565-d179-5fa6-b46b-d339801fbc68

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_RingHom_existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace BiAffine29

variable {𝒪 : Type} [CommRing 𝒪]

section Dictionary

variable {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))

noncomputable def baseHom : 𝒪 →+* Γ(M, ⊤) :=
  fM.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of 𝒪)).inv.hom

noncomputable def toHom {B : Type} [CommRing B] (φ : Spec (CommRingCat.of B) ⟶ M) : Γ(M, ⊤) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp φ.appTop.hom

theorem ΓSpecIso_inv_hom_apply (R : Type) [CommRing R] (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom r = r
  rw [Iso.inv_hom_id]; rfl

theorem ΓSpecIso_hom_inv_apply (R : Type) [CommRing R] (r : Γ(Spec (CommRingCat.of R), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom r = r
  rw [Iso.hom_inv_id]; rfl

theorem ΓSpecIso_nat_apply {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (r : Γ(Spec (CommRingCat.of R), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom r) =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
  have := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  have h := congrArg (fun g : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of S => g.hom r) this
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using h

theorem toHom_comp_baseHom {B : Type} [CommRing B] [Algebra 𝒪 B] (φ : Spec (CommRingCat.of B) ⟶ M)
    (hφ : φ ≫ fM = Scheme.specOver B) : (toHom φ).comp (baseHom fM) = algebraMap 𝒪 B := by
  apply RingHom.ext
  intro o
  show (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.appTop.hom (fM.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of 𝒪)).inv.hom o))) =
    algebraMap 𝒪 B o
  have h1 : φ.appTop.hom (fM.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of 𝒪)).inv.hom o)) =
      (Scheme.specOver (𝒪 := 𝒪) B).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of 𝒪)).inv.hom o) := by
    rw [← hφ, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [h1, Scheme.specOver, ΓSpecIso_nat_apply, ΓSpecIso_inv_hom_apply]

private noncomputable def _root_.BiAffine29.ofHom [IsAffine M] {B : Type} [CommRing B] (ξ : Γ(M, ⊤) →+* B) : Spec (CommRingCat.of B) ⟶ M :=
  Spec.map (CommRingCat.ofHom ξ) ≫ M.isoSpec.inv

p2m_export "BiAffine29" "ofHom"
theorem ofHom_toHom [IsAffine M] {B : Type} [CommRing B] (φ : Spec (CommRingCat.of B) ⟶ M) : ofHom (toHom φ) = φ := by
  unfold ofHom toHom
  rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom, Spec.map_comp, SpecMap_ΓSpecIso_hom,
    Category.assoc, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, Scheme.toSpecΓ_isoSpec_inv,
    Category.comp_id]

theorem toHom_ofHom [IsAffine M] {B : Type} [CommRing B] (ξ : Γ(M, ⊤) →+* B) : toHom (ofHom ξ) = ξ := by
  unfold ofHom toHom
  apply RingHom.ext
  intro a
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply, ΓSpecIso_nat_apply]
  congr 1

  have h1 : M.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(M, ⊤)).hom := by rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
  have h2 : M.isoSpec.hom.appTop ≫ M.isoSpec.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]; simp
  have h3 : M.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(M, ⊤)).hom = 𝟙 _ := by
    rw [← h1, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id]; simp
  have := congrArg (fun g : Γ(M, ⊤) ⟶ Γ(M, ⊤) => g.hom a) h3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
  exact this

theorem isoSpec_inv_comp [IsAffine M] :
    M.isoSpec.inv ≫ fM = Spec.map (CommRingCat.ofHom (baseHom fM)) := by
  have h1 : fM = M.toSpecΓ ≫ Spec.map fM.appTop ≫ (Spec (CommRingCat.of 𝒪)).isoSpec.inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  have h2 : (Spec (CommRingCat.of 𝒪)).isoSpec.inv = Spec.map (Scheme.ΓSpecIso (CommRingCat.of 𝒪)).inv :=
    Scheme.isoSpec_Spec_inv _
  rw [Iso.inv_comp_eq, Scheme.isoSpec_hom]
  conv_lhs => rw [h1]
  rw [h2, ← Spec.map_comp, baseHom, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom]

theorem ofHom_over [IsAffine M] {B : Type} [CommRing B] [Algebra 𝒪 B] (ξ : Γ(M, ⊤) →+* B)
    (hξ : ξ.comp (baseHom fM) = algebraMap 𝒪 B) : ofHom ξ ≫ fM = Scheme.specOver B := by
  unfold ofHom
  rw [Category.assoc, isoSpec_inv_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hξ]

end Dictionary

section Action

variable {M : Scheme.{0}} {G : Type} [Group G] (ρ : G →* Aut M)

noncomputable def sectionsAction : MulSemiringAction G Γ(M, ⊤) where
  smul g a := (ρ g⁻¹).hom.appTop.hom a
  one_smul a := by
    show (ρ 1⁻¹).hom.appTop.hom a = a
    rw [inv_one, map_one]
    show (𝟙 M : M ⟶ M).appTop.hom a = a
    simp
  mul_smul g h a := by
    show (ρ (g * h)⁻¹).hom.appTop.hom a = (ρ g⁻¹).hom.appTop.hom ((ρ h⁻¹).hom.appTop.hom a)
    rw [mul_inv_rev, map_mul, Aut.Aut_mul_def, Iso.trans_hom, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
  smul_zero g := map_zero _
  smul_add g a b := map_add _ a b
  smul_one g := map_one _
  smul_mul g a b := map_mul _ a b

theorem sectionsAction_smul (g : G) (a : Γ(M, ⊤)) :
    (letI := sectionsAction ρ; g • a) = (ρ g⁻¹).hom.appTop.hom a := rfl

theorem ofHom_comp_hom [IsAffine M] {B : Type} [CommRing B] (ξ : Γ(M, ⊤) →+* B) (h : M ⟶ M) :
    ofHom ξ ≫ h = ofHom (ξ.comp h.appTop.hom) := by
  unfold ofHom
  have hnat : h = M.isoSpec.hom ≫ Spec.map h.appTop ≫ M.isoSpec.inv := by
    rw [Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  conv_lhs => rw [hnat]
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, ← Spec.map_comp, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_hom]

end Action

section Points

variable {M : Scheme.{0}} [IsAffine M]

theorem specMap_comp_ofHom {B B' : Type} [CommRing B] [CommRing B'] (ξ : Γ(M, ⊤) →+* B) (φ : B →+* B') :
    Spec.map (CommRingCat.ofHom φ) ≫ ofHom ξ = ofHom (φ.comp ξ) := by
  unfold ofHom
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem toHom_specMap_comp {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B') (x : Spec (CommRingCat.of B) ⟶ M) :
    toHom (Spec.map (CommRingCat.ofHom φ) ≫ x) = φ.comp (toHom x) := by
  conv_lhs => rw [← ofHom_toHom x, specMap_comp_ofHom]
  rw [toHom_ofHom]

theorem toHom_comp {Y : Scheme.{0}} {B : Type} [CommRing B] (x : Spec (CommRingCat.of B) ⟶ M) (h : M ⟶ Y) :
    toHom (x ≫ h) = (toHom x).comp h.appTop.hom := by
  unfold toHom
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc]

end Points

section Ev

variable {X T : Scheme.{0}} [IsAffine T] (f : X ⟶ Spec (CommRingCat.of 𝒪)) (t : T ⟶ Spec (CommRingCat.of 𝒪))
  {ϖ : Γ(X, ⊤)} (d : ∀ n : ℕ, Γ(T, ⊤) →+* Γ(X, ⊤) ⧸ Ideal.span {ϖ ^ n})

noncomputable def evHom {B : Type} [CommRing B] (η : Γ(X, ⊤) →+* B) (N : ℕ)
    (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) : Γ(T, ⊤) →+* B :=
  (Ideal.Quotient.lift _ η hN).comp (d N)

theorem kill_mono (ϖ : Γ(X, ⊤)) {B : Type} [CommRing B] (η : Γ(X, ⊤) →+* B) (N j : ℕ)
    (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) : ∀ a ∈ Ideal.span {ϖ ^ (N + j)}, η a = 0 :=
  fun a ha => hN a (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_add_right N j)) ha)

theorem kill_of_pow_eq_zero {B : Type} [CommRing B] [Algebra 𝒪 B] (π : 𝒪) (η : Γ(X, ⊤) →+* B)
    (hη : η.comp (baseHom f) = algebraMap 𝒪 B) (N : ℕ) (hN : algebraMap 𝒪 B π ^ N = 0) :
    ∀ a ∈ Ideal.span {baseHom f π ^ N}, η a = 0 := by
  intro a ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [map_mul, map_pow, show η (baseHom f π) = algebraMap 𝒪 B π from by rw [← hη]; rfl, hN, mul_zero]

variable (hdc : ∀ n : ℕ, (Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ n)))).comp (d (n + 1)) = d n)

include hdc in
theorem evHom_add {B : Type} [CommRing B] (η : Γ(X, ⊤) →+* B) (N j : ℕ)
    (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) (hNj : ∀ a ∈ Ideal.span {ϖ ^ (N + j)}, η a = 0) :
    evHom d η N hN = evHom d η (N + j) hNj := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [ih (kill_mono ϖ η N j hN), evHom, evHom, ← hdc (N + j), ← RingHom.comp_assoc]
    congr 1
    exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

include hdc in
theorem evHom_indep {B : Type} [CommRing B] (η : Γ(X, ⊤) →+* B) (N N' : ℕ)
    (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) (hN' : ∀ a ∈ Ideal.span {ϖ ^ N'}, η a = 0) :
    evHom d η N hN = evHom d η N' hN' := by
  rw [evHom_add d hdc η N N' hN (kill_mono ϖ η N N' hN), evHom_add d hdc η N' N hN' (kill_mono ϖ η N' N hN')]
  suffices key : ∀ (m m' : ℕ) (_ : m = m') (h : ∀ a ∈ Ideal.span {ϖ ^ m}, η a = 0)
      (h' : ∀ a ∈ Ideal.span {ϖ ^ m'}, η a = 0), evHom d η m h = evHom d η m' h' from
    key _ _ (Nat.add_comm N N') _ _
  rintro m _ rfl h h'
  rfl

theorem evHom_congr {B : Type} [CommRing B] {η η' : Γ(X, ⊤) →+* B} (e : η = η') (N : ℕ)
    (h : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) (h' : ∀ a ∈ Ideal.span {ϖ ^ N}, η' a = 0) :
    evHom d η N h = evHom d η' N h' := by
  subst e; rfl

theorem comp_evHom {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B') (η : Γ(X, ⊤) →+* B) (N : ℕ)
    (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) (hN' : ∀ a ∈ Ideal.span {ϖ ^ N}, φ.comp η a = 0) :
    φ.comp (evHom d η N hN) = evHom d (φ.comp η) N hN' := by
  rw [evHom, evHom, ← RingHom.comp_assoc]
  congr 1
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk]

theorem evHom_comp_baseHom (hdO : ∀ (n : ℕ) (o : 𝒪), d n (baseHom t o) = Ideal.Quotient.mk _ (baseHom f o))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (η : Γ(X, ⊤) →+* B) (hη : η.comp (baseHom f) = algebraMap 𝒪 B)
    (N : ℕ) (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) : (evHom d η N hN).comp (baseHom t) = algebraMap 𝒪 B := by
  apply RingHom.ext
  intro o
  rw [← hη, evHom, RingHom.comp_apply, RingHom.comp_apply, hdO, Ideal.Quotient.lift_mk, RingHom.comp_apply]

theorem lift_comp_quotientMap {A B : Type} [CommRing A] [CommRing B] (ι : Γ(X, ⊤) →+* A) (ξ : A →+* B) (N : ℕ)
    (hξ : ∀ a ∈ Ideal.span {ι ϖ ^ N}, ξ a = 0) (hη : ∀ a ∈ Ideal.span {ϖ ^ N}, ξ.comp ι a = 0) :
    (Ideal.Quotient.lift _ ξ hξ).comp (Ideal.quotientMap (Ideal.span {ι ϖ ^ N}) ι
      (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← map_pow]; exact Ideal.subset_span rfl)) =
    Ideal.Quotient.lift _ (ξ.comp ι) hη := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]

end Ev

section Tower

variable {Y T : Scheme.{0}} [IsAffine Y] [IsAffine T] (fY : Y ⟶ Spec (CommRingCat.of 𝒪)) (t : T ⟶ Spec (CommRingCat.of 𝒪))
  (π : 𝒪)

noncomputable def canPt (a : Γ(Y, ⊤)) (n : ℕ) :
    letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
    (Scheme.nilpPoints fY).obj (Γ(Y, ⊤) ⧸ Ideal.span {a ^ n}) :=
  letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
  ⟨ofHom (Ideal.Quotient.mk _), ofHom_over fY _ rfl⟩

theorem canPt_val (a : Γ(Y, ⊤)) (n : ℕ) :
    letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
    (canPt fY a n).1 = ofHom (Ideal.Quotient.mk (Ideal.span {a ^ n})) := rfl

variable (v : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
    (Scheme.nilpPoints fY).obj B → (Scheme.nilpPoints t).obj B)
  (hv_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints fY).obj B), v B' hB' ((Scheme.nilpPoints fY).map φ x) = (Scheme.nilpPoints t).map φ (v B hB x))

include hv_nat in

theorem tower_compat (a : Γ(Y, ⊤)) :
    letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
    ∀ (hBn : ∀ n : ℕ, IsNilpotent (algebraMap 𝒪 (Γ(Y, ⊤) ⧸ Ideal.span {a ^ n}) π)) (n : ℕ),
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ n)))).comp
        (toHom (v _ (hBn (n + 1)) (canPt fY a (n + 1))).1) = toHom (v _ (hBn n) (canPt fY a n)).1 := by
  intro hBn n
  letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
  let φn : (Γ(Y, ⊤) ⧸ Ideal.span {a ^ (n + 1)}) →ₐ[𝒪] (Γ(Y, ⊤) ⧸ Ideal.span {a ^ n}) :=
    Ideal.Quotient.factorₐ 𝒪 (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ n)))
  have hφn : φn.toRingHom = Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ n))) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  have hpt : (Scheme.nilpPoints fY).map φn (canPt fY a (n + 1)) = canPt fY a n := by
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom φn.toRingHom) ≫ ofHom (Ideal.Quotient.mk _) = ofHom (Ideal.Quotient.mk _)
    rw [specMap_comp_ofHom]
    congr 1
  have hz := hv_nat _ _ (hBn (n + 1)) (hBn n) φn (canPt fY a (n + 1))
  rw [hpt] at hz
  rw [hz, ← hφn]
  exact (toHom_specMap_comp φn.toRingHom _).symm

theorem eq_map_canPt (a : Γ(Y, ⊤)) {B : Type} [CommRing B] [Algebra 𝒪 B] (y : (Scheme.nilpPoints fY).obj B) (N : ℕ)
    (hN : ∀ a' ∈ Ideal.span {a ^ N}, toHom y.1 a' = 0) :
    letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
    ∃ ξN : (Γ(Y, ⊤) ⧸ Ideal.span {a ^ N}) →ₐ[𝒪] B,
      ξN.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {a ^ N})) = toHom y.1 ∧ y = (Scheme.nilpPoints fY).map ξN (canPt fY a N) := by
  letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
  have hξ : (toHom y.1).comp (baseHom fY) = algebraMap 𝒪 B := toHom_comp_baseHom fY y.1 y.2
  let ξN : (Γ(Y, ⊤) ⧸ Ideal.span {a ^ N}) →ₐ[𝒪] B :=
    Ideal.Quotient.liftₐ _ (AlgHom.mk (toHom y.1) (fun o => by rw [← hξ]; rfl)) hN
  have hξN : ξN.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {a ^ N})) = toHom y.1 := RingHom.ext fun _ => rfl
  refine ⟨ξN, hξN, Subtype.ext ?_⟩
  show y.1 = Spec.map (CommRingCat.ofHom ξN.toRingHom) ≫ ofHom (Ideal.Quotient.mk _)
  rw [specMap_comp_ofHom, hξN]
  exact (ofHom_toHom y.1).symm

end Tower

section Invariance

variable {M T : Scheme.{0}} [IsAffine M] [IsAffine T] (fM : M ⟶ Spec (CommRingCat.of 𝒪)) (t : T ⟶ Spec (CommRingCat.of 𝒪))
  (π : 𝒪) {G : Type} [Group G] (ρ : G →* Aut M) (hover : ∀ g : G, (ρ g).hom ≫ fM = fM)
  (u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
    (Scheme.nilpPoints fM).obj B → (Scheme.nilpPoints t).obj B)
  (hu_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints fM).obj B), u B' hB' ((Scheme.nilpPoints fM).map φ x) = (Scheme.nilpPoints t).map φ (u B hB x))
  (hu_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : G) (y : (Scheme.nilpPoints fM).obj B),
    u B hB ((Scheme.nilpPoints.mapHom fM fM (ρ g).hom (hover g)).app B y) = u B hB y)

include hu_nat hu_inv in

theorem tower_invariant (a : Γ(M, ⊤)) (ha : ∀ g : G, (ρ g).hom.appTop.hom a = a)
    (hcomm : ∀ (g : G) (o : 𝒪), (ρ g).hom.appTop.hom (baseHom fM o) = baseHom fM o) :
    letI : Algebra 𝒪 Γ(M, ⊤) := (baseHom fM).toAlgebra
    ∀ (hBn : ∀ n : ℕ, IsNilpotent (algebraMap 𝒪 (Γ(M, ⊤) ⧸ Ideal.span {a ^ n}) π)) (n : ℕ) (g : G)
      (zC : Γ(T, ⊤)) (b : Γ(M, ⊤)),
      Ideal.Quotient.mk _ b = toHom (u _ (hBn n) (canPt fM a n)).1 zC →
      Ideal.Quotient.mk (Ideal.span {a ^ n}) ((ρ g).hom.appTop.hom b) = toHom (u _ (hBn n) (canPt fM a n)).1 zC := by
  intro hBn n g zC b hb
  letI : Algebra 𝒪 Γ(M, ⊤) := (baseHom fM).toAlgebra
  let σ : Γ(M, ⊤) →ₐ[𝒪] Γ(M, ⊤) := AlgHom.mk (ρ g).hom.appTop.hom (hcomm g)
  have hσI : Ideal.span {a ^ n} ≤ (Ideal.span {a ^ n}).comap σ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    show (ρ g).hom.appTop.hom (a ^ n) ∈ Ideal.span {a ^ n}
    rw [map_pow, ha]
    exact Ideal.subset_span rfl
  let gbar : (Γ(M, ⊤) ⧸ Ideal.span {a ^ n}) →ₐ[𝒪] (Γ(M, ⊤) ⧸ Ideal.span {a ^ n}) := Ideal.quotientMapₐ _ σ hσI
  have hpt : (Scheme.nilpPoints fM).map gbar (canPt fM a n) =
      (Scheme.nilpPoints.mapHom fM fM (ρ g).hom (hover g)).app _ (canPt fM a n) := by
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom gbar.toRingHom) ≫ ofHom (Ideal.Quotient.mk _) = ofHom (Ideal.Quotient.mk _) ≫ (ρ g).hom
    rw [specMap_comp_ofHom, ofHom_comp_hom]
    congr 1
  have hz : (Scheme.nilpPoints t).map gbar (u _ (hBn n) (canPt fM a n)) = u _ (hBn n) (canPt fM a n) := by
    rw [← hu_nat _ _ (hBn n) (hBn n) gbar (canPt fM a n), hpt]
    exact hu_inv _ (hBn n) g (canPt fM a n)
  have hcg : gbar.toRingHom.comp (toHom (u _ (hBn n) (canPt fM a n)).1) = toHom (u _ (hBn n) (canPt fM a n)).1 := by
    conv_rhs => rw [← hz]
    exact (toHom_specMap_comp gbar.toRingHom _).symm
  rw [← hcg, RingHom.comp_apply, ← hb]
  rfl

end Invariance

section Compat

theorem descent_comp_eq {𝒪 R A C : Type} [CommRing 𝒪] [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [CommRing C] (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]
    (hinj : Function.Injective (algebraMap R A))
    (hinv : ∀ a : A, (∀ g : G, g • a = a) → a ∈ Set.range (algebraMap R A)) (ϖ : R)
    (c : ∀ n : ℕ, C →+* A ⧸ Ideal.span {algebraMap R A ϖ ^ n})
    (hc : ∀ n : ℕ, (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap R A ϖ) (Nat.le_succ n)))).comp (c (n + 1)) = c n)
    (hG : ∀ (n : ℕ) (g : G) (z : C) (a : A), Ideal.Quotient.mk _ a = c n z →
      Ideal.Quotient.mk (Ideal.span {algebraMap R A ϖ ^ n}) (g • a) = c n z)
    (d : ∀ n : ℕ, C →+* R ⧸ Ideal.span {ϖ ^ n})
    (hdc : ∀ n : ℕ, (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ n)))).comp (d (n + 1)) = d n)
    (hdf : ∀ n : ℕ, (Ideal.quotientMap (Ideal.span {algebraMap R A ϖ ^ n}) (algebraMap R A)
      (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← map_pow]; exact Ideal.subset_span rfl)).comp (d n) = c n)
    (τC : 𝒪 →+* C) (τR : 𝒪 →+* R)
    (hτ : ∀ n : ℕ, (c n).comp τC = (Ideal.Quotient.mk _).comp ((algebraMap R A).comp τR)) :
    ∀ (n : ℕ) (o : 𝒪), d n (τC o) = Ideal.Quotient.mk (Ideal.span {ϖ ^ n}) (τR o) := by
  let c' : ∀ n : ℕ, 𝒪 →+* A ⧸ Ideal.span {algebraMap R A ϖ ^ n} := fun n => (c n).comp τC
  have hc' : ∀ n : ℕ, (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap R A ϖ) (Nat.le_succ n)))).comp (c' (n + 1)) = c' n :=
    fun n => by show (_ : _ →+* _).comp ((c (n + 1)).comp τC) = (c n).comp τC; rw [← RingHom.comp_assoc, hc n]
  have hG' : ∀ (n : ℕ) (g : G) (o : 𝒪) (a : A), Ideal.Quotient.mk _ a = c' n o →
      Ideal.Quotient.mk (Ideal.span {algebraMap R A ϖ ^ n}) (g • a) = c' n o := fun n g o a ha => hG n g (τC o) a ha
  obtain ⟨d', -, huniq'⟩ :=
    RingHom.existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing R A 𝒪 G hinj hinv ϖ c' hc' hG'
  have h1 : (fun n => (d n).comp τC) = d' := by
    apply huniq'
    refine ⟨fun n => ?_, fun n => ?_⟩
    · show (_ : _ →+* _).comp ((d (n + 1)).comp τC) = (d n).comp τC
      rw [← RingHom.comp_assoc, hdc n]
    · show (_ : _ →+* _).comp ((d n).comp τC) = (c n).comp τC
      rw [← RingHom.comp_assoc, hdf n]
  have h2 : (fun n => (Ideal.Quotient.mk (Ideal.span {ϖ ^ n})).comp τR) = d' := by
    apply huniq'
    refine ⟨fun n => ?_, fun n => ?_⟩
    · rfl
    · show _ = c' n
      rw [show c' n = (c n).comp τC from rfl, hτ]
      apply RingHom.ext
      intro o
      rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.quotientMap_mk]
      rfl
  intro n o
  have := congrFun (h1.trans h2.symm) n
  exact congrArg (fun φ : 𝒪 →+* _ => φ o) this

end Compat

end BiAffine29

open BiAffine29

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] (π : 𝒪)
    {M X : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪)) (f : X ⟶ Spec (CommRingCat.of 𝒪))
    (hlft : LocallyOfFiniteType fM) (hlftX : LocallyOfFiniteType f)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut M) (hover : ∀ g : G, (ρ g).hom ≫ fM = fM)
    (p : M ⟶ X) (hp : p ≫ f = fM) (hρp : ∀ g : G, (ρ g).hom ≫ p = p)
    (hint : IsIntegralHom p) (haff : IsAffineHom p) (hsurj : Function.Surjective p.base)
    (hsec : ∀ V : X.Opens, Function.Injective (p.app V))
    (hinv : ∀ V : X.Opens, Set.range (p.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hρp g]) s = s})
    (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints fM).obj B → (Scheme.nilpPoints t).obj B)
    (hu_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints fM).obj B), u B' hB' ((Scheme.nilpPoints fM).map φ x) = (Scheme.nilpPoints t).map φ (u B hB x))
    (hu_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : G) (y : (Scheme.nilpPoints fM).obj B),
      u B hB ((Scheme.nilpPoints.mapHom fM fM (ρ g).hom (hover g)).app B y) = u B hB y)
    (hX : IsAffine X) (hT : IsAffine T) :
    ∃ ubar : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), ubar B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (ubar B hB x)) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fM).obj B),
        ubar B hB ((Scheme.nilpPoints.mapHom fM f p hp).app B y) = u B hB y) ∧
      ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u' B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fM).obj B),
          u' B hB ((Scheme.nilpPoints.mapHom fM f p hp).app B y) = u B hB y) →
        ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints f).obj B), u' B hB z = ubar B hB z := by
  classical
  haveI : IsAffine X := hX
  haveI : IsAffine T := hT
  haveI : IsAffineHom p := haff
  haveI : IsAffine M := isAffine_of_isAffineHom p
  haveI : Fintype G := Fintype.ofFinite G

  letI algA : Algebra 𝒪 Γ(M, ⊤) := (baseHom fM).toAlgebra
  letI algR : Algebra 𝒪 Γ(X, ⊤) := (baseHom f).toAlgebra
  letI algRA : Algebra Γ(X, ⊤) Γ(M, ⊤) := p.appTop.hom.toAlgebra
  letI act : MulSemiringAction G Γ(M, ⊤) := sectionsAction ρ
  have hι : ∀ r : Γ(X, ⊤), algebraMap Γ(X, ⊤) Γ(M, ⊤) r = p.appTop.hom r := fun _ => rfl
  have hbase : ∀ o : 𝒪, baseHom fM o = p.appTop.hom (baseHom f o) := by
    intro o
    show (fM.appTop.hom.comp _) o = p.appTop.hom ((f.appTop.hom.comp _) o)
    rw [← hp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rfl
  haveI : IsScalarTower 𝒪 Γ(X, ⊤) Γ(M, ⊤) := IsScalarTower.of_algebraMap_eq hbase
  have hρapp : ∀ (g : G) (r : Γ(X, ⊤)), (ρ g).hom.appTop.hom (p.appTop.hom r) = p.appTop.hom r := by
    intro g r
    have := congrArg (fun q : M ⟶ X => q.appTop.hom r) (hρp g)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using this
  have hcomm : ∀ (g : G) (o : 𝒪), (ρ g).hom.appTop.hom (baseHom fM o) = baseHom fM o := fun g o => by
    rw [hbase, hρapp]
  haveI : SMulCommClass G Γ(X, ⊤) Γ(M, ⊤) := ⟨fun g r a => by
    rw [Algebra.smul_def, Algebra.smul_def, sectionsAction_smul, sectionsAction_smul, map_mul, hι, hρapp]⟩

  have hftR : (baseHom f).FiniteType := by
    have h1 : f.appTop.hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hlftX
    exact h1.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of 𝒪)).symm.commRingCatIsoToRingEquiv.surjective)
  haveI : IsNoetherianRing Γ(X, ⊤) := @Algebra.FiniteType.isNoetherianRing 𝒪 Γ(X, ⊤) _ _ algR hftR _
  have hftA : (baseHom fM).FiniteType := by
    have h1 : fM.appTop.hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hlft
    exact h1.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of 𝒪)).symm.commRingCatIsoToRingEquiv.surjective)
  haveI : Algebra.FiniteType 𝒪 Γ(M, ⊤) := hftA
  haveI : Algebra.FiniteType Γ(X, ⊤) Γ(M, ⊤) := Algebra.FiniteType.of_restrictScalars_finiteType 𝒪 _ _
  have hintp : p.appTop.hom.IsIntegral := ((HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)).mp hint).2
  haveI : Algebra.IsIntegral Γ(X, ⊤) Γ(M, ⊤) := ⟨fun a => hintp a⟩
  haveI : Module.Finite Γ(X, ⊤) Γ(M, ⊤) := Algebra.IsIntegral.finite
  have hinj : Function.Injective (algebraMap Γ(X, ⊤) Γ(M, ⊤)) := hsec ⊤
  have hinvA : ∀ a : Γ(M, ⊤), (∀ g : G, g • a = a) → a ∈ Set.range (algebraMap Γ(X, ⊤) Γ(M, ⊤)) := by
    intro a ha
    have : a ∈ Set.range (p.app ⊤) := by
      rw [hinv ⊤]
      intro g
      have h1 := ha g⁻¹
      rw [sectionsAction_smul, inv_inv] at h1
      rw [show (ρ g).hom.appLE (p ⁻¹ᵁ ⊤) (p ⁻¹ᵁ ⊤) (by rw [← Scheme.Hom.comp_preimage, hρp g]) = (ρ g).hom.appTop by
        simp [Scheme.Hom.appLE]]
      exact h1
    exact this

  let πR : Γ(X, ⊤) := baseHom f π
  let πA : Γ(M, ⊤) := algebraMap Γ(X, ⊤) Γ(M, ⊤) πR
  have hπA : algebraMap 𝒪 Γ(M, ⊤) π = πA := hbase π
  have hBn : ∀ n : ℕ, IsNilpotent (algebraMap 𝒪 (Γ(M, ⊤) ⧸ Ideal.span {πA ^ n}) π) := fun n => ⟨n, by
    show Ideal.Quotient.mk (Ideal.span {πA ^ n}) (algebraMap 𝒪 Γ(M, ⊤) π) ^ n = 0
    rw [hπA, show Ideal.Quotient.mk (Ideal.span {πA ^ n}) πA ^ n = Ideal.Quotient.mk (Ideal.span {πA ^ n}) (πA ^ n) from
      (map_pow _ _ _).symm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl⟩
  have hRn : ∀ n : ℕ, IsNilpotent (algebraMap 𝒪 (Γ(X, ⊤) ⧸ Ideal.span {πR ^ n}) π) := fun n => ⟨n, by
    show Ideal.Quotient.mk (Ideal.span {πR ^ n}) πR ^ n = 0
    rw [show Ideal.Quotient.mk (Ideal.span {πR ^ n}) πR ^ n = Ideal.Quotient.mk (Ideal.span {πR ^ n}) (πR ^ n) from
      (map_pow _ _ _).symm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl⟩
  let zT : ∀ n : ℕ, (Scheme.nilpPoints t).obj (Γ(M, ⊤) ⧸ Ideal.span {πA ^ n}) := fun n => u _ (hBn n) (canPt fM πA n)
  let c : ∀ n : ℕ, Γ(T, ⊤) →+* Γ(M, ⊤) ⧸ Ideal.span {πA ^ n} := fun n => toHom (zT n).1
  have hc : ∀ n : ℕ, (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow πA (Nat.le_succ n)))).comp (c (n + 1)) = c n :=
    tower_compat fM t π u hu_nat πA hBn
  have hπAinv : ∀ g : G, (ρ g).hom.appTop.hom πA = πA := fun g => hρapp g πR
  have hG : ∀ (n : ℕ) (g : G) (zC : Γ(T, ⊤)) (a : Γ(M, ⊤)), Ideal.Quotient.mk _ a = c n zC →
      Ideal.Quotient.mk (Ideal.span {πA ^ n}) (g • a) = c n zC := by
    intro n g zC a ha
    rw [sectionsAction_smul]
    exact tower_invariant fM t π ρ hover u hu_nat hu_inv πA hπAinv hcomm hBn n g⁻¹ zC a ha

  obtain ⟨d, ⟨hdc, hdf⟩, huniq⟩ :=
    RingHom.existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing Γ(X, ⊤) Γ(M, ⊤) Γ(T, ⊤) G
      hinj hinvA πR c hc hG

  have hdO : ∀ (n : ℕ) (o : 𝒪), d n (baseHom t o) = Ideal.Quotient.mk (Ideal.span {πR ^ n}) (baseHom f o) :=
    descent_comp_eq G hinj hinvA πR c hc hG d hdc hdf (baseHom t) (baseHom f) (fun n => by
      show (toHom (zT n).1).comp (baseHom t) = _
      rw [toHom_comp_baseHom t (zT n).1 (zT n).2]
      exact RingHom.ext fun o => by show Ideal.Quotient.mk _ (baseHom fM o) = _; rw [hbase]; rfl)

  have hηover : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : (Scheme.nilpPoints f).obj B),
      (toHom x.1).comp (baseHom f) = algebraMap 𝒪 B := fun B _ _ x => toHom_comp_baseHom f x.1 x.2
  have hxkill : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (x : (Scheme.nilpPoints f).obj B), ∀ a ∈ Ideal.span {πR ^ hB.choose}, toHom x.1 a = 0 := fun B _ _ hB x =>
    kill_of_pow_eq_zero f π (toHom x.1) (hηover B x) hB.choose hB.choose_spec
  let ubar : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B := fun B _ _ hB x =>
    ⟨ofHom (evHom d (toHom x.1) hB.choose (hxkill B hB x)),
      ofHom_over t _ (evHom_comp_baseHom f t d hdO (toHom x.1) (hηover B x) _ _)⟩
  have hubar : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (x : (Scheme.nilpPoints f).obj B), (ubar B hB x).1 = ofHom (evHom d (toHom x.1) hB.choose (hxkill B hB x)) :=
    fun _ _ _ _ _ => rfl

  have hubar_any : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (x : (Scheme.nilpPoints f).obj B) (N : ℕ) (hN : ∀ a ∈ Ideal.span {πR ^ N}, toHom x.1 a = 0),
      (ubar B hB x).1 = ofHom (evHom d (toHom x.1) N hN) := fun B _ _ hB x N hN => by
    rw [hubar, evHom_indep d hdc (toHom x.1) hB.choose N (hxkill B hB x) hN]

  have hnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B),
      ubar B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (ubar B hB x) := by
    intro B _ _ B' _ _ hB hB' φ x
    have hx' : toHom ((Scheme.nilpPoints f).map φ x).1 = φ.toRingHom.comp (toHom x.1) := toHom_specMap_comp φ.toRingHom x.1
    have hkφ : ∀ a ∈ Ideal.span {πR ^ hB.choose}, φ.toRingHom.comp (toHom x.1) a = 0 := fun a ha => by
      rw [RingHom.comp_apply, hxkill B hB x a ha, map_zero]
    have hkφ' : ∀ a ∈ Ideal.span {πR ^ hB.choose}, toHom ((Scheme.nilpPoints f).map φ x).1 a = 0 := by rw [hx']; exact hkφ
    apply Subtype.ext
    rw [hubar_any B' hB' _ hB.choose hkφ']
    show ofHom _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ofHom _
    rw [specMap_comp_ofHom, comp_evHom d φ.toRingHom (toHom x.1) hB.choose (hxkill B hB x) hkφ]
    congr 1
    exact evHom_congr d hx' _ _ _

  have hpbase : p.appTop.hom.comp (baseHom f) = baseHom fM := RingHom.ext fun o => (hbase o).symm
  have hfac : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (y : (Scheme.nilpPoints fM).obj B), ubar B hB ((Scheme.nilpPoints.mapHom fM f p hp).app B y) = u B hB y := by
    intro B _ _ hB y
    have hN : algebraMap 𝒪 B π ^ hB.choose = 0 := hB.choose_spec
    have hξ : (toHom y.1).comp (baseHom fM) = algebraMap 𝒪 B := toHom_comp_baseHom fM y.1 y.2
    have hξkill : ∀ a ∈ Ideal.span {πA ^ hB.choose}, toHom y.1 a = 0 := by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, map_pow, ← hπA, show toHom y.1 (algebraMap 𝒪 Γ(M, ⊤) π) = algebraMap 𝒪 B π from by rw [← hξ]; rfl,
        hN, mul_zero]
    obtain ⟨ξN, hξN, hy⟩ := eq_map_canPt fM πA y hB.choose hξkill
    have hη : toHom ((Scheme.nilpPoints.mapHom fM f p hp).app B y).1 = (toHom y.1).comp p.appTop.hom := toHom_comp y.1 p
    have hk1 : ∀ a ∈ Ideal.span {πR ^ hB.choose}, (toHom y.1).comp (algebraMap Γ(X, ⊤) Γ(M, ⊤)) a = 0 :=
      kill_of_pow_eq_zero f π _ (by show ((toHom y.1).comp p.appTop.hom).comp (baseHom f) = _; rw [RingHom.comp_assoc, hpbase, hξ]) _ hN
    have hkη : ∀ a ∈ Ideal.span {πR ^ hB.choose}, toHom ((Scheme.nilpPoints.mapHom fM f p hp).app B y).1 a = 0 := by
      rw [hη]; exact hk1
    apply Subtype.ext
    rw [hubar_any B hB ((Scheme.nilpPoints.mapHom fM f p hp).app B y) hB.choose hkη]
    conv_rhs => rw [hy, hu_nat _ _ (hBn hB.choose) hB ξN (canPt fM πA hB.choose)]
    show ofHom _ = Spec.map (CommRingCat.ofHom ξN.toRingHom) ≫ (zT hB.choose).1
    conv_rhs => rw [← ofHom_toHom (zT hB.choose).1, specMap_comp_ofHom]
    congr 1
    have step1 : evHom d (toHom ((Scheme.nilpPoints.mapHom fM f p hp).app B y).1) hB.choose hkη =
        evHom d ((toHom y.1).comp (algebraMap Γ(X, ⊤) Γ(M, ⊤))) hB.choose hk1 := by congr 1
    rw [step1, evHom, ← lift_comp_quotientMap (X := X) (algebraMap Γ(X, ⊤) Γ(M, ⊤)) (toHom y.1) hB.choose hξkill hk1,
      RingHom.comp_assoc, hdf hB.choose]
    show _ = ξN.toRingHom.comp (c hB.choose)
    congr 1
    exact Ideal.Quotient.ringHom_ext (hξN.symm ▸ rfl)
  refine ⟨ubar, hnat, hfac, ?_⟩

  intro u' hu'nat hu'fac B _ _ hB x

  obtain ⟨ηN, hηN, hx⟩ := eq_map_canPt f πR x hB.choose (hxkill B hB x)
  rw [hx, hu'nat _ _ (hRn hB.choose) hB ηN, hnat _ _ (hRn hB.choose) hB ηN]
  congr 1

  let d' : ∀ n : ℕ, Γ(T, ⊤) →+* Γ(X, ⊤) ⧸ Ideal.span {πR ^ n} := fun n => toHom (u' _ (hRn n) (canPt f πR n)).1
  have hd'c : ∀ n : ℕ, (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow πR (Nat.le_succ n)))).comp (d' (n + 1)) = d' n :=
    tower_compat f t π u' hu'nat πR hRn
  have hd'f : ∀ n : ℕ, (Ideal.quotientMap (Ideal.span {algebraMap Γ(X, ⊤) Γ(M, ⊤) πR ^ n}) (algebraMap Γ(X, ⊤) Γ(M, ⊤))
      (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← map_pow]; exact Ideal.subset_span rfl)).comp (d' n) = c n := by
    intro n

    let ιn : (Γ(X, ⊤) ⧸ Ideal.span {πR ^ n}) →ₐ[𝒪] (Γ(M, ⊤) ⧸ Ideal.span {πA ^ n}) :=
      Ideal.quotientMapₐ _ (AlgHom.mk (algebraMap Γ(X, ⊤) Γ(M, ⊤)) (fun o => (hbase o).symm))
        (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; exact Ideal.subset_span (by rw [map_pow]; rfl))
    have hpt : (Scheme.nilpPoints f).map ιn (canPt f πR n) = (Scheme.nilpPoints.mapHom fM f p hp).app _ (canPt fM πA n) := by
      apply Subtype.ext
      show Spec.map (CommRingCat.ofHom ιn.toRingHom) ≫ ofHom (Ideal.Quotient.mk _) = ofHom (Ideal.Quotient.mk _) ≫ p
      rw [specMap_comp_ofHom, ← ofHom_toHom (ofHom (Ideal.Quotient.mk (Ideal.span {πA ^ n})) ≫ p), toHom_comp, toHom_ofHom]
      congr 1
    have h1 := hu'nat _ _ (hRn n) (hBn n) ιn (canPt f πR n)
    rw [hpt, hu'fac _ (hBn n)] at h1

    show _ = toHom (zT n).1
    show _ = toHom (u _ (hBn n) (canPt fM πA n)).1
    rw [h1]
    have := toHom_specMap_comp ιn.toRingHom (u' _ (hRn n) (canPt f πR n)).1
    refine (Eq.trans ?_ this.symm)
    rfl
  have hdd : d' = d := huniq d' ⟨hd'c, hd'f⟩

  apply Subtype.ext
  have hkn : ∀ a ∈ Ideal.span {πR ^ hB.choose}, toHom (canPt f πR hB.choose).1 a = 0 := by
    intro a ha
    rw [canPt_val, toHom_ofHom]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  rw [hubar_any _ (hRn hB.choose) _ hB.choose hkn, ← ofHom_toHom (u' _ (hRn hB.choose) (canPt f πR hB.choose)).1]
  congr 1
  show d' hB.choose = _
  rw [hdd, evHom]
  conv_lhs => rw [← RingHom.id_comp (d hB.choose)]
  congr 1
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.lift_mk, RingHom.id_apply, canPt_val, toHom_ofHom]

end S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing (solution)
