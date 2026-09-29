-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5159840e-9dbf-590b-a8bc-8f4216d013b9

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_TorsionCharacter
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard AlgebraicGeometry.DescentCharacter"

noncomputable section

namespace UnitOnSquare

p2m_open "GoodReductionJacobian.RelativeGroupLaw"

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem mul_coe_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {P₁ Q₁ : SchemeHomOver t₁ f} {P₂ Q₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht; rw [Subtype.ext hP, Subtype.ext hQ]

theorem inv_coe_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {P₁ : SchemeHomOver t₁ f} {P₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) :
    (L.inv t₁ P₁).1 = (L.inv t₂ P₂).1 := by
  subst ht; rw [Subtype.ext hP]

theorem one_coe_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂) :
    (L.one t₁).1 = (L.one t₂).1 := by
  subst ht; rfl

theorem nsmul_coe_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂) (n : ℕ)
    {P₁ : SchemeHomOver t₁ f} {P₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) :
    (L.nsmul t₁ n P₁).1 = (L.nsmul t₂ n P₂).1 := by
  subst ht; rw [Subtype.ext hP]

theorem inv_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t
  letI := L.pointGroup t'
  let F : SchemeHomOver t f →* SchemeHomOver t' f :=
    MonoidHom.mk' (schemeHomOverComp ψ hψ) (fun a b => L.mul_natural t t' ψ hψ a b)
  exact map_inv F x

theorem nsmul_coe_eq_comp_schemeNsmul {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (n : ℕ)
    (x : SchemeHomOver t f) : (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have h := congrArg Subtype.val (L.nsmul_natural f t x.1 x.2 n idPoint)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  have hx : schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x := Subtype.ext (Category.comp_id _)
  rw [hx] at h
  exact h.symm

theorem one_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 = t ≫ (L.one (𝟙 _)).1 := by
  have h := congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  exact h.symm

theorem inv_mul_mul_cancel {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (a x : SchemeHomOver t f) :
    L.mul t (L.inv t a) (L.mul t a x) = x := by
  letI := L.pointGroup t
  exact inv_mul_cancel_left a x

theorem diff_sq_eq_one (hc : L.IsCommutative) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (a b : SchemeHomOver t f) (h : L.nsmul t 2 a = L.nsmul t 2 b) :
    L.nsmul t 2 (L.mul t (L.inv t a) b) = L.one t := by
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := fun x y => hc.mul_comm t x y }
  change (1 * a) * a = (1 * b) * b at h
  change (1 * (a⁻¹ * b)) * (a⁻¹ * b) = 1
  simp only [_root_.one_mul] at h ⊢
  rw [mul_mul_mul_comm, ← h]
  group

theorem diff_mul_diff {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (a₁ a₂ b₂ : SchemeHomOver t f) :
    L.mul t (L.mul t (L.inv t a₁) a₂) (L.mul t (L.inv t a₂) b₂) = L.mul t (L.inv t a₁) b₂ := by
  letI := L.pointGroup t
  change (a₁⁻¹ * a₂) * (a₂⁻¹ * b₂) = a₁⁻¹ * b₂
  group

theorem inv_one_mul_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    L.mul t (L.inv t (L.one t)) (L.one t) = L.one t := by
  letI := L.pointGroup t
  change (1 : SchemeHomOver t f)⁻¹ * 1 = 1
  group

end UnitOnSquare

namespace UnitOnSquare

p2m_open "GoodReductionJacobian.RelativeGroupLaw"

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem isTorsionPoint_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂) (n : ℕ)
    {P₁ : SchemeHomOver t₁ f} {P₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) (h : L.IsTorsionPoint t₁ n P₁) :
    L.IsTorsionPoint t₂ n P₂ := by
  subst ht; cases Subtype.ext hP; exact h

theorem isTorsionPoint_two_mul (hc : L.IsCommutative) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t f) (hP : L.IsTorsionPoint t 2 P) (hQ : L.IsTorsionPoint t 2 Q) :
    L.IsTorsionPoint t 2 (L.mul t P Q) := by
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := fun x y => hc.mul_comm t x y }
  change (1 * P) * P = 1 at hP
  change (1 * Q) * Q = 1 at hQ
  change (1 * (P * Q)) * (P * Q) = 1
  simp only [_root_.one_mul] at hP hQ ⊢
  rw [mul_mul_mul_comm, hP, hQ, _root_.one_mul]

private theorem _root_.UnitOnSquare.val_one {R : Type} [CommRing R] {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}
    (χ : L.TorsionCharacter 2 ι) (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (h : L.IsTorsionPoint (κ ≫ ι) 2 (L.one (κ ≫ ι))) : χ.val T κ (L.one (κ ≫ ι)) h = 1 := by
  have hm : L.mul (κ ≫ ι) (L.one (κ ≫ ι)) (L.one (κ ≫ ι)) = L.one (κ ≫ ι) := L.one_mul _ _
  have h2 : L.IsTorsionPoint (κ ≫ ι) 2 (L.mul (κ ≫ ι) (L.one (κ ≫ ι)) (L.one (κ ≫ ι))) := by rw [hm]; exact h
  have := χ.val_mul T κ (L.one _) (L.one _) h h h2
  have key : χ.val T κ (L.mul (κ ≫ ι) (L.one (κ ≫ ι)) (L.one (κ ≫ ι))) h2 = χ.val T κ (L.one (κ ≫ ι)) h := by
    congr 1
  rw [key] at this

  have h3 := this.symm
  rwa [mul_eq_left] at h3

p2m_export "UnitOnSquare" "val_one"
section Kernel

variable {R : Type} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))

theorem baseChange_nsmul {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (y : SchemeHomOver t' (baseChangeStr ι f)) :
    (L.baseChange ι).nsmul t' n y = baseChangePointOfBase ι (L.nsmul (t' ≫ ι) n (baseChangePointToBase ι y)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmul_succ, nsmul_succ, ih, baseChange_mul, baseChangePointToBase_ofBase]

theorem isTorsionPoint_toBase {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (y : SchemeHomOver t' (baseChangeStr ι f)) (hy : (L.baseChange ι).IsTorsionPoint t' n y) :
    L.IsTorsionPoint (t' ≫ ι) n (baseChangePointToBase ι y) := by
  have h := congrArg (baseChangePointToBase ι) hy
  rw [baseChange_nsmul, baseChangePointToBase_ofBase, baseChangePointToBase_one] at h
  exact h

abbrev K2 : Scheme.{0} := (L.baseChange ι).schemeKer 2
abbrev kfst : K2 L ι ⟶ pullback f ι := pullback.fst _ _
abbrev kstr : K2 L ι ⟶ Spec (CommRingCat.of R) := (L.baseChange ι).schemeKerStr 2

theorem kfst_str : kfst L ι ≫ pullback.snd f ι = kstr L ι := by
  have h1 : (L.baseChange ι).schemeNsmul 2 ≫ pullback.snd f ι = pullback.snd f ι := (L.baseChange ι).schemeNsmul_over 2
  have h2 : ((L.baseChange ι).one (𝟙 _)).1 ≫ pullback.snd f ι = 𝟙 _ := ((L.baseChange ι).one _).2
  calc kfst L ι ≫ pullback.snd f ι = (kfst L ι ≫ (L.baseChange ι).schemeNsmul 2) ≫ pullback.snd f ι := by
        rw [Category.assoc, h1]
    _ = (kstr L ι ≫ ((L.baseChange ι).one (𝟙 _)).1) ≫ pullback.snd f ι := by rw [pullback.condition]
    _ = kstr L ι := by rw [Category.assoc, h2, Category.comp_id]

def ptR {T : Scheme.{0}} (z : T ⟶ K2 L ι) : SchemeHomOver (z ≫ kstr L ι) (baseChangeStr ι f) :=
  ⟨z ≫ kfst L ι, by rw [Category.assoc, kfst_str]⟩

def ptA {T : Scheme.{0}} (z : T ⟶ K2 L ι) : SchemeHomOver ((z ≫ kstr L ι) ≫ ι) f :=
  baseChangePointToBase ι (ptR L ι z)

@[scoped simp] theorem ptA_coe {T : Scheme.{0}} (z : T ⟶ K2 L ι) : (ptA L ι z).1 = z ≫ kfst L ι ≫ pullback.fst f ι := by
  simp only [ptA, ptR, baseChangePointToBase_coe, Category.assoc]

theorem ptR_torsion {T : Scheme.{0}} (z : T ⟶ K2 L ι) : (L.baseChange ι).IsTorsionPoint (z ≫ kstr L ι) 2 (ptR L ι z) := by
  apply Subtype.ext
  rw [nsmul_coe_eq_comp_schemeNsmul, one_coe]
  show (z ≫ kfst L ι) ≫ (L.baseChange ι).schemeNsmul 2 = (z ≫ kstr L ι) ≫ _
  rw [Category.assoc, pullback.condition, Category.assoc]

theorem ptA_torsion {T : Scheme.{0}} (z : T ⟶ K2 L ι) : L.IsTorsionPoint ((z ≫ kstr L ι) ≫ ι) 2 (ptA L ι z) :=
  isTorsionPoint_toBase L ι _ 2 _ (ptR_torsion L ι z)

def toK {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t (baseChangeStr ι f))
    (hy : (L.baseChange ι).IsTorsionPoint t 2 y) : T ⟶ K2 L ι :=
  pullback.lift y.1 t (by
    have h := congrArg Subtype.val hy
    rw [nsmul_coe_eq_comp_schemeNsmul, one_coe] at h
    exact h)

@[scoped simp] theorem toK_fst {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t (baseChangeStr ι f))
    (hy : (L.baseChange ι).IsTorsionPoint t 2 y) : toK L ι y hy ≫ kfst L ι = y.1 := pullback.lift_fst _ _ _

@[scoped simp] theorem toK_str {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t (baseChangeStr ι f))
    (hy : (L.baseChange ι).IsTorsionPoint t 2 y) : toK L ι y hy ≫ kstr L ι = t := pullback.lift_snd _ _ _

theorem isAffine_K2 (h : IsAffineHom (L.schemeNsmul 2)) : IsAffine (K2 L ι) := by
  have h2 : IsAffineHom ((L.baseChange ι).schemeNsmul 2) :=
    (isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange ι L 2).2 _ inferInstance h
  haveI : IsAffineHom (kstr L ι) := MorphismProperty.pullback_snd _ _ h2
  exact isAffine_of_isAffineHom (kstr L ι)

variable (χ : L.TorsionCharacter 2 ι) [IsAffine (K2 L ι)]

abbrev zK : Spec (CommRingCat.of ↑(Γ(K2 L ι, ⊤))) ⟶ K2 L ι := (K2 L ι).isoSpec.inv

def u₀ : ↑(Γ(K2 L ι, ⊤)) :=
  ((χ.val _ (zK L ι ≫ kstr L ι) (ptA L ι (zK L ι)) (ptA_torsion L ι _) : _ˣ) : ↑(Γ(K2 L ι, ⊤)))

theorem isoSpec_inv_appTop (X : Scheme.{0}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  have h : X.isoSpec.hom.appTop ≫ X.isoSpec.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
  rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop] at h
  rw [← Category.id_comp X.isoSpec.inv.appTop, ← (Scheme.ΓSpecIso Γ(X, ⊤)).inv_hom_id, Category.assoc, h,
    Category.comp_id]

theorem appTop_u₀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (y : Spec (CommRingCat.of T) ⟶ K2 L ι) (hy : y ≫ kstr L ι = κ)
    (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x) (hxy : x.1 = y ≫ kfst L ι ≫ pullback.fst f ι) :
    y.appTop (u₀ L ι χ) = (Scheme.ΓSpecIso (CommRingCat.of T)).inv (χ.val T κ x hx : Tˣ) := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ (K2 L ι).isoSpec.hom)
  have hy' : y = Spec.map ψ ≫ zK L ι := by rw [hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hnat := χ.val_natural _ T (zK L ι ≫ kstr L ι) κ ψ.hom
    (by rw [CommRingCat.ofHom_hom, ← Category.assoc, ← hy', hy])
    (ptA L ι (zK L ι)) (ptA_torsion L ι _) x hx
    (by rw [CommRingCat.ofHom_hom, ptA_coe, hxy, hy']; simp only [Category.assoc])
  rw [hnat, Units.coe_map, MonoidHom.coe_coe, hy', Scheme.Hom.comp_appTop, isoSpec_inv_appTop]
  change ((Scheme.ΓSpecIso Γ(K2 L ι, ⊤)).inv ≫ (Spec.map ψ).appTop) (u₀ L ι χ) =
    (ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).inv) (u₀ L ι χ)
  rw [Scheme.ΓSpecIso_inv_naturality]

end Kernel

end UnitOnSquare
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val.UnitOnSquare"

namespace UnitOnSquare

p2m_open "GoodReductionJacobian.RelativeGroupLaw"

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
variable {R : Type} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))

def ptR' {T : Scheme.{0}} (z₁ z₂ : T ⟶ K2 L ι) (hz : z₁ ≫ kstr L ι = z₂ ≫ kstr L ι) :
    SchemeHomOver (z₁ ≫ kstr L ι) (baseChangeStr ι f) :=
  ⟨z₂ ≫ kfst L ι, by rw [Category.assoc, kfst_str, hz]⟩

theorem ptR'_torsion (hc : L.IsCommutative) {T : Scheme.{0}} (z₁ z₂ : T ⟶ K2 L ι) (hz : z₁ ≫ kstr L ι = z₂ ≫ kstr L ι) :
    (L.baseChange ι).IsTorsionPoint (z₁ ≫ kstr L ι) 2 (ptR' L ι z₁ z₂ hz) :=
  isTorsionPoint_congr (L.baseChange ι) hz.symm 2 (P₁ := ptR L ι z₂) rfl (ptR_torsion L ι z₂)

def prodK (hc : L.IsCommutative) {T : Scheme.{0}} (z₁ z₂ : T ⟶ K2 L ι) (hz : z₁ ≫ kstr L ι = z₂ ≫ kstr L ι) :
    T ⟶ K2 L ι :=
  toK L ι ((L.baseChange ι).mul _ (ptR L ι z₁) (ptR' L ι z₁ z₂ hz))
    (isTorsionPoint_two_mul _ (hc.baseChange ι) _ _ _ (ptR_torsion L ι z₁) (ptR'_torsion L ι hc z₁ z₂ hz))

theorem prodK_fst (hc : L.IsCommutative) {T : Scheme.{0}} (z₁ z₂ : T ⟶ K2 L ι) (hz : z₁ ≫ kstr L ι = z₂ ≫ kstr L ι) :
    prodK L ι hc z₁ z₂ hz ≫ kfst L ι = ((L.baseChange ι).mul _ (ptR L ι z₁) (ptR' L ι z₁ z₂ hz)).1 :=
  toK_fst _ _ _ _

theorem prodK_str (hc : L.IsCommutative) {T : Scheme.{0}} (z₁ z₂ : T ⟶ K2 L ι) (hz : z₁ ≫ kstr L ι = z₂ ≫ kstr L ι) :
    prodK L ι hc z₁ z₂ hz ≫ kstr L ι = z₁ ≫ kstr L ι :=
  toK_str _ _ _ _

theorem comp_prodK (hc : L.IsCommutative) {T T' : Scheme.{0}} (w : T' ⟶ T) (z₁ z₂ : T ⟶ K2 L ι)
    (hz : z₁ ≫ kstr L ι = z₂ ≫ kstr L ι) :
    w ≫ prodK L ι hc z₁ z₂ hz = prodK L ι hc (w ≫ z₁) (w ≫ z₂) (by rw [Category.assoc, Category.assoc, hz]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, prodK_fst L ι hc z₁ z₂ hz, prodK_fst L ι hc (w ≫ z₁) (w ≫ z₂)]
    have hn := congrArg Subtype.val ((L.baseChange ι).mul_natural (z₁ ≫ kstr L ι) (w ≫ z₁ ≫ kstr L ι) w rfl
      (ptR L ι z₁) (ptR' L ι z₁ z₂ hz))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at hn
    rw [hn]
    apply mul_coe_congr
    · rw [Category.assoc]
    · simp only [GoodReductionJacobian.schemeHomOverComp_coe, ptR, Category.assoc]
    · simp only [GoodReductionJacobian.schemeHomOverComp_coe, ptR', Category.assoc]
  · rw [Category.assoc, prodK_str L ι hc z₁ z₂ hz, prodK_str L ι hc (w ≫ z₁) (w ≫ z₂), Category.assoc]

theorem appTop_injective_of_isAffine (X : Scheme.{0}) [IsAffine X] {v₁ v₂ : ↑(Γ(X, ⊤))}
    (h : X.isoSpec.inv.appTop v₁ = X.isoSpec.inv.appTop v₂) : v₁ = v₂ := by
  have key : ∀ v : ↑(Γ(X, ⊤)), X.isoSpec.hom.appTop (X.isoSpec.inv.appTop v) = v := by
    intro v
    change (X.isoSpec.inv.appTop ≫ X.isoSpec.hom.appTop) v = v
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
    rfl
  rw [← key v₁, ← key v₂, h]

variable (χ : L.TorsionCharacter 2 ι) [IsAffine (K2 L ι)]

theorem appTop_u₀_univ (hc : L.IsCommutative) (hk : IsAffineHom (kstr L ι)) :
    letI : IsAffineHom (pullback.snd (kstr L ι) (kstr L ι)) := MorphismProperty.pullback_snd _ _ hk
    letI : IsAffine (pullback (kstr L ι) (kstr L ι)) := isAffine_of_isAffineHom (pullback.snd (kstr L ι) (kstr L ι))
    (prodK L ι hc (pullback.fst (kstr L ι) (kstr L ι)) (pullback.snd (kstr L ι) (kstr L ι)) pullback.condition).appTop
        (u₀ L ι χ) =
      (pullback.fst (kstr L ι) (kstr L ι)).appTop (u₀ L ι χ) * (pullback.snd (kstr L ι) (kstr L ι)).appTop (u₀ L ι χ) := by
  haveI : IsAffineHom (pullback.snd (kstr L ι) (kstr L ι)) := MorphismProperty.pullback_snd _ _ hk
  haveI hKK : IsAffine (pullback (kstr L ι) (kstr L ι)) := isAffine_of_isAffineHom (pullback.snd (kstr L ι) (kstr L ι))
  apply appTop_injective_of_isAffine (pullback (kstr L ι) (kstr L ι))
  rw [map_mul]
  simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]

  have hpr : pullback.fst (kstr L ι) (kstr L ι) ≫ kstr L ι = pullback.snd (kstr L ι) (kstr L ι) ≫ kstr L ι :=
    pullback.condition
  have hX₁ := ptA_torsion L ι ((pullback (kstr L ι) (kstr L ι)).isoSpec.inv ≫ pullback.fst (kstr L ι) (kstr L ι))
  have hb₂ : (((pullback (kstr L ι) (kstr L ι)).isoSpec.inv ≫ pullback.snd (kstr L ι) (kstr L ι)) ≫ kstr L ι) ≫ ι =
      (((pullback (kstr L ι) (kstr L ι)).isoSpec.inv ≫ pullback.fst (kstr L ι) (kstr L ι)) ≫ kstr L ι) ≫ ι := by
    simp only [Category.assoc, hpr]
  have hX₂ := isTorsionPoint_congr L hb₂ 2
    (P₁ := ptA L ι ((pullback (kstr L ι) (kstr L ι)).isoSpec.inv ≫ pullback.snd (kstr L ι) (kstr L ι)))
    (P₂ := ⟨(ptA L ι ((pullback (kstr L ι) (kstr L ι)).isoSpec.inv ≫ pullback.snd (kstr L ι) (kstr L ι))).1, by
      rw [← hb₂]; exact (ptA L ι _).2⟩) rfl (ptA_torsion L ι _)
  have hX₁₂ := isTorsionPoint_two_mul L hc _ _ _ hX₁ hX₂
  rw [appTop_u₀ L ι χ _ _ ((pullback (kstr L ι) (kstr L ι)).isoSpec.inv ≫ pullback.fst (kstr L ι) (kstr L ι)) rfl _ hX₁
      (by rw [ptA_coe, Category.assoc]),
    appTop_u₀ L ι χ _ _ ((pullback (kstr L ι) (kstr L ι)).isoSpec.inv ≫ pullback.snd (kstr L ι) (kstr L ι))
      (by simp only [Category.assoc, hpr]) _ hX₂ (by rw [ptA_coe, Category.assoc]),
    appTop_u₀ L ι χ _ _ ((pullback (kstr L ι) (kstr L ι)).isoSpec.inv ≫ prodK L ι hc _ _ hpr)
      (by rw [Category.assoc, prodK_str, Category.assoc]) _ hX₁₂ ?_,
    χ.val_mul _ _ _ _ hX₁ hX₂ hX₁₂, Units.val_mul, map_mul]

  symm
  rw [Category.assoc _ (prodK L ι hc _ _ hpr) _, ← Category.assoc (prodK L ι hc _ _ hpr) (kfst L ι) (pullback.fst f ι),
    prodK_fst L ι hc]
  have h1 := congrArg Subtype.val (L.baseChangePointToBase_mul ι (pullback.fst (kstr L ι) (kstr L ι) ≫ kstr L ι)
    (ptR L ι (pullback.fst (kstr L ι) (kstr L ι))) (ptR' L ι _ _ hpr))
  rw [baseChangePointToBase_coe] at h1
  rw [h1]
  have h2 := congrArg Subtype.val (L.mul_natural ((pullback.fst (kstr L ι) (kstr L ι) ≫ kstr L ι) ≫ ι)
    ((pullback (kstr L ι) (kstr L ι)).isoSpec.inv ≫ (pullback.fst (kstr L ι) (kstr L ι) ≫ kstr L ι) ≫ ι)
    (pullback (kstr L ι) (kstr L ι)).isoSpec.inv rfl
    (baseChangePointToBase ι (ptR L ι (pullback.fst (kstr L ι) (kstr L ι))))
    (baseChangePointToBase ι (ptR' L ι _ _ hpr)))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
  rw [h2]
  apply mul_coe_congr L
  · simp only [Category.assoc]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, baseChangePointToBase_coe, ptR, ptA_coe, Category.assoc]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, baseChangePointToBase_coe, ptR', ptA_coe, Category.assoc]

theorem appTop_u₀_prodK (hc : L.IsCommutative) (hk : IsAffineHom (kstr L ι)) {T : Scheme.{0}} (z₁ z₂ : T ⟶ K2 L ι)
    (hz : z₁ ≫ kstr L ι = z₂ ≫ kstr L ι) :
    (prodK L ι hc z₁ z₂ hz).appTop (u₀ L ι χ) = z₁.appTop (u₀ L ι χ) * z₂.appTop (u₀ L ι χ) := by
  have univ := appTop_u₀_univ L ι χ hc hk
  have hw : pullback.lift z₁ z₂ hz ≫ prodK L ι hc (pullback.fst (kstr L ι) (kstr L ι)) (pullback.snd (kstr L ι) (kstr L ι))
      pullback.condition = prodK L ι hc z₁ z₂ hz := by
    rw [comp_prodK]
    congr 1
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  have e1 : z₁.appTop (u₀ L ι χ) = (pullback.lift z₁ z₂ hz).appTop ((pullback.fst (kstr L ι) (kstr L ι)).appTop (u₀ L ι χ)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_fst]
  have e2 : z₂.appTop (u₀ L ι χ) = (pullback.lift z₁ z₂ hz).appTop ((pullback.snd (kstr L ι) (kstr L ι)).appTop (u₀ L ι χ)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_snd]
  rw [← hw, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, univ, map_mul, e1, e2]

end UnitOnSquare
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val.UnitOnSquare"

namespace UnitOnSquareGeom

p2m_open "GoodReductionJacobian.RelativeGroupLaw"

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem mul_coe_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {P₁ Q₁ : SchemeHomOver t₁ f} {P₂ Q₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht; rw [Subtype.ext hP, Subtype.ext hQ]

theorem mul_inv_cancel {R : Type} [CommRing R] {B : Scheme.{0}} {g : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R g)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t g) : G.mul t x (G.inv t x) = G.one t := by
  have h1 := G.inv_mul_cancel t (G.inv t x)
  calc G.mul t x (G.inv t x)
      = G.mul t (G.one t) (G.mul t x (G.inv t x)) := (G.one_mul t _).symm
    _ = G.mul t (G.mul t (G.inv t (G.inv t x)) (G.inv t x)) (G.mul t x (G.inv t x)) := by rw [h1]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.mul t (G.inv t x) x) (G.inv t x)) := by
        rw [G.mul_assoc, ← G.mul_assoc t (G.inv t x) x]
    _ = G.one t := by rw [G.inv_mul_cancel, G.one_mul, h1]

theorem mul_left_cancel {R : Type} [CommRing R] {B : Scheme.{0}} {g : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R g)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (a y z : SchemeHomOver t g) (h : G.mul t a y = G.mul t a z) : y = z := by
  have := congrArg (G.mul t (G.inv t a)) h
  rwa [← G.mul_assoc, ← G.mul_assoc, G.inv_mul_cancel, G.one_mul, G.one_mul] at this

noncomputable def fstPt {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) :
    SchemeHomOver (pullback.fst f σ ≫ f) f := ⟨pullback.fst f σ, rfl⟩

noncomputable def sndPt {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver σ f) :
    SchemeHomOver (pullback.fst f σ ≫ f) f :=
  ⟨pullback.snd f σ ≫ x.1, by rw [Category.assoc, x.2, pullback.condition]⟩

theorem translate_fst {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver σ f) :
    (L.baseChange σ).translate (baseChangePointOfBase σ (t' := 𝟙 (Spec (CommRingCat.of T))) ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫
        pullback.fst f σ =
      (L.mul (pullback.fst f σ ≫ f) (fstPt σ) (sndPt σ x)).1 := by
  unfold RelativeGroupLaw.translate
  rw [baseChange_mul, baseChangePointOfBase_coe, pullback.lift_fst]
  apply mul_coe_congr L
  · exact pullback.condition.symm
  · rw [baseChangePointToBase_coe]; exact Category.id_comp _
  · rw [baseChangePointToBase_coe, Category.assoc, baseChangePointOfBase_coe, pullback.lift_fst]; rfl

theorem baseChangeSnd_fst {T T' : Type} [CommRing T] [CommRing T']
    {s : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)} {s' : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver s' s) : baseChangeSnd f ψ ≫ pullback.fst f s = pullback.fst f s' := by
  unfold baseChangeSnd; rw [pullback.lift_fst, Category.comp_id]

theorem baseChangeSnd_snd {T T' : Type} [CommRing T] [CommRing T']
    {s : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)} {s' : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver s' s) : baseChangeSnd f ψ ≫ pullback.snd f s = pullback.snd f s' ≫ ψ.1 := by
  unfold baseChangeSnd; rw [pullback.lift_snd]

theorem comp_diff_eq_const
    {R : Type} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    {P : Scheme.{0}} (p₁ p₂ : P ⟶ pullback f ι) (hp₂ : p₂ ≫ pullback.snd f ι = p₁ ≫ pullback.snd f ι)
    (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver (κ ≫ ι) f)
    (s : pullback f (κ ≫ ι) ⟶ P)
    (hs₁ : s ≫ p₁ = RelPicard.baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι))
    (hs₂ : s ≫ p₂ = (L.baseChange (κ ≫ ι)).translate
          (RelativeGroupLaw.baseChangePointOfBase (κ ≫ ι) (t' := 𝟙 (Spec (CommRingCat.of T)))
            ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫
        RelPicard.baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)) :
    s ≫ ((L.baseChange ι).mul (p₁ ≫ pullback.snd f ι)
          ((L.baseChange ι).inv (p₁ ≫ pullback.snd f ι) ⟨p₁, rfl⟩) ⟨p₂, hp₂⟩).1 =
      pullback.snd f (κ ≫ ι) ≫ (RelativeGroupLaw.baseChangePointOfBase ι (t' := κ) x).1 := by

  set G := L.baseChange ι with hG
  set tP : P ⟶ Spec (CommRingCat.of R) := p₁ ≫ pullback.snd f ι with htP
  set P₁ : SchemeHomOver tP (pullback.snd f ι) := ⟨p₁, rfl⟩ with hP₁
  set P₂ : SchemeHomOver tP (pullback.snd f ι) := ⟨p₂, hp₂⟩ with hP₂
  set D := G.mul tP (G.inv tP P₁) P₂ with hD
  have g_snd : RelPicard.baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι) ≫ pullback.snd f ι = pullback.snd f (κ ≫ ι) ≫ κ :=
    baseChangeSnd_snd _
  have g_fst : RelPicard.baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι) ≫ pullback.fst f ι = pullback.fst f (κ ≫ ι) :=
    baseChangeSnd_fst _
  have hst : s ≫ tP = pullback.snd f (κ ≫ ι) ≫ κ := by
    rw [htP, ← Category.assoc, hs₁, g_snd]

  let X₀ : SchemeHomOver (s ≫ tP) (pullback.snd f ι) :=
    ⟨pullback.snd f (κ ≫ ι) ≫ (RelativeGroupLaw.baseChangePointOfBase ι (t' := κ) x).1, by
      rw [Category.assoc, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd, hst]⟩

  have h1 : G.mul tP P₁ D = P₂ := by
    rw [hD, ← G.mul_assoc, mul_inv_cancel G, G.one_mul]

  have h2 : G.mul (s ≫ tP) (schemeHomOverComp s rfl P₁) (schemeHomOverComp s rfl D) = schemeHomOverComp s rfl P₂ := by
    rw [← G.mul_natural tP (s ≫ tP) s rfl, h1]

  have h3 : G.mul (s ≫ tP) (schemeHomOverComp s rfl P₁) X₀ = schemeHomOverComp s rfl P₂ := by
    apply Subtype.ext
    apply pullback.hom_ext
    ·
      rw [hG, baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst,
        GoodReductionJacobian.schemeHomOverComp_coe]
      have rhs : (s ≫ P₂.1) ≫ pullback.fst f ι =
          (L.mul (pullback.fst f (κ ≫ ι) ≫ f) (fstPt (κ ≫ ι)) (sndPt (κ ≫ ι) x)).1 := by
        rw [show P₂.1 = p₂ from rfl, hs₂, Category.assoc, g_fst]
        exact translate_fst L (κ ≫ ι) x
      rw [rhs]
      apply mul_coe_congr L
      · rw [hst, Category.assoc]; exact pullback.condition.symm
      · rw [baseChangePointToBase_coe, GoodReductionJacobian.schemeHomOverComp_coe, show P₁.1 = p₁ from rfl, hs₁, g_fst]
        rfl
      · show (pullback.snd f (κ ≫ ι) ≫ (RelativeGroupLaw.baseChangePointOfBase ι (t' := κ) x).1) ≫ pullback.fst f ι = _
        rw [Category.assoc, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
        rfl
    ·
      rw [(G.mul (s ≫ tP) _ X₀).2, (schemeHomOverComp s rfl P₂).2]

  have h4 : schemeHomOverComp s rfl D = X₀ := mul_left_cancel G (s ≫ tP) _ _ _ (h2.trans h3.symm)
  have h5 := congrArg Subtype.val h4
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h5
  exact h5

end UnitOnSquareGeom
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val.UnitOnSquare"

namespace UnitOnSquare

p2m_open "GoodReductionJacobian.RelativeGroupLaw"

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
variable {R : Type} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))

theorem comp_diff {P T : Scheme.{0}} (p₁ p₂ : P ⟶ pullback f ι) (hp₂ : p₂ ≫ pullback.snd f ι = p₁ ≫ pullback.snd f ι)
    (w : T ⟶ P) :
    w ≫ ((L.baseChange ι).mul (p₁ ≫ pullback.snd f ι) ((L.baseChange ι).inv (p₁ ≫ pullback.snd f ι) ⟨p₁, rfl⟩) ⟨p₂, hp₂⟩).1 =
      ((L.baseChange ι).mul ((w ≫ p₁) ≫ pullback.snd f ι)
        ((L.baseChange ι).inv ((w ≫ p₁) ≫ pullback.snd f ι) ⟨w ≫ p₁, rfl⟩)
        ⟨w ≫ p₂, by rw [Category.assoc, hp₂, Category.assoc]⟩).1 := by
  have hn := congrArg Subtype.val ((L.baseChange ι).mul_natural (p₁ ≫ pullback.snd f ι) (w ≫ p₁ ≫ pullback.snd f ι) w rfl
    ((L.baseChange ι).inv (p₁ ≫ pullback.snd f ι) ⟨p₁, rfl⟩) ⟨p₂, hp₂⟩)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at hn
  rw [hn, inv_natural]
  apply mul_coe_congr
  · rw [Category.assoc]
  · apply inv_coe_congr
    · rw [Category.assoc]
    · rfl
  · rfl

end UnitOnSquare
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val.UnitOnSquare"

open UnitOnSquare _root_.GoodReductionJacobian.RelativeGroupLaw in
theorem solution
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (hker : IsFinite (L.schemeKerStr 2) ∧ Flat (L.schemeKerStr 2) ∧ LocallyOfFinitePresentation (L.schemeKerStr 2))
    (h2fl : IsAffineHom (L.schemeNsmul 2) ∧ Flat (L.schemeNsmul 2) ∧ Surjective (L.schemeNsmul 2))
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (χ : L.TorsionCharacter 2 ι)
    {P P₃ : Scheme} (p₁ p₂ : P ⟶ pullback f ι)
    (hp : p₁ ≫ (L.baseChange ι).schemeNsmul 2 = p₂ ≫ (L.baseChange ι).schemeNsmul 2)
    (δ : pullback f ι ⟶ P) (hδ₁ : δ ≫ p₁ = 𝟙 _) (hδ₂ : δ ≫ p₂ = 𝟙 _)
    (a b : P₃ ⟶ P) (hab : a ≫ p₂ = b ≫ p₁) (c : P₃ ⟶ P) (hca : c ≫ p₁ = a ≫ p₁) (hcb : c ≫ p₂ = b ≫ p₂) :
    ∃ u : Γ(P, ⊤), δ.appTop u = 1 ∧ a.appTop u * b.appTop u = c.appTop u ∧
      ∀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
        (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x)
        (s : pullback f (κ ≫ ι) ⟶ P)
        (hs₁ : s ≫ p₁ = RelPicard.baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι))
        (hs₂ : s ≫ p₂ = (L.baseChange (κ ≫ ι)).translate
              (RelativeGroupLaw.baseChangePointOfBase (κ ≫ ι) (t' := 𝟙 (Spec (CommRingCat.of T)))
                ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫
            RelPicard.baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)),
        s.appTop u =
          (pullback.snd f (κ ≫ ι)).appTop ((Scheme.ΓSpecIso (CommRingCat.of T)).inv ((χ.val T κ x hx : Tˣ) : T)) := by
  classical
  obtain ⟨h2aff, -, -⟩ := h2fl

  have hk2 : IsAffineHom ((L.baseChange ι).schemeNsmul 2) :=
    (isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange ι L 2).2 _ inferInstance h2aff
  have hk : IsAffineHom (kstr L ι) := MorphismProperty.pullback_snd _ _ hk2
  haveI : IsAffine (K2 L ι) := isAffine_of_isAffineHom (kstr L ι)

  have hq : (L.baseChange ι).schemeNsmul 2 ≫ pullback.snd f ι = pullback.snd f ι := (L.baseChange ι).schemeNsmul_over 2
  have hp₂ : p₂ ≫ pullback.snd f ι = p₁ ≫ pullback.snd f ι := by
    calc p₂ ≫ pullback.snd f ι = (p₂ ≫ (L.baseChange ι).schemeNsmul 2) ≫ pullback.snd f ι := by rw [Category.assoc, hq]
      _ = (p₁ ≫ (L.baseChange ι).schemeNsmul 2) ≫ pullback.snd f ι := by rw [hp]
      _ = p₁ ≫ pullback.snd f ι := by rw [Category.assoc, hq]
  let tP : P ⟶ Spec (CommRingCat.of R) := p₁ ≫ pullback.snd f ι
  let Q₁ : SchemeHomOver tP (baseChangeStr ι f) := ⟨p₁, rfl⟩
  let Q₂ : SchemeHomOver tP (baseChangeStr ι f) := ⟨p₂, hp₂⟩
  let d : SchemeHomOver tP (baseChangeStr ι f) := (L.baseChange ι).mul tP ((L.baseChange ι).inv tP Q₁) Q₂
  have hsq : (L.baseChange ι).nsmul tP 2 Q₁ = (L.baseChange ι).nsmul tP 2 Q₂ := by
    apply Subtype.ext
    rw [nsmul_coe_eq_comp_schemeNsmul, nsmul_coe_eq_comp_schemeNsmul]
    exact hp
  have hd : (L.baseChange ι).IsTorsionPoint tP 2 d := diff_sq_eq_one _ (hc.baseChange ι) tP Q₁ Q₂ hsq
  let dK : P ⟶ K2 L ι := toK L ι d hd
  have hdK₁ : dK ≫ kfst L ι = d.1 := toK_fst _ _ _ _
  have hdK₂ : dK ≫ kstr L ι = tP := toK_str _ _ _ _
  refine ⟨dK.appTop (u₀ L ι χ), ?_, ?_, ?_⟩
  ·

    have he₀ : (L.baseChange ι).IsTorsionPoint (𝟙 (Spec (CommRingCat.of R))) 2 ((L.baseChange ι).one _) :=
      isTorsionPoint_unit _ _ 2
    let eK : Spec (CommRingCat.of R) ⟶ K2 L ι := toK L ι ((L.baseChange ι).one (𝟙 _)) he₀
    have hδ : δ ≫ dK = pullback.snd f ι ≫ eK := by
      apply pullback.hom_ext
      · rw [Category.assoc, hdK₁, Category.assoc, toK_fst, ← one_coe, comp_diff L ι p₁ p₂ hp₂ δ]
        have h1 : (δ ≫ p₁) ≫ pullback.snd f ι = pullback.snd f ι := by rw [hδ₁, Category.id_comp]
        rw [← (L.baseChange ι).inv_mul_cancel (pullback.snd f ι) ⟨𝟙 _, Category.id_comp _⟩]
        apply mul_coe_congr
        · exact h1
        · exact inv_coe_congr _ h1 hδ₁
        · exact hδ₂
      · rw [Category.assoc, hdK₂, Category.assoc, toK_str, Category.comp_id]
        show δ ≫ p₁ ≫ pullback.snd f ι = pullback.snd f ι
        rw [← Category.assoc, hδ₁, Category.id_comp]

    have hE : L.IsTorsionPoint (𝟙 _ ≫ ι) 2 (L.one (𝟙 _ ≫ ι)) := isTorsionPoint_unit _ _ 2
    have heval := appTop_u₀ L ι χ R (𝟙 _) eK (toK_str _ _ _ _) (L.one _) hE (by
      rw [← Category.assoc, toK_fst, ← baseChangePointToBase_coe, baseChangePointToBase_one])
    rw [val_one] at heval
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hδ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, heval,
      Units.val_one, map_one, map_one]
  ·
    have hab' : (a ≫ dK) ≫ kstr L ι = (b ≫ dK) ≫ kstr L ι := by
      rw [Category.assoc, hdK₂, Category.assoc, hdK₂]
      show a ≫ p₁ ≫ pullback.snd f ι = b ≫ p₁ ≫ pullback.snd f ι
      rw [← hp₂, ← Category.assoc, hab, Category.assoc, hp₂]
    have hc' : c ≫ dK = prodK L ι hc (a ≫ dK) (b ≫ dK) hab' := by
      apply pullback.hom_ext
      · rw [prodK_fst, Category.assoc, hdK₁, comp_diff L ι p₁ p₂ hp₂ c]

        have eP : (ptR L ι (a ≫ dK)).1 = ((L.baseChange ι).mul ((a ≫ p₁) ≫ pullback.snd f ι)
            ((L.baseChange ι).inv ((a ≫ p₁) ≫ pullback.snd f ι) ⟨a ≫ p₁, rfl⟩)
            ⟨a ≫ p₂, by rw [Category.assoc, hp₂, Category.assoc]⟩).1 := by
          simp only [ptR, Category.assoc, hdK₁]; rw [comp_diff L ι p₁ p₂ hp₂ a]
        have eQ : (ptR' L ι (a ≫ dK) (b ≫ dK) hab').1 = ((L.baseChange ι).mul ((b ≫ p₁) ≫ pullback.snd f ι)
            ((L.baseChange ι).inv ((b ≫ p₁) ≫ pullback.snd f ι) ⟨b ≫ p₁, rfl⟩)
            ⟨b ≫ p₂, by rw [Category.assoc, hp₂, Category.assoc]⟩).1 := by
          simp only [ptR', Category.assoc, hdK₁]; rw [comp_diff L ι p₁ p₂ hp₂ b]

        have hbase_b : (b ≫ p₁) ≫ pullback.snd f ι = (a ≫ p₁) ≫ pullback.snd f ι := by
          rw [← hab, Category.assoc, hp₂, Category.assoc]
        have hbase_c : (c ≫ p₁) ≫ pullback.snd f ι = (a ≫ p₁) ≫ pullback.snd f ι := by rw [hca]
        have hbase_d : (a ≫ dK) ≫ kstr L ι = (a ≫ p₁) ≫ pullback.snd f ι := by rw [Category.assoc, hdK₂, Category.assoc]
        let A₁ : SchemeHomOver ((a ≫ p₁) ≫ pullback.snd f ι) (baseChangeStr ι f) := ⟨a ≫ p₁, rfl⟩
        let A₂ : SchemeHomOver ((a ≫ p₁) ≫ pullback.snd f ι) (baseChangeStr ι f) :=
          ⟨a ≫ p₂, by rw [Category.assoc, hp₂, Category.assoc]⟩
        let B₂ : SchemeHomOver ((a ≫ p₁) ≫ pullback.snd f ι) (baseChangeStr ι f) :=
          ⟨b ≫ p₂, by rw [Category.assoc, hp₂, ← Category.assoc, ← hab, Category.assoc, hp₂, ← Category.assoc]⟩
        have key := congrArg Subtype.val (diff_mul_diff (L.baseChange ι) ((a ≫ p₁) ≫ pullback.snd f ι) A₁ A₂ B₂)
        calc _ = ((L.baseChange ι).mul _ ((L.baseChange ι).inv _ A₁) B₂).1 :=
              mul_coe_congr _ hbase_c (inv_coe_congr _ hbase_c hca) hcb
          _ = _ := key.symm
          _ = _ := by
            apply mul_coe_congr _ hbase_d.symm
            · exact eP.symm
            · rw [eQ]; exact mul_coe_congr _ hbase_b.symm (inv_coe_congr _ hbase_b.symm hab) rfl
      · rw [prodK_str, Category.assoc, hdK₂, Category.assoc, hdK₂]
        show c ≫ p₁ ≫ pullback.snd f ι = a ≫ p₁ ≫ pullback.snd f ι
        rw [← Category.assoc, hca, Category.assoc]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hc', appTop_u₀_prodK L ι χ hc hk]
  ·
    intro T _ κ x hx s hs₁ hs₂

    let XR : SchemeHomOver κ (baseChangeStr ι f) := baseChangePointOfBase ι (t' := κ) x
    have hXR : (L.baseChange ι).IsTorsionPoint κ 2 XR := by
      rw [isTorsionPoint_def, baseChange_nsmul, baseChangePointToBase_ofBase, baseChange_one]
      exact congrArg _ hx
    let xK : Spec (CommRingCat.of T) ⟶ K2 L ι := toK L ι XR hXR
    have hsx : s ≫ dK = pullback.snd f (κ ≫ ι) ≫ xK := by
      apply pullback.hom_ext
      · rw [Category.assoc, hdK₁, Category.assoc, toK_fst]
        exact UnitOnSquareGeom.comp_diff_eq_const L ι p₁ p₂ hp₂ T κ x s hs₁ hs₂
      · rw [Category.assoc, hdK₂, Category.assoc, toK_str]
        show s ≫ p₁ ≫ pullback.snd f ι = pullback.snd f (κ ≫ ι) ≫ κ
        rw [← Category.assoc, hs₁]
        exact pullback.lift_snd _ _ _
    have heval := appTop_u₀ L ι χ T κ xK (toK_str _ _ _ _) x hx
      (by rw [← Category.assoc, toK_fst, baseChangePointOfBase_coe, pullback.lift_fst])
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hsx, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, heval]

end
end S_AlgebraicGeometry_Polarisation_exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val (solution)
