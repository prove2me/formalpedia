-- Prove2me | solution 1 for AlgebraicGeometry.SplitTorus.exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/926e0e60-5d82-562c-801b-a072a3ca2f19

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus

namespace SplitTorusLawEngine

noncomputable def homRingHom {T : Scheme.{u}} {B : CommRingCat.{u}} (φ : T ⟶ Spec B) :
    B ⟶ Γ(T, ⊤) :=
  (Scheme.ΓSpecIso B).inv ≫ φ.appTop

theorem toSpecΓ_specMap_homRingHom {T : Scheme.{u}} {B : CommRingCat.{u}} (φ : T ⟶ Spec B) :
    T.toSpecΓ ≫ Spec.map (homRingHom φ) = φ := by
  unfold homRingHom
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

theorem homRingHom_toSpecΓ_specMap {T : Scheme.{u}} {B : CommRingCat.{u}} (ψ : B ⟶ Γ(T, ⊤)) :
    homRingHom (T.toSpecΓ ≫ Spec.map ψ) = ψ := by
  unfold homRingHom
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem homRingHom_comp {T' T : Scheme.{u}} {B : CommRingCat.{u}} (ψ : T' ⟶ T) (φ : T ⟶ Spec B) :
    homRingHom (ψ ≫ φ) = homRingHom φ ≫ ψ.appTop := by
  unfold homRingHom
  rw [Scheme.Hom.comp_appTop, Category.assoc]

theorem homRingHom_specMap {B C : CommRingCat.{u}} (f : B ⟶ C) :
    homRingHom (Spec.map f) = f ≫ (Scheme.ΓSpecIso C).inv := by
  unfold homRingHom
  rw [Scheme.ΓSpecIso_inv_naturality]

theorem homRingHom_injective {T : Scheme.{u}} {B : CommRingCat.{u}} :
    Function.Injective (homRingHom (T := T) (B := B)) := by
  intro φ ψ h
  rw [← toSpecΓ_specMap_homRingHom φ, ← toSpecΓ_specMap_homRingHom ψ, h]

end SplitTorusLawEngine

namespace SplitTorusLawEngine

variable {S : Type u} [CommRing S] {d : ℕ}

section CharHom
variable {M : Type u} [CommMonoid M]

noncomputable def charHom (u : Fin d → Mˣ) : Multiplicative (Fin d → ℤ) →* Mˣ where
  toFun v := ∏ i, u i ^ (Multiplicative.toAdd v i)
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem charHom_apply (u : Fin d → Mˣ) (v : Multiplicative (Fin d → ℤ)) :
    charHom u v = ∏ i, u i ^ (Multiplicative.toAdd v i) := rfl

theorem charHom_single (u : Fin d → Mˣ) (i : Fin d) :
    charHom u (Multiplicative.ofAdd (Pi.single i 1)) = u i := by
  rw [charHom_apply, toAdd_ofAdd, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem monoidHom_eq_charHom (φ : Multiplicative (Fin d → ℤ) →* Mˣ) :
    φ = charHom (fun i => φ (Multiplicative.ofAdd (Pi.single i 1))) := by
  ext i : 4
  change Additive.toMul (Additive.ofMul (φ (Multiplicative.ofAdd (Pi.single i 1)))) =
    Additive.toMul (Additive.ofMul
      (charHom (fun i => φ (Multiplicative.ofAdd (Pi.single i 1))) (Multiplicative.ofAdd (Pi.single i 1))))
  rw [charHom_single]

end CharHom

noncomputable def genUnit (S : Type u) [CommRing S] (d : ℕ) (i : Fin d) : (torusCoord S d)ˣ :=
  (AddMonoidAlgebra.of S (Fin d → ℤ)).toHomUnits (Multiplicative.ofAdd (Pi.single i 1))

@[scoped simp] theorem val_genUnit (i : Fin d) :
    (genUnit S d i : torusCoord S d) = AddMonoidAlgebra.single (Pi.single i 1) 1 := rfl

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

noncomputable def ptRingHom (x : SchemeHomOver t (torusStr S d)) : torusCoord S d →+* Γ(T, ⊤) :=
  (homRingHom x.1).hom

noncomputable def baseRingHom : S →+* Γ(T, ⊤) := (homRingHom t).hom

theorem ptRingHom_comp_algebraMap (x : SchemeHomOver t (torusStr S d)) :
    (ptRingHom t x).comp (algebraMap S (torusCoord S d)) = baseRingHom t := by
  have h := homRingHom_comp x.1 (torusStr S d)
  rw [x.2, homRingHom_specMap, Category.assoc] at h

  change (CommRingCat.ofHom (algebraMap S (torusCoord S d)) ≫ homRingHom x.1).hom = (homRingHom t).hom
  rw [h]; rfl

theorem ptRingHom_single_zero (x : SchemeHomOver t (torusStr S d)) (b : S) :
    ptRingHom t x (AddMonoidAlgebra.single 0 b) = baseRingHom t b := by
  rw [← ptRingHom_comp_algebraMap t x]; rfl

noncomputable def ptUnits (x : SchemeHomOver t (torusStr S d)) : Fin d → Γ(T, ⊤)ˣ :=
  fun i => Units.map (ptRingHom t x).toMonoidHom (genUnit S d i)

@[scoped simp] theorem val_ptUnits (x : SchemeHomOver t (torusStr S d)) (i : Fin d) :
    (ptUnits t x i : Γ(T, ⊤)) = ptRingHom t x (AddMonoidAlgebra.single (Pi.single i 1) 1) := rfl

noncomputable def ringHomOfUnits (u : Fin d → Γ(T, ⊤)ˣ) : torusCoord S d →+* Γ(T, ⊤) :=
  AddMonoidAlgebra.liftNCRingHom (baseRingHom t) ((Units.coeHom _).comp (charHom u))
    (fun _ _ => Commute.all _ _)

theorem ringHomOfUnits_single (u : Fin d → Γ(T, ⊤)ˣ) (a : Fin d → ℤ) (b : S) :
    ringHomOfUnits t u (AddMonoidAlgebra.single a b) =
      baseRingHom t b * (charHom u (Multiplicative.ofAdd a) : Γ(T, ⊤)) := by
  unfold ringHomOfUnits
  rw [AddMonoidAlgebra.liftNCRingHom]
  dsimp
  rw [AddMonoidAlgebra.liftNC_single]
  rfl

theorem ringHomOfUnits_comp_algebraMap (u : Fin d → Γ(T, ⊤)ˣ) :
    (ringHomOfUnits t u).comp (algebraMap S (torusCoord S d)) = baseRingHom t := by
  ext b
  change ringHomOfUnits t u (AddMonoidAlgebra.single 0 b) = _
  rw [ringHomOfUnits_single, ofAdd_zero, map_one, Units.val_one, mul_one]

noncomputable def ptOfUnits (u : Fin d → Γ(T, ⊤)ˣ) : SchemeHomOver t (torusStr S d) :=
  ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (ringHomOfUnits t u)), by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ringHomOfUnits_comp_algebraMap]
    exact toSpecΓ_specMap_homRingHom t⟩

theorem ptRingHom_ptOfUnits (u : Fin d → Γ(T, ⊤)ˣ) :
    ptRingHom t (ptOfUnits t u) = ringHomOfUnits t u := by
  unfold ptRingHom ptOfUnits
  dsimp only
  rw [homRingHom_toSpecΓ_specMap]
  rfl

theorem ptUnits_ptOfUnits (u : Fin d → Γ(T, ⊤)ˣ) : ptUnits t (ptOfUnits t u) = u := by
  funext i
  ext
  rw [val_ptUnits, ptRingHom_ptOfUnits, ringHomOfUnits_single, map_one, one_mul, charHom_single]

theorem ptRingHom_eq_ringHomOfUnits (x : SchemeHomOver t (torusStr S d)) :
    ptRingHom t x = ringHomOfUnits t (ptUnits t x) := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun a => ?_)
  · rw [ptRingHom_single_zero, ringHomOfUnits_single, ofAdd_zero, map_one, Units.val_one, mul_one]
  · rw [ringHomOfUnits_single, map_one, one_mul]

    let φ : Multiplicative (Fin d → ℤ) →* Γ(T, ⊤)ˣ :=
      (Units.map (ptRingHom t x).toMonoidHom).comp (AddMonoidAlgebra.of S (Fin d → ℤ)).toHomUnits
    have hφ : ∀ v, (φ v : Γ(T, ⊤)) = ptRingHom t x (AddMonoidAlgebra.single (Multiplicative.toAdd v) 1) :=
      fun v => rfl
    have hu : (fun i => φ (Multiplicative.ofAdd (Pi.single i 1))) = ptUnits t x := by
      funext i; ext; rw [hφ]; rfl
    rw [← hu, ← monoidHom_eq_charHom φ, hφ, toAdd_ofAdd]

theorem ptOfUnits_ptUnits (x : SchemeHomOver t (torusStr S d)) : ptOfUnits t (ptUnits t x) = x := by
  apply Subtype.ext
  apply homRingHom_injective
  apply CommRingCat.hom_ext
  change ptRingHom t (ptOfUnits t (ptUnits t x)) = ptRingHom t x
  rw [ptRingHom_ptOfUnits, ← ptRingHom_eq_ringHomOfUnits]

noncomputable def ptEquiv : SchemeHomOver t (torusStr S d) ≃ (Fin d → Γ(T, ⊤)ˣ) where
  toFun := ptUnits t
  invFun := ptOfUnits t
  left_inv := ptOfUnits_ptUnits t
  right_inv := ptUnits_ptOfUnits t

theorem ptUnits_injective : Function.Injective (ptUnits (d := d) t) := (ptEquiv t).injective

theorem ptUnits_comp {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t (torusStr S d)) (i : Fin d) :
    ptUnits t' (schemeHomOverComp ψ hψ x) i = Units.map ψ.appTop.hom.toMonoidHom (ptUnits t x i) := by
  ext
  change ptRingHom t' (schemeHomOverComp ψ hψ x) _ = ψ.appTop.hom (ptRingHom t x _)
  unfold ptRingHom
  rw [schemeHomOverComp_coe, homRingHom_comp]
  rfl

end SplitTorusLawEngine
p2m_reactivate "P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq.SplitTorusLawEngine"

namespace SplitTorusLawEngine

variable (S : Type u) [CommRing S] (d : ℕ)

noncomputable def torusLaw : RelativeGroupLaw S (torusStr S d) where
  mul t x y := ptOfUnits t (ptUnits t x * ptUnits t y)
  one t := ptOfUnits t 1
  inv t x := ptOfUnits t (ptUnits t x)⁻¹
  mul_assoc t x y z := by simp only [ptUnits_ptOfUnits, mul_assoc]
  one_mul t x := by simp only [ptUnits_ptOfUnits, one_mul, ptOfUnits_ptUnits]
  mul_one t x := by simp only [ptUnits_ptOfUnits, mul_one, ptOfUnits_ptUnits]
  inv_mul_cancel t x := by simp only [ptUnits_ptOfUnits, inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply ptUnits_injective t'
    funext i
    rw [ptUnits_comp, ptUnits_ptOfUnits, ptUnits_ptOfUnits, Pi.mul_apply, Pi.mul_apply, map_mul,
      ptUnits_comp, ptUnits_comp]

variable {S d}

theorem ptUnits_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (x y : SchemeHomOver t (torusStr S d)) :
    ptUnits t ((torusLaw S d).mul t x y) = ptUnits t x * ptUnits t y :=
  ptUnits_ptOfUnits t _

theorem ptUnits_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    ptUnits t ((torusLaw S d).one t) = 1 :=
  ptUnits_ptOfUnits t _

theorem isCommutative_torusLaw : (torusLaw S d).IsCommutative := by
  intro T t x y
  change ptOfUnits t (ptUnits t x * ptUnits t y) = ptOfUnits t (ptUnits t y * ptUnits t x)
  rw [mul_comm]

theorem ptUnits_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (n : ℕ) (x : SchemeHomOver t (torusStr S d)) :
    ptUnits t ((torusLaw S d).nsmul t n x) = ptUnits t x ^ n := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, ptUnits_one, pow_zero]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ptUnits_mul, ih, pow_succ]

section Conv
variable (S' : Type u) [CommRing S'] [Algebra S S']

theorem convMul_ofConv_single (χ χ' : WithConv (torusCoord S d →ₐ[S] S')) (v : Fin d → ℤ) :
    (χ * χ').ofConv (AddMonoidAlgebra.single v 1) =
      χ.ofConv (AddMonoidAlgebra.single v 1) * χ'.ofConv (AddMonoidAlgebra.single v 1) := by
  rw [AlgHom.convMul_apply]
  erw [AddMonoidAlgebra.comul_single]
  simp

theorem ptUnits_torusPt (χ : torusCoord S d →ₐ[S] S') (i : Fin d) :
    (ptUnits _ (torusPt S S' d χ) i : Γ(Spec (CommRingCat.of S'), ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of S')).inv (χ (AddMonoidAlgebra.single (Pi.single i 1) 1)) := by
  rw [val_ptUnits]
  unfold ptRingHom torusPt
  dsimp only
  rw [homRingHom_specMap]
  rfl

theorem torusPt_convMul (χ χ' : WithConv (torusCoord S d →ₐ[S] S')) :
    torusPt S S' d (χ * χ').ofConv =
      (torusLaw S d).mul _ (torusPt S S' d χ.ofConv) (torusPt S S' d χ'.ofConv) := by
  apply ptUnits_injective
  funext i
  ext
  rw [ptUnits_mul, Pi.mul_apply, Units.val_mul, ptUnits_torusPt, ptUnits_torusPt, ptUnits_torusPt,
    convMul_ofConv_single, map_mul]

theorem torusPt_convOne :
    torusPt S S' d (1 : WithConv (torusCoord S d →ₐ[S] S')).ofConv = (torusLaw S d).one _ := by
  apply ptUnits_injective
  funext i
  ext
  rw [ptUnits_one, ptUnits_torusPt, Pi.one_apply, Units.val_one]
  erw [AlgHom.convOne_apply]
  erw [AddMonoidAlgebra.counit_single]
  simp

end Conv
p2m_reactivate "P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq.SplitTorusLawEngine"

noncomputable abbrev powRingHom (S : Type u) [CommRing S] (d n : ℕ) : torusCoord S d →+* torusCoord S d :=
  AddMonoidAlgebra.mapDomainRingHom S (n • AddMonoidHom.id (Fin d → ℤ))

theorem powRingHom_single (n : ℕ) (a : Fin d → ℤ) (b : S) :
    powRingHom S d n (AddMonoidAlgebra.single a b) = AddMonoidAlgebra.single (n • a) b := by
  simp [AddMonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]

theorem schemeNsmul_torusLaw (n : ℕ) :
    (torusLaw S d).schemeNsmul n = Spec.map (CommRingCat.ofHom (powRingHom S d n)) := by

  apply homRingHom_injective
  apply CommRingCat.hom_ext
  change ptRingHom (torusStr S d) ((torusLaw S d).nsmul (torusStr S d) n RelativeGroupLaw.idPoint) =
    (homRingHom (Spec.map (CommRingCat.ofHom (powRingHom S d n)))).hom
  rw [ptRingHom_eq_ringHomOfUnits, ptUnits_nsmul, homRingHom_specMap]
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun a => ?_)
  · rw [ringHomOfUnits_single, ofAdd_zero, map_one, Units.val_one, mul_one]
    change _ = (Scheme.ΓSpecIso (CommRingCat.of (torusCoord S d))).inv (powRingHom S d n (AddMonoidAlgebra.single 0 b))
    rw [powRingHom_single, smul_zero, ← ptRingHom_single_zero (torusStr S d) RelativeGroupLaw.idPoint]
    unfold ptRingHom homRingHom
    simp
  · rw [ringHomOfUnits_single, map_one, one_mul]
    change _ = (Scheme.ΓSpecIso (CommRingCat.of (torusCoord S d))).inv (powRingHom S d n (AddMonoidAlgebra.single a 1))
    rw [powRingHom_single]

    let ι : torusCoord S d →+* Γ(torusScheme S d, ⊤) := ptRingHom (torusStr S d) RelativeGroupLaw.idPoint
    have hι : ι = (Scheme.ΓSpecIso (CommRingCat.of (torusCoord S d))).inv.hom := by
      change (homRingHom (𝟙 _)).hom = _
      unfold homRingHom
      simp
    let φ : Multiplicative (Fin d → ℤ) →* Γ(torusScheme S d, ⊤)ˣ :=
      (Units.map ι.toMonoidHom).comp (AddMonoidAlgebra.of S (Fin d → ℤ)).toHomUnits
    have hφu : (fun i => φ (Multiplicative.ofAdd (Pi.single i 1))) = ptUnits (torusStr S d) RelativeGroupLaw.idPoint := by
      funext i; rfl
    have hpow : ptUnits (torusStr S d) RelativeGroupLaw.idPoint ^ n =
        fun i => (φ ^ n) (Multiplicative.ofAdd (Pi.single i 1)) := by
      funext i; rw [Pi.pow_apply, MonoidHom.pow_apply, ← hφu]
    rw [hpow, ← monoidHom_eq_charHom (φ ^ n), MonoidHom.pow_apply, ← map_pow, ← ofAdd_nsmul]
    change (ι (AddMonoidAlgebra.single (Multiplicative.toAdd (Multiplicative.ofAdd (n • a))) 1)) = _
    rw [toAdd_ofAdd, hι]

end SplitTorusLawEngine
p2m_reactivate "P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq.SplitTorusLawEngine"

namespace SplitTorusLawEngine

variable {S : Type u} [CommRing S] {d : ℕ}

scoped instance addMonoidFG_pi : AddMonoid.FG (Fin d → ℤ) := by
  rw [← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]; infer_instance

theorem powRingHom_comp_algebraMap (n : ℕ) :
    (powRingHom S d n).comp (algebraMap S (torusCoord S d)) = algebraMap S (torusCoord S d) := by
  refine RingHom.ext fun b => ?_
  change powRingHom S d n (AddMonoidAlgebra.single 0 b) = AddMonoidAlgebra.single 0 b
  rw [powRingHom_single, smul_zero]

theorem finiteType_powRingHom (n : ℕ) : (powRingHom S d n).FiniteType := by
  refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap S (torusCoord S d)) ?_
  rw [powRingHom_comp_algebraMap]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

theorem isIntegral_powRingHom (n : ℕ) (hn : 0 < n) : (powRingHom S d n).IsIntegral := by
  intro x
  induction x using AddMonoidAlgebra.induction_on with
  | of a =>
    refine ⟨Polynomial.X ^ n - Polynomial.C (AddMonoidAlgebra.single a 1),
      Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, powRingHom_single]
    change AddMonoidAlgebra.single a (1 : S) ^ n - AddMonoidAlgebra.single (n • a) 1 = 0
    rw [AddMonoidAlgebra.single_pow, one_pow, sub_self]
  | add x y hx hy => exact hx.add _ hy
  | smul r x hx =>
    rw [Algebra.smul_def]
    refine RingHom.IsIntegralElem.mul _ ?_ hx
    have : algebraMap S (torusCoord S d) r = powRingHom S d n (algebraMap S (torusCoord S d) r) := by
      rw [← RingHom.comp_apply, powRingHom_comp_algebraMap]
    rw [this]
    exact RingHom.isIntegralElem_map _

theorem finite_powRingHom (n : ℕ) (hn : 0 < n) : (powRingHom S d n).Finite :=
  (isIntegral_powRingHom n hn).to_finite (finiteType_powRingHom n)

theorem isFinite_schemeNsmul_torusLaw (n : ℕ) (hn : 0 < n) :
    IsFinite ((torusLaw S d).schemeNsmul n) := by
  rw [schemeNsmul_torusLaw, IsFinite.SpecMap_iff]
  exact finite_powRingHom n hn

end SplitTorusLawEngine
p2m_reactivate "P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq.SplitTorusLawEngine"

namespace SplitTorusLawEngine

variable (S : Type u) [CommRing S] (d n : ℕ)

def PowTarget (S : Type u) [CommRing S] (d _n : ℕ) : Type u := torusCoord S d

noncomputable scoped instance : CommRing (PowTarget S d n) := inferInstanceAs (CommRing (torusCoord S d))

noncomputable scoped instance PowTarget.instAlgebra : Algebra (torusCoord S d) (PowTarget S d n) :=
  (powRingHom S d n).toAlgebra

p2m_reactivate "P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq.SplitTorusLawEngine P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq.SplitTorusLawEngine.PowTarget"

noncomputable def PowTarget.of : torusCoord S d ≃+* PowTarget S d n := RingEquiv.refl _

variable {S d n}

theorem PowTarget.algebraMap_apply (a : torusCoord S d) :
    algebraMap (torusCoord S d) (PowTarget S d n) a = PowTarget.of S d n (powRingHom S d n a) := rfl

theorem PowTarget.smul_def (a : torusCoord S d) (b : PowTarget S d n) :
    a • b = PowTarget.of S d n (powRingHom S d n a) * b := rfl

section basis
variable (hn : 0 < n)

def modPart (hn : 0 < n) (v : Fin d → ℤ) : Fin d → Fin n :=
  fun i => ⟨(v i % n).toNat, by
    have h1 : v i % n < n := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
    have h0 : 0 ≤ v i % n := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
    exact (Int.toNat_lt h0).mpr h1⟩

def divPart (n : ℕ) (v : Fin d → ℤ) : Fin d → ℤ := fun i => v i / n

def resVec (r : Fin d → Fin n) : Fin d → ℤ := fun i => (r i : ℕ)

theorem nsmul_divPart_add_resVec_modPart (v : Fin d → ℤ) :
    n • divPart n v + resVec (modPart hn v) = v := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, divPart, resVec, modPart]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn.ne'))]
  exact Int.mul_ediv_add_emod _ _

theorem modPart_nsmul_add_resVec (w : Fin d → ℤ) (r : Fin d → Fin n) :
    modPart hn (n • w + resVec r) = r := by
  funext i
  apply Fin.ext
  simp only [modPart]
  rw [Pi.add_apply, Pi.smul_apply, resVec, nsmul_eq_mul, add_comm, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (r i).isLt), Int.toNat_natCast]

include hn in
theorem divPart_nsmul_add_resVec (w : Fin d → ℤ) (r : Fin d → Fin n) :
    divPart n (n • w + resVec r) = w := by
  funext i
  simp only [divPart]
  rw [Pi.add_apply, Pi.smul_apply, resVec, nsmul_eq_mul, add_comm,
    Int.add_mul_ediv_left _ _ (by exact_mod_cast hn.ne'),
    Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast (r i).isLt), zero_add]

noncomputable def resBasisVec (r : Fin d → Fin n) : PowTarget S d n :=
  PowTarget.of S d n (AddMonoidAlgebra.single (resVec r) 1)

noncomputable def resComb : ((Fin d → Fin n) →₀ torusCoord S d) →ₗ[torusCoord S d] PowTarget S d n :=
  Finsupp.linearCombination (torusCoord S d) (resBasisVec (S := S) (d := d) (n := n))

theorem resComb_single_single (r : Fin d → Fin n) (w : Fin d → ℤ) (s : S) :
    resComb (Finsupp.single r (AddMonoidAlgebra.single w s)) =
      PowTarget.of S d n (AddMonoidAlgebra.single (n • w + resVec r) s) := by
  rw [resComb, Finsupp.linearCombination_single, PowTarget.smul_def, resBasisVec, ← map_mul,
    powRingHom_single, AddMonoidAlgebra.single_mul_single, mul_one]

noncomputable def resDecomp : PowTarget S d n →+ ((Fin d → Fin n) →₀ torusCoord S d) :=
  (Finsupp.liftAddHom fun v : Fin d → ℤ =>
    ((Finsupp.singleAddHom (modPart hn v)).comp
      (AddMonoidAlgebra.singleAddHom (divPart n v) : S →+ torusCoord S d))).comp
    (AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom.comp (PowTarget.of S d n).symm.toAddMonoidHom)

theorem resDecomp_of_single (v : Fin d → ℤ) (s : S) :
    resDecomp hn (PowTarget.of S d n (AddMonoidAlgebra.single v s)) =
      Finsupp.single (modPart hn v) (AddMonoidAlgebra.single (divPart n v) s) := by
  change (Finsupp.liftAddHom _) ((PowTarget.of S d n).symm (PowTarget.of S d n (AddMonoidAlgebra.single v s))).coeff = _
  rw [RingEquiv.symm_apply_apply, AddMonoidAlgebra.coeff_single]
  erw [Finsupp.liftAddHom_apply_single]
  rfl

theorem resDecomp_resComb (l : (Fin d → Fin n) →₀ torusCoord S d) :
    resDecomp hn (resComb l) = l := by

  suffices h : (resDecomp hn).comp (resComb (S := S) (d := d) (n := n)).toAddMonoidHom =
      AddMonoidHom.id _ from DFunLike.congr_fun h l
  refine Finsupp.addHom_ext' fun r => AddMonoidAlgebra.addHom_ext' fun w => AddMonoidHom.ext fun s => ?_
  change resDecomp hn (resComb (Finsupp.single r (AddMonoidAlgebra.single w s))) =
    Finsupp.single r (AddMonoidAlgebra.single w s)
  rw [resComb_single_single, resDecomp_of_single, modPart_nsmul_add_resVec hn,
    divPart_nsmul_add_resVec hn]

theorem resComb_resDecomp (b : PowTarget S d n) : resComb (resDecomp hn b) = b := by
  suffices h : (resComb (S := S) (d := d) (n := n)).toAddMonoidHom.comp
      ((resDecomp hn).comp (PowTarget.of S d n).toAddMonoidHom) = (PowTarget.of S d n).toAddMonoidHom by
    have := DFunLike.congr_fun h ((PowTarget.of S d n).symm b)
    simpa using this
  refine AddMonoidAlgebra.addHom_ext' fun v => AddMonoidHom.ext fun s => ?_
  change resComb (resDecomp hn (PowTarget.of S d n (AddMonoidAlgebra.single v s))) =
    PowTarget.of S d n (AddMonoidAlgebra.single v s)
  rw [resDecomp_of_single, resComb_single_single, nsmul_divPart_add_resVec_modPart hn]

noncomputable def resBasis : Module.Basis (Fin d → Fin n) (torusCoord S d) (PowTarget S d n) :=
  Module.Basis.ofRepr
    (LinearEquiv.ofBijective (resComb (S := S) (d := d) (n := n))
      ⟨fun x y h => by simpa [resDecomp_resComb hn] using congrArg (resDecomp hn) h,
       fun b => ⟨resDecomp hn b, resComb_resDecomp hn b⟩⟩).symm

include hn in
theorem free_powTarget : Module.Free (torusCoord S d) (PowTarget S d n) :=
  Module.Free.of_basis (resBasis hn)

include hn in
theorem flat_powRingHom : (powRingHom S d n).Flat := by
  haveI := free_powTarget (S := S) (d := d) hn
  exact (inferInstance : Module.Flat (torusCoord S d) (PowTarget S d n))

end basis
p2m_reactivate "P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq.SplitTorusLawEngine P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq.SplitTorusLawEngine.PowTarget"

theorem flat_schemeNsmul_torusLaw (n : ℕ) (hn : 0 < n) : Flat ((torusLaw S d).schemeNsmul n) := by
  rw [schemeNsmul_torusLaw, HasRingHomProperty.Spec_iff (P := @Flat)]
  exact flat_powRingHom hn

end SplitTorusLawEngine
p2m_reactivate "P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq.SplitTorusLawEngine P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq.SplitTorusLawEngine.PowTarget"

open SplitTorusLawEngine in
theorem solution
    (S : Type u) [CommRing S] (d : ℕ) :
    ∃ L : RelativeGroupLaw S (torusStr S d),
      L.IsCommutative ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)),
        ∃ e : SchemeHomOver t (torusStr S d) ≃ (Fin d → Γ(T, ⊤)ˣ),
          (∀ (x : SchemeHomOver t (torusStr S d)) (i : Fin d),
            (e x i : Γ(T, ⊤)) =
              ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord S d))).inv ≫ x.1.appTop).hom
                (AddMonoidAlgebra.single (Pi.single i 1) 1)) ∧
          (∀ x y : SchemeHomOver t (torusStr S d), e (L.mul t x y) = e x * e y)) ∧
      (∀ (S' : Type u) [CommRing S'] [Algebra S S'] (χ χ' : WithConv (torusCoord S d →ₐ[S] S')),
        torusPt S S' d (χ * χ').ofConv =
          L.mul _ (torusPt S S' d χ.ofConv) (torusPt S S' d χ'.ofConv)) ∧
      (∀ (S' : Type u) [CommRing S'] [Algebra S S'],
        torusPt S S' d (1 : WithConv (torusCoord S d →ₐ[S] S')).ofConv = L.one _) ∧
      (∀ n : ℕ, L.schemeNsmul n =
        Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.mapDomainRingHom S (n • AddMonoidHom.id (Fin d → ℤ))))) ∧
      (∀ n : ℕ, 0 < n → IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n)) := by
  refine ⟨torusLaw S d, isCommutative_torusLaw, fun t => ?_, fun S' _ _ χ χ' => torusPt_convMul S' χ χ',
    fun S' _ _ => torusPt_convOne S', schemeNsmul_torusLaw,
    fun n hn => ⟨isFinite_schemeNsmul_torusLaw n hn, flat_schemeNsmul_torusLaw n hn⟩⟩
  exact ⟨ptEquiv t, fun x i => rfl, fun x y => ptUnits_mul t x y⟩

end S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq
end P2MW
export P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq (solution)
