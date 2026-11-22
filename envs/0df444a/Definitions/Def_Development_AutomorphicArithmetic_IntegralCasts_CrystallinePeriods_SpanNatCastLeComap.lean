-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:45:57.996228+00:00
-- url     : https://prove2.me/theorems/4076adfb-2229-414e-aaa3-6d962bd16e93
-- title:
--   Span Nat Cast Le Comap
-- statement:
--   Definitions and structural lemmas for Span Nat Cast Le Comap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
namespace Reformulated.AutPerF
universe u v w
section Adic
variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
theorem pow_le_comap_pow {I : Ideal A} {J : Ideal B} {f : A →+* B} (h : I ≤ J.comap f) (n : ℕ) :
    I ^ n ≤ (J ^ n).comap f :=
  (Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n)
def adicMap (I : Ideal A) (J : Ideal B) (f : A →+* B) (h : I ≤ J.comap f) :
    AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) f (pow_le_comap_pow h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n))
    (fun {m n} hle => by
      ext x
      induction x using AdicCompletion.induction_on with
      | h x =>
        simp only [RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk,
          Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
        rw [← Ideal.quotientMap_mk (H := pow_le_comap_pow h m),
          ← Ideal.quotientMap_mk (H := pow_le_comap_pow h m), AdicCompletion.Ideal.mk_eq_mk I hle])
theorem evalₐ_adicMap (I : Ideal A) (J : Ideal B) (f : A →+* B) (h : I ≤ J.comap f) (n : ℕ)
    (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (adicMap I J f h x) =
      Ideal.quotientMap (J ^ n) f (pow_le_comap_pow h n) (AdicCompletion.evalₐ I n x) := by
  unfold adicMap
  rw [AdicCompletion.evalₐ_liftRingHom]
  · rfl
  · intro m n hle
    ext x
    induction x using AdicCompletion.induction_on with
    | h x =>
      simp only [RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk,
        Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
      rw [← Ideal.quotientMap_mk (H := pow_le_comap_pow h m),
        ← Ideal.quotientMap_mk (H := pow_le_comap_pow h m), AdicCompletion.Ideal.mk_eq_mk I hle]
@[simp] theorem adicMap_algebraMap (I : Ideal A) (J : Ideal B) (f : A →+* B) (h : I ≤ J.comap f)
    (a : A) : adicMap I J f h (algebraMap A _ a) = algebraMap B _ (f a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_adicMap, AlgHom.commutes, AlgHom.commutes]
  rfl
theorem span_natCast_le_comap (p : ℕ) (f : A →+* B) :
    span {(p : A)} ≤ (span {(p : B)}).comap f := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  simp [Ideal.mem_comap]
end Adic
variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)]
variable (S : Type v) [CommRing S] [Fact ¬IsUnit (p : S)]
variable (U : Type w) [CommRing U] [Fact ¬IsUnit (p : U)]
abbrev Tilt : Type u := PreTilt R p
abbrev Ainf : Type u := WittVector p (Tilt p R)
abbrev AinfInv : Type u := Localization.Away (p : Ainf p R)
variable {R S U}
namespace Tilt
def map (f : R →+* S) : Tilt p R →+* Tilt p S :=
  Perfection.map p (Ideal.quotientMap (span {(p : S)}) f (span_natCast_le_comap p f))
variable {p}
theorem ext {x y : Tilt p R} (h : ∀ n, PreTilt.coeff n x = PreTilt.coeff n y) : x = y :=
  Perfection.ext h
theorem coeff_map (f : R →+* S) (x : Tilt p R) (n : ℕ) :
    PreTilt.coeff n (map p f x) =
      Ideal.quotientMap (span {(p : S)}) f (span_natCast_le_comap p f) (PreTilt.coeff n x) := rfl
@[simp] theorem map_id (x : Tilt p R) : map p (RingHom.id R) x = x := by
  refine ext fun n => ?_
  rw [coeff_map]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  rw [← ha]; rfl
variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
end Tilt
namespace Ainf
abbrev teich : Tilt p R →* Ainf p R := WittVector.teichmuller p
variable (R) in

def frob : Ainf p R →+* Ainf p R := WittVector.frobenius
def map (f : R →+* S) : Ainf p R →+* Ainf p S := WittVector.map (Tilt.map p f)
variable (R) in

def ofPadicInt : ℤ_[p] →+* Ainf p R :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (Tilt p R))).comp (WittVector.equiv p).symm.toRingHom
instance : Algebra ℤ_[p] (Ainf p R) := (ofPadicInt p R).toAlgebra
variable {p}
@[simp] theorem map_id (x : Ainf p R) : map p (RingHom.id R) x = x := by
  ext n; simp [map]
@[simp] theorem map_teich (f : R →+* S) (x : Tilt p R) :
    map p f (teich p x) = teich p (Tilt.map p f x) := WittVector.map_teichmuller p _ x
theorem frob_eq_map : frob p R = WittVector.map (frobenius (Tilt p R) p) :=
  WittVector.frobenius_eq_map_frobenius p
@[simp] theorem frob_teich (x : Tilt p R) : frob p R (teich p x) = teich p x ^ p := by
  rw [frob_eq_map, ← map_pow]; exact WittVector.map_teichmuller p _ x
@[simp] theorem map_algebraMap (f : R →+* S) (a : ℤ_[p]) :
    map p f (algebraMap ℤ_[p] _ a) = algebraMap ℤ_[p] _ a := by
  ext n
  change Tilt.map p f (ZMod.castHom (dvd_refl p) (Tilt p R) _) = ZMod.castHom (dvd_refl p) _ _
  exact RingHom.congr_fun (Subsingleton.elim ((Tilt.map p f).comp (ZMod.castHom (dvd_refl p) _))
    (ZMod.castHom (dvd_refl p) (Tilt p S))) _
@[simp] theorem frob_algebraMap (a : ℤ_[p]) :
    frob p R (algebraMap ℤ_[p] _ a) = algebraMap ℤ_[p] _ a := by
  rw [frob_eq_map]
  ext n
  change frobenius _ p (ZMod.castHom (dvd_refl p) (Tilt p R) _) = ZMod.castHom (dvd_refl p) _ _
  exact RingHom.congr_fun (Subsingleton.elim ((frobenius _ p).comp (ZMod.castHom (dvd_refl p) _))
    (ZMod.castHom (dvd_refl p) (Tilt p R))) _
variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
variable (p R) in

def theta : Ainf p R →+* R := WittVector.fontaineTheta R p
@[simp] theorem theta_teich (x : Tilt p R) : theta p R (teich p x) = PreTilt.untilt x :=
  WittVector.fontaineTheta_teichmuller x
end Ainf
namespace AinfInv
theorem isUnit_p : IsUnit (p : AinfInv p R) := by
  simpa using IsLocalization.Away.algebraMap_isUnit (S := AinfInv p R) (p : Ainf p R)
def extend (f : Ainf p R →+* Ainf p S) : AinfInv p R →+* AinfInv p S :=
  IsLocalization.Away.lift (p : Ainf p R) (g := (algebraMap (Ainf p S) (AinfInv p S)).comp f)
    (by simpa using isUnit_p p)
variable {p} in
@[simp] theorem extend_algebraMap (f : Ainf p R →+* Ainf p S) (x : Ainf p R) :
    extend p f (algebraMap _ _ x) = algebraMap _ _ (f x) :=
  IsLocalization.Away.lift_eq _ _ x
variable {p} in
theorem hom_ext {B : Type*} [CommRing B] {f g : AinfInv p R →+* B}
    (h : ∀ x : Ainf p R, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : Ainf p R)) (RingHom.ext h)
variable (R) in

def frob : AinfInv p R →+* AinfInv p R := extend p (Ainf.frob p R)
def map (f : R →+* S) : AinfInv p R →+* AinfInv p S := extend p (Ainf.map p f)
end AinfInv
def padicLift {B : Type*} [CommRing B] (f : ℤ_[p] →+* B) (h : IsUnit (p : B)) : ℚ_[p] →+* B :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (g := f) (by
    rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
    change IsUnit (f x)
    rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast]
    exact ((Units.isUnit _).map f).mul (h.pow _))
@[simp] theorem padicLift_algebraMap {B : Type*} [CommRing B] (f : ℤ_[p] →+* B)
    (h : IsUnit (p : B)) (a : ℤ_[p]) : padicLift p f h (algebraMap _ _ a) = f a :=
  IsLocalization.lift_eq _ a
namespace AinfInv
instance : Algebra ℚ_[p] (AinfInv p R) :=
  (padicLift p (algebraMap ℤ_[p] (AinfInv p R)) (isUnit_p p)).toAlgebra
instance : Algebra ℚ (AinfInv p R) :=
  ((algebraMap ℚ_[p] (AinfInv p R)).comp (algebraMap ℚ ℚ_[p])).toAlgebra
instance : IsScalarTower ℤ_[p] ℚ_[p] (AinfInv p R) :=
  IsScalarTower.of_algebraMap_eq fun a => (padicLift_algebraMap p _ _ a).symm
variable {p}
@[simp] theorem map_algebraMap (f : R →+* S) (x : Ainf p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Ainf.map p f x) := extend_algebraMap _ x
@[simp] theorem frob_algebraMap (x : Ainf p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (Ainf.frob p R x) := extend_algebraMap _ x
@[simp] theorem map_id (x : AinfInv p R) : map p (RingHom.id R) x = x :=
  RingHom.congr_fun (hom_ext (f := map p (RingHom.id R)) (g := RingHom.id _) (by simp)) x
variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
variable (p R) in

def theta : AinfInv p R →+* Localization.Away (p : R) := fontaineThetaInvertP R p
@[simp] theorem theta_algebraMap (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = algebraMap R _ (Ainf.theta p R x) := by
  unfold theta fontaineThetaInvertP Localization.awayLift
  rw [IsLocalization.Away.lift_eq]
  rfl
end AinfInv
def awayMap {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    Localization.Away (p : R) →+* Localization.Away (p : S) :=
  IsLocalization.Away.lift (p : R) (g := (algebraMap S (Localization.Away (p : S))).comp f)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : S)) (p : S))
end Reformulated.AutPerF


