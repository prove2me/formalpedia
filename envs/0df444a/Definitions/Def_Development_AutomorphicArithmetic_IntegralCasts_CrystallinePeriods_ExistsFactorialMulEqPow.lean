-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T09:45:06.38257+00:00
-- url     : https://prove2.me/theorems/09ff4b9b-17e3-5b23-a339-8b84f62743bb
-- title:
--   Exists Factorial Mul Eq Pow
-- statement:
--   Definitions and structural lemmas for Exists Factorial Mul Eq Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/ExistsFactorialMulEqPow.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Theorems.Thm_Reformulated_AutPerF_AcrisZero_factorial_mul_gamma
import Theorems.Thm_Reformulated_AutPerF_Acris_ext_eval
import Theorems.Thm_Reformulated_AutPerF_Acris_hom_ext
import Theorems.Thm_Reformulated_AutPerF_Acris_logTeich_pow
import Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_map
import Theorems.Thm_Reformulated_AutPerF_Ainf_p_dvd_frob_sub_pow
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_map
import Theorems.Thm_Reformulated_AutPerF_Bcris_isUnit_logTeich
import Theorems.Thm_Reformulated_AutPerF_Bcris_isUnit_p
import Theorems.Thm_Reformulated_AutPerF_Bcris_logTeich_one
import Theorems.Thm_Reformulated_AutPerF_Bcris_logTeich_pow
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_ext_eval
import Theorems.Thm_Reformulated_AutPerF_Bst_hom_ext
import Theorems.Thm_Reformulated_AutPerF_Bst_logFlat_twist
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_Tilt_untilt_map
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
import Theorems.Thm_Reformulated_AutPerF_padic_hom_ext
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bcris.logTeich_one
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap


set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
namespace Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]
theorem exists_factorial_mul_eq_pow (n : ℕ) : ∃ a : ℤ_[p], (n ! : ℤ_[p]) * a = p ^ n := by
  have hp : p.Prime := Fact.out
  obtain ⟨v, m, hm, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) p hp.ne_one
  have hv : v ≤ n := by
    have h1 : v ≤ padicValNat p n ! :=
      (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).1 ⟨m, h⟩
    exact h1.trans (padicValNat_factorial_le p n)
  have hu : IsUnit (m : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.2 hm
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hv
  refine ⟨w * p ^ d, ?_⟩
  rw [h]
  push_cast
  linear_combination (p : ℤ_[p]) ^ (v + d) * hw
def tateModule.map (f : R →+* S) : tateModule p R →* tateModule p S where
  toFun η := ⟨Tilt.map p f η.1, by
    change PreTilt.untilt _ = 1
    rw [Tilt.untilt_map, show PreTilt.untilt η.1 = 1 from η.2, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
def PFlat.map (f : R →+* S) (ϖ : PFlat p R) : PFlat p S :=
  ⟨Tilt.map p f ϖ.1, by rw [Tilt.untilt_map, ϖ.2, map_natCast]⟩
variable {p}
@[simp] theorem tateModule.coe_map (f : R →+* S) (η : tateModule p R) :
    (tateModule.map p f η).1 = Tilt.map p f η.1 := rfl
@[simp] theorem tateModule.map_id (η : tateModule p R) : tateModule.map p (RingHom.id R) η = η :=
  Subtype.ext (Tilt.map_id _)
@[simp] theorem PFlat.coe_map (f : R →+* S) (ϖ : PFlat p R) :
    (PFlat.map p f ϖ).1 = Tilt.map p f ϖ.1 := rfl
@[simp] theorem PFlat.map_id (ϖ : PFlat p R) : PFlat.map p (RingHom.id R) ϖ = ϖ :=
  Subtype.ext (Tilt.map_id _)
theorem PFlat.map_twist (f : R →+* S) (η : tateModule p R) (ϖ : PFlat p R) :
    PFlat.map p f (ϖ.twist η) = (PFlat.map p f ϖ).twist (tateModule.map p f η) :=
  Subtype.ext (map_mul (Tilt.map p f) _ _)
theorem IsPrimitive.map {ε : tateModule p R} (h : IsPrimitive ε) (f : R →+* S)
    (hf : Function.Injective f) : IsPrimitive (tateModule.map p f ε) := by
  unfold IsPrimitive at h ⊢
  rw [tateModule.coe_map, ← RingHom.map_frobeniusEquiv_symm, Tilt.untilt_map]
  exact fun h' => h (hf (by rw [h', map_one]))
omit [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S] in
theorem AinfInv.map_gamma (f : AinfInv p R →+* AinfInv p S) (n : ℕ) (x : AinfInv p R) :
    f (AinfInv.gamma n x) = AinfInv.gamma n (f x) := by
  simp [AinfInv.gamma, map_rat_smul]
omit [IsAdicComplete (span {(p : R)}) R] in
theorem AinfInv.factorial_mul_gamma (n : ℕ) (x : AinfInv p R) :
    (n ! : AinfInv p R) * AinfInv.gamma n x = x ^ n := by
  rw [AinfInv.gamma, Algebra.smul_def, ← map_natCast (algebraMap ℚ (AinfInv p R)), ← mul_assoc,
    ← map_mul, mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one, one_mul]
omit [IsAdicComplete (span {(p : R)}) R] in
theorem AinfInv.eq_gamma {n : ℕ} {x y : AinfInv p R} (h : (n ! : AinfInv p R) * y = x ^ n) :
    AinfInv.gamma n x = y := by
  have hu : IsUnit (n ! : AinfInv p R) := by
    rw [← map_natCast (algebraMap ℚ (AinfInv p R))]
    exact (IsUnit.mk0 _ (by exact_mod_cast Nat.factorial_ne_zero _)).map _
  exact hu.mul_left_cancel (by rw [AinfInv.factorial_mul_gamma, h])
namespace AcrisZero
theorem extend_mem (ψ : Ainf p R →+* Ainf p S)
    (h : ∀ n x, Ainf.theta p R x = 0 → AinfInv.gamma n (algebraMap _ _ (ψ x)) ∈ acrisZero p S)
    {y : AinfInv p R} (hy : y ∈ acrisZero p R) : AinfInv.extend p ψ y ∈ acrisZero p S := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rw [AinfInv.map_gamma, AinfInv.extend_algebraMap]
    exact h n x hx
  | algebraMap r => rw [AinfInv.extend_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
def extend (ψ : Ainf p R →+* Ainf p S)
    (h : ∀ n x, Ainf.theta p R x = 0 → AinfInv.gamma n (algebraMap _ _ (ψ x)) ∈ acrisZero p S) :
    AcrisZero p R →+* AcrisZero p S where
  toFun y := ⟨AinfInv.extend p ψ y.1, extend_mem ψ h y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
theorem gamma_map_mem (f : R →+* S) (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    AinfInv.gamma n (algebraMap _ _ (Ainf.map p f x)) ∈ acrisZero p S :=
  (gamma n (Ainf.map p f x) (by rw [Ainf.theta_map, hx, map_zero])).2
theorem p_dvd_frob (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (p : AcrisZero p R) ∣ algebraMap (Ainf p R) (AcrisZero p R) (Ainf.frob p R x) := by
  obtain ⟨y, hy⟩ := Ainf.p_dvd_frob_sub_pow x
  rw [eq_add_of_sub_eq hy, map_add, map_mul, map_natCast, map_pow, ← factorial_mul_gamma p x hx]
  refine dvd_add (dvd_mul_right _ _) (Dvd.dvd.mul_right ?_ _)
  exact Nat.cast_dvd_cast (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl)
theorem gamma_p_mul_mem (n : ℕ) (z : AcrisZero p R) :
    AinfInv.gamma n ((p : AinfInv p R) * z.1) ∈ acrisZero p R := by
  obtain ⟨a, ha⟩ := exists_factorial_mul_eq_pow p n
  have ha' := congrArg ((algebraMap (Ainf p R) (AinfInv p R)).comp (algebraMap ℤ_[p] _)) ha
  rw [map_mul, map_pow, map_natCast, map_natCast, RingHom.comp_apply] at ha'
  rw [AinfInv.eq_gamma (y := algebraMap (Ainf p R) _ (algebraMap ℤ_[p] _ a) * z.1 ^ n)
    (by rw [← mul_assoc, ha', mul_pow])]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem z.2 _)
theorem gamma_frob_mem (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    AinfInv.gamma n (algebraMap _ _ (Ainf.frob p R x)) ∈ acrisZero p R := by
  obtain ⟨z, hz⟩ := p_dvd_frob x hx
  have hz' := congrArg Subtype.val hz
  simp only [MulMemClass.coe_mul, SubringClass.coe_natCast, Subalgebra.coe_algebraMap] at hz'
  rw [hz']
  exact gamma_p_mul_mem n z
variable (p) in

def map (f : R →+* S) : AcrisZero p R →+* AcrisZero p S := extend (Ainf.map p f) (gamma_map_mem f)
variable (p R) in

def frob : AcrisZero p R →+* AcrisZero p R := extend (Ainf.frob p R) gamma_frob_mem
@[simp] theorem coe_map (f : R →+* S) (x : AcrisZero p R) :
    (map p f x : AinfInv p S) = AinfInv.map p f x := rfl
@[simp] theorem coe_frob (x : AcrisZero p R) : (frob p R x : AinfInv p R) = AinfInv.frob p R x := rfl
@[simp] theorem map_algebraMap (f : R →+* S) (x : Ainf p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Ainf.map p f x) :=
  Subtype.ext (AinfInv.map_algebraMap f x)
@[simp] theorem frob_algebraMap (x : Ainf p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (Ainf.frob p R x) :=
  Subtype.ext (AinfInv.frob_algebraMap x)
@[simp] theorem map_id (x : AcrisZero p R) : map p (RingHom.id R) x = x :=
  Subtype.ext (AinfInv.map_id _)
end AcrisZero
namespace Acris
def extend (g : AcrisZero p R →+* AcrisZero p S) : Acris p R →+* Acris p S :=
  adicMap _ _ g (span_natCast_le_comap p g)
@[simp] theorem extend_algebraMap (g : AcrisZero p R →+* AcrisZero p S) (a : AcrisZero p R) :
    extend g (algebraMap _ _ a) = algebraMap _ _ (g a) :=
  adicMap_algebraMap _ _ g _ a
theorem eval_extend (g : AcrisZero p R →+* AcrisZero p S) (n : ℕ) (x : Acris p R) :
    eval p S n (extend g x) =
      Ideal.quotientMap _ g (pow_le_comap_pow (span_natCast_le_comap p g) n) (eval p R n x) :=
  evalₐ_adicMap _ _ g _ n x
theorem extend_log (g : AcrisZero p R →+* AcrisZero p S) (u : Ainf p R) (v : Ainf p S)
    (hu : Ainf.theta p R u = 1) (hv : Ainf.theta p S v = 1)
    (h : g (algebraMap _ _ u) = algebraMap _ _ v) : extend g (log u hu) = log v hv := by
  refine ext_eval fun n => ?_
  obtain ⟨l, hl, hl'⟩ := exists_quot u hu n
  rw [eval_extend, hl', Ideal.quotientMap_mk, eval_log_of_mul_eq v hv n (g l)]
  rw [← h, ← map_natCast g, ← map_pow, ← map_mul, hl, map_sub, map_pow, map_one]
variable (p) in

def map (f : R →+* S) : Acris p R →+* Acris p S := extend (AcrisZero.map p f)
variable (p R) in

def frob : Acris p R →+* Acris p R := extend (AcrisZero.frob p R)
@[simp] theorem map_algebraMap_zero (f : R →+* S) (x : AcrisZero p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (AcrisZero.map p f x) := extend_algebraMap _ x
@[simp] theorem frob_algebraMap_zero (x : AcrisZero p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (AcrisZero.frob p R x) := extend_algebraMap _ x
@[simp] theorem map_algebraMap (f : R →+* S) (x : Ainf p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Ainf.map p f x) := by
  rw [IsScalarTower.algebraMap_apply (Ainf p R) (AcrisZero p R) (Acris p R), map_algebraMap_zero,
    AcrisZero.map_algebraMap, ← IsScalarTower.algebraMap_apply]
@[simp] theorem frob_algebraMap (x : Ainf p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (Ainf.frob p R x) := by
  rw [IsScalarTower.algebraMap_apply (Ainf p R) (AcrisZero p R) (Acris p R), frob_algebraMap_zero,
    AcrisZero.frob_algebraMap, ← IsScalarTower.algebraMap_apply]
@[simp] theorem map_algebraMap_padicInt (f : R →+* S) (a : ℤ_[p]) :
    map p f (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] (Ainf p R) (Acris p R), map_algebraMap,
    Ainf.map_algebraMap, ← IsScalarTower.algebraMap_apply]
@[simp] theorem frob_algebraMap_padicInt (a : ℤ_[p]) :
    frob p R (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] (Ainf p R) (Acris p R), frob_algebraMap,
    Ainf.frob_algebraMap]
@[simp] theorem map_id (x : Acris p R) : map p (RingHom.id R) x = x :=
  RingHom.congr_fun (hom_ext (f := map p (RingHom.id R)) (g := RingHom.id _) (by simp)) x
@[simp] theorem map_logTeich (f : R →+* S) (η : tateModule p R) :
    map p f (logTeich η) = logTeich (tateModule.map p f η) :=
  extend_log _ _ _ _ _ (by rw [AcrisZero.map_algebraMap, Ainf.map_teich]; rfl)
@[simp] theorem frob_logTeich (η : tateModule p R) : frob p R (logTeich η) = p * logTeich η := by
  rw [← logTeich_pow]
  exact extend_log _ _ _ _ _ (by rw [AcrisZero.frob_algebraMap, Ainf.frob_teich, ← map_pow]; rfl)
end Acris
namespace BcrisPlus
def lift {B : Type*} [CommRing B] (g : Acris p R →+* B) (h : IsUnit (p : B)) :
    BcrisPlus p R →+* B :=
  IsLocalization.Away.lift (p : Acris p R) (g := g) (by simpa using h)
@[simp] theorem lift_algebraMap {B : Type*} [CommRing B] (g : Acris p R →+* B)
    (h : IsUnit (p : B)) (x : Acris p R) : lift g h (algebraMap _ _ x) = g x :=
  IsLocalization.Away.lift_eq _ _ x
theorem hom_ext {B : Type*} [CommRing B] {f g : BcrisPlus p R →+* B}
    (h : ∀ x : Acris p R, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : Acris p R)) (RingHom.ext h)
theorem algebraMap_padicInt (a : ℤ_[p]) :
    algebraMap ℚ_[p] (BcrisPlus p R) (algebraMap ℤ_[p] ℚ_[p] a) =
      algebraMap (Acris p R) _ (algebraMap ℤ_[p] _ a) :=
  padicLift_algebraMap p _ _ a
variable (p) in

def map (f : R →+* S) : BcrisPlus p R →+* BcrisPlus p S :=
  lift ((algebraMap (Acris p S) _).comp (Acris.map p f)) (isUnit_p p S)
variable (p R) in

def frob : BcrisPlus p R →+* BcrisPlus p R :=
  lift ((algebraMap (Acris p R) _).comp (Acris.frob p R)) (isUnit_p p R)
@[simp] theorem map_algebraMap (f : R →+* S) (x : Acris p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Acris.map p f x) := lift_algebraMap _ _ x
@[simp] theorem frob_algebraMap (x : Acris p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (Acris.frob p R x) := lift_algebraMap _ _ x
@[simp] theorem map_algebraMap_padic (f : R →+* S) (a : ℚ_[p]) :
    map p f (algebraMap _ _ a) = algebraMap _ _ a :=
  RingHom.congr_fun (padic_hom_ext (f := (map p f).comp (algebraMap ℚ_[p] _))
    (g := algebraMap ℚ_[p] _) (fun a => by
      rw [RingHom.comp_apply, algebraMap_padicInt, algebraMap_padicInt, map_algebraMap,
        Acris.map_algebraMap_padicInt])) a
@[simp] theorem frob_algebraMap_padic (a : ℚ_[p]) :
    frob p R (algebraMap _ _ a) = algebraMap _ _ a :=
  RingHom.congr_fun (padic_hom_ext (f := (frob p R).comp (algebraMap ℚ_[p] _))
    (g := algebraMap ℚ_[p] _) (fun a => by
      rw [RingHom.comp_apply, algebraMap_padicInt, frob_algebraMap,
        Acris.frob_algebraMap_padicInt])) a
@[simp] theorem map_id (x : BcrisPlus p R) : map p (RingHom.id R) x = x :=
  RingHom.congr_fun (hom_ext (f := map p (RingHom.id R)) (g := RingHom.id _) (by simp)) x
end BcrisPlus
namespace Bcris
def lift {B : Type*} [CommRing B] (g : BcrisPlus p R →+* B)
    (h : ∀ ε : tateModule p R, IsPrimitive ε →
      IsUnit (g (algebraMap (Acris p R) _ (Acris.logTeich ε)))) : Bcris p R →+* B :=
  IsLocalization.lift (M := BcrisPlus.periods p R) (g := g) (by
    rintro ⟨x, hx⟩
    induction hx using Submonoid.closure_induction with
    | mem x hx => obtain ⟨ε, hε, rfl⟩ := hx; exact h ε hε
    | one => simp
    | mul x y _ _ hx hy => simpa using hx.mul hy)
@[simp] theorem lift_algebraMap {B : Type*} [CommRing B] (g : BcrisPlus p R →+* B)
    (h : ∀ ε : tateModule p R, IsPrimitive ε →
      IsUnit (g (algebraMap (Acris p R) _ (Acris.logTeich ε)))) (x : BcrisPlus p R) :
    lift g h (algebraMap _ _ x) = g x :=
  IsLocalization.lift_eq _ x
theorem hom_ext {B : Type*} [CommRing B] {f g : Bcris p R →+* B}
    (h : ∀ x : BcrisPlus p R, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (BcrisPlus.periods p R) (RingHom.ext h)
variable (p) in

def map (f : R →+* S) (hf : Function.Injective f) : Bcris p R →+* Bcris p S :=
  lift ((algebraMap (BcrisPlus p S) _).comp (BcrisPlus.map p f)) (fun ε hε => by
    rw [RingHom.comp_apply, BcrisPlus.map_algebraMap, Acris.map_logTeich]
    exact isUnit_logTeich (hε.map f hf))
variable (p R) in

def frob : Bcris p R →+* Bcris p R :=
  lift ((algebraMap (BcrisPlus p R) _).comp (BcrisPlus.frob p R)) (fun ε hε => by
    rw [RingHom.comp_apply, BcrisPlus.frob_algebraMap, Acris.frob_logTeich, map_mul, map_mul,
      map_natCast, map_natCast]
    exact isUnit_p.mul (isUnit_logTeich hε))
@[simp] theorem map_algebraMap (f : R →+* S) (hf : Function.Injective f) (x : BcrisPlus p R) :
    map p f hf (algebraMap _ _ x) = algebraMap _ _ (BcrisPlus.map p f x) := lift_algebraMap _ _ x
@[simp] theorem frob_algebraMap (x : BcrisPlus p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (BcrisPlus.frob p R x) := lift_algebraMap _ _ x
@[simp] theorem map_algebraMap_acris (f : R →+* S) (hf : Function.Injective f) (x : Acris p R) :
    map p f hf (algebraMap _ _ x) = algebraMap _ _ (Acris.map p f x) := by
  rw [IsScalarTower.algebraMap_apply (Acris p R) (BcrisPlus p R) (Bcris p R), map_algebraMap,
    BcrisPlus.map_algebraMap, ← IsScalarTower.algebraMap_apply]
@[simp] theorem frob_algebraMap_acris (x : Acris p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (Acris.frob p R x) := by
  rw [IsScalarTower.algebraMap_apply (Acris p R) (BcrisPlus p R) (Bcris p R), frob_algebraMap,
    BcrisPlus.frob_algebraMap, ← IsScalarTower.algebraMap_apply]
@[simp] theorem map_algebraMap_padic (f : R →+* S) (hf : Function.Injective f) (a : ℚ_[p]) :
    map p f hf (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (BcrisPlus p R) (Bcris p R), map_algebraMap,
    BcrisPlus.map_algebraMap_padic, ← IsScalarTower.algebraMap_apply]
@[simp] theorem frob_algebraMap_padic (a : ℚ_[p]) :
    frob p R (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (BcrisPlus p R) (Bcris p R), frob_algebraMap,
    BcrisPlus.frob_algebraMap_padic]
@[simp] theorem map_id (h : Function.Injective (RingHom.id R)) (x : Bcris p R) :
    map p (RingHom.id R) h x = x :=
  RingHom.congr_fun (hom_ext (f := map p (RingHom.id R) h) (g := RingHom.id _) (by simp)) x
@[simp] theorem map_logTeich (f : R →+* S) (hf : Function.Injective f) (η : tateModule p R) :
    map p f hf (logTeich η) = logTeich (tateModule.map p f η) := by
  simp [logTeich]
@[simp] theorem frob_logTeich (η : tateModule p R) : frob p R (logTeich η) = p * logTeich η := by
  simp [logTeich]
end Bcris
namespace Bst
variable (p) in

def map (f : R →+* S) (hf : Function.Injective f) : Bst p R →+* Bst p S :=
  lift ((algebraMap (Bcris p S) _).comp (Bcris.map p f hf)) (fun ϖ => logFlat (PFlat.map p f ϖ))
    (fun η ϖ => by rw [PFlat.map_twist, logFlat_twist, RingHom.comp_apply, Bcris.map_logTeich])
variable (p R) in

def frob : Bst p R →+* Bst p R :=
  lift ((algebraMap (Bcris p R) _).comp (Bcris.frob p R)) (fun ϖ => p * logFlat ϖ)
    (fun η ϖ => by
      rw [logFlat_twist, RingHom.comp_apply, Bcris.frob_logTeich, map_mul, map_natCast, mul_add])
end Bst
end Reformulated.AutPerF


