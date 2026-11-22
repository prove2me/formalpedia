-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:34.661288+00:00
-- url     : https://prove2.me/theorems/a4543013-7a50-4690-8bda-fb3f66623f36
-- title:
--   Trunc Log Eq Of Pow Eq Zero
-- statement:
--   Definitions and structural lemmas for Trunc Log Eq Of Pow Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap


set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
namespace Reformulated.AutPerF
universe u v w
section Adic
variable {A : Type u} [CommRing A]
def adicMk (I : Ideal A) (x : ∀ n : ℕ, A ⧸ I ^ n)
    (h : ∀ (m n : ℕ) (hle : m ≤ n), Ideal.Quotient.factorPow I hle (x n) = x m) :
    AdicCompletion I A :=
  AdicCompletion.liftRingHom I
    (fun n => Polynomial.eval₂RingHom (Int.castRingHom (A ⧸ I ^ n)) (x n))
    (fun {m n} hle => by
      apply Polynomial.ringHom_ext'
      · exact Subsingleton.elim _ _
      · simpa using h m n hle) Polynomial.X
@[simp] theorem evalₐ_adicMk (I : Ideal A) (x : ∀ n : ℕ, A ⧸ I ^ n)
    (h : ∀ (m n : ℕ) (hle : m ≤ n), Ideal.Quotient.factorPow I hle (x n) = x m) (n : ℕ) :
    AdicCompletion.evalₐ I n (adicMk I x h) = x n := by
  unfold adicMk
  rw [AdicCompletion.evalₐ_liftRingHom]
  · simp
  · intro m n hle
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simpa using h m n hle
theorem factorPow_evalₐ (I : Ideal A) {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | h x =>
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    exact AdicCompletion.Ideal.mk_eq_mk I hle x
theorem evalₐ_pow_eq_zero (I : Ideal A) {x : AdicCompletion I A}
    (hx : AdicCompletion.evalOneₐ I x = 0) (n : ℕ) : AdicCompletion.evalₐ I n x ^ n = 0 := by
  rcases n with _ | n
  · exact Subsingleton.elim (h := Ideal.Quotient.subsingleton_iff.2 (by simp)) _ _
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  have h1 := factorPow_evalₐ I (show 1 ≤ n + 1 by omega) x
  rw [← AdicCompletion.factorₐ_evalₐ_one, ← h1, ← ha] at hx
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [← ha, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hx _
def truncLog {B : Type*} [CommRing B] [Algebra ℚ B] (N : ℕ) (x : B) : B :=
  ∑ k ∈ Finset.range N, ((-1 : ℚ) ^ k / (k + 1)) • x ^ (k + 1)
theorem map_truncLog {B B' : Type*} [CommRing B] [Algebra ℚ B] [CommRing B'] [Algebra ℚ B']
    (f : B →+* B') (N : ℕ) (x : B) : f (truncLog N x) = truncLog N (f x) := by
  simp [truncLog, map_rat_smul]
theorem truncLog_eq_of_pow_eq_zero {B : Type*} [CommRing B] [Algebra ℚ B] {x : B} {m n : ℕ}
    (h : x ^ m = 0) (hle : m ≤ n) : truncLog n x = truncLog m x := by
  induction n, hle using Nat.le_induction with
  | base => rfl
  | succ n hle ih =>
    rw [← ih, truncLog, Finset.sum_range_succ, pow_eq_zero_of_le (by omega) h, smul_zero, add_zero]
    rfl
def adicLog [Algebra ℚ A] (I : Ideal A) (u : AdicCompletion I A)
    (hu : AdicCompletion.evalOneₐ I u = 1) : AdicCompletion I A :=
  adicMk I (fun n => truncLog n (AdicCompletion.evalₐ I n (u - 1))) (fun m n hle => by
    rw [map_truncLog, factorPow_evalₐ]
    exact truncLog_eq_of_pow_eq_zero (evalₐ_pow_eq_zero I (by simp [hu]) m) hle)
end Adic
variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
abbrev AinfInv.kerTheta : Ideal (AinfInv p R) := RingHom.ker (AinfInv.theta p R)
def BdRPlus : Type u := AdicCompletion (AinfInv.kerTheta p R) (AinfInv p R)
namespace BdRPlus
instance : CommRing (BdRPlus p R) :=
  inferInstanceAs (CommRing (AdicCompletion (AinfInv.kerTheta p R) (AinfInv p R)))
instance : Algebra (AinfInv p R) (BdRPlus p R) :=
  inferInstanceAs (Algebra (AinfInv p R) (AdicCompletion (AinfInv.kerTheta p R) (AinfInv p R)))
instance : Algebra (Ainf p R) (BdRPlus p R) :=
  ((algebraMap (AinfInv p R) (BdRPlus p R)).comp (algebraMap _ _)).toAlgebra
instance : Algebra ℚ_[p] (BdRPlus p R) :=
  ((algebraMap (AinfInv p R) (BdRPlus p R)).comp (algebraMap _ _)).toAlgebra
instance : Algebra ℚ (BdRPlus p R) :=
  ((algebraMap (AinfInv p R) (BdRPlus p R)).comp (algebraMap _ _)).toAlgebra
instance : IsScalarTower (Ainf p R) (AinfInv p R) (BdRPlus p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance : IsScalarTower ℚ_[p] (AinfInv p R) (BdRPlus p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
def eval (n : ℕ) : BdRPlus p R →+* AinfInv p R ⧸ AinfInv.kerTheta p R ^ n :=
  (AdicCompletion.evalₐ (AinfInv.kerTheta p R) n).toRingHom
def theta : BdRPlus p R →+* Localization.Away (p : R) :=
  (RingHom.kerLift (AinfInv.theta p R)).comp
    (AdicCompletion.evalOneₐ (AinfInv.kerTheta p R)).toRingHom
def fil (n : ℕ) : Ideal (BdRPlus p R) := RingHom.ker (theta p R) ^ n
variable {p R}
@[simp] theorem eval_algebraMap (n : ℕ) (x : AinfInv p R) :
    eval p R n (algebraMap _ _ x) = Ideal.Quotient.mk _ x :=
  AdicCompletion.evalₐ_of _ n x
@[simp] theorem theta_algebraMap (x : AinfInv p R) :
    theta p R (algebraMap _ _ x) = AinfInv.theta p R x := rfl
theorem theta_eq_one_iff (x : BdRPlus p R) :
    theta p R x = 1 ↔ AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) x = 1 :=
  map_eq_one_iff _ (RingHom.kerLift_injective _)
def log (u : BdRPlus p R) (hu : theta p R u = 1) : BdRPlus p R :=
  adicLog (AinfInv.kerTheta p R) u ((theta_eq_one_iff u).1 hu)
end BdRPlus
def BdR : Type u := FractionRing (BdRPlus p R)
namespace BdR
instance : CommRing (BdR p R) := inferInstanceAs (CommRing (FractionRing (BdRPlus p R)))
instance : Algebra (BdRPlus p R) (BdR p R) :=
  inferInstanceAs (Algebra (BdRPlus p R) (FractionRing (BdRPlus p R)))
instance : IsFractionRing (BdRPlus p R) (BdR p R) :=
  inferInstanceAs (IsFractionRing (BdRPlus p R) (FractionRing (BdRPlus p R)))
instance : Algebra ℚ_[p] (BdR p R) :=
  ((algebraMap (BdRPlus p R) (BdR p R)).comp (algebraMap _ _)).toAlgebra
instance : IsScalarTower ℚ_[p] (BdRPlus p R) (BdR p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
def filNat (n : ℕ) : Submodule (BdRPlus p R) (BdR p R) :=
  Submodule.map (Algebra.linearMap (BdRPlus p R) (BdR p R)) (BdRPlus.fil p R n)
def fil (i : ℤ) : Submodule (BdRPlus p R) (BdR p R) :=
  filNat p R i.toNat / filNat p R (-i).toNat
end BdR
variable {p R} in

def AinfInv.gamma (n : ℕ) (x : AinfInv p R) : AinfInv p R := ((n ! : ℚ)⁻¹) • x ^ n
def acrisZero : Subalgebra (Ainf p R) (AinfInv p R) :=
  Algebra.adjoin (Ainf p R)
    {y | ∃ (n : ℕ) (x : Ainf p R), Ainf.theta p R x = 0 ∧ y = AinfInv.gamma n (algebraMap _ _ x)}
abbrev AcrisZero : Type u := acrisZero p R
variable {p R} in

def AcrisZero.gamma (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) : AcrisZero p R :=
  ⟨AinfInv.gamma n (algebraMap _ _ x), Algebra.subset_adjoin ⟨n, x, hx, rfl⟩⟩
def Acris : Type u := AdicCompletion (span {(p : AcrisZero p R)}) (AcrisZero p R)
namespace Acris
instance : CommRing (Acris p R) :=
  inferInstanceAs (CommRing (AdicCompletion (span {(p : AcrisZero p R)}) (AcrisZero p R)))
instance : Algebra (AcrisZero p R) (Acris p R) :=
  inferInstanceAs (Algebra (AcrisZero p R)
    (AdicCompletion (span {(p : AcrisZero p R)}) (AcrisZero p R)))
instance : Algebra (Ainf p R) (Acris p R) :=
  ((algebraMap (AcrisZero p R) (Acris p R)).comp (algebraMap _ _)).toAlgebra
instance : Algebra ℤ_[p] (Acris p R) :=
  ((algebraMap (Ainf p R) (Acris p R)).comp (algebraMap _ _)).toAlgebra
instance : IsScalarTower (Ainf p R) (AcrisZero p R) (Acris p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance : IsScalarTower ℤ_[p] (Ainf p R) (Acris p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
def eval (n : ℕ) : Acris p R →+* AcrisZero p R ⧸ span {(p : AcrisZero p R)} ^ n :=
  (AdicCompletion.evalₐ (span {(p : AcrisZero p R)}) n).toRingHom
variable {p R}
@[simp] theorem eval_algebraMap (n : ℕ) (x : AcrisZero p R) :
    eval p R n (algebraMap _ _ x) = Ideal.Quotient.mk _ x :=
  AdicCompletion.evalₐ_of _ n x
def logPartial (N : ℕ) (u : Ainf p R) (hu : Ainf.theta p R u = 1) : AcrisZero p R :=
  ∑ k ∈ Finset.range N,
    ((-1) ^ k * (k ! : AcrisZero p R)) * AcrisZero.gamma (k + 1) (u - 1) (by simp [hu])
theorem logPartial_sub_mem (u : Ainf p R) (hu : Ainf.theta p R u = 1) {n M N : ℕ}
    (hM : p ^ n ≤ M) (hN : M ≤ N) :
    logPartial N u hu - logPartial M u hu ∈ span {(p : AcrisZero p R)} ^ n := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [logPartial, Finset.sum_range_succ, add_sub_right_comm]
    refine add_mem ih (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ?_))
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (pow_pos (Fact.out : p.Prime).pos n) (hM.trans hN)
    rw [hc, Nat.cast_mul, Nat.cast_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (mem_span_singleton_self _) _)
def log (u : Ainf p R) (hu : Ainf.theta p R u = 1) : Acris p R :=
  adicMk _ (fun n => Ideal.Quotient.mk _ (logPartial (p ^ n) u hu)) (fun m n hle => by
    simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    exact Ideal.Quotient.eq.2 (logPartial_sub_mem u hu le_rfl
      (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hle)))
end Acris
def tateModule : Submonoid (Tilt p R) := MonoidHom.mker (PreTilt.untilt (O := R) (p := p))
variable {p R} in

def Acris.logTeich (η : tateModule p R) : Acris p R :=
  Acris.log (Ainf.teich p η.1) (by rw [Ainf.theta_teich]; exact η.2)
variable {p R} in

def IsPrimitive (ε : tateModule p R) : Prop :=
  PreTilt.untilt ((frobeniusEquiv (Tilt p R) p).symm ε.1) ≠ 1
def BcrisPlus : Type u := Localization.Away (p : Acris p R)
namespace BcrisPlus
instance : CommRing (BcrisPlus p R) :=
  inferInstanceAs (CommRing (Localization.Away (p : Acris p R)))
instance : Algebra (Acris p R) (BcrisPlus p R) :=
  inferInstanceAs (Algebra (Acris p R) (Localization.Away (p : Acris p R)))
instance : IsLocalization.Away (p : Acris p R) (BcrisPlus p R) :=
  inferInstanceAs (IsLocalization.Away (p : Acris p R) (Localization.Away (p : Acris p R)))
theorem isUnit_p : IsUnit (p : BcrisPlus p R) := by
  simpa using IsLocalization.Away.algebraMap_isUnit (S := BcrisPlus p R) (p : Acris p R)
instance : Algebra ℚ_[p] (BcrisPlus p R) :=
  (padicLift p ((algebraMap (Acris p R) (BcrisPlus p R)).comp (algebraMap ℤ_[p] _))
    (isUnit_p p R)).toAlgebra
def periods : Submonoid (BcrisPlus p R) :=
  Submonoid.closure {x | ∃ ε : tateModule p R, IsPrimitive ε ∧
    x = algebraMap (Acris p R) _ (Acris.logTeich ε)}
end BcrisPlus
def Bcris : Type u := Localization (BcrisPlus.periods p R)
namespace Bcris
instance : CommRing (Bcris p R) := inferInstanceAs (CommRing (Localization (BcrisPlus.periods p R)))
instance : Algebra (BcrisPlus p R) (Bcris p R) :=
  inferInstanceAs (Algebra (BcrisPlus p R) (Localization (BcrisPlus.periods p R)))
instance : IsLocalization (BcrisPlus.periods p R) (Bcris p R) :=
  inferInstanceAs (IsLocalization _ (Localization (BcrisPlus.periods p R)))
instance : Algebra (Acris p R) (Bcris p R) :=
  ((algebraMap (BcrisPlus p R) (Bcris p R)).comp (algebraMap _ _)).toAlgebra
instance : Algebra ℚ_[p] (Bcris p R) :=
  ((algebraMap (BcrisPlus p R) (Bcris p R)).comp (algebraMap _ _)).toAlgebra
instance : IsScalarTower (Acris p R) (BcrisPlus p R) (Bcris p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance : IsScalarTower ℚ_[p] (BcrisPlus p R) (Bcris p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
variable {p R} in

def logTeich (η : tateModule p R) : Bcris p R := algebraMap (Acris p R) _ (Acris.logTeich η)
end Bcris
def PFlat : Type u := {ϖ : Tilt p R // PreTilt.untilt ϖ = (p : R)}
variable {p R} in

def PFlat.twist (η : tateModule p R) (ϖ : PFlat p R) : PFlat p R :=
  ⟨η.1 * ϖ.1, by rw [map_mul, ϖ.2, show PreTilt.untilt η.1 = 1 from η.2, one_mul]⟩
def Bst.relations : Ideal (MvPolynomial (PFlat p R) (Bcris p R)) :=
  span {f | ∃ (η : tateModule p R) (ϖ : PFlat p R), f = MvPolynomial.X (ϖ.twist η) -
    (MvPolynomial.C (Bcris.logTeich η) + MvPolynomial.X ϖ)}
def Bst : Type u := MvPolynomial (PFlat p R) (Bcris p R) ⧸ Bst.relations p R
namespace Bst
instance : CommRing (Bst p R) :=
  inferInstanceAs (CommRing (MvPolynomial (PFlat p R) (Bcris p R) ⧸ Bst.relations p R))
instance : Algebra (Bcris p R) (Bst p R) :=
  inferInstanceAs (Algebra (Bcris p R) (MvPolynomial (PFlat p R) (Bcris p R) ⧸ Bst.relations p R))
instance : Algebra ℚ_[p] (Bst p R) :=
  ((algebraMap (Bcris p R) (Bst p R)).comp (algebraMap _ _)).toAlgebra
instance : IsScalarTower ℚ_[p] (Bcris p R) (Bst p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
def mk : MvPolynomial (PFlat p R) (Bcris p R) →ₐ[Bcris p R] Bst p R :=
  Ideal.Quotient.mkₐ (Bcris p R) (Bst.relations p R)
theorem mk_surjective : Function.Surjective (mk p R) := Ideal.Quotient.mk_surjective
variable {p R}
def logFlat (ϖ : PFlat p R) : Bst p R := mk p R (MvPolynomial.X ϖ)
def lift {B : Type*} [CommRing B] (f : Bcris p R →+* B) (l : PFlat p R → B)
    (h : ∀ η ϖ, l (PFlat.twist η ϖ) = f (Bcris.logTeich η) + l ϖ) : Bst p R →+* B :=
  Ideal.Quotient.lift (Bst.relations p R) (MvPolynomial.eval₂Hom f l) (by
    intro a ha
    refine (show Bst.relations p R ≤ RingHom.ker (MvPolynomial.eval₂Hom f l) from ?_) ha
    rw [Bst.relations, Ideal.span_le]
    rintro _ ⟨η, ϖ, rfl⟩
    simp [RingHom.mem_ker, h])
@[simp] theorem lift_algebraMap {B : Type*} [CommRing B] (f : Bcris p R →+* B) (l : PFlat p R → B)
    (h : ∀ η ϖ, l (PFlat.twist η ϖ) = f (Bcris.logTeich η) + l ϖ) (x : Bcris p R) :
    lift f l h (algebraMap _ _ x) = f x :=
  (Ideal.Quotient.lift_mk _ _ _).trans (MvPolynomial.eval₂Hom_C f l x)
@[simp] theorem lift_logFlat {B : Type*} [CommRing B] (f : Bcris p R →+* B) (l : PFlat p R → B)
    (h : ∀ η ϖ, l (PFlat.twist η ϖ) = f (Bcris.logTeich η) + l ϖ) (ϖ : PFlat p R) :
    lift f l h (logFlat ϖ) = l ϖ :=
  (Ideal.Quotient.lift_mk _ _ _).trans (MvPolynomial.eval₂Hom_X' f l ϖ)
variable (p R) in

def monodromyDerivation : Derivation (Bcris p R) (MvPolynomial (PFlat p R) (Bcris p R))
    (MvPolynomial (PFlat p R) (Bcris p R)) :=
  MvPolynomial.mkDerivation (Bcris p R) fun _ => -1
theorem monodromyDerivation_mem {f : MvPolynomial (PFlat p R) (Bcris p R)} (hf : f ∈ Bst.relations p R) :
    monodromyDerivation p R f ∈ Bst.relations p R := by
  induction hf using Submodule.span_induction with
  | mem f hf => obtain ⟨η, ϖ, rfl⟩ := hf; simp [monodromyDerivation]
  | zero => simp
  | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
  | smul a f h hf =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ hf) (Ideal.mul_mem_right _ _ h)
variable (p R) in

def monodromyLin : Bst p R →ₗ[Bcris p R] Bst p R :=
  (Submodule.Quotient.restrictScalarsEquiv (Bcris p R) (Bst.relations p R)).toLinearMap ∘ₗ
    Submodule.mapQ ((Bst.relations p R).restrictScalars (Bcris p R))
      ((Bst.relations p R).restrictScalars (Bcris p R)) (monodromyDerivation p R).toLinearMap
      (fun _ hf => monodromyDerivation_mem hf) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv (Bcris p R) (Bst.relations p R)).symm.toLinearMap
theorem monodromyLin_mk (f : MvPolynomial (PFlat p R) (Bcris p R)) :
    monodromyLin p R (mk p R f) = mk p R (monodromyDerivation p R f) := rfl
variable (p R) in

def monodromy : Derivation (Bcris p R) (Bst p R) (Bst p R) :=
  Derivation.mk' (monodromyLin p R) (by
    intro a b
    obtain ⟨a, rfl⟩ := mk_surjective p R a
    obtain ⟨b, rfl⟩ := mk_surjective p R b
    rw [← map_mul, monodromyLin_mk, monodromyLin_mk, monodromyLin_mk, Derivation.leibniz]
    simp)
end Bst
end Reformulated.AutPerF


