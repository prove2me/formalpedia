-- Prove2me | Definitions.Def_AlpoGeB000
-- name    : AlpoGeB000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-21T16:21:52.077219+00:00
-- url     : https://prove2.me/theorems/4eada639-2bf6-4174-a6e6-80779f2279dc
-- title:
--   Definitions bundle AlpoGeB000 of the alpo.ge GRH release, first cut (Row0b, IsRecT)
-- statement:
--   A definitions bundle of the first cut of L. Alpöge's Lean proof of GRH for Dirichlet $L$-functions (released 20 November 2026, written with Claude; announcement [alpo.ge/remark.pdf](https://alpo.ge/remark.pdf)). The declarations and their proofs are the release's, carved mechanically for this platform: the carve reorders them, restates the namespaces and `open`s each needs, and writes a few declarations from their elaborated form. Two patches are recorded in the carve: an anonymous instance is given its original generated name, and an additive structure that a `to_additive` attribute names is restored beside the structure that names it. The release builds with `maxHeartbeats 4000000` and `maxSynthPendingDepth 3` as project options (and `synthInstance.maxHeartbeats 400000` for its local and global field libraries); since the verifier sets none of these, each carved module section states them as `set_option` lines. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   The first cut publishes the two inputs from which the release concludes its main theorem: `AlpoGe.galoisLocalGlobalStrong_recParameter` (the release's `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`) and `AlpoGe.everyCharacter_of_row` (the release's `UpperTheory.FinalTheorems.everyCharacter_of_row`). These bundles hold the definitions their statements need, with the theorems those definitions use.
--
--   **Contents.** It holds 242 declarations of the release's Lean: 82 definitions, 11 inductive types or structures, 39 instances and 110 theorems. The definitions and types are `Formalism.BasicNotions.DV.Geo`, `Formalism.BasicNotions.DV.ITh`, `Formalism.BasicNotions.HLat`, `Formalism.BasicNotions.JetLoc`, `Formalism.BasicNotions.JetLoc1`, `Formalism.BasicNotions.Loc.Ainf`, `Formalism.BasicNotions.Loc.FinExt`, `Formalism.BasicNotions.Loc.GK`, `Formalism.BasicNotions.Loc.GQ`, `Formalism.BasicNotions.Loc.K0`, `Formalism.BasicNotions.Loc.MaximalUnramifiedExtension`, `Formalism.BasicNotions.Loc.OC`, `Formalism.BasicNotions.Loc.OCb`, `Formalism.BasicNotions.Loc.OL`, `Formalism.BasicNotions.Loc.Om`, `Formalism.BasicNotions.LocAinf`, `Formalism.BasicNotions.LocBridge`, `Formalism.BasicNotions.LocBridge.IsCrysE`, `Formalism.BasicNotions.LocBridge.IsdRE`, `Formalism.BasicNotions.LocBridge.multE`, `Formalism.BasicNotions.LocBridge.repE`, `Formalism.BasicNotions.LocPrime`, `Formalism.BasicNotions.LocRings`, `Formalism.Per.Ainf`, `Formalism.Per.OC`, `Formalism.WeaklyAdmissibleFiltrations.Dcris`, `Formalism.WeaklyAdmissibleFiltrations.DdR`, `Formalism.WeaklyAdmissibleFiltrations.DdRE`, `Formalism.WeaklyAdmissibleFiltrations.FilV`, `Formalism.WeaklyAdmissibleFiltrations.FildR`, `Formalism.WeaklyAdmissibleFiltrations.IsCrys`, `Formalism.WeaklyAdmissibleFiltrations.PeriodData`, `Formalism.WeaklyAdmissibleFiltrations.actVB`, `Formalism.WeaklyAdmissibleFiltrations.actVdR`, `Formalism.WeaklyAdmissibleFiltrations.mulVdR`, `Formalism.WeaklyAdmissibleFiltrations.multV`, `Reformulated.AutPerF.Acris`, `Reformulated.AutPerF.Acris.eval`, `Reformulated.AutPerF.Acris.extend`, `Reformulated.AutPerF.Acris.frob`, `Reformulated.AutPerF.Acris.log`, `Reformulated.AutPerF.Acris.logPartial`, `Reformulated.AutPerF.Acris.logTeich`, `Reformulated.AutPerF.Acris.map`, `Reformulated.AutPerF.AcrisZero`, `Reformulated.AutPerF.AcrisZero.extend`, `Reformulated.AutPerF.AcrisZero.frob`, `Reformulated.AutPerF.AcrisZero.gamma`, `Reformulated.AutPerF.AcrisZero.map`, `Reformulated.AutPerF.Ainf`, `Reformulated.AutPerF.Ainf.frob`, `Reformulated.AutPerF.Ainf.map`, `Reformulated.AutPerF.Ainf.ofPadicInt`, `Reformulated.AutPerF.Ainf.teich`, `Reformulated.AutPerF.Ainf.theta`, `Reformulated.AutPerF.Ainf.xi`, `Reformulated.AutPerF.AinfInv`, `Reformulated.AutPerF.AinfInv.extend`, `Reformulated.AutPerF.AinfInv.frob`, `Reformulated.AutPerF.AinfInv.gamma`, and 33 more.
-- source:
--   L. Alpöge, working with Claude, Lean formalization of the Riemann hypothesis and of GRH for Dirichlet L-functions, released 20 November 2026 (announcement https://alpo.ge/remark.pdf; Lean archive https://alpo.ge/lean.tar.gz.part01 to part14, joined tarball sha256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc)

import Mathlib

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovariantDegrees
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

@[reducible] noncomputable def UpperTheory.Reformulated.B.CovariantDegrees.Om :
    (l : Nat) → [Fact (Nat.Prime l)] → Type :=
    fun (l : Nat) [inst : Fact (Nat.Prime l)] ↦ @PadicAlgCl l inst
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.SpanNatCastLeComap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

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

theorem untilt_map (f : R →+* S) (x : Tilt p R) :
    PreTilt.untilt (map p f x) = f (PreTilt.untilt x) := by
  refine Perfection.teichmuller_spec fun n => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  refine ⟨f a, ?_, ?_⟩
  · change _ = PreTilt.coeff n (map p f x)
    rw [coeff_map, ← ha]; rfl
  · have h := Perfection.teichmuller_sModEq (p := p) (I := span {(p : R)}) (x := x) (y := a)
      (n := n) ha
    rw [SModEq.sub_mem] at h ⊢
    have h2 := pow_le_comap_pow (span_natCast_le_comap p f) (n + 1) (neg_mem h)
    rw [Ideal.mem_comap, neg_sub, map_sub, map_pow] at h2
    exact h2

end Tilt

namespace Ainf

abbrev teich : Tilt p R →* Ainf p R := WittVector.teichmuller p

variable (R) in

def frob : Ainf p R →+* Ainf p R := WittVector.frobenius

def map (f : R →+* S) : Ainf p R →+* Ainf p S := WittVector.map (Tilt.map p f)

variable (R) in

def ofPadicInt : ℤ_[p] →+* Ainf p R :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (Tilt p R))).comp (WittVector.equiv p).symm.toRingHom

instance instAlgebraPadicInt : Algebra ℤ_[p] (Ainf p R) := (ofPadicInt p R).toAlgebra

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

theorem p_dvd_frob_sub_pow (x : Ainf p R) : (p : Ainf p R) ∣ frob p R x - x ^ p := by
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow,
    frob_eq_map]
  simp [frobenius_def]

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

variable (p R) in

def theta : Ainf p R →+* R := WittVector.fontaineTheta R p

@[simp] theorem theta_teich (x : Tilt p R) : theta p R (teich p x) = PreTilt.untilt x :=
  WittVector.fontaineTheta_teichmuller x

theorem theta_map (f : R →+* S) (x : Ainf p R) : theta p S (map p f x) = f (theta p R x) := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : S)})]
  intro n
  rw [smul_eq_mul, Ideal.mul_top, SModEq]
  have := WittVector.eq_of_apply_teichmuller_eq
    ((Ideal.Quotient.mk (span {(p : S)} ^ n)).comp ((theta p S).comp (map p f)))
    ((Ideal.Quotient.mk (span {(p : S)} ^ n)).comp (f.comp (theta p R)))
    (by
      refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (span {(p : S)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (mem_span_singleton_self _) _)
    (by intro y; simp [Tilt.untilt_map])
  exact RingHom.congr_fun this x

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

instance instAlgebraPadic : Algebra ℚ_[p] (AinfInv p R) :=
  (padicLift p (algebraMap ℤ_[p] (AinfInv p R)) (isUnit_p p)).toAlgebra

instance instAlgebraRat : Algebra ℚ (AinfInv p R) :=
  ((algebraMap ℚ_[p] (AinfInv p R)).comp (algebraMap ℚ ℚ_[p])).toAlgebra

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

omit [Fact p.Prime] in
@[simp] theorem awayMap_algebraMap {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : R) : awayMap p f (algebraMap _ _ x) = algebraMap _ _ (f x) :=
  IsLocalization.Away.lift_eq _ _ x

variable {p} in
theorem AinfInv.theta_map [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
    (f : R →+* S) (x : AinfInv p R) :
    AinfInv.theta p S (AinfInv.map p f x) = awayMap p f (AinfInv.theta p R x) :=
  RingHom.congr_fun (AinfInv.hom_ext (f := (AinfInv.theta p S).comp (AinfInv.map p f))
    (g := (awayMap p f).comp (AinfInv.theta p R)) (by simp [Ainf.theta_map])) x

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

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

end Adic

variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

abbrev AinfInv.kerTheta : Ideal (AinfInv p R) := RingHom.ker (AinfInv.theta p R)

def BdRPlus : Type u := AdicCompletion (AinfInv.kerTheta p R) (AinfInv p R)

namespace BdRPlus

instance instCommRing : CommRing (BdRPlus p R) :=
  inferInstanceAs (CommRing (AdicCompletion (AinfInv.kerTheta p R) (AinfInv p R)))
instance instAlgebraAinfInv : Algebra (AinfInv p R) (BdRPlus p R) :=
  inferInstanceAs (Algebra (AinfInv p R) (AdicCompletion (AinfInv.kerTheta p R) (AinfInv p R)))
instance instAlgebraAinf : Algebra (Ainf p R) (BdRPlus p R) :=
  ((algebraMap (AinfInv p R) (BdRPlus p R)).comp (algebraMap _ _)).toAlgebra
instance instIsScalarTowerAinfAinfInv : IsScalarTower (Ainf p R) (AinfInv p R) (BdRPlus p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def eval (n : ℕ) : BdRPlus p R →+* AinfInv p R ⧸ AinfInv.kerTheta p R ^ n :=
  (AdicCompletion.evalₐ (AinfInv.kerTheta p R) n).toRingHom

def theta : BdRPlus p R →+* Localization.Away (p : R) :=
  (RingHom.kerLift (AinfInv.theta p R)).comp
    (AdicCompletion.evalOneₐ (AinfInv.kerTheta p R)).toRingHom

variable {p R}

@[simp] theorem eval_algebraMap (n : ℕ) (x : AinfInv p R) :
    eval p R n (algebraMap _ _ x) = Ideal.Quotient.mk _ x :=
  AdicCompletion.evalₐ_of _ n x

@[simp] theorem theta_algebraMap (x : AinfInv p R) :
    theta p R (algebraMap _ _ x) = AinfInv.theta p R x := rfl

end BdRPlus

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

instance instCommRing : CommRing (Acris p R) :=
  inferInstanceAs (CommRing (AdicCompletion (span {(p : AcrisZero p R)}) (AcrisZero p R)))
instance instAlgebraAcrisZero : Algebra (AcrisZero p R) (Acris p R) :=
  inferInstanceAs (Algebra (AcrisZero p R)
    (AdicCompletion (span {(p : AcrisZero p R)}) (AcrisZero p R)))
instance instAlgebraAinf : Algebra (Ainf p R) (Acris p R) :=
  ((algebraMap (AcrisZero p R) (Acris p R)).comp (algebraMap _ _)).toAlgebra
instance instAlgebraPadicInt : Algebra ℤ_[p] (Acris p R) :=
  ((algebraMap (Ainf p R) (Acris p R)).comp (algebraMap _ _)).toAlgebra
instance instIsScalarTowerAinfAcrisZero : IsScalarTower (Ainf p R) (AcrisZero p R) (Acris p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance instIsScalarTowerPadicIntAinf : IsScalarTower ℤ_[p] (Ainf p R) (Acris p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def eval (n : ℕ) : Acris p R →+* AcrisZero p R ⧸ span {(p : AcrisZero p R)} ^ n :=
  (AdicCompletion.evalₐ (span {(p : AcrisZero p R)}) n).toRingHom

variable {p R}

theorem ext_eval {x y : Acris p R} (h : ∀ n, eval p R n x = eval p R n y) : x = y :=
  AdicCompletion.ext_evalₐ h

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

theorem eval_log (u : Ainf p R) (hu : Ainf.theta p R u = 1) {n N : ℕ} (hN : p ^ n ≤ N) :
    eval p R n (log u hu) = Ideal.Quotient.mk _ (logPartial N u hu) :=
  (evalₐ_adicMk _ _ _ n).trans (Ideal.Quotient.eq.2 (logPartial_sub_mem u hu le_rfl hN)).symm

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

instance instCommRing : CommRing (BcrisPlus p R) :=
  inferInstanceAs (CommRing (Localization.Away (p : Acris p R)))
instance instAlgebraAcris : Algebra (Acris p R) (BcrisPlus p R) :=
  inferInstanceAs (Algebra (Acris p R) (Localization.Away (p : Acris p R)))
instance instAwayAcrisCast : IsLocalization.Away (p : Acris p R) (BcrisPlus p R) :=
  inferInstanceAs (IsLocalization.Away (p : Acris p R) (Localization.Away (p : Acris p R)))

theorem isUnit_p : IsUnit (p : BcrisPlus p R) := by
  simpa using IsLocalization.Away.algebraMap_isUnit (S := BcrisPlus p R) (p : Acris p R)

def periods : Submonoid (BcrisPlus p R) :=
  Submonoid.closure {x | ∃ ε : tateModule p R, IsPrimitive ε ∧
    x = algebraMap (Acris p R) _ (Acris.logTeich ε)}

end BcrisPlus

def Bcris : Type u := Localization (BcrisPlus.periods p R)

namespace Bcris

instance instCommRing : CommRing (Bcris p R) := inferInstanceAs (CommRing (Localization (BcrisPlus.periods p R)))
instance instAlgebraBcrisPlus : Algebra (BcrisPlus p R) (Bcris p R) :=
  inferInstanceAs (Algebra (BcrisPlus p R) (Localization (BcrisPlus.periods p R)))
instance instIsLocalizationBcrisPlusPeriods : IsLocalization (BcrisPlus.periods p R) (Bcris p R) :=
  inferInstanceAs (IsLocalization _ (Localization (BcrisPlus.periods p R)))
instance instAlgebraAcris : Algebra (Acris p R) (Bcris p R) :=
  ((algebraMap (BcrisPlus p R) (Bcris p R)).comp (algebraMap _ _)).toAlgebra
instance instIsScalarTowerAcrisBcrisPlus : IsScalarTower (Acris p R) (BcrisPlus p R) (Bcris p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {p R} in

def logTeich (η : tateModule p R) : Bcris p R := algebraMap (Acris p R) _ (Acris.logTeich η)

end Bcris

def PFlat : Type u := {ϖ : Tilt p R // PreTilt.untilt ϖ = (p : R)}

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

namespace Tilt

@[simp] theorem untilt_zero : PreTilt.untilt (0 : Tilt p R) = 0 := Perfection.teichmuller_zero

end Tilt

namespace Ainf

def xi (ϖ : PFlat p R) : Ainf p R := (p : Ainf p R) - teich p ϖ.1

@[simp] theorem theta_xi (ϖ : PFlat p R) : theta p R (xi ϖ) = 0 := by
  simp [xi, ϖ.2]

end Ainf

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]

namespace BdRPlus

omit [IsDomain R] [ValuationRing R] [CharZero R] in
@[simp] theorem theta_algebraMap_ainf (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = algebraMap R _ (Ainf.theta p R x) :=
  AinfInv.theta_algebraMap x

end BdRPlus

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
attribute [-simp] _root_.Reformulated.AutPerF.Ainf.theta_xi _root_.Reformulated.AutPerF.BdRPlus.theta_algebraMap_ainf _root_.Reformulated.AutPerF.Tilt.untilt_zero
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]

theorem AinfInv.kerTheta_le_comap (f : R →+* S) :
    AinfInv.kerTheta p R ≤ (AinfInv.kerTheta p S).comap (AinfInv.map p f) := by
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, AinfInv.theta_map, RingHom.mem_ker.1 hx, map_zero]

namespace BdRPlus

def map (f : R →+* S) : BdRPlus p R →+* BdRPlus p S :=
  adicMap _ _ (AinfInv.map p f) (AinfInv.kerTheta_le_comap p f)

variable {p}

@[simp] theorem map_algebraMap (f : R →+* S) (x : AinfInv p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (AinfInv.map p f x) :=
  adicMap_algebraMap _ _ _ _ x

@[simp] theorem map_algebraMap_ainf (f : R →+* S) (x : Ainf p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Ainf.map p f x) := by
  rw [IsScalarTower.algebraMap_apply _ (AinfInv p R), map_algebraMap, AinfInv.map_algebraMap,
    ← IsScalarTower.algebraMap_apply]

end BdRPlus

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.EqZeroOfPMulEqZero
attribute [-simp] _root_.Reformulated.AutPerF.Ainf.theta_xi _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap_ainf _root_.Reformulated.AutPerF.BdRPlus.theta_algebraMap_ainf _root_.Reformulated.AutPerF.Tilt.untilt_zero
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

section Adic

variable {A : Type u} [CommRing A]

theorem descFactorial_pred_modEq {m k : ℕ} (hk : k < m) :
    ∃ c : ℤ, ((m - 1).descFactorial k : ℤ) = (-1) ^ k * (k ! : ℤ) + m * c := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih (by omega)
    have h : ((m - 1 - k : ℕ) : ℤ) = m - (k + 1) := by omega
    refine ⟨(-1) ^ k * (k ! : ℤ) + (m - (k + 1)) * c, ?_⟩
    rw [Nat.descFactorial_succ, Nat.cast_mul, h, hc, Nat.factorial_succ]
    push_cast
    ring

theorem mul_sum_descFactorial {B : Type*} [CommRing B] [Algebra ℚ B] (m : ℕ) (x : B) :
    (m : B) * ∑ k ∈ Finset.range m,
      ((m - 1).descFactorial k : B) * ((((k + 1) ! : ℕ) : ℚ)⁻¹ • x ^ (k + 1)) = (x + 1) ^ m - 1 := by
  rw [add_pow, Finset.sum_range_succ', Finset.mul_sum]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := Finset.mem_range.1 hk; omega⟩
  rw [← mul_assoc, ← Nat.cast_mul, Nat.add_sub_cancel, ← Nat.succ_descFactorial_succ,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Algebra.smul_def,
    ← map_natCast (algebraMap ℚ B) (k + 1)!]
  have : algebraMap ℚ B ((k + 1)! : ℕ) * algebraMap ℚ B (((k + 1)! : ℕ) : ℚ)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one]
  linear_combination (((m + 1).choose (k + 1) : ℕ) : B) * x ^ (k + 1) * this

end Adic

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

namespace AcrisZero

@[simp] theorem coe_gamma (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (gamma n x hx : AinfInv p R) = AinfInv.gamma n (algebraMap _ _ x) := rfl

theorem p_pow_mul_cancel (n : ℕ) {x y : AcrisZero p R} (h : (p : AcrisZero p R) ^ n * x = p ^ n * y) :
    x = y := by
  apply Subtype.ext
  have h' := congrArg (Subtype.val) h
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast] at h'
  exact ((AinfInv.isUnit_p p).pow n).mul_left_cancel h'

theorem mem_span_pow_iff (n : ℕ) (x : AcrisZero p R) :
    x ∈ span {(p : AcrisZero p R)} ^ n ↔ (p : AcrisZero p R) ^ n ∣ x := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem factorial_mul_gamma (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (n ! : AcrisZero p R) * gamma n x hx = algebraMap (Ainf p R) _ x ^ n := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, coe_gamma,
    AinfInv.gamma, Subalgebra.coe_algebraMap]
  rw [Algebra.smul_def, ← map_natCast (algebraMap ℚ (AinfInv p R)), ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one, one_mul]

end AcrisZero

namespace Acris

theorem exists_quot (u : Ainf p R) (hu : Ainf.theta p R u = 1) (n : ℕ) :
    ∃ l : AcrisZero p R, (p : AcrisZero p R) ^ n * l = algebraMap (Ainf p R) _ u ^ p ^ n - 1 ∧
      eval p R n (log u hu) = Ideal.Quotient.mk _ l := by
  refine ⟨∑ k ∈ Finset.range (p ^ n), ((p ^ n - 1).descFactorial k : AcrisZero p R) *
    AcrisZero.gamma (k + 1) (u - 1) (by simp [hu]), ?_, ?_⟩
  · apply Subtype.ext
    have := mul_sum_descFactorial (p ^ n) (algebraMap (Ainf p R) (AinfInv p R) (u - 1))
    rw [← map_one (algebraMap (Ainf p R) (AinfInv p R)), ← map_add, sub_add_cancel, map_one,
      Nat.cast_pow] at this
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast,
      AddSubmonoidClass.coe_finset_sum, AcrisZero.coe_gamma, AinfInv.gamma,
      AddSubgroupClass.coe_sub, OneMemClass.coe_one, Subalgebra.coe_algebraMap]
    exact this
  · rw [eval_log u hu le_rfl, Ideal.Quotient.eq, logPartial, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun k hk => ?_
    rw [← sub_mul]
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨c, hc⟩ := descFactorial_pred_modEq (Finset.mem_range.1 hk)
    have hc' := congrArg (Int.cast : ℤ → AcrisZero p R) hc
    push_cast at hc'
    rw [AcrisZero.mem_span_pow_iff, hc']
    exact ⟨-c, by ring⟩

theorem eval_log_of_mul_eq (u : Ainf p R) (hu : Ainf.theta p R u = 1) (n : ℕ) (l : AcrisZero p R)
    (hl : (p : AcrisZero p R) ^ n * l = algebraMap (Ainf p R) _ u ^ p ^ n - 1) :
    eval p R n (log u hu) = Ideal.Quotient.mk _ l := by
  obtain ⟨l', h1, h2⟩ := exists_quot u hu n
  rw [h2, AcrisZero.p_pow_mul_cancel n (h1.trans hl.symm)]

theorem log_congr {u v : Ainf p R} (hu : Ainf.theta p R u = 1) (hv : Ainf.theta p R v = 1)
    (h : u = v) : log u hu = log v hv := by subst h; rfl

theorem log_mul (u v : Ainf p R) (hu : Ainf.theta p R u = 1) (hv : Ainf.theta p R v = 1)
    (huv : Ainf.theta p R (u * v) = 1) : log (u * v) huv = log u hu + log v hv := by
  refine ext_eval fun n => ?_
  obtain ⟨a, ha, ha'⟩ := exists_quot u hu n
  obtain ⟨b, hb, hb'⟩ := exists_quot v hv n
  rw [map_add, ha', hb', eval_log_of_mul_eq _ huv n (a + b + p ^ n * a * b), ← map_add,
    Ideal.Quotient.eq, AcrisZero.mem_span_pow_iff]
  · exact ⟨a * b, by ring⟩
  · rw [map_mul, mul_pow, eq_add_of_sub_eq ha.symm, eq_add_of_sub_eq hb.symm]
    ring

@[simp] theorem log_one (h : Ainf.theta p R 1 = 1) : log (1 : Ainf p R) h = 0 :=
  ext_eval fun n => by rw [eval_log_of_mul_eq _ h n 0 (by simp), map_zero, map_zero]

theorem logTeich_mul (η η' : tateModule p R) : logTeich (η * η') = logTeich η + logTeich η' := by
  unfold logTeich
  rw [← log_mul _ _ _ _ (by
    rw [map_mul, Ainf.theta_teich, Ainf.theta_teich, show PreTilt.untilt η.1 = 1 from η.2,
      show PreTilt.untilt η'.1 = 1 from η'.2, one_mul])]
  exact log_congr _ _ (map_mul _ _ _)

@[simp] theorem logTeich_one : logTeich (1 : tateModule p R) = 0 :=
  (log_congr _ (map_one _) (map_one _)).trans (log_one _)

theorem logTeich_pow (η : tateModule p R) (m : ℕ) : logTeich (η ^ m) = m * logTeich η := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, logTeich_mul, ih]; push_cast; ring

end Acris

namespace Bcris

@[simp] theorem logTeich_one : logTeich (1 : tateModule p R) = 0 := by simp [logTeich]

theorem isUnit_logTeich {ε : tateModule p R} (h : IsPrimitive ε) : IsUnit (logTeich ε) :=
  IsLocalization.map_units (M := BcrisPlus.periods p R) (Bcris p R)
    ⟨_, Submonoid.subset_closure ⟨ε, h, rfl⟩⟩

theorem isUnit_p : IsUnit (p : Bcris p R) := by
  simpa using (BcrisPlus.isUnit_p p R).map (algebraMap _ (Bcris p R))

end Bcris

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
attribute [-simp] _root_.Reformulated.AutPerF.Ainf.theta_xi _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap_ainf _root_.Reformulated.AutPerF.BdRPlus.theta_algebraMap_ainf _root_.Reformulated.AutPerF.Tilt.untilt_zero
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

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

@[simp] theorem map_logTeich (f : R →+* S) (hf : Function.Injective f) (η : tateModule p R) :
    map p f hf (logTeich η) = logTeich (tateModule.map p f η) := by
  simp [logTeich]

end Bcris

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
attribute [-instance] _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal Filter Topology

namespace Reformulated.AutPerF

universe u v

class IsUnitBall {C : Type u} [NormedField C] (O : ValuationSubring C) : Prop where
  mem_iff : ∀ x : C, x ∈ O ↔ ‖x‖ ≤ 1

namespace IsUnitBall

variable {C : Type u} [NormedField C] (O : ValuationSubring C) [IsUnitBall O]

variable {O} in
theorem norm_le_one (x : O) : ‖(x : C)‖ ≤ 1 := (mem_iff x.1).1 x.2

variable {O} in
theorem dvd_iff_norm_le (x y : O) : x ∣ y ↔ ‖(y : C)‖ ≤ ‖(x : C)‖ := by
  constructor
  · rintro ⟨c, rfl⟩
    push_cast
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one c)
  · intro h
    by_cases hx : (x : C) = 0
    · rw [hx, norm_zero, norm_le_zero_iff] at h
      rw [show y = 0 from Subtype.ext h]
      exact dvd_zero _
    · refine ⟨⟨(y : C) / x, (mem_iff _).2 ?_⟩, Subtype.ext ?_⟩
      · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · push_cast; field_simp

variable {O} in
theorem isUnit_iff_norm_eq_one (x : O) : IsUnit x ↔ ‖(x : C)‖ = 1 := by
  rw [isUnit_iff_dvd_one, dvd_iff_norm_le]
  push_cast
  rw [norm_one]
  exact ⟨fun h => le_antisymm (norm_le_one x) h, fun h => h.ge⟩

variable (p : ℕ)

theorem mem_span_pow_iff (n : ℕ) (x : O) :
    x ∈ (span {(p : O)} ^ n • ⊤ : Submodule O O) ↔ ‖(x : C)‖ ≤ ‖(p : C)‖ ^ n := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    dvd_iff_norm_le]
  push_cast
  rw [norm_pow]

variable [hp : Fact (‖(p : C)‖ < 1)]

instance instFactNotIsUnitSubtypeMemValuationSubringCast : Fact ¬IsUnit (p : O) :=
  ⟨by rw [isUnit_iff_norm_eq_one]; exact_mod_cast hp.out.ne⟩

instance instIsAdicCompleteSubtypeMemValuationSubringSpanSingletonSetCastOfCompleteSpace [CompleteSpace C] : IsAdicComplete (span {(p : O)}) O where
  haus' x hx := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : C)) hp.out
    have : ‖(x : C)‖ ≤ 0 := ge_of_tendsto' ht fun n => by
      have := hx n
      rwa [SModEq.zero, mem_span_pow_iff] at this
    exact Subtype.ext (norm_le_zero_iff.1 this)
  prec' f hf := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : C)) hp.out
    have h1 : ∀ m n, m ≤ n → dist (f m : C) (f n) ≤ ‖(p : C)‖ ^ m := fun m n h => by
      have := hf h
      rw [SModEq.sub_mem, mem_span_pow_iff] at this
      rw [dist_eq_norm]
      exact_mod_cast this
    have hc : CauchySeq fun n => (f n : C) := cauchySeq_of_le_tendsto_0' _ h1 ht
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun n => norm_le_one (f n)
    refine ⟨⟨L, (mem_iff L).2 hL1⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_span_pow_iff]
    have : dist (f n : C) L ≤ ‖(p : C)‖ ^ n :=
      le_of_tendsto (tendsto_const_nhds.dist hL)
        (eventually_atTop.2 ⟨n, fun m hm => h1 n m hm⟩)
    rw [dist_eq_norm] at this
    exact_mod_cast this

instance instAwaySubtypeMemValuationSubringCastOfCharZeroOfNeZeroNat [CharZero C] [NeZero p] : IsLocalization.Away (p : O) C where
  map_units := by
    rintro ⟨_, n, rfl⟩
    simp only [map_pow, map_natCast]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (NeZero.ne p))).pow n
  surj z := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : C)) hp.out).const_mul ‖z‖
    rw [mul_zero] at ht
    obtain ⟨n, hn⟩ := (ht.eventually_le_const zero_lt_one).exists
    refine ⟨⟨⟨z * p ^ n, (mem_iff _).2 (by rwa [norm_mul, norm_pow])⟩, ⟨_, n, rfl⟩⟩, ?_⟩
    simp only [map_pow, map_natCast]
    rfl
  exists_of_eq h := ⟨1, by rw [show _ = _ from Subtype.ext h]⟩

def awayEquiv [CharZero C] [NeZero p] : Localization.Away (p : O) ≃ₐ[O] C :=
  IsLocalization.algEquiv (Submonoid.powers (p : O)) _ _

@[simp] theorem awayEquiv_algebraMap [CharZero C] [NeZero p] (x : O) :
    awayEquiv O p (algebraMap O _ x) = (x : C) := (awayEquiv O p).commutes x

omit hp in
variable {O} in

def restrict {C' : Type*} [NormedField C'] (O' : ValuationSubring C') [IsUnitBall O']
    (f : C →+* C') (hf : ∀ x, ‖f x‖ ≤ ‖x‖) : O →+* O' :=
  (f.comp O.subtype).codRestrict O' fun x => (mem_iff _).2 ((hf _).trans (norm_le_one x))

omit hp in
variable {O} in
@[simp] theorem coe_restrict {C' : Type*} [NormedField C'] (O' : ValuationSubring C')
    [IsUnitBall O'] (f : C →+* C') (hf : ∀ x, ‖f x‖ ≤ ‖x‖) (x : O) :
    (restrict O' f hf x : C') = f x := rfl

section Action

variable (G : Type v) [Monoid G] [MulSemiringAction G C] [IsIsometricSMul G C]

omit hp in
theorem norm_smul_eq (g : G) (x : C) : ‖g • x‖ = ‖x‖ := by
  simpa using (isometry_smul C g).dist_eq x 0

omit hp in

instance : MulSemiringAction G O where
  smul g x := ⟨g • (x : C), (mem_iff _).2 (by rw [norm_smul_eq]; exact norm_le_one x)⟩
  one_smul x := Subtype.ext (one_smul G (x : C))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : C))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g (x : C) y)
  smul_one g := Subtype.ext (smul_one g)
  smul_mul g x y := Subtype.ext (smul_mul' g (x : C) y)

omit hp in
variable {O G} in
@[simp] theorem coe_smul (g : G) (x : O) : ((g • x : O) : C) = g • (x : C) := rfl

end Action

end IsUnitBall

section PadicComplex

variable (p : ℕ) [Fact p.Prime]

instance instIsUnitBallPadicComplexPadicComplexInt : IsUnitBall (PadicComplexInt p) :=
  ⟨fun x => by
    rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm,
      Valuation.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]⟩

instance instFactLtRealNormPadicComplexCastOfNat_solutions : Fact (‖(p : ℂ_[p])‖ < 1) :=
  ⟨by
    rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
      ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p))]
    exact (PadicAlgCl.norm_extends p p).trans_lt Padic.norm_p_lt_one⟩

end PadicComplex

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.Per

open Reformulated.AutPerF

section Cp
abbrev OC (p : ℕ) [Fact p.Prime] : Type := ↥(PadicComplexInt p)
end Cp

section Explicit
variable (l : ℕ) [Fact l.Prime]
scoped instance instFactNotIsUnitOCCast : Fact (¬ IsUnit ((l : ℕ) : OC l)) := inferInstance
scoped instance instIsAdicCompleteOCSpanSingletonSetCast : IsAdicComplete (Ideal.span {((l : ℕ) : OC l)}) (OC l) := inferInstance
abbrev Ainf : Type := Reformulated.AutPerF.Ainf l (OC l)
end Explicit

end Formalism.Per
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalRingCardinality.DataArith
attribute [-instance] _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.BasicNotions

structure HLat (K : Type) [Field K] [NumberField K] [StarRing K] where
  V : Type
  [addV : AddCommGroup V]
  [modV : Module K V]
  [modOV : Module (𝓞 K) V]
  [towV : IsScalarTower (𝓞 K) K V]
  ι : Type
  [finι : Fintype ι]
  [decι : DecidableEq ι]
  b : Basis ι K V
  X : InfinitePlace K → Matrix ι ι ℂ
  L : Submodule (𝓞 K) V

attribute [instance] HLat.addV HLat.modV HLat.modOV HLat.towV HLat.finι HLat.decι

end Formalism.BasicNotions
end
end

section
-- module Solutions.AlpoGe.Formalism.WeaklyAdmissibleFiltrations.Statement
attribute [-instance] _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

structure PeriodData (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] where
  p : ℕ
  hp : p.Prime
  finK₀ : FiniteDimensional Qp K₀
  finK : FiniteDimensional Qp K
  σ : K₀ →ₐ[Qp] K₀
  σ_bij : Function.Bijective σ
  actB : G →* (B ≃ₐ[K₀] B)
  invB : ∀ b : B, (∀ g, actB g b = b) → ∃ c : K₀, algebraMap K₀ B c = b
  φ : B →ₐ[Qp] B
  φ_inj : Function.Injective φ
  φ_K₀ : ∀ c : K₀, φ (algebraMap K₀ B c) = algebraMap K₀ B (σ c)
  φ_comm : ∀ g b, φ (actB g b) = actB g (φ b)
  actdR : G →* (BdR ≃ₐ[K] BdR)
  invdR : ∀ b : BdR, (∀ g, actdR g b = b) → ∃ c : K, algebraMap K BdR c = b
  ι : B →ₐ[K₀] BdR
  ι_inj : Function.Injective ι
  ι_comm : ∀ g b, ι (actB g b) = actdR g (ι b)
  Fil : ℤ → Submodule K BdR
  Fil_anti : ∀ a, Fil (a + 1) ≤ Fil a
  one_mem : (1 : BdR) ∈ Fil 0
  Fil_mul : ∀ a b x y, x ∈ Fil a → y ∈ Fil b → x * y ∈ Fil (a + b)
  Fil_exh : ∀ x, ∃ a, x ∈ Fil a
  Fil_sep : ∀ x, (∀ a, x ∈ Fil a) → x = 0
  Fil_G : ∀ g a x, x ∈ Fil a → actdR g x ∈ Fil a
  χ : G →* Qpˣ
  t : B
  t_unit : IsUnit t
  t_act : ∀ g, actB g t = ((χ g : Qpˣ) : Qp) • t
  t_φ : φ t = (p : Qp) • t
  mem_filtration_one : ι t ∈ Fil 1
  not_mem_filtration_two : ι t ∉ Fil 2
  fund : ∀ b : B, φ b = b → ι b ∈ Fil 0 → ∃ c : Qp, algebraMap Qp B c = b

section Galois

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

def actVB (g : G) : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.map (ρ g) (((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp)

def actVdR (g : G) : V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR :=
  AlgebraTensorModule.map (ρ g) (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp)

def Dcris : Submodule LL (V ⊗[Qp] B) :=
  ⨅ g : G, LinearMap.ker (actVB PD ρ g - LinearMap.id)

def DdR : Submodule LL (V ⊗[Qp] BdR) :=
  ⨅ g : G, LinearMap.ker (actVdR PD ρ g - LinearMap.id)

def mulVdR (c : K) : V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp (algebraMap K BdR c))

def DdRE (τ : K →ₐ[Qp] LL) : Submodule LL (V ⊗[Qp] BdR) :=
  DdR PD ρ ⊓ ⨅ c : K, LinearMap.ker (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c - τ c • LinearMap.id)

def FilV (a : ℤ) : Submodule LL (V ⊗[Qp] BdR) :=
  LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
    ((PD.Fil a).restrictScalars Qp).subtype)

def FildR (τ : K →ₐ[Qp] LL) (a : ℤ) : Submodule LL (V ⊗[Qp] BdR) :=
  DdRE PD ρ τ ⊓ FilV PD (LL := LL) (V := V) a

def IsCrys : Prop := finrank LL ↥(Dcris PD ρ) = finrank Qp K₀ * finrank LL V

end Galois

section Ops

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}

def multV (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) : ℤ :=
  (finrank LL ↥(FildR PD ρ τ a) : ℤ) - finrank LL ↥(FildR PD ρ τ (a + 1))

end Ops

end Formalism.WeaklyAdmissibleFiltrations
end
end

section
-- module Solutions.AlpoGe.Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
attribute [-instance] _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instFactNotIsUnitSubtypeMemValuationSubringCast _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.BasicNotions

open Formalism.WeaklyAdmissibleFiltrations PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

section Fam

namespace Loc

variable (l : ℕ) [Fact l.Prime]

abbrev Om : Type := PadicAlgCl l

abbrev GQ : Type := Om l ≃ₐ[ℚ_[l]] Om l

def MaximalUnramifiedExtension : IntermediateField ℚ_[l] (Om l) :=
  IntermediateField.adjoin ℚ_[l] {x | ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ^ m = 1}

abbrev FinExt : Type := {K : IntermediateField ℚ_[l] (Om l) // FiniteDimensional ℚ_[l] K}

variable {l}

def K0 (K : FinExt l) : IntermediateField ℚ_[l] (Om l) := K.1 ⊓ MaximalUnramifiedExtension l

def GK (K : FinExt l) : Subgroup (GQ l) := K.1.fixingSubgroup

def OL (LL : FinExt l) : Subalgebra ℤ_[l] ↥LL.1 := integralClosure ℤ_[l] ↥LL.1

instance maxUnramifiedAlgebra (K : FinExt l) : Algebra ↥(K0 K) ↥K.1 :=
  (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toAlgebra

instance maxUnramifiedScalarTower (K : FinExt l) : IsScalarTower ℚ_[l] ↥(K0 K) ↥K.1 :=
  IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.ext
    rfl

end Loc

open Loc

variable {l : ℕ} [Fact l.Prime]

structure LocRings (l : ℕ) [Fact l.Prime] where
  B : Type
  BdR : Type
  [rB : CommRing B]
  [rdR : CommRing BdR]
  [aQB : Algebra ℚ_[l] B]
  [aUB : Algebra ↥(MaximalUnramifiedExtension l) B]
  [tUB : IsScalarTower ℚ_[l] ↥(MaximalUnramifiedExtension l) B]
  [aOdR : Algebra (Om l) BdR]
  [aQdR : Algebra ℚ_[l] BdR]
  [tQdR : IsScalarTower ℚ_[l] (Om l) BdR]

attribute [instance] LocRings.rB LocRings.rdR LocRings.aQB LocRings.aUB LocRings.tUB LocRings.aOdR
  LocRings.aQdR LocRings.tQdR

instance maxUnramifiedCrisAlgebra (R : LocRings l) (K : FinExt l) : Algebra ↥(K0 K) R.B :=
  ((algebraMap ↥(MaximalUnramifiedExtension l) R.B).comp
    (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)).toRingHom).toAlgebra

instance maxUnramifiedCrisTower (R : LocRings l) (K : FinExt l) : IsScalarTower ℚ_[l] ↥(K0 K) R.B :=
  IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap ℚ_[l] R.B x = algebraMap ↥(MaximalUnramifiedExtension l) R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x)
    exact IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) R.B x

instance maxUnramifiedDeRhamTower (R : LocRings l) (K : FinExt l) : IsScalarTower ↥(K0 K) ↥K.1 R.BdR :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

structure LocPrime (l : ℕ) [Fact l.Prime] where
  R : LocRings l
  PD : ∀ K : FinExt l, PeriodData ↥(GK K) ℚ_[l] ↥(K0 K) ↥K.1 R.B R.BdR
  actQ : GQ l →* (R.B ≃ₐ[ℚ_[l]] R.B)
  actQdR : GQ l →* (R.BdR ≃ₐ[ℚ_[l]] R.BdR)
  φB : R.B →ₐ[ℚ_[l]] R.B
  ιB : R.B →ₐ[ℚ_[l]] R.BdR
  tB : R.B
  χQ : GQ l →* ℚ_[l]ˣ
  PD_p : ∀ K : FinExt l, (PD K).p = l
  PD_actB : ∀ (K : FinExt l) (g : ↥(GK K)) b, (PD K).actB g b = actQ (g : GQ l) b
  PD_actdR : ∀ (K : FinExt l) (g : ↥(GK K)) b, (PD K).actdR g b = actQdR (g : GQ l) b
  PD_φ : ∀ (K : FinExt l) b, (PD K).φ b = φB b
  PD_ι : ∀ (K : FinExt l) b, (PD K).ι b = ιB b
  period_datum_t_eq : ∀ K : FinExt l, (PD K).t = tB
  PD_χ : ∀ (K : FinExt l) (g : ↥(GK K)), (((PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = χQ (g : GQ l)
  PD_Fil : ∀ (K K' : FinExt l) a, (((PD K).Fil a : Submodule ↥K.1 R.BdR) : Set R.BdR) = ((PD K').Fil a : Set R.BdR)

  actQ_Kur : ∀ (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)), g (c : Om l) = (c' : Om l) →
    actQ g (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) R.B c'
  actQdR_Om : ∀ (g : GQ l) (x : Om l), actQdR g (algebraMap (Om l) R.BdR x) = algebraMap (Om l) R.BdR (g x)

  PD_σ : ∀ (K : FinExt l) (x : ↥(K0 K)), ‖((x : ↥(K0 K)) : Om l)‖ ≤ 1 →
    ‖((((PD K).σ x : ↥(K0 K))) : Om l) - ((x : ↥(K0 K)) : Om l) ^ l‖ < 1

  χQ_cyc : ∀ (g : GQ l) (m : ℕ) (ζ : Om l), ζ ^ (l ^ m) = 1 →
    ∃ a : ℕ, ‖(χQ g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g ζ = ζ ^ a

  ζQ : ℕ → Om l
  ζQ_zero : ζQ 0 = 1
  ζQ_succ : ∀ m, ζQ (m + 1) ^ l = ζQ m
  ζQ_one : ζQ 1 ≠ 1

  v : ∀ LL : FinExt l, AddValuation ↥LL.1 (WithTop ℚ)
  v_l : ∀ LL : FinExt l, v LL (l : ↥LL.1) = 1
  v_O : ∀ (LL : FinExt l) (x : ↥LL.1), 0 ≤ v LL x ↔ x ∈ OL LL

end Fam

section Bridge

open Loc

variable {l : ℕ} [Fact l.Prime]

structure LocBridge (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω]
    (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] where
  Kw : FinExt l
  j : Ω →+* Om l
  j_E : ∀ x : E, j (algebraMap E Ω x) ∈ Kw.1
  j_dense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range fun x : E => j (algebraMap E Ω x))
  e : ↥Gw ≃* ↥(GK Kw)
  e_cont : Continuous e
  e_symm_cont : Continuous e.symm
  e_comm : ∀ (g : ↥Gw) (x : Ω), ((e g : ↥(GK Kw)) : GQ l) (j x) = j ((g : Ω ≃ₐ[E] Ω) x)
  LL : FinExt l

  LL_split : ∀ (τ : ↥Kw.1 →ₐ[ℚ_[l]] Om l) (x : ↥Kw.1), τ x ∈ LL.1
  eO : O ≃+* ↥(OL LL)

  eO_alg : ∀ z : ℤ_[l], eO (algebraMap ℤ_[l] O z) = algebraMap ℤ_[l] ↥(OL LL) z
  eO_cont : Continuous eO
  eO_symm_cont : Continuous eO.symm

end Bridge

section BridgeDefs

open Loc

variable {l : ℕ} [Fact l.Prime]

theorem GK_le {K K' : FinExt l} (h : K.1 ≤ K'.1) : GK K' ≤ GK K := fun _ hg x => hg ⟨x.1, h x.2⟩

end BridgeDefs

end Formalism.BasicNotions

namespace Formalism.BasicNotions

open Loc NNReal

namespace Loc

variable (l : ℕ) [Fact l.Prime]

theorem OC_l_not_unit : ¬ IsUnit ((l : ℕ) : PadicComplexInt l) := by
  intro h
  have h1 := ((PadicComplexInt.integers l).isUnit_iff_valuation_eq_one).mp h
  have h2 : (PadicComplex.valued l).v
      (algebraMap (PadicComplexInt l) (PadicComplex l) ((l : ℕ) : PadicComplexInt l))
      = 1 / (l : ℝ≥0) := by
    rw [map_natCast]
    exact PadicComplex.valuation_p l
  rw [h1] at h2
  have hl : (2 : ℝ≥0) ≤ (l : ℝ≥0) := by exact_mod_cast (Fact.out : l.Prime).two_le
  have : (1 : ℝ≥0) / (l : ℝ≥0) < 1 := by
    rw [div_lt_one (by positivity)]
    exact lt_of_lt_of_le (by norm_num) hl
  exact absurd h2 (ne_of_gt this)

instance factOC : Fact (¬ IsUnit ((l : ℕ) : PadicComplexInt l)) := ⟨OC_l_not_unit l⟩

abbrev OC : Type := ↥(PadicComplexInt l)

abbrev OCb : Type := PreTilt (OC l) l

abbrev Ainf : Type := WittVector l (OCb l)

instance domOCb : IsDomain (OCb l) :=
  PreTilt.isDomain (PadicComplex l) (PadicComplex.valued l).v (OC l) (PadicComplexInt.integers l) l

end Loc

structure LocAinf (l : ℕ) [Fact l.Prime] (P : LocPrime l) where

  actC : GQ l →* (PadicComplex l ≃+* PadicComplex l)
  actC_ext : ∀ (g : GQ l) (x : Om l), actC g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l)
  actC_norm : ∀ (g : GQ l) (y : PadicComplex l), ‖actC g y‖ = ‖y‖

  actT : GQ l →* (OCb l ≃+* OCb l)
  actT_coeff : ∀ (g : GQ l) (x : OCb l) (n : ℕ) (y : OC l),
    PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y →
      ∃ y' : OC l, (y' : PadicComplex l) = actC g (y : PadicComplex l) ∧
        PreTilt.coeff n (actT g x) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y'

  ζ : ℕ → OC l
  ζ_zero : ζ 0 = 1
  ζ_succ : ∀ n, ζ (n + 1) ^ l = ζ n
  ζ_one : ζ 1 ≠ 1

  ε : OCb l
  ε_coeff : ∀ n, PreTilt.coeff n ε = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (ζ n)

  ιA : Ainf l →+* P.R.B
  ιA_inj : Function.Injective ιA
  ιA_act : ∀ (g : GQ l) (a : Ainf l),
    ιA (WittVector.map (actT g : OCb l ≃+* OCb l).toRingHom a) = P.actQ g (ιA a)
  ιA_φ : ∀ a : Ainf l, ιA (WittVector.frobenius a) = P.φB (ιA a)

  ζ_eq : ∀ m, ((ζ m : OC l) : PadicComplex l) = ((P.ζQ m : Om l) : PadicComplex l)

  ainf_image_mem_filtration_zero : ∀ (K : FinExt l) (a : Ainf l), P.ιB (ιA a) ∈ (P.PD K).Fil 0
  ainf_image_mem_filtration_one_iff : ∀ (K : FinExt l) (a : Ainf l), P.ιB (ιA a) ∈ (P.PD K).Fil 1 ↔
    ∃ b : Ainf l, a = (∑ i ∈ Finset.range l,
      (WittVector.teichmuller l ((frobeniusEquiv (OCb l) l).symm ε)) ^ i) * b

  ιA_teich : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ xb : OCb l,
    (∀ k : ℕ, ∃ y : OC l, (y : PadicComplex l) ^ (l ^ k) = ((c : Om l) : PadicComplex l) ∧ y ^ m = 1 ∧
      PreTilt.coeff k xb = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) →
    ιA (WittVector.teichmuller l xb) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c

end Formalism.BasicNotions
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalRingCardinality.DataJet
attribute [-instance] _root_.Formalism.BasicNotions.Loc.factOC _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Classical

namespace Formalism.BasicNotions

structure JetLoc where

  l : ℕ
  [hl : Fact l.Prime]

  five_le_l : 5 ≤ l

  d : ℕ
  [hd : NeZero d]
  d_even : Even d
  two_le_d : 2 ≤ d

  N0 : ℕ
  N1 : ℕ

  Th : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]

attribute [instance] JetLoc.hl JetLoc.hd

structure JetLoc1 where
  l : ℕ
  [hl : Fact l.Prime]

  five_le_l : 5 ≤ l
  N0 : ℕ
  N1 : ℕ

  Th : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[l]

attribute [instance] JetLoc1.hl

end Formalism.BasicNotions

end
end

section
-- module Solutions.AlpoGe.Formalism.SharpRestriction.LevelLetterCocycles.DataN
attribute [-instance] _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.BasicNotions

open Loc Formalism.WeaklyAdmissibleFiltrations

namespace LocBridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

def repE (LL' : FinExt l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) ↥LL'.1) :
    Representation ↥LL'.1 ↥(GK Bw.Kw) (Fin m → ↥LL'.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
    ((Units.coeHom _).comp (r.comp Bw.e.symm.toMonoidHom))

def IsCrysE (P : LocPrime l) (LL' : FinExt l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) ↥LL'.1) : Prop :=
  IsCrys (P.PD Bw.Kw) (Bw.repE LL' r)

def IsdRE (P : LocPrime l) (LL' : FinExt l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) ↥LL'.1) : Prop :=
  Module.finrank ↥LL'.1 ↥(DdR (P.PD Bw.Kw) (Bw.repE LL' r)) = Module.finrank ℚ_[l] ↥Bw.Kw.1 * m

def multE (P : LocPrime l) (LL' : FinExt l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) ↥LL'.1)
    (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (a : ℤ) : ℤ :=
  multV (P.PD Bw.Kw) (Bw.repE LL' r) τ a

end LocBridge

end Formalism.BasicNotions

end
end

section
-- module Solutions.AlpoGe.Formalism.LocalRingCardinality.DataDIV
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology MvPolynomial Finset

namespace Formalism.BasicNotions.DV

open Formalism.BasicNotions

structure Geo (F : Type) [Field F] [NumberField F] [StarRing F] where

  Var : Type

  dim : Var → ℕ

  Fn : Var → Type
  [fnField : ∀ Y, Field (Fn Y)]
  [fnAlg : ∀ Y, Algebra F (Fn Y)]

  Dv : Var → Type
  [dvGrp : ∀ Y, AddCommGroup (Dv Y)]

  Eff : ∀ Y, Dv Y → Prop
  eff_zero : ∀ Y, Eff Y 0
  eff_add : ∀ Y a b, Eff Y a → Eff Y b → Eff Y (a + b)

  H0 : ∀ Y, Dv Y → Submodule F (Fn Y)
  degreeZeroCohomology_finiteDimensional : ∀ Y Δ, FiniteDimensional F (H0 Y Δ)
  mul_mem_riemannRochSpace_add : ∀ Y Δ Δ' (f g : Fn Y), f ∈ H0 Y Δ → g ∈ H0 Y Δ' → f * g ∈ H0 Y (Δ + Δ')
  riemannRoch_mono : ∀ Y Δ Δ', Eff Y (Δ' - Δ) → H0 Y Δ ≤ H0 Y Δ'

  KY : ∀ Y, Dv Y

  Cl : Var → Type

  properCl : ∀ Y, Cl Y → Prop

  subCl : ∀ Y, Cl Y → Cl Y → Prop

  supp : ∀ Y, Dv Y → Cl Y

  inter : ∀ Y, (Fin (dim Y) → Dv Y) → ℤ

  nef : ∀ Y, Dv Y → Prop

  big : ∀ Y, Dv Y → Prop

  bpf : ∀ Y, Dv Y → Set (Fn Y) → Prop

  phiBir : ∀ Y, Dv Y → Set (Fn Y) → Prop

  phiNoContr : ∀ Y, Dv Y → Set (Fn Y) → Cl Y → Prop

  vanishOn : ∀ Y, Dv Y → Fn Y → Cl Y → Prop

  hdim : ∀ Y, ℕ → Dv Y → ℕ

  pts : ∀ Y, (F →+* ℂ) → Type
  [ptsMeas : ∀ Y σ, MeasurableSpace (pts Y σ)]

  vol : ∀ Y σ, Measure (pts Y σ)

  FnC : ∀ Y, (F →+* ℂ) → Type
  [fnCRing : ∀ Y σ, CommRing (FnC Y σ)]
  [fnCAlg : ∀ Y σ, Algebra ℂ (FnC Y σ)]

  cx : ∀ Y σ, Fn Y →+* FnC Y σ
  cx_smul : ∀ Y σ (a : F) (f : Fn Y), cx Y σ (a • f) = σ a • cx Y σ f

  Met : ∀ Y, (F →+* ℂ) → Dv Y → Type

  mAdd : ∀ Y σ Δ Δ', Met Y σ Δ → Met Y σ Δ' → Met Y σ (Δ + Δ')

  mPow : ∀ Y σ Δ (k : ℕ), Met Y σ Δ → Met Y σ (k • Δ)

  fsMet : ∀ Y σ Δ {k : Type} [Fintype k], (k → FnC Y σ) → Met Y σ Δ

  pn : ∀ Y σ Δ, Met Y σ Δ → FnC Y σ → pts Y σ → ℝ

  pnK : ∀ Y σ Δ, Met Y σ Δ → FnC Y σ → pts Y σ → ℝ

  mSmooth : ∀ Y σ Δ, Met Y σ Δ → Prop

  mPsh : ∀ Y σ Δ, Met Y σ Δ → (pts Y σ → ℝ) → Prop

  redZero : ∀ Y σ, Dv Y → (Fin (dim Y) → FnC Y σ) → Set (pts Y σ) → Prop

  agreeOn : ∀ Y σ, Dv Y → FnC Y σ → FnC Y σ → Set (pts Y σ) → Prop

  resNorm : ∀ Y σ Δ, Met Y σ Δ → ∀ Δs, Met Y σ Δs → (Fin (dim Y) → FnC Y σ) → FnC Y σ →
    pts Y σ → ℝ

  Adl : Var → Type

  ofW : ∀ Y (L : Dv Y) (W : HLat F), (W.V →ₗ[F] Fn Y) → Adl Y

  twist : ∀ Y, Adl Y → (InfinitePlace F → ℝ) → (HeightOneSpectrum (𝓞 F) → ℝ) → Adl Y

  arTop : ∀ Y, Adl Y → ℝ

  arVol : ∀ Y, Adl Y → ℝ

  nefA : ∀ Y, Adl Y → Prop

  supInf : ∀ Y, Adl Y → InfinitePlace F → ℕ → Fn Y → ℝ

  supFin : ∀ Y, Adl Y → HeightOneSpectrum (𝓞 F) → ℕ → Fn Y → ℝ

  cutGood : ∀ Y, Cl Y → ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Fn Y) → (Fin (dim Y) → Fin n → 𝓞 E) → Prop

  cutHt : ∀ Y, Adl Y → ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Fn Y) → (Fin (dim Y) → Fin n → 𝓞 E) → ℝ

  cutOrd : ∀ Y (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Fn Y) → (Fin (dim Y) → Fin n → 𝓞 E) → Dv Y → Fn Y → ℕ

  resFull : ∀ Y (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Fn Y) → (Fin (dim Y) → Fin n → 𝓞 E) → ∀ (M0 : HLat F), (M0.V →ₗ[F] Fn Y) →
    Adl Y → Prop

  resDeg : ∀ Y (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Fn Y) → (Fin (dim Y) → Fin n → 𝓞 E) → ∀ (M0 : HLat F), (M0.V →ₗ[F] Fn Y) →
    Adl Y → ℝ

  supInf_ofW : ∀ Y (L : Dv Y) (W : HLat F) (ι : W.V →ₗ[F] Fn Y) (v : InfinitePlace F) (τ : ℕ)
    (f : Fn Y), supInf Y (ofW Y L W ι) v τ f =
      ⨆ y, Real.sqrt (pn Y v.embedding (τ • L) (mPow Y v.embedding L τ
        (fsMet Y v.embedding L (fun k : W.ι => ∑ i, (W.X v) i k • cx Y v.embedding (ι (W.b i)))))
        (cx Y v.embedding f) y)

  supInf_twist : ∀ Y (Lb : Adl Y) ci cf, (Function.support cf).Finite → ∀ (v : InfinitePlace F) (τ : ℕ) (f : Fn Y),
    supInf Y (twist Y Lb ci cf) v τ f = Real.exp (-((τ : ℝ) * ci v)) * supInf Y Lb v τ f
  supFin_twist : ∀ Y (Lb : Adl Y) ci cf, (Function.support cf).Finite → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : ℕ)
    (f : Fn Y), supFin Y (twist Y Lb ci cf) v τ f = Real.exp (-((τ : ℝ) * cf v)) * supFin Y Lb v τ f

  regOn : ∀ Y σ, Dv Y → FnC Y σ → Set (pts Y σ) → Prop

attribute [instance] Geo.fnField Geo.fnAlg Geo.dvGrp Geo.ptsMeas Geo.fnCRing Geo.fnCAlg

end Formalism.BasicNotions.DV

namespace Formalism.BasicNotions

open Formalism.BasicNotions.DV

namespace DV

structure ITh where

  LB : Type

  Ch : Type
  [ring : CommRing Ch]
  [alg : Algebra ℚ Ch]

  c1 : LB → Ch

  VDiv : Type
  [grp : AddCommGroup VDiv]
  [modQ : Module ℚ VDiv]

  cD : VDiv →ₗ[ℚ] Ch

  capDeg : VDiv →ₗ[ℚ] Ch →ₗ[ℚ] ℚ

  divP : VDiv

  cD_divP : cD divP = 0

  dim : ℕ

attribute [instance] ITh.ring ITh.alg ITh.grp ITh.modQ

end DV

end Formalism.BasicNotions

end
end

section
-- module Solutions.AlpoGe.Formalism.LocalRingCardinality.SpanPowerMembership.NDLocD
attribute [-instance] _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial Pointwise Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l}
  {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)

instance compact_GK (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    CompactSpace ↥K.fixingSubgroup :=
  isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed K).isCompact

end Formalism.BasicNotions.Examples₂.LB
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
attribute [-instance] _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime]

variable (LL : FinExt l)

instance instFiniteDimensionalPadicSubtypeOmMemIntermediateFieldVal : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2

instance OL_finite : Module.Finite ℤ_[l] ↥(OL LL) :=
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

instance OL_frac : IsFractionRing ↥(OL LL) ↥LL.1 :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1

end Formalism.BasicNotions.Examples₂.LB
end
end

section
-- module Solutions.AlpoGe.Formalism.Statement
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

end Formalism
end
end

section
-- module Solutions.AlpoGe.Lemmata.NearbyExistence.ExistsNear
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.fact_prime_seven _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

namespace Bl.NearbyExistence

lemma exists_near (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) :
    ∃ y : F, Valued.v (x - algebraMap F (v.adicCompletion F) y) < 1 := by
  have hn : {z : v.adicCompletion F | Valued.v (x - z) < 1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun z hz => ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_one_iff] at hz ⊢
    rwa [Valuation.map_sub_swap]
  obtain ⟨z, hz, y, rfl⟩ := mem_closure_iff_nhds.mp
    (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := F) v x) _ hn
  exact ⟨y, hz⟩

theorem goal1 :
  ∀ {F : Type} [inst : Field.{0} F] [inst_1 : NumberField.{0} F]
  (v : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} F))
  (x :
    Subtype.{1} fun (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} F v) ↦
      Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.{0, 0} F v) x),
  Exists.{1} fun (r : NumberField.RingOfIntegers.{0} F) ↦
    LT.lt.{0}
      (DFunLike.coe.{1, 1, 1} Valued.v.{0, 0}
        (HSub.hSub.{0, 0, 0} (Subtype.val.{1} x)
          (DFunLike.coe.{1, 1, 1}
            (Algebra.algebraMap.{0, 0} (NumberField.RingOfIntegers.{0} F)
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} F v))
            r)))
      1 := by
  intro F _ _ v x
  obtain ⟨y, hy⟩ := exists_near F v x.1
  have hx : Valued.v x.1 ≤ 1 := x.2
  have hyc : Valued.v (algebraMap F (v.adicCompletion F) y) ≤ 1 := by
    have e : algebraMap F (v.adicCompletion F) y = x.1 - (x.1 - algebraMap F (v.adicCompletion F) y) := by
      ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hx hy.le)
  have hyv : v.valuation F y ≤ 1 := by
    have e2 : Valued.v (algebraMap F (v.adicCompletion F) y) = v.valuation F y :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y
    rwa [e2] at hyc
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hyv 1
  refine ⟨a, ?_⟩
  have e1 : x.1 - algebraMap (NumberField.RingOfIntegers F) (v.adicCompletion F) a
      = (x.1 - algebraMap F (v.adicCompletion F) y) +
        algebraMap F (v.adicCompletion F) (y - algebraMap (NumberField.RingOfIntegers F) F a) := by
    rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers F) F (v.adicCompletion F), map_sub]
    ring
  rw [e1]
  refine Valuation.map_add_lt _ hy ?_
  have e3 : Valued.v (algebraMap F (v.adicCompletion F) (y - algebraMap (NumberField.RingOfIntegers F) F a))
      = v.valuation F (y - algebraMap (NumberField.RingOfIntegers F) F a) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [e3, Valuation.map_sub_swap]
  simpa using ha

end Bl.NearbyExistence
end


