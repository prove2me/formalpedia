-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
-- name    : Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:59:02.571808+00:00
-- url     : https://prove2.me/theorems/f51930bd-4d14-45e7-a541-da46da8c8aa1
-- title:
--   Finite Homogeneous Inf
-- statement:
--   Definitions and structural lemmas for Finite Homogeneous Inf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/FiniteHomogeneousInf.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_ExistsArBaseAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g : ℕ} {J : Type}
def SecCoord {X : Scheme.{0}} (M : LB X) {I : Type} (σ : I → M.Sec) {R : Type} [CommRing R] (x : Sp R ⟶ X) (v : I → R) : Prop :=
  ∃ τ : (M.pull x).Gen, τ.IsGen ∧ ∀ (i : I) (j : PUnit → M.ι) (h : (M.pull x).U j ≤ x ⁻¹ᵁ M.U (j PUnit.unit)),
    (x.appLE _ _ h).hom ((σ i).f (j PUnit.unit)) =
      resG (Sp R) le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) * (show Γ(Sp R, (M.pull x).U j) from (τ.s j).val)
structure MMPre (n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) where
  MM : Scheme.{0}
  s : MM ⟶ Sp o
  qproj : IsQProjOver s
  flat : Flat s
  reduced : IsReduced MM
  de : LB MM
  isLB : de.IsLB
  th : Ix g (N' ^ 2) → de.Sec
  loc : ∀ (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ MM) (v : Ix g (N' ^ 2) → R), x ≫ s = spMap β →
    SecCoord de th x v → InMM n N' I β v
  pts : ∀ (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R), InMM n N' I β v →
    ∃! x : Sp R ⟶ MM, x ≫ s = spMap β ∧ SecCoord de th x v
def TObj.Emb {N' : ℕ} {b : TBase o (N' ^ 2)} {s : S ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (m : ℕ) (T : Over S)
    (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) T)) : Prop :=
  ∃ (th : LB.Sec (Out.LPow t.A t.L 1 T)) (s1 : LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) T))
    (α : LB.Gen (LB.LinComb t.L (K := Fin 2) ![(snd T t.A).left, (snd T t.A ^ m).left] ![(m : ℤ) ^ 2, -1]))
    (U : Ix g (N' ^ 2) → Out.ThetaGrp t.A t.L ((m : ℤ) ^ 2) T),
    Out.IsGenSec t.A t.L 1 th ∧ α.IsGen ∧
    Out.IsTwistPull t.A t.L (Out.mulT t.A T m) (snd T t.A ^ m) (lift_snd _ _) ((m : ℤ) ^ 2) 1 α th s1 ∧
    (∀ a, Out.SymLift t.A t.L ((m : ℤ) ^ 2) (m ^ 2)
      (((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S) ≫ t.lab a) ^ ((N' / m) ^ 2)) (U a)) ∧
    ∀ a, Out.IsActOf t.A t.L ((m : ℤ) ^ 2) (U a) s1 (σ a)
def VeryDense {R : Type} [CommRing R] (P : Set (Ideal R)) : Prop :=
  ∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p
def objPrimes {N' : ℕ} (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) {R : Type} [CommRing R]
    (β : o →+* R) (v : Ix g (N' ^ 2) → R) : Set (Ideal R) :=
  {p | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (t : TObj g (N' ^ 2) J b (spMap x ≫ spMap β)),
    RingHom.ker x = p ∧ t.Shape Mat κ ∧ t.HasTh (𝟙 _) (fun a => x (v a))}
def ProjRep {R σ : Type} [CommRing R] (I : Ideal (MvPolynomial σ R)) {Z : Scheme.{0}} (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) : Prop :=
  M.IsLB ∧ (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Z) (v : σ → R'), x ≫ s = spMap β → SecCoord M th x v →
    Ideal.span (Set.range v) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) ∧
  ∀ (R' : Type) [CommRing R'] (β : R →+* R') (v : σ → R'), Ideal.span (Set.range v) = ⊤ → (∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) →
    ∃! x : Sp R' ⟶ Z, x ≫ s = spMap β ∧ SecCoord M th x v
def idealOf {R σ : Type} [CommRing R] {Y X : Scheme.{0}} (s : Y ⟶ Sp R) (M : LB X) (th : σ → M.Sec) (a : Y ⟶ X) :
    Ideal (MvPolynomial σ R) :=
  ⨅ (R' : Type) (_ : CommRing R') (β : R →+* R') (y : Sp R' ⟶ Y) (v : σ → R') (_ : y ≫ s = spMap β ∧ SecCoord M th (y ≫ a) v),
    RingHom.ker (MvPolynomial.eval₂Hom β v)
def graphIdeal {R σ₁ σ₂ : Type} [CommRing R] {Y X₁ X₂ : Scheme.{0}} (s : Y ⟶ Sp R) (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁)
    (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂) : Ideal (MvPolynomial (σ₁ × σ₂) R) :=
  ⨅ (R' : Type) (_ : CommRing R') (β : R →+* R') (y : Sp R' ⟶ Y) (v₁ : σ₁ → R') (v₂ : σ₂ → R')
    (_ : y ≫ s = spMap β ∧ SecCoord M₁ th₁ (y ≫ a₁) v₁ ∧ SecCoord M₂ th₂ (y ≫ a₂) v₂),
    RingHom.ker (MvPolynomial.eval₂Hom β (fun i : σ₁ × σ₂ => v₁ i.1 * v₂ i.2))
def dimDeg {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) (e : ℕ) : ℕ :=
  Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ I.restrictScalars K)
def vanIdeal {R σ Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R) : Ideal (MvPolynomial σ R) :=
  Ideal.span {F | F.IsHomogeneous d ∧ ∀ h, MvPolynomial.eval (p h) F = 0}
def CutBy {K σ Hh : Type} [Field K] (I : Ideal (MvPolynomial σ K)) (Q : Polynomial ℚ) (d : ℕ) (p : Hh → σ → K) : Prop :=
  ∀ e ≥ d, (dimDeg I e : ℚ) = Q.eval (e : ℚ) ∧ ∀ F, F.IsHomogeneous e → (F ∈ I ↔ F ∈ vanIdeal d p)
example : ¬ VeryDense {(⊥ : Ideal ℤ)} := fun h => by
  have hp : (Ideal.span {(2 : ℤ)}).IsPrime := (Ideal.span_singleton_prime two_ne_zero).2 Int.prime_two
  obtain ⟨p, rfl, -, h1, -⟩ := h _ 1 hp ((Ideal.ne_top_iff_one _).1 hp.ne_top)
  exact two_ne_zero (Ideal.mem_bot.1 (h1 (Ideal.mem_span_singleton_self (2 : ℤ))))
theorem vanIdeal_unit_one (K : Type) [Field K] (d : ℕ) : vanIdeal d (fun (_ : Unit) (_ : Unit) => (1 : K)) = ⊥ := by
  refine Ideal.span_eq_bot.2 ?_
  rintro F ⟨hF, h0⟩
  have key : ∀ m : Unit →₀ ℕ, m ≠ Finsupp.single () d → F.coeff m = 0 := by
    intro m hm
    apply hF.coeff_eq_zero
    intro hdeg
    apply hm
    ext
    simpa [Finsupp.degree_eq_sum] using hdeg
  have hF' : F = MvPolynomial.monomial (Finsupp.single () d) (F.coeff (Finsupp.single () d)) := by
    ext m
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · rw [h]
    · exact key m (Ne.symm h)
  have h1 := h0 ()
  rw [hF', MvPolynomial.eval_monomial] at h1
  simp at h1
  rw [hF', h1, map_zero]
example (K : Type) [Field K] (Q : Polynomial ℚ) (d : ℕ) :
    ¬ CutBy (⊤ : Ideal (MvPolynomial Unit K)) Q d (fun (_ : Unit) (_ : Unit) => (1 : K)) := fun h => by
  have h1 := ((h d le_rfl).2 (MvPolynomial.X () ^ d) (by simpa using (MvPolynomial.isHomogeneous_X K ()).pow d)).1 trivial
  rw [vanIdeal_unit_one, Ideal.mem_bot] at h1
  exact pow_ne_zero d (MvPolynomial.X_ne_zero ()) h1
namespace OnePoint
def unitSec (X : Scheme.{0}) : (Out.Inh.trivLB X).Sec :=
  ⟨fun _ => 1, fun _ _ => (_root_.one_mul _).symm⟩
theorem restrict_restrict {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
theorem secCoord_one {X : Scheme.{0}} {I : Type} [Unique I] {R : Type} [CommRing R] (x : Sp R ⟶ X) (v : I → R) :
    SecCoord (Out.Inh.trivLB X) (fun _ : I => unitSec X) x v ↔ IsUnit (v default) := by
  have hU : ∀ j, ((Out.Inh.trivLB X).pull x).U j = ⊤ := by
    intro j
    simp [LB.pull, LB.LinComb, LB.wchart, Out.Inh.trivLB]
  have hres : ∀ (h : (⊤ : (Sp R).Opens) ≤ ⊤) (a : Γ(Sp R, ⊤)), resG (Sp R) h a = a := by
    intro h a
    simp [resG]
  have hone : ∀ (j : PUnit.{1} → (Out.Inh.trivLB X).ι)
      (h : ((Out.Inh.trivLB X).pull x).U j ≤ x ⁻¹ᵁ (Out.Inh.trivLB X).U (j PUnit.unit)),
      (x.appLE _ _ h).hom ((unitSec X).f (j PUnit.unit)) = 1 := fun j h => map_one _
  constructor
  · rintro ⟨τ, -, hτ⟩
    have e := hτ default (fun _ => PUnit.unit)
      ((hU (fun _ => PUnit.unit)).le.trans (by simp [Out.Inh.trivLB]))
    have hu : IsUnit (resG (Sp R) (le_top : ((Out.Inh.trivLB X).pull x).U (fun _ => PUnit.unit) ≤ ⊤)
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v default))) := isUnit_iff_exists_inv.2 ⟨_, ((hone _ _).symm.trans e).symm⟩
    have hu2 := hu.map (resG (Sp R) (hU (fun _ => PUnit.unit)).ge)
    rw [restrict_restrict, hres] at hu2
    simpa using hu2.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  · intro hv
    refine ⟨⟨fun j => (Units.map ((resG (Sp R) (le_top : ((Out.Inh.trivLB X).pull x).U j ≤ ⊤)).comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toMonoidHom hv.unit)⁻¹⟩, ?_, ?_⟩
    · unfold LB.Gen.IsGen
      intro i j
      obtain rfl : i = j := Subsingleton.elim (α := PUnit.{1} → PUnit.{1}) i j
      have hg : ((Out.Inh.trivLB X).pull x).g i i = 1 := by
        apply Units.ext
        simp only [LB.pull, LB.LinComb, Out.Inh.trivLB]
        simp [res, pullU]
        erw [Units.coe_map, Units.val_one, map_one]
        rfl
      rw [hg, _root_.one_mul]
    · intro i j h
      rw [hone, Unique.eq_default i]
      simp only [Units.coe_map_inv, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.coe_comp,
        Function.comp_apply, ← map_mul, IsUnit.mul_val_inv, map_one]
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem isQProjOver_id (R : Type) [CommRing R] : IsQProjOver (𝟙 (Sp R)) := by
  classical
  refine ⟨0, ?_⟩
  have hX : (MvPolynomial.X 0 : MvPolynomial (Fin (0 + 1)) R) ∈ MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R 1 :=
    MvPolynomial.isHomogeneous_X R 0
  let L : Localization.Away (MvPolynomial.X 0 : MvPolynomial (Fin (0 + 1)) R) →+* R :=
    IsLocalization.Away.lift (MvPolynomial.X 0 : MvPolynomial (Fin (0 + 1)) R) (g := MvPolynomial.eval fun _ => (1 : R)) (by simp)
  let φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R) (MvPolynomial.X 0) →+* R :=
    L.comp (algebraMap _ _)
  have key : (φ.comp (HomogeneousLocalization.fromZeroRingHom _ _)).comp
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R 0)) = RingHom.id R := by
    ext r
    simp only [RingHom.comp_apply, φ, L, HomogeneousLocalization.algebraMap_apply, RingHom.id_apply]
    rw [show (HomogeneousLocalization.fromZeroRingHom _ _ (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R 0) r)).val =
        algebraMap (MvPolynomial (Fin (0 + 1)) R) (Localization.Away (MvPolynomial.X 0 : MvPolynomial (Fin (0 + 1)) R))
          (MvPolynomial.C r) from by
      simp [HomogeneousLocalization.fromZeroRingHom]; rfl]
    rw [IsLocalization.Away.lift_eq, MvPolynomial.eval_C]
  let i := Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι _ _ hX one_pos
  have hi : i ≫ Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R) ≫
      spMap (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R 0)) = 𝟙 (Sp R) := by
    simp only [i, Category.assoc, Proj.awayι_toSpecZero_assoc, spMap, ← Spec.map_comp]
    rw [← Spec.map_id]
    congr 1
    ext r
    exact congrArg (fun f => f r) key
  have : IsClosedImmersion (i ≫ Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R) ≫
      spMap (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R 0))) := by
    rw [hi]; infer_instance
  have : IsClosedImmersion i := IsClosedImmersion.of_comp i (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R) ≫
    spMap (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R 0)))
  exact ⟨i, inferInstance, inferInstance, hi⟩
end OnePoint
theorem inMM_zero_iff (n N' : ℕ) {R : Type} [CommRing R] (β : o →+* R) (v : Ix 0 (N' ^ 2) → R) (a : Ix 0 (N' ^ 2)) :
    InMM n N' (⊥ : Ideal (MvPolynomial (Ix 0 (N' ^ 2)) o)) β v ↔ IsUnit (v a) := by
  have hsub : ∀ b : Ix 0 (N' ^ 2), b = a := fun b => funext fun i => i.elim0
  constructor
  · rintro ⟨-, h⟩
    by_contra hu
    obtain ⟨m, hm, ham⟩ := exists_max_ideal_of_mem_nonunits hu
    obtain ⟨c, hc⟩ := h m hm.isPrime a
    rw [hsub (a + (N' / n) • c)] at hc
    exact hc ham
  · intro hu
    refine ⟨fun F hF => by rw [Ideal.mem_bot.1 hF, MvPolynomial.eval₂_zero], fun q hq b => ⟨0, ?_⟩⟩
    rw [hsub (b + (N' / n) • 0)]
    exact fun h => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
def mmPrePoint (o : Type) [CommRing o] [_root_.IsReduced o] (n N' : ℕ) :
    MMPre (g := 0) n N' (⊥ : Ideal (MvPolynomial (Ix 0 (N' ^ 2)) o)) :=
  letI : Unique (Ix 0 (N' ^ 2)) := ⟨⟨0⟩, fun _ => funext fun i => i.elim0⟩
  { MM := Sp o
    s := 𝟙 _
    qproj := OnePoint.isQProjOver_id o
    flat := inferInstance
    reduced := inferInstance
    de := Out.Inh.trivLB _
    isLB := Out.Inh.trivLB_isLB _
    th := fun _ => OnePoint.unitSec _
    loc := fun R _ β x v _ h => (inMM_zero_iff n N' β v default).2 ((OnePoint.secCoord_one x v).1 h)
    pts := fun R _ β v h => ⟨spMap β, ⟨by simp, (OnePoint.secCoord_one _ v).2 ((inMM_zero_iff n N' β v default).1 h)⟩,
      fun y hy => by simpa using hy.1⟩ }
example (n N' : ℕ) : Nonempty (mmPrePoint ℤ n N').MM := inferInstanceAs (Nonempty (PrimeSpectrum ℤ))
end GlobalTheory.ZM
end


