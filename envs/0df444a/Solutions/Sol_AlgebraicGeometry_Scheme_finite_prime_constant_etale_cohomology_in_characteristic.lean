-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_in_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-19T23:03:24.071741+00:00
-- url     : https://prove2.me/submissions/b1771511-78f2-4df7-9440-b3510c7735ea

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_AlgebraicGeometry_SmallEtaleAdditive
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper
import Theorems.Thm_AlgebraicGeometry_Scheme_smallEtale_additive_cohomology_equiv_orderedCech

noncomputable section

section

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators
open Polynomial

namespace PhilipponArtinSchreierLinear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {p : ℕ} [CharP K p] [FiniteDimensional K V]
variable (F : V →+ V) (hF : ∀ a : K, ∀ v : V, F (a • v) = a ^ p • F v)

private theorem derivative_pow_char (P : K[X]) : (P ^ p).derivative = 0 := by
  rw [derivative_pow]
  simp

private theorem derivative_ne_zero_of_neg_one {P : K[X]} (h : P.derivative = -1) :
    P.derivative ≠ 0 := by
  rw [h]
  simp

include hF in
/-- The fixed vectors form a finite set, even over an imperfect field. -/
theorem finite_fixed : Finite {v : V // F v = v} := by
  classical
  let S : Set V := {v | F v = v}
  obtain ⟨b, hb, hspan, hind⟩ := Submodule.exists_fun_fin_finrank_span_eq K S
  have hrepr (x : S) : ∃ a : _ → K, ∑ i, a i • b i = x.val := by
    apply (Submodule.mem_span_range_iff_exists_fun (R := K)).mp
    rw [hspan]
    exact Submodule.subset_span x.property
  choose a ha using hrepr
  let Q : K[X] := X ^ p - X
  have hQ : Q.derivative = -1 := by
    simp only [Q, derivative_sub, derivative_pow_char, derivative_X, zero_sub]
  letI : Finite {r : K // Q.IsRoot r} :=
    (finite_setOfPred_isRoot fun he =>
      derivative_ne_zero_of_neg_one hQ (by simp [he])).to_subtype
  have hscalar (x : S) (i) : (a x i) ^ p = a x i := by
    refine hind.eq_coords_of_eq (f := fun j => (a x j) ^ p) (g := a x) ?_ i
    calc
      (∑ j, (a x j) ^ p • b j) = F (∑ j, a x j • b j) := by
        simp only [map_sum, hF]
        exact Finset.sum_congr rfl (fun j _ => by rw [show F (b j) = b j from hb j])
      _ = x.val := (congrArg F (ha x)).trans x.property
      _ = ∑ j, a x j • b j := (ha x).symm
  let encode (x : S) (i : _) : {r : K // Q.IsRoot r} :=
    ⟨a x i, by simpa [Q, IsRoot, sub_eq_zero] using hscalar x i⟩
  refine Finite.of_injective encode ?_
  intro x y hxy
  have h : a x = a y := by
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  exact Subtype.ext ((ha x).symm.trans (h ▸ ha y))

private theorem exists_iterate_relation (v : ℕ → V) :
    ∃ n : ℕ, v (n + 1) ∈ Submodule.span K (Set.range fun i : Fin (n + 1) => v i) ∨
      v 0 = 0 := by
  classical
  let bad (n : ℕ) := ¬ LinearIndependent K (fun i : Fin (n + 1) => v i)
  have hbad : ∃ n, bad n := by
    refine ⟨Module.finrank K V, fun h => ?_⟩
    have hle := h.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hle
    exact Nat.not_succ_le_self _ hle
  generalize hk : Nat.find hbad = k
  have hd : bad k := hk ▸ Nat.find_spec hbad
  cases k with
  | zero =>
    refine ⟨0, Or.inr ?_⟩
    by_contra h
    apply hd
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hz : g 0 • v 0 = 0 := by simpa using hg
    simpa [Fin.fin_one_eq_zero i] using (smul_eq_zero.mp hz).resolve_right h
  | succ n =>
    refine ⟨n, Or.inl ?_⟩
    by_contra h
    apply hd
    apply linearIndependent_finSucc'.mpr
    refine ⟨?_, h⟩
    change LinearIndependent K (fun i : Fin (n + 1) => v i)
    by_contra hin
    have hle := Nat.find_min' hbad hin
    rw [hk] at hle
    exact Nat.not_succ_le_self _ hle

private noncomputable def coefficientPolynomial (p : ℕ) (c : ℕ → K) : ℕ → K[X]
  | 0 => C (c 0) * X ^ p - 1
  | i + 1 => coefficientPolynomial p c i ^ p + C (c (i + 1)) * X ^ p

private theorem coefficientPolynomial_derivative (c : ℕ → K) (n : ℕ) :
    (coefficientPolynomial p c n).derivative = 0 := by
  cases n <;>
    simp [coefficientPolynomial, derivative_pow_char, derivative_mul, derivative_C]

omit [CharP K p] [FiniteDimensional K V] in
private theorem sum_coefficientPolynomial_balance (v : ℕ → V) (c : ℕ → K)
    (t : K) (n : ℕ) :
    let a := fun i : ℕ => (coefficientPolynomial p c i).eval t
    (∑ i ∈ Finset.range (n + 1), (a i) ^ p • v (i + 1)) -
        (∑ i ∈ Finset.range (n + 1), a i • v i) =
      (a n) ^ p • v (n + 1) - t ^ p • (∑ i ∈ Finset.range (n + 1), c i • v i) + v 0 := by
  intro a
  have h₀ : a 0 = c 0 * t ^ p - 1 := by simp [a, coefficientPolynomial]
  have hs (i : ℕ) : a (i + 1) = (a i) ^ p + c (i + 1) * t ^ p := by
    simp [a, coefficientPolynomial]
  induction n with
  | zero =>
    simp only [Nat.zero_add, Finset.sum_range_one]
    have hab : a 0 • v 0 = (t ^ p * c 0) • v 0 - v 0 := by
      rw [h₀, sub_smul, one_smul, mul_comm (c 0)]
    rw [hab, smul_smul]
    abel
  | succ n ih =>
    simp only [Finset.sum_range_succ _ (n + 1)]
    rw [show (∑ i ∈ Finset.range (n + 1), a i ^ p • v (i + 1)) +
          a (n + 1) ^ p • v (n + 2) -
        ((∑ i ∈ Finset.range (n + 1), a i • v i) + a (n + 1) • v (n + 1)) =
        ((∑ i ∈ Finset.range (n + 1), a i ^ p • v (i + 1)) -
          (∑ i ∈ Finset.range (n + 1), a i • v i)) +
          a (n + 1) ^ p • v (n + 2) - a (n + 1) • v (n + 1) by abel]
    rw [ih, smul_add, hs n, add_smul, smul_smul, mul_comm (c (n + 1))]
    abel

include hF in
/-- In finite dimension, (F-1) is onto over a separably closed field.
A finite span of iterates of the target reduces the equation to one separable polynomial. -/
theorem surjective_sub_id [IsSepClosed K] : Function.Surjective (fun v : V => F v - v) := by
  classical
  intro w
  let v (i : ℕ) : V := F^[i] w
  have v_zero : v 0 = w := rfl
  have hv (i : ℕ) : F (v i) = v (i + 1) := (Function.iterate_succ_apply' _ _ _).symm
  obtain ⟨n, hn | hzero⟩ := exists_iterate_relation (K := K) v
  · obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (R := K)).mp hn
    let c (i : ℕ) : K := if hi : i < n + 1 then b ⟨i, hi⟩ else 0
    have hc : (∑ i ∈ Finset.range (n + 1), c i • v i) = v (n + 1) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine (Finset.sum_congr rfl (fun i _ => ?_)).trans hb
      simp only [c, dif_pos i.isLt]
    let P : K[X] := coefficientPolynomial p c n - X
    have hP : P.derivative = -1 := by
      simp only [P, derivative_sub, coefficientPolynomial_derivative, derivative_X, zero_sub]
    have hdeg : P.degree ≠ 0 := by
      intro hd
      have he := eq_C_of_degree_le_zero hd.le
      exact derivative_ne_zero_of_neg_one hP (by rw [he, derivative_C])
    have hsep : P.Separable := by
      rw [separable_def']
      exact ⟨0, -1, by simp [hP]⟩
    obtain ⟨t, ht⟩ := IsSepClosed.exists_root P hdeg hsep
    let a (i : ℕ) : K := (coefficientPolynomial p c i).eval t
    have ha : a n = t := by simpa [P, a, IsRoot, sub_eq_zero] using ht
    refine ⟨∑ i ∈ Finset.range (n + 1), a i • v i, ?_⟩
    simp only [map_sum, hF, hv]
    have hbal := sum_coefficientPolynomial_balance (p := p) v c t n
    change (∑ i ∈ Finset.range (n + 1), a i ^ p • v (i + 1)) -
      (∑ i ∈ Finset.range (n + 1), a i • v i) =
      a n ^ p • v (n + 1) - t ^ p • (∑ i ∈ Finset.range (n + 1), c i • v i) + v 0 at hbal
    simpa only [ha, hc, sub_self, zero_add, v_zero] using hbal
  · exact ⟨0, by simpa [v_zero] using hzero.symm⟩

end PhilipponArtinSchreierLinear

end

section

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace PhilipponArtinSchreierCohomology

universe u v w w'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

private theorem injective_cohomology_of_surjective_previous
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact) (q : ℕ)
    (h : ∀ n, Function.Surjective (Sheaf.H.map S.g n)) :
    Function.Injective (Sheaf.H.map S.f q) := by
  let Z := (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  cases q with
  | zero =>
    haveI := hS.mono_f
    exact Ext.postcomp_mk₀_injective_of_mono Z S.f
  | succ n =>
    rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro x hx
    change Sheaf.H.map S.f (n + 1) x = 0 at hx
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Z hS x hx (n₀ := n) rfl
    obtain ⟨z, hz⟩ := h n y
    rw [← hy, ← hz]
    simp only [Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero,
      ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

private theorem map_sub_id {B : Sheaf J AddCommGrpCat.{w}} (F : B ⟶ B) (q : ℕ) (x : B.H q) :
    Sheaf.H.map (F - 𝟙 B) q x = Sheaf.H.map F q x - x := by
  apply eq_sub_of_add_eq
  calc
    Sheaf.H.map (F - 𝟙 B) q x + x =
        Sheaf.H.map (F - 𝟙 B) q x + Sheaf.H.map (𝟙 B) q x := by rw [Sheaf.H.map_id_apply]
    _ = Sheaf.H.map F q x := by rw [← Sheaf.H.map_add_apply, sub_add_cancel]

/-- The short exact Artin–Schreier sequence gives an injection on cohomology
into the fixed vectors whenever the higher cohomology of the additive sheaf
is finite-dimensional and its Frobenius satisfies the scalar rule. -/
theorem finite_of_shortExact
    {K : Type*} [Field K] [IsSepClosed K] {p : ℕ} [CharP K p]
    {A B : Sheaf J AddCommGrpCat.{w}} (f : A ⟶ B) (F : B ⟶ B)
    (hz : f ≫ (F - 𝟙 B) = 0)
    (hS : (ShortComplex.mk f (F - 𝟙 B) hz).ShortExact)
    (M : ∀ n : ℕ, Module K (B.H n))
    (hM : ∀ n : ℕ, @Module.Finite K (B.H n) _ _ (M n))
    (hF : ∀ (n : ℕ) (a : K) (x : B.H n),
      Sheaf.H.map F n ((M n).smul a x) = (M n).smul (a ^ p) (Sheaf.H.map F n x))
    (q : ℕ) : Finite (A.H q) := by
  have hsurj (n : ℕ) : Function.Surjective (Sheaf.H.map (F - 𝟙 B) n) := by
    letI := M n
    letI := hM n
    simpa only [Function.Surjective, map_sub_id] using
      (PhilipponArtinSchreierLinear.surjective_sub_id (K := K) (p := p) (Sheaf.H.map F n) (hF n))
  have hinj : Function.Injective (Sheaf.H.map f q) :=
    injective_cohomology_of_surjective_previous _ hS q hsurj
  letI := M q
  letI := hM q
  letI := PhilipponArtinSchreierLinear.finite_fixed (K := K) (p := p) (Sheaf.H.map F q) (hF q)
  let lift (x : A.H q) : {b : B.H q // Sheaf.H.map F q b = b} :=
    ⟨Sheaf.H.map f q x, by
      apply sub_eq_zero.mp
      rw [← map_sub_id, ← Sheaf.H.map_comp_apply, hz]
      simp [Sheaf.H.map_apply]⟩
  exact Finite.of_injective lift (fun x y h => hinj (congrArg Subtype.val h))

end PhilipponArtinSchreierCohomology

end

section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace PhilipponArtinSchreierLocalRing

/-- A solution of the homogeneous Artin–Schreier equation in a local
algebra is a prime-field scalar, including when the algebra has nilpotents. -/
theorem exists_scalar {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ}
    (hp : p.Prime) (f : ZMod p →+* R) (x : R) (hx : x ^ p = x) :
    ∃ a : ZMod p, f a = x := by
  letI : Fact p.Prime := ⟨hp⟩
  let k := IsLocalRing.ResidueField R
  let g := IsLocalRing.residue R
  letI : CharP R p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    simpa only [map_natCast, map_zero] using congrArg f (CharP.cast_eq_zero (ZMod p) p))
  letI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    simpa only [map_natCast, map_zero] using congrArg g (CharP.cast_eq_zero R p))
  have hres : (g x) ^ p = g x := by rw [← map_pow, hx]
  have hmem : g x ∈ (⊥ : Subfield k) := (Subfield.mem_bot_iff_pow_eq_self k p).mpr hres
  have hbot : (g.comp f).fieldRange = (⊥ : Subfield k) := by
    rw [RingHom.ext_zmod (g.comp f) (ZMod.castHom (m := p) dvd_rfl k),
      ZMod.fieldRange_castHom_eq_bot]
  rw [← hbot, RingHom.mem_fieldRange] at hmem
  obtain ⟨a, ha⟩ := hmem
  let w := x - f a
  have hw : g w = 0 := by
    change g (x - f a) = 0
    rw [map_sub, sub_eq_zero]
    exact ha.symm
  have hwp : w ^ p = w := by
    change (x - f a) ^ p = x - f a
    rw [sub_pow_char, hx, ← map_pow, ZMod.pow_card]
  have hu : IsUnit (1 - w ^ (p - 1)) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [map_sub, map_one, map_pow, hw, zero_pow (Nat.sub_ne_zero_of_lt hp.one_lt), sub_zero]
    exact one_ne_zero
  have hprod : (1 - w ^ (p - 1)) * w = 0 := by
    rw [sub_mul, one_mul, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hwp, sub_self]
  have : w = 0 := hu.mul_right_inj.mp (hprod.trans (mul_zero _).symm)
  exact ⟨a, (sub_eq_zero.mp this).symm⟩

end PhilipponArtinSchreierLocalRing

end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite Polynomial


namespace PhilipponArtinSchreierEtaleCover

universe u
variable {R : Type u} [CommRing R]

private def equation (p : ℕ) (a : R) : R[X] := X ^ p - (X + C a)

private theorem monic_equation (p : ℕ) (hp : 1 < p) (a : R) : (equation p a).Monic := by
  apply monic_X_pow_sub
  exact (degree_add_le _ _).trans_lt
    ((max_le degree_X_le (degree_C_le.trans zero_le_one)).trans_lt (by exact_mod_cast hp))

private theorem degree_equation [Nontrivial R] (p : ℕ) (hp : 1 < p) (a : R) :
    (equation p a).degree = p := by
  unfold equation
  rw [degree_sub_eq_left_of_degree_lt, degree_X_pow]
  rw [degree_X_pow]
  exact (degree_add_le _ _).trans_lt
    ((max_le degree_X_le (degree_C_le.trans zero_le_one)).trans_lt (by exact_mod_cast hp))

private theorem root_equation (p : ℕ) (a : R) :
    (AdjoinRoot.root (equation p a)) ^ p - AdjoinRoot.root (equation p a) =
      algebraMap R (AdjoinRoot (equation p a)) a := by
  have h := AdjoinRoot.eval₂_root (equation p a)
  simp only [equation, eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_iff_eq_add.mpr ((sub_eq_zero.mp h).trans (add_comm _ _))

private theorem etale (p : ℕ) (hp : 1 < p) (hR : (p : R) = 0) (a : R) :
    Algebra.Etale R (AdjoinRoot (equation p a)) := by
  let f := equation p a
  let A := AdjoinRoot f
  have hd : f.derivative = -1 := by
    simp [f, equation, derivative_X_pow, hR]
  have hder : IsUnit (AdjoinRoot.mk f f.derivative) := by rw [hd, map_neg, map_one]; exact isUnit_one.neg
  let P : StandardEtalePair R := ⟨f, monic_equation p hp a, f.derivative, 1, 0, 1, by simp⟩
  let away : A ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnit A (Localization.Away (AdjoinRoot.mk f f.derivative))
      (AdjoinRoot.mk f f.derivative) hder).restrictScalars R
  letI : Algebra.IsStandardEtale R A := Algebra.IsStandardEtale.of_equiv
    (P.equivAwayAdjoinRoot.trans away.symm)
  infer_instance

private theorem algebraMap_injective [Nontrivial R] (p : ℕ) (hp : 1 < p) (a : R) :
    Function.Injective (algebraMap R (AdjoinRoot (equation p a))) := by
  let f := equation p a
  have hm : f.Monic := monic_equation p hp a
  have hleft : Function.LeftInverse (fun x => (AdjoinRoot.modByMonicHom hm x).coeff 0)
      (algebraMap R (AdjoinRoot f)) := by
    intro r
    change (AdjoinRoot.modByMonicHom hm (AdjoinRoot.mk f (C r))).coeff 0 = r
    have hdeg : (C r).degree < f.degree := by
      rw [degree_equation p hp a]
      exact degree_C_le.trans_lt (by exact_mod_cast hp.pos)
    rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hm).mpr hdeg, coeff_C_zero]
  exact hleft.injective

/-- A finite étale surjection where a given affine section has an Artin–Schreier preimage. -/
theorem exists_root_spec (R : CommRingCat.{u}) (p : ℕ) (hp : 1 < p)
    (hR : (p : Γ(Spec R, ⊤)) = 0) (a : Γ(Spec R, ⊤)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec R) (b : Γ(Y, ⊤)),
      IsFinite f ∧ Etale f ∧ Surjective f ∧ b ^ p - b = f.appTop a := by
  let e := Scheme.ΓSpecIso R
  rcases subsingleton_or_nontrivial R with h | h
  · letI : Subsingleton Γ(Spec R, ⊤) := e.commRingCatIsoToRingEquiv.injective.subsingleton
    exact ⟨_, 𝟙 _, 0, inferInstance, inferInstance, inferInstance, Subsingleton.elim _ _⟩
  · letI : Nontrivial R := h
    have hR' : (p : R) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg (fun r : Γ(Spec R, ⊤) => e.hom r) hR
    let b := e.hom a
    let f := equation p b
    let A := AdjoinRoot f
    let g : R ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap R A)
    letI : Module.Finite R A := (monic_equation p hp b).finite_adjoinRoot
    letI : Algebra.Etale R A := etale p hp hR' b
    have hfinite : (algebraMap R A).Finite := RingHom.finite_algebraMap.mpr inferInstance
    have hetale : (algebraMap R A).Etale := RingHom.etale_algebraMap.mpr inferInstance
    refine ⟨_, Spec.map g, (Scheme.ΓSpecIso _).inv (AdjoinRoot.root f),
      (IsFinite.SpecMap_iff g).mpr hfinite, (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hetale,
      ⟨hfinite.to_isIntegral.comap_surjective (algebraMap_injective p hp b)⟩, ?_⟩
    rw [← map_pow, ← map_sub, root_equation p b]
    change (e.hom ≫ g ≫ (Scheme.ΓSpecIso _).inv) a = _
    rw [Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, e.hom_inv_id, Category.id_comp]

private theorem exists_root_affine (X : Scheme.{u}) [IsAffine X] (p : ℕ) (hp : 1 < p)
    (hX : (p : Γ(X, ⊤)) = 0) (a : Γ(X, ⊤)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (b : Γ(Y, ⊤)),
      IsFinite f ∧ Etale f ∧ Surjective f ∧ b ^ p - b = f.appTop a := by
  let e := X.isoSpec
  have hX' : (p : Γ(Spec Γ(X, ⊤), ⊤)) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (fun r : Γ(X, ⊤) => e.inv.appTop r) hX
  obtain ⟨Y, f, b, hf, he, hs, hb⟩ := exists_root_spec _ p hp hX' (e.inv.appTop a)
  letI := hf
  letI := he
  letI := hs
  refine ⟨Y, f ≫ e.inv, b, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Scheme.Hom.comp_appTop]
  exact hb

private theorem exists_root_near (X : Scheme.{u}) (p : ℕ) (hp : 1 < p)
    (hX : (p : Γ(X, ⊤)) = 0) (a : Γ(X, ⊤)) (x : X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (y : Y) (b : Γ(Y, ⊤)),
      Etale f ∧ f y = x ∧ b ^ p - b = f.appTop a := by
  obtain ⟨i, z, rfl⟩ := X.affineCover.exists_eq x
  let g := X.affineCover.f i
  have hg : (p : Γ(X.affineCover.X i, ⊤)) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (fun r : Γ(X, ⊤) => g.appTop r) hX
  obtain ⟨Y, f, b, _, he, hs, hb⟩ := exists_root_affine _ p hp hg (g.appTop a)
  obtain ⟨y, rfl⟩ := hs.surj z
  letI := he
  refine ⟨Y, f ≫ g, y, b, inferInstance, rfl, ?_⟩
  rw [Scheme.Hom.comp_appTop]
  exact hb

open AlgebraicGeometry.SmallEtaleAdditive

/-- The Artin–Schreier map is locally onto on the actual small étale site. -/
theorem locally_surjective {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))
    {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0) :
    Sheaf.IsLocallySurjective (frobenius π hp hK - 𝟙 (sheaf X)) := by
  classical
  constructor
  intro U a
  let a₀ : Γ(U.left, ⊤) := a
  choose Y f y b he hx hr using fun x : U.left =>
    exists_root_near U.left p hp.one_lt (cast_eq_zero π hK U) a₀ x
  let W (x : U.left) : X.Etale := by
    letI := he x
    exact Scheme.Etale.mk (f x ≫ U.hom)
  let g (x : U.left) : W x ⟶ U := MorphismProperty.Over.homMk (f x) rfl trivial
  refine X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows W g) ?_ ?_
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨x⟩
    exact ⟨b x, hr x⟩
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, y x, hx x⟩

end PhilipponArtinSchreierEtaleCover

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponArtinSchreierKernel

open AlgebraicGeometry.SmallEtaleAdditive

universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))
variable {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0)

private def primeScalar : ZMod p →+* K := by
  letI : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hK
  exact ZMod.castHom (m := p) dvd_rfl K

private abbrev coeff (p : ℕ) : AddCommGrpCat.{u} := AddCommGrpCat.of (ULift.{u} (ZMod p))

private abbrev difference : sheaf X ⟶ sheaf X := frobenius π hp hK - 𝟙 (sheaf X)

private def constantToAdditive : (Functor.const X.Etaleᵒᵖ).obj (coeff p) ⟶ (sheaf X).obj where
  app U := AddCommGrpCat.ofHom
    (((scalar π U.unop).hom.comp (primeScalar hp hK)).toAddMonoidHom.comp
      (AddEquiv.ulift : ULift.{u} (ZMod p) ≃+ ZMod p).toAddMonoidHom)
  naturality := by
    intro U V f
    apply AddCommGrpCat.ext
    intro a
    change ULift (ZMod p) at a
    change scalar π V.unop (primeScalar hp hK a.down) =
      f.unop.left.appTop (scalar π U.unop (primeScalar hp hK a.down))
    have h : scalar π U.unop ≫ f.unop.left.appTop = scalar π V.unop := by
      rw [scalar, scalar, Category.assoc, ← Scheme.Hom.comp_appTop,
        ← Category.assoc, MorphismProperty.Over.w f.unop]
    exact (ConcreteCategory.congr_hom h _).symm

private theorem constantToAdditive_zero :
    constantToAdditive π hp hK ≫ (difference π hp hK).hom = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  change ULift (ZMod p) at a
  let s := (scalar π U.unop).hom.comp (primeScalar hp hK)
  change (s a.down) ^ p - s a.down = 0
  letI : Fact p.Prime := ⟨hp⟩
  rw [← map_pow, ZMod.pow_card, sub_self]

private def constantToKernel :
    (Functor.const X.Etaleᵒᵖ).obj (coeff p) ⟶ (kernel (difference π hp hK)).obj :=
  kernel.lift (difference π hp hK).hom (constantToAdditive π hp hK)
    (constantToAdditive_zero π hp hK) ≫
      (PreservesKernel.iso (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (difference π hp hK)).inv

private theorem constantToKernel_ι (U : X.Etale) (a : ULift.{u} (ZMod p)) :
    (kernel.ι (difference π hp hK)).hom.app (op U)
      ((constantToKernel π hp hK).app (op U) a) = scalar π U (primeScalar hp hK a.down) := by
  have h : constantToKernel π hp hK ≫ (kernel.ι (difference π hp hK)).hom =
      constantToAdditive π hp hK := by
    let F := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}
    change (_ ≫ (PreservesKernel.iso F (difference π hp hK)).inv) ≫
      F.map (kernel.ι (difference π hp hK)) = _
    rw [Category.assoc, PreservesKernel.iso_inv_ι]
    exact kernel.lift_ι _ _ _
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op U)) a

private theorem kernel_ι_injective (U : X.Etale) :
    Function.Injective ((kernel.ι (difference π hp hK)).hom.app (op U)) := by
  let : Mono (kernel.ι (difference π hp hK)).hom := inferInstanceAs
    (Mono ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).map (kernel.ι (difference π hp hK))))
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

private theorem locally_injective :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constantToKernel π hp hK) := by
  constructor
  intro U a b hab
  let W : U.unop.left → X.Etale := fun _ => U.unop
  let f (x : U.unop.left) : W x ⟶ U.unop := 𝟙 _
  refine X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows W f) ?_ ?_
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨x⟩
    have h := congrArg ((kernel.ι (difference π hp hK)).hom.app (op U.unop)) hab
    change (kernel.ι (difference π hp hK)).hom.app (op U.unop)
        ((constantToKernel π hp hK).app (op U.unop) a) =
      (kernel.ι (difference π hp hK)).hom.app (op U.unop)
        ((constantToKernel π hp hK).app (op U.unop) b) at h
    rw [constantToKernel_ι, constantToKernel_ι] at h
    let g := (U.unop.left.presheaf.germ ⊤ x trivial).hom.comp
      ((scalar π U.unop).hom.comp (primeScalar hp hK))
    letI : Fact p.Prime := ⟨hp⟩
    have h' : g a.down = g b.down := congrArg (U.unop.left.presheaf.germ ⊤ x trivial).hom h
    have : a = b := ULift.ext a b (g.injective h')
    exact congrArg _ this
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, x, rfl⟩

private theorem exists_open_of_fixed (U : X.Etale) (a : Γ(U.left, ⊤)) (ha : a ^ p = a) (x : U.left) :
    ∃ (V : U.left.Opens), x ∈ V ∧ ∃ r : ZMod p,
      V.ι.appTop a = V.ι.appTop (scalar π U (primeScalar hp hK r)) := by
  let g := (U.left.presheaf.germ ⊤ x trivial).hom
  have hfixed : (g a) ^ p = g a := by rw [← map_pow, ha]
  obtain ⟨r, hr⟩ := PhilipponArtinSchreierLocalRing.exists_scalar hp
    (g.comp ((scalar π U).hom.comp (primeScalar hp hK))) (g a) hfixed
  change g (scalar π U (primeScalar hp hK r)) = g a at hr
  obtain ⟨V, hxV, i, j, h⟩ := U.left.presheaf.germ_eq x
    (show x ∈ (⊤ : U.left.Opens) from trivial) (show x ∈ (⊤ : U.left.Opens) from trivial)
    a (scalar π U (primeScalar hp hK r)) hr.symm
  change U.left.Opens at V
  refine ⟨V, hxV, r, ?_⟩
  let k : V.ι ''ᵁ ⊤ ⟶ V := eqToHom V.ι_image_top
  have h' := congrArg (U.left.presheaf.map k.op).hom h
  change U.left.presheaf.map k.op (U.left.presheaf.map i.op a) =
    U.left.presheaf.map k.op (U.left.presheaf.map j.op (scalar π U (primeScalar hp hK r))) at h'
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp] at h'
  rw [Scheme.Opens.ι_appTop]
  exact (Subsingleton.elim (k ≫ i) (homOfLE le_top)) ▸
    (Subsingleton.elim (k ≫ j) (homOfLE le_top)) ▸ h'

private theorem locally_surjective :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (constantToKernel π hp hK) := by
  constructor
  intro U a
  let α : Γ(U.left, ⊤) := (kernel.ι (difference π hp hK)).hom.app (op U) a
  have hα : α ^ p = α := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun f => f.hom) (kernel.condition (difference π hp hK))) (op U)) a
    change α ^ p - α = 0 at h
    exact sub_eq_zero.mp h
  choose V hx r hr using fun x : U.left => exists_open_of_fixed π hp hK U α hα x
  let W (x : U.left) : X.Etale := Scheme.Etale.mk ((V x).ι ≫ U.hom)
  let f (x : U.left) : W x ⟶ U := MorphismProperty.Over.homMk (V x).ι rfl trivial
  refine X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows W f) ?_ ?_
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨x⟩
    refine ⟨ULift.up (r x), kernel_ι_injective π hp hK (W x) ?_⟩
    rw [constantToKernel_ι, NatTrans.naturality_apply (kernel.ι (difference π hp hK)).hom (f x).op]
    change scalar π (W x) (primeScalar hp hK (r x)) = (V x).ι.appTop α
    rw [hr x]
    have h : scalar π U ≫ (V x).ι.appTop = scalar π (W x) := by
      change scalar π U ≫ (f x).left.appTop = scalar π (W x)
      rw [scalar, scalar, Category.assoc, ← Scheme.Hom.comp_appTop,
        ← Category.assoc, MorphismProperty.Over.w (f x)]
    exact (ConcreteCategory.congr_hom h _).symm
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, ⟨x, hx x⟩, rfl⟩

/-- The kernel of Frobenius minus identity is the constant prime-field sheaf. -/
def constantIsoKernel :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (coeff p) ≅
      kernel (difference π hp hK) := by
  letI := locally_injective π hp hK
  letI := locally_surjective π hp hK
  have h := X.smallEtaleTopology.W_of_isLocallyBijective (constantToKernel π hp hK)
  letI := (X.smallEtaleTopology.W_iff (constantToKernel π hp hK)).mp h
  exact asIso ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map (constantToKernel π hp hK)) ≪≫
    asIso ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}).counit.app
      (kernel (difference π hp hK)))

end PhilipponArtinSchreierKernel

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite

namespace AlgebraicGeometry.SmallEtaleAdditive

universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))
variable {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0)

private theorem frobenius_mulScalar (a : K) :
    mulScalar π a ≫ frobenius π hp hK = frobenius π hp hK ≫ mulScalar π (a ^ p) := by
  ext U x
  change Γ(U.unop.left, ⊤) at x
  change (scalar π U.unop a * x) ^ p = scalar π U.unop (a ^ p) * x ^ p
  rw [map_pow, mul_pow]

/-- Frobenius acts semilinearly on sheaf cohomology for the scalar action
defined by multiplication on the actual étale structure sheaf. -/
theorem frobenius_cohomology_smul (n : ℕ) (a : K) (x : (sheaf X).H n) :
    Sheaf.H.map (frobenius π hp hK) n ((cohomologyModule π n).smul a x) =
      (cohomologyModule π n).smul (a ^ p) (Sheaf.H.map (frobenius π hp hK) n x) := by
  change Sheaf.H.map (frobenius π hp hK) n (Sheaf.H.map (mulScalar π a) n x) =
    Sheaf.H.map (mulScalar π (a ^ p)) n (Sheaf.H.map (frobenius π hp hK) n x)
  rw [← Sheaf.H.map_comp_apply, frobenius_mulScalar, Sheaf.H.map_comp_apply]

end AlgebraicGeometry.SmallEtaleAdditive

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SmallEtaleAdditive

universe u

private theorem finite_additive_cohomology
    (K : Type u) [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [IsProper π]
    (q : ℕ) :
    @Module.Finite K ((sheaf X).H q) _ _ (cohomologyModule π q) := by
  classical
  letI := QuasiCompact.compactSpace_of_compactSpace π
  let V := X.affineCover.finiteSubcover
  letI : LinearOrder V.I₀ :=
    LinearOrder.lift' (Fintype.equivFin V.I₀) (Fintype.equivFin V.I₀).injective
  let U : X.OrderedAffineCover :=
    { ι := V.I₀
      U i := (V.f i).opensRange
      isAffineOpen i := isAffineOpen_opensRange (V.f i)
      iSup_eq_top := V.iSup_opensRange }
  letI : ∀ n : ℕ, Module K ((sheaf X).H n) := fun n => cohomologyModule π n
  have hfinite := OModulePresheaf.cechFinite_unit_of_isProper π U
  obtain ⟨h0, hs⟩ := Scheme.smallEtale_additive_cohomology_equiv_orderedCech K π U
  cases q with
  | zero =>
    letI := hfinite.1
    exact Module.Finite.equiv h0.some.symm
  | succ n =>
    letI := hfinite.2 n
    exact Module.Finite.equiv (hs n).some.symm

theorem solution
    (K : Type u) [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (p : ℕ) (hp : p.Prime)
    (hK : (p : K) = 0) (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod p)))).H q) := by
  letI : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hK
  let B := sheaf X
  let F := frobenius π hp hK
  let g : B ⟶ B := F - 𝟙 B
  let e := PhilipponArtinSchreierKernel.constantIsoKernel π hp hK
  let f := e.hom ≫ kernel.ι g
  have hz : f ≫ g = 0 := by simp [f, Category.assoc]
  let S := ShortComplex.mk f g hz
  let T := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  letI : Sheaf.IsLocallySurjective g := PhilipponArtinSchreierEtaleCover.locally_surjective π hp hK
  have hT : T.ShortExact := { exact := ShortComplex.exact_kernel g }
  let i : T ≅ S := ShortComplex.isoMk e.symm (Iso.refl B) (Iso.refl B)
    (by change e.inv ≫ (e.hom ≫ kernel.ι g) = kernel.ι g ≫ 𝟙 B; simp) (by simp [S, T])
  have hS : S.ShortExact := ShortComplex.shortExact_of_iso i hT
  exact PhilipponArtinSchreierCohomology.finite_of_shortExact f F hz hS
    (fun n => cohomologyModule π n) (finite_additive_cohomology K π)
    (frobenius_cohomology_smul π hp hK) q

end
