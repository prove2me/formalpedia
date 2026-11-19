-- Prove2me | solution 1 for APSCounting893.Main.perron_exceptional_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:39:23.543961+00:00
-- url     : https://prove2.me/submissions/e4596b76-2bf2-4992-bfc8-7e01bb9191cd

import Definitions.Def_APSCounting893_Main_Geometry
import Definitions.Def_APSCounting893_Main_LineGeometry
import Definitions.Def_APSCounting893_Main_Resultant
import Mathlib
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Tactic
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_exists
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def affineEvaluation {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    Polynomials K n →ₗ[K] (X → K) where
  toFun p := fun x => MvPolynomial.eval x.val p
  map_add' p q := by funext x; exact map_add (MvPolynomial.eval x.val) p q
  map_smul' c p := by
    funext x
    simp [MvPolynomial.smul_eq_C_mul]

lemma affineFilteredPiece_eq_map {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    affineFilteredPiece X d = (MvPolynomial.restrictTotalDegree (Fin n) K d).map (affineEvaluation X) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨p, hp, rfl⟩
    exact Submodule.mem_map.mpr ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) d p).mpr hp, rfl⟩
  · rintro f ⟨p, hp, rfl⟩
    apply Submodule.subset_span
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) d p).mp hp, rfl⟩

instance affineFilteredPiece_finite {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) : Module.Finite K (affineFilteredPiece X d) := by
  rw [affineFilteredPiece_eq_map]
  exact Module.Finite.map (MvPolynomial.restrictTotalDegree (Fin n) K d) (affineEvaluation X)

lemma mem_affineFilteredPiece {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) (f : X → K) :
    f ∈ affineFilteredPiece X d ↔ ∃ p : Polynomials K n, p.totalDegree ≤ d ∧
      f = fun x => MvPolynomial.eval x.val p := by
  rw [affineFilteredPiece_eq_map, Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) d p).mp hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) d p).mpr hp, rfl⟩

lemma totalDegree_eval₂_bounded {K L : Type} [CommRing K] [CommRing L] {n m : ℕ}
    (f : K →+* L) (g : Fin n → MvPolynomial (Fin m) L) (D : ℕ)
    (hg : ∀ i, (g i).totalDegree ≤ D) (p : MvPolynomial (Fin n) K) :
    (eval₂Hom (MvPolynomial.C.comp f) g p).totalDegree ≤ D * p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [RingHom.coe_comp, Function.comp_apply, totalDegree_C, zero_add]
  rw [Finsupp.prod_pow]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))))
  rw [← Finset.sum_mul]
  simpa [Finsupp.sum_fintype, Nat.mul_comm] using Nat.mul_le_mul_right D (le_totalDegree he)

end APSCounting893.Main
end Component_0

section Component_1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma finsupp_nat_sum_eq {n : ℕ} (e : Fin n →₀ ℕ) :
    e.sum (fun _ v => v) = ∑ i, e i := Finsupp.sum_fintype _ _ (fun _ => rfl)

noncomputable def boundedExponentEquivSum (n d : ℕ) :
    {e : Fin n →₀ ℕ // e.sum (fun _ v => v) ≤ d} ≃
      {f : Fin (n + 1) → ℕ // ∑ i, f i = d} where
  toFun e := ⟨Fin.cons (d - e.val.sum (fun _ v => v)) e.val, by
    rw [Fin.sum_univ_succ]
    have he := e.property
    rw [finsupp_nat_sum_eq] at he
    simp only [Fin.cons_zero, Fin.cons_succ, finsupp_nat_sum_eq]
    omega⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => f.val i.succ), by
    have hf := f.property
    rw [Fin.sum_univ_succ] at hf
    rw [Finsupp.equivFunOnFinite_symm_sum]
    omega⟩
  left_inv e := by
    apply Subtype.ext
    ext i
    simp
  right_inv f := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hf := f.property
      rw [Fin.sum_univ_succ] at hf
      change d - (Finsupp.equivFunOnFinite.symm (fun j : Fin n => f.val j.succ)).sum (fun _ v => v) = f.val 0
      rw [Finsupp.equivFunOnFinite_symm_sum]
      omega
    · simp

noncomputable def boundedExponentEquivSym (n d : ℕ) :
    {e : Fin n →₀ ℕ // e.sum (fun _ v => v) ≤ d} ≃ Sym (Fin (n + 1)) d :=
  (boundedExponentEquivSum n d).trans (Sym.equivNatSumOfFintype (Fin (n + 1)) d).symm

lemma restrictTotalDegree_finrank (K : Type) [Field K] (n d : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K d) = (n + d).choose n := by
  classical
  let E := {e : Fin n →₀ ℕ // e.sum (fun _ v => v) ≤ d}
  let eqv : E ≃ Sym (Fin (n + 1)) d := boundedExponentEquivSym n d
  letI : Fintype E := Fintype.ofEquiv _ eqv.symm
  calc
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K d) = Fintype.card E :=
      Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K _)
    _ = Fintype.card (Sym (Fin (n + 1)) d) := Fintype.card_congr eqv
    _ = (n + d).choose n := by
      rw [Sym.card_sym_eq_choose]
      simp only [Fintype.card_fin]
      rw [show n + 1 + d - 1 = n + d by omega, Nat.choose_symm_add]

lemma affineEvaluation_univ_injective {K : Type} [Field K] [Infinite K] {n : ℕ} :
    Function.Injective (affineEvaluation (Set.univ : Set (Affine K n))) := by
  intro p q h
  apply MvPolynomial.funext
  intro x
  exact congrFun h ⟨x, Set.mem_univ x⟩

lemma univ_affineHilbertFunction {K : Type} [Field K] [Infinite K] (n d : ℕ) :
    affineHilbertFunction (Set.univ : Set (Affine K n)) d = (n + d).choose n := by
  unfold affineHilbertFunction
  rw [affineFilteredPiece_eq_map]
  rw [← (Submodule.equivMapOfInjective (affineEvaluation (Set.univ : Set (Affine K n)))
    affineEvaluation_univ_injective (MvPolynomial.restrictTotalDegree (Fin n) K d)).finrank_eq]
  exact restrictTotalDegree_finrank K n d

end APSCounting893.Main
end Component_1

section Component_2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma evaluation_substitution {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (p : Polynomials K m) (x : Affine K n) :
    eval x (eval₂Hom MvPolynomial.C F p) = eval (evaluate F x) p := by
  have heq : (eval x).comp (eval₂Hom MvPolynomial.C F) = eval (evaluate F x) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro i; simp [evaluate]
  exact RingHom.congr_fun heq p

lemma image_vanishingIdeal_eq_kernel {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) :
    vanishingIdeal K (Set.range (evaluate F)) = RingHom.ker (eval₂Hom MvPolynomial.C F) := by
  ext p
  constructor
  · intro hp
    rw [RingHom.mem_ker]
    apply MvPolynomial.funext
    intro x
    rw [evaluation_substitution]
    simpa only [map_zero, aeval_def, Algebra.algebraMap_self, eval₂_id] using
      hp (evaluate F x) (Set.mem_range_self x)
  · intro hp y hy
    obtain ⟨x, rfl⟩ := hy
    rw [RingHom.mem_ker] at hp
    rw [aeval_def, Algebra.algebraMap_self, eval₂_id, ← evaluation_substitution, hp, map_zero]

lemma hasAPS_iff_annihilator {n m : ℕ} (F : PolynomialMap ℂ n m) :
    hasAPS F ↔ ∀ p ∈ annihilator F, eval (0 : Affine ℂ m) p = 0 := by
  unfold hasAPS imageClosure RSCapacity.zClosure
  rw [image_vanishingIdeal_eq_kernel]
  rfl

lemma isAlgSet_zeroLocus {K : Type} [Field K] {n : ℕ}
    (I : Ideal (Polynomials K n)) : RSCapacity.IsAlgSet (zeroLocus K I) := by
  refine ⟨I, ?_⟩
  ext x
  simp only [mem_zeroLocus_iff, RSCapacity.zeroSet, Set.mem_setOf_eq,
    aeval_def, Algebra.algebraMap_self, eval₂_id, SetLike.mem_coe]

lemma isAlgSet_eq_zeroLocus {K : Type} [Field K] {n : ℕ}
    {X : Set (Affine K n)} (hX : RSCapacity.IsAlgSet X) :
    X = zeroLocus K (vanishingIdeal K X) := by
  apply Set.Subset.antisymm (zeroLocus_vanishingIdeal_le X)
  obtain ⟨S, rfl⟩ := hX
  intro x hx p hp
  have hv : p ∈ vanishingIdeal K (RSCapacity.zeroSet S) := by
    intro y hy
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hy p hp
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hx p hv

lemma irreducibleAffine_ideal_prime {K : Type} [Field K] {n : ℕ}
    {X : Set (Affine K n)} (hX : IrreducibleAffine X) :
    (vanishingIdeal K X).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    obtain ⟨x, hx⟩ := hX.1
    have hone : (1 : Polynomials K n) ∈ vanishingIdeal K X := by rw [htop]; trivial
    have := hone x hx
    simpa using this
  · intro p q hpq
    let A := RSCapacity.zeroSet ({p} : Set (Polynomials K n))
    let B := RSCapacity.zeroSet ({q} : Set (Polynomials K n))
    have hAB : X ⊆ A ∪ B := by
      intro x hx
      have hprod : eval x p * eval x q = 0 := by
        simpa only [map_mul, aeval_def, Algebra.algebraMap_self, eval₂_id] using hpq x hx
      rcases mul_eq_zero.mp hprod with hp | hq
      · left; simpa [A, RSCapacity.zeroSet] using hp
      · right; simpa [B, RSCapacity.zeroSet] using hq
    rcases hX.2.2 A B ⟨{p}, rfl⟩ ⟨{q}, rfl⟩ hAB with hA | hB
    · left
      intro x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using (hA hx) p (Set.mem_singleton p)
    · right
      intro x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using (hB hx) q (Set.mem_singleton q)

lemma prime_ideal_irreducibleAffine {K : Type} [Field K] {n : ℕ}
    {X : Set (Affine K n)} (hne : X.Nonempty) (hclosed : RSCapacity.IsAlgSet X)
    (hprime : (vanishingIdeal K X).IsPrime) : IrreducibleAffine X := by
  classical
  refine ⟨hne, hclosed, ?_⟩
  intro A B hA hB hAB
  by_cases hXA : X ⊆ A
  · exact Or.inl hXA
  by_cases hXB : X ⊆ B
  · exact Or.inr hXB
  obtain ⟨x, hx, hxA⟩ := Set.not_subset.mp hXA
  obtain ⟨y, hy, hyB⟩ := Set.not_subset.mp hXB
  rw [isAlgSet_eq_zeroLocus hA] at hxA
  rw [isAlgSet_eq_zeroLocus hB] at hyB
  simp only [mem_zeroLocus_iff, not_forall, exists_prop] at hxA hyB
  obtain ⟨p, hpA, hpx⟩ := hxA
  obtain ⟨q, hqB, hqy⟩ := hyB
  have hpq : p * q ∈ vanishingIdeal K X := by
    intro z hz
    rcases hAB hz with hzA | hzB
    · simp only [map_mul, hpA z hzA, zero_mul]
    · simp only [map_mul, hqB z hzB, mul_zero]
  rcases hprime.mem_or_mem hpq with hpX | hqX
  · exact (hpx (hpX x hx)).elim
  · exact (hqy (hqX y hy)).elim

lemma vanishingIdeal_zClosure {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    vanishingIdeal K (RSCapacity.zClosure X) = vanishingIdeal K X := by
  apply le_antisymm
  · exact vanishingIdeal_anti_mono (zeroLocus_vanishingIdeal_le X)
  · intro p hp x hx
    exact hx p hp

lemma irreducibleAffine_imageClosure {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : IrreducibleAffine (imageClosure F) := by
  apply prime_ideal_irreducibleAffine
  · exact ⟨evaluate F 0, zeroLocus_vanishingIdeal_le _ (Set.mem_range_self 0)⟩
  · exact isAlgSet_zeroLocus _
  · unfold imageClosure
    rw [vanishingIdeal_zClosure, image_vanishingIdeal_eq_kernel]
    exact RingHom.ker_isPrime _

noncomputable def coordinatePullback {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) :
    Polynomials K m →+* CoordinateRing X :=
  (Ideal.Quotient.mk (vanishingIdeal K X)).comp (eval₂Hom MvPolynomial.C F)

noncomputable def coordinatePullbackAlgebra {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) :
    Algebra (Polynomials K m) (CoordinateRing X) := (coordinatePullback X F).toAlgebra

lemma finiteMorphism_module_finite {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) (hfinite : FiniteMorphism X F) :
    letI : Algebra (Polynomials K m) (CoordinateRing X) := coordinatePullbackAlgebra X F
    Module.Finite (Polynomials K m) (CoordinateRing X) := by
  classical
  letI : Algebra (Polynomials K m) (CoordinateRing X) := coordinatePullbackAlgebra X F
  have halg : algebraMap (Polynomials K m) (CoordinateRing X) = coordinatePullback X F := rfl
  obtain ⟨s, generators, hgen⟩ := hfinite
  let g : Fin s → CoordinateRing X := fun i => Ideal.Quotient.mk _ (generators i)
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨Set.range g, Set.finite_range g, ?_⟩
  rw [Submodule.eq_top_iff']
  intro b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨coefficients, hcoeff⟩ := hgen p
  have hz : p - ∑ i : Fin s, (eval₂Hom MvPolynomial.C F (coefficients i)) * generators i ∈
      vanishingIdeal K X := by
    intro x hx
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, map_sum, map_mul,
      evaluation_substitution, sub_eq_zero]
    exact hcoeff x hx
  have heq : Ideal.Quotient.mk (vanishingIdeal K X) p =
      ∑ i : Fin s, coefficients i • g i := by
    apply sub_eq_zero.mp
    have h := (Ideal.Quotient.eq_zero_iff_mem).mpr hz
    simpa only [map_sub, map_sum, map_mul, Algebra.smul_def,
      halg, coordinatePullback, RingHom.comp_apply, g] using h
  rw [heq]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

lemma coordinatePullback_injective_of_dominant {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m)
    (hdom : RSCapacity.zClosure (evaluate F '' X) = Set.univ) :
    Function.Injective (coordinatePullback X F) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm ?_ bot_le
  intro p hp
  have hz : eval₂Hom MvPolynomial.C F p ∈ vanishingIdeal K X :=
    Ideal.Quotient.eq_zero_iff_mem.mp hp
  have hpI : p ∈ vanishingIdeal K (evaluate F '' X) := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using hz x hx
  rw [Ideal.mem_bot]
  apply MvPolynomial.funext
  intro y
  have hy : y ∈ RSCapacity.zClosure (evaluate F '' X) := by rw [hdom]; trivial
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_zero] using hy p hpI

noncomputable def hahnValuationRing : ValuationSubring PuiseuxAmbient :=
  (AddValuation.toValuation (HahnSeries.addVal ℚ ℂ)).valuationSubring

lemma constant_in_hahnValuationRing (c : ℂ) : HahnSeries.C c ∈ hahnValuationRing := by
  change 0 ≤ (HahnSeries.single (0 : ℚ) c).orderTop
  exact HahnSeries.orderTop_single_le

lemma positive_series_relation {m : ℕ} (p : Polynomials ℂ m)
    (y : Affine PuiseuxAmbient m) (hy : ∀ i, 0 < (y i).orderTop)
    (hrel : MvPolynomial.eval₂ HahnSeries.C y p = 0) :
    eval (0 : Affine ℂ m) p = 0 := by
  classical
  let V := hahnValuationRing
  let c0 : ℂ →+* V :=
    { toFun := fun c => ⟨HahnSeries.C c, constant_in_hahnValuationRing c⟩
      map_zero' := Subtype.ext (HahnSeries.C.map_zero)
      map_one' := Subtype.ext (HahnSeries.C.map_one)
      map_add' := fun a b => Subtype.ext (HahnSeries.C.map_add a b)
      map_mul' := fun a b => Subtype.ext (HahnSeries.C.map_mul a b) }
  let z : Fin m → V := fun i => ⟨y i, le_of_lt (hy i)⟩
  have hz : MvPolynomial.eval₂ c0 z p = 0 := by
    apply Subtype.val_injective
    change V.subtype (MvPolynomial.eval₂ c0 z p) = 0
    rw [MvPolynomial.hom_eval₂]
    exact hrel
  let res := IsLocalRing.residue V
  have hzi (i : Fin m) : res (z i) = 0 := by
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    apply (Valuation.mem_maximalIdeal_iff (v := AddValuation.toValuation (HahnSeries.addVal ℚ ℂ))).mpr
    exact hy i
  let phi : ℂ →+* IsLocalRing.ResidueField V := res.comp c0
  have heq : MvPolynomial.eval₂ phi (fun _ : Fin m => 0) p = 0 := by
    have h := congrArg res hz
    rw [MvPolynomial.hom_eval₂] at h
    simpa only [hzi, map_zero] using h
  apply phi.injective
  rw [map_zero]
  have hmap : phi (eval (0 : Affine ℂ m) p) = MvPolynomial.eval₂ phi (fun _ : Fin m => 0) p := by
    simpa only [RingHom.comp_id, Pi.zero_apply, map_zero, eval₂_id] using
      (MvPolynomial.hom_eval₂ p (RingHom.id ℂ) phi (0 : Affine ℂ m))
  exact hmap.trans heq

lemma approximateVanishing_implies_hasAPS {n m : ℕ} (F : PolynomialMap ℂ n m)
    (hF : (approximateVanishing F).Nonempty) : hasAPS F := by
  rw [hasAPS_iff_annihilator]
  obtain ⟨x, hx⟩ := hF
  intro p hp
  apply positive_series_relation p (fun j => MvPolynomial.eval₂ HahnSeries.C x (F j)) hx.2
  have heq : (MvPolynomial.eval₂Hom HahnSeries.C x).comp (MvPolynomial.eval₂Hom MvPolynomial.C F) =
      MvPolynomial.eval₂Hom HahnSeries.C (fun j => MvPolynomial.eval₂ HahnSeries.C x (F j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro j; simp
  have hp0 : MvPolynomial.eval₂Hom MvPolynomial.C F p = 0 := hp
  have h := RingHom.congr_fun heq p
  rw [RingHom.comp_apply, hp0, map_zero] at h
  exact h.symm

end APSCounting893.Main
end Component_2

section Component_3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def filteredLinearPullback {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (pi : PolynomialMap K n m) (t : ℕ)
    (hpi : ∀ i, (pi i).totalDegree ≤ 1) :
    affineFilteredPiece (Set.univ : Set (Affine K m)) t →ₗ[K] affineFilteredPiece X t where
  toFun f := ⟨fun x => f.val ⟨evaluate pi x.val, Set.mem_univ _⟩, by
    obtain ⟨p, hp, hrepr⟩ := (mem_affineFilteredPiece _ _ f.val).mp f.property
    apply (mem_affineFilteredPiece _ _ _).mpr
    refine ⟨eval₂Hom MvPolynomial.C pi p, ?_, ?_⟩
    · have hh := totalDegree_eval₂_bounded (RingHom.id K) pi 1 hpi p
      have hh' : (eval₂Hom MvPolynomial.C pi p).totalDegree ≤ p.totalDegree := by simpa using hh
      exact hh'.trans hp
    · funext x
      rw [hrepr]
      exact (evaluation_substitution pi p x.val).symm⟩
  map_add' f g := by apply Subtype.ext; funext x; rfl
  map_smul' c f := by apply Subtype.ext; funext x; rfl

lemma filteredLinearPullback_injective {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (pi : PolynomialMap K n m) (t : ℕ)
    (hpi : ∀ i, (pi i).totalDegree ≤ 1)
    (hsurj : ∀ y : Affine K m, ∃ x ∈ X, evaluate pi x = y) :
    Function.Injective (filteredLinearPullback X pi t hpi) := by
  intro f g h
  apply Subtype.ext
  funext y
  obtain ⟨x, hx, hxy⟩ := hsurj y.val
  have hh := congrArg (fun z : affineFilteredPiece X t => z.val ⟨x, hx⟩) h
  change f.val ⟨evaluate pi x, _⟩ = g.val ⟨evaluate pi x, _⟩ at hh
  simpa only [hxy] using hh

lemma affineHilbert_lower_of_linear_surjection {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (X : Set (Affine K n)) (pi : PolynomialMap K n m) (t : ℕ)
    (hpi : ∀ i, (pi i).totalDegree ≤ 1)
    (hsurj : ∀ y : Affine K m, ∃ x ∈ X, evaluate pi x = y) :
    (m + t).choose m ≤ affineHilbertFunction X t := by
  have hh := LinearMap.finrank_le_finrank_of_injective (filteredLinearPullback_injective X pi t hpi hsurj)
  change affineHilbertFunction (Set.univ : Set (Affine K m)) t ≤ affineHilbertFunction X t at hh
  simpa only [univ_affineHilbertFunction] using hh

lemma normalizationPolynomials_degree_le {n : ℕ} (c : Affine ℂ n) (i : Fin n) :
    (normalizationPolynomials c i).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simp

lemma normalization_affineHilbert_lower {n : ℕ} (Y : Set (Affine ℂ (n + 1)))
    (c : Affine ℂ n) (hc : IsNormalization Y c) (t : ℕ) :
    (n + t).choose n ≤ affineHilbertFunction Y t := by
  apply affineHilbert_lower_of_linear_surjection Y (normalizationPolynomials c) t
    (normalizationPolynomials_degree_le c)
  intro y
  obtain ⟨x, hx, hxy⟩ := (Set.mem_image _ _ _).mp (show y ∈ normalization c '' Y by rw [hc.2.1]; trivial)
  exact ⟨x, hx, hxy⟩

end APSCounting893.Main
end Component_3

section Component_4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace APSCounting893.Main

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

lemma polynomial_prime_height_one_of_contract_zero {R : Type} [CommRing R] [IsDomain R]
    (P : Ideal R[X]) [P.IsPrime] (hP : P ≠ ⊥)
    (hcontract : Ideal.comap Polynomial.C P = ⊥) : P.height = 1 := by
  let K := FractionRing R
  let M : Submonoid R[X] := (nonZeroDivisors R).map Polynomial.C
  let Q : Ideal K[X] := P.map (algebraMap R[X] K[X])
  have hd : Disjoint (M : Set R[X]) (P : Set R[X]) := by
    refine Set.disjoint_left.mpr ?_
    rintro q ⟨r, hr, rfl⟩ hq
    have hr0 : r = 0 := by
      have hh : r ∈ Ideal.comap Polynomial.C P := hq
      rw [hcontract, Ideal.mem_bot] at hh
      exact hh
    exact (nonZeroDivisors.ne_zero hr) hr0
  haveI : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M K[X] P inferInstance hd
  have hinj : Function.Injective (algebraMap R[X] K[X]) :=
    Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  have hQ : Q ≠ ⊥ := by
    intro h
    exact hP ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  haveI : Q.IsMaximal := IsPrime.to_maximal_ideal hQ
  have hh := IsPrincipalIdealRing.height_eq_one_of_isMaximal Q (Polynomial.not_isField K)
  have he := IsLocalization.height_map_of_disjoint (S := K[X]) M P hd
  exact he.symm.trans hh

lemma polynomial_prime_principal_of_contract_zero {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R]
    (P : Ideal R[X]) [P.IsPrime] (hcontract : Ideal.comap Polynomial.C P = ⊥) :
    P.IsPrincipal := by
  by_cases hP : P = ⊥
  · rw [hP]; infer_instance
  · exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
      (polynomial_prime_height_one_of_contract_zero P hP hcontract)

end APSCounting893.Main
end Component_4

section Component_5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma finSuccEquiv_rename_succ {K : Type} [Field K] (n : ℕ) (p : MvPolynomial (Fin n) K) :
    MvPolynomial.finSuccEquiv K n (rename Fin.succ p) = Polynomial.C p := by
  have h : (MvPolynomial.finSuccEquiv K n).toRingEquiv.toRingHom.comp (rename Fin.succ).toRingHom =
      (Polynomial.C : MvPolynomial (Fin n) K →+* Polynomial (MvPolynomial (Fin n) K)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [MvPolynomial.finSuccEquiv_apply]
    · intro i; simp [MvPolynomial.finSuccEquiv_X_succ]
  exact RingHom.congr_fun h p

lemma mv_prime_principal_of_contract_succ_zero {K : Type} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hcontract : I.comap (rename Fin.succ) = ⊥) : I.IsPrincipal := by
  let e := MvPolynomial.finSuccEquiv K n
  let P : Ideal (Polynomial (MvPolynomial (Fin n) K)) := I.comap e.symm.toRingEquiv.toRingHom
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : P.comap Polynomial.C = ⊥ := by
    ext p
    change e.symm (Polynomial.C p) ∈ I ↔ p ∈ (⊥ : Ideal _)
    have he : e.symm (Polynomial.C p) = rename Fin.succ p := by
      apply e.injective
      rw [AlgEquiv.apply_symm_apply, finSuccEquiv_rename_succ]
    rw [he]
    exact SetLike.ext_iff.mp hcontract p
  have hp := polynomial_prime_principal_of_contract_zero P hP
  obtain ⟨p, hgen⟩ := hp
  refine ⟨e.symm p, ?_⟩
  have hmap := congrArg (Ideal.map e.symm.toRingEquiv.toRingHom) hgen
  rw [Ideal.map_span, Set.image_singleton] at hmap
  have hPI : P.map e.symm.toRingEquiv.toRingHom = I :=
    Ideal.map_comap_of_surjective _ e.symm.surjective _
  rwa [hPI] at hmap

lemma polynomial_map_kernel_ne_bot {K : Type} [Field K] (n : ℕ)
    (F : Fin (n + 1) → MvPolynomial (Fin n) K) :
    RingHom.ker (MvPolynomial.aeval (R := K) F).toRingHom ≠ ⊥ := by
  intro h
  have hind : AlgebraicIndependent K F :=
    (RingHom.injective_iff_ker_eq_bot _).mpr h
  have hh := AlgebraicIndependent.cardinalMk_le_trdeg (R := K) (A := MvPolynomial (Fin n) K) hind
  rw [MvPolynomial.trdeg_of_isDomain] at hh
  simp only [Cardinal.mk_fin, Cardinal.lift_natCast] at hh
  have hh' : n + 1 ≤ n := by exact_mod_cast hh
  omega

end APSCounting893.Main
end Component_5

section Component_6

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def filteredEvaluation {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (t : ℕ) :
    restrictTotalDegree (Fin n) K t →ₗ[K] (X → K) :=
  (affineEvaluation X).comp (restrictTotalDegree (Fin n) K t).subtype

lemma filteredEvaluation_range {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (t : ℕ) :
    LinearMap.range (filteredEvaluation X t) = affineFilteredPiece X t := by
  rw [affineFilteredPiece_eq_map]
  ext f
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨p.val, p.property, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩

noncomputable def filteredPrincipalMultiple {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K n) (t : ℕ) (ht : p.totalDegree ≤ t) :
    restrictTotalDegree (Fin n) K (t - p.totalDegree) →ₗ[K]
      restrictTotalDegree (Fin n) K t where
  toFun q := ⟨p * q.val, by
    apply (mem_restrictTotalDegree _ _ _).mpr
    have hq := (mem_restrictTotalDegree _ _ _).mp q.property
    exact (totalDegree_mul p q.val).trans (by omega)⟩
  map_add' q r := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' c q := by apply Subtype.ext; exact mul_smul_comm _ _ _

lemma filteredPrincipalMultiple_injective {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K n) (hp : p ≠ 0) (t : ℕ) (ht : p.totalDegree ≤ t) :
    Function.Injective (filteredPrincipalMultiple p t ht) := by
  intro q r h
  apply Subtype.ext
  exact mul_left_cancel₀ hp (congrArg Subtype.val h)

lemma filteredPrincipalMultiple_range {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (p : Polynomials K n) (hp : p ≠ 0)
    (hX : vanishingIdeal K X = Ideal.span {p}) (t : ℕ) (ht : p.totalDegree ≤ t) :
    LinearMap.range (filteredPrincipalMultiple p t ht) = LinearMap.ker (filteredEvaluation X t) := by
  ext q
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨r, rfl⟩
    funext x
    have hpX : p ∈ vanishingIdeal K X := by rw [hX]; exact Ideal.subset_span (Set.mem_singleton p)
    change eval x.val (p * r.val) = 0
    have hz : eval x.val p = 0 := by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hpX x.val x.property
    rw [map_mul, hz, zero_mul]
  · intro hq
    have hqX : q.val ∈ vanishingIdeal K X := by
      intro x hx
      exact congrFun hq ⟨x, hx⟩
    rw [hX, Ideal.mem_span_singleton] at hqX
    obtain ⟨r, hr⟩ := hqX
    have hrdeg : r.totalDegree ≤ t - p.totalDegree := by
      by_cases hr0 : r = 0
      · simp [hr0]
      · have hqdeg := (mem_restrictTotalDegree _ _ _).mp q.property
        rw [hr, totalDegree_mul_of_isDomain hp hr0] at hqdeg
        omega
    exact ⟨⟨r, (mem_restrictTotalDegree _ _ _).mpr hrdeg⟩, Subtype.ext hr.symm⟩

lemma principal_affineHilbertFunction {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (p : Polynomials K n) (hp : p ≠ 0)
    (hX : vanishingIdeal K X = Ideal.span {p}) (t : ℕ) (ht : p.totalDegree ≤ t) :
    affineHilbertFunction X t + (n + (t - p.totalDegree)).choose n = (n + t).choose n := by
  have hh := (filteredEvaluation X t).finrank_range_add_finrank_ker
  rw [filteredEvaluation_range, ← filteredPrincipalMultiple_range X p hp hX t ht,
    LinearMap.finrank_range_of_inj (filteredPrincipalMultiple_injective p hp t ht),
    restrictTotalDegree_finrank, restrictTotalDegree_finrank] at hh
  exact hh

end APSCounting893.Main
end Component_6

section Component_7

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def filteredImagePullback {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (D t : ℕ) (hD : ∀ i, (F i).totalDegree ≤ D) :
    affineFilteredPiece (imageClosure F) t →ₗ[K]
      affineFilteredPiece (Set.univ : Set (Affine K n)) (D * t) where
  toFun f :=
    ⟨fun x => f.val ⟨evaluate F x.val, zeroLocus_vanishingIdeal_le _ (Set.mem_range_self _)⟩, by
      obtain ⟨p, hp, hrepr⟩ := (mem_affineFilteredPiece _ _ f.val).mp f.property
      apply (mem_affineFilteredPiece _ _ _).mpr
      refine ⟨eval₂Hom MvPolynomial.C F p, ?_, ?_⟩
      · have hd := totalDegree_eval₂_bounded (RingHom.id K) F D hD p
        have hd' : (eval₂Hom MvPolynomial.C F p).totalDegree ≤ D * p.totalDegree := by simpa using hd
        exact hd'.trans (Nat.mul_le_mul_left D hp)
      · funext x
        rw [hrepr]
        exact (evaluation_substitution F p x.val).symm⟩
  map_add' f g := by apply Subtype.ext; funext x; rfl
  map_smul' c f := by apply Subtype.ext; funext x; rfl

lemma filteredImagePullback_injective {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (D t : ℕ) (hD : ∀ i, (F i).totalDegree ≤ D) :
    Function.Injective (filteredImagePullback F D t hD) := by
  intro f g h
  obtain ⟨p, hp, hfp⟩ := (mem_affineFilteredPiece _ _ f.val).mp f.property
  obtain ⟨q, hq, hgq⟩ := (mem_affineFilteredPiece _ _ g.val).mp g.property
  have hI : p - q ∈ vanishingIdeal K (Set.range (evaluate F)) := by
    rintro y ⟨x, rfl⟩
    have hh := congrArg (fun z : affineFilteredPiece (Set.univ : Set (Affine K n)) (D * t) =>
      z.val ⟨x, Set.mem_univ x⟩) h
    change f.val ⟨evaluate F x, _⟩ = g.val ⟨evaluate F x, _⟩ at hh
    rw [hfp, hgq] at hh
    change eval (evaluate F x) (p - q) = 0
    rw [map_sub, sub_eq_zero]
    exact hh
  have hIc : p - q ∈ vanishingIdeal K (imageClosure F) := by
    simpa only [imageClosure, vanishingIdeal_zClosure] using hI
  apply Subtype.ext
  funext y
  rw [hfp, hgq]
  have hh := hIc y.val y.property
  change eval y.val (p - q) = 0 at hh
  rwa [map_sub, sub_eq_zero] at hh

lemma image_affineHilbertFunction_le {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (D t : ℕ) (hD : ∀ i, (F i).totalDegree ≤ D) :
    affineHilbertFunction (imageClosure F) t ≤ affineHilbertFunction (Set.univ : Set (Affine K n)) (D * t) := by
  exact LinearMap.finrank_le_finrank_of_injective (filteredImagePullback_injective F D t hD)

end APSCounting893.Main
end Component_7

section Component_8

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Polynomial
namespace APSCounting893.Main

lemma coefficient_le_of_eventual_nat_eval_le (p q : Polynomial ℚ) (n : ℕ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (heval : ∃ N : ℕ, ∀ m ≥ N, p.eval (m : ℚ) ≤ q.eval (m : ℚ)) :
    p.coeff n ≤ q.coeff n := by
  by_contra h
  have hcoeff : (q - p).coeff n < 0 := by rw [coeff_sub]; linarith
  have hne : q - p ≠ 0 := by intro hz; simp [hz] at hcoeff
  have hdeg : (q - p).natDegree = n :=
    le_antisymm ((natDegree_sub_le q p).trans (max_le hq hp))
      (le_natDegree_of_ne_zero (ne_of_lt hcoeff))
  have hlc : (q - p).leadingCoeff < 0 := by simpa only [leadingCoeff, hdeg] using hcoeff
  obtain ⟨N, hN⟩ := heval
  by_cases hn : n = 0
  · have hz : q - p = C ((q - p).coeff 0) := eq_C_of_natDegree_eq_zero (hdeg.trans hn)
    have hval := hN N le_rfl
    have hr : 0 ≤ (q - p).eval (N : ℚ) := by rw [eval_sub]; linarith
    rw [hz, eval_C] at hr
    rw [hn] at hcoeff
    linarith
  · have hdpos : 0 < (q - p).degree := natDegree_pos_iff_degree_pos.mp (by omega)
    have hlim := ((q - p).tendsto_atBot_of_leadingCoeff_nonpos hdpos hlc.le).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℚ)) atTop atTop)
    obtain ⟨m, hm, hneg⟩ := ((eventually_ge_atTop N).and (hlim.eventually_lt_atBot 0)).exists
    change (q - p).eval (m : ℚ) < 0 at hneg
    have hval := hN m hm
    have hr : 0 ≤ (q - p).eval (m : ℚ) := by rw [eval_sub]; linarith
    linarith

end APSCounting893.Main
end Component_8

section Component_9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Polynomial
namespace APSCounting893.Main

lemma imageHilbert_le_choose {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (D t : ℕ) (hD : ∀ i, (F i).totalDegree ≤ D) :
    affineHilbertFunction (imageClosure F) t ≤ (n + D * t).choose n := by
  simpa only [univ_affineHilbertFunction] using image_affineHilbertFunction_le F D t hD

lemma imageHilbert_leading_bound {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (D : ℕ) (hDpos : 0 < D) (hD : ∀ i, (F i).totalDegree ≤ D)
    (p : Polynomial ℚ) (hpdeg : p.natDegree = n)
    (hp : ∃ N : ℕ, ∀ t ≥ N, p.eval (t : ℚ) = (affineHilbertFunction (imageClosure F) t : ℚ)) :
    p.leadingCoeff * (n.factorial : ℚ) ≤ (D : ℚ) ^ n := by
  classical
  let H := Polynomial.preHilbertPoly ℚ n 0
  let Q := H.comp (Polynomial.C (D : ℚ) * Polynomial.X)
  have hDne : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hlin : (Polynomial.C (D : ℚ) * Polynomial.X).natDegree = 1 := natDegree_C_mul_X (D : ℚ) hDne
  have hQdeg : Q.natDegree = n := by
    simp only [Q, Polynomial.natDegree_comp, H, Polynomial.natDegree_preHilbertPoly, hlin, mul_one]
  have hQc : Q.coeff n = (n.factorial : ℚ)⁻¹ * (D : ℚ) ^ n := by
    have hh := Polynomial.coeff_comp_degree_mul_degree
      (p := H) (q := Polynomial.C (D : ℚ) * Polynomial.X) (by rw [hlin]; decide)
    simpa only [Q, H, Polynomial.natDegree_preHilbertPoly, hlin, mul_one,
      Polynomial.leadingCoeff_preHilbertPoly, Polynomial.leadingCoeff_C_mul_X] using hh
  have hQeval (t : ℕ) : Q.eval (t : ℚ) = ((n + D * t).choose n : ℚ) := by
    rw [Polynomial.eval_comp]
    have hv : (Polynomial.C (D : ℚ) * Polynomial.X).eval (t : ℚ) = ((D * t : ℕ) : ℚ) := by simp
    rw [hv]
    have hh := Polynomial.preHilbertPoly_eq_choose_sub_add (F := ℚ) n (k := 0) (n := D * t) (Nat.zero_le _)
    simpa only [H, Nat.sub_zero, Nat.add_comm] using hh
  have heval : ∃ N : ℕ, ∀ t ≥ N, p.eval (t : ℚ) ≤ Q.eval (t : ℚ) := by
    obtain ⟨N, hN⟩ := hp
    refine ⟨N, ?_⟩
    intro t ht
    rw [hN t ht, hQeval t]
    exact_mod_cast imageHilbert_le_choose F D t hD
  have hc := coefficient_le_of_eventual_nat_eval_le p Q n hpdeg.le hQdeg.le heval
  rw [← hpdeg, Polynomial.coeff_natDegree] at hc
  rw [hpdeg, hQc] at hc
  have hfac : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ (n.factorial : ℚ) by positivity)
  have hr : (n.factorial : ℚ)⁻¹ * (D : ℚ) ^ n * (n.factorial : ℚ) = (D : ℚ) ^ n := by field_simp
  rwa [hr] at hm

end APSCounting893.Main
end Component_9

section Component_10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open Polynomial
namespace APSCounting893.Main

lemma choose_hypersurface_sum (n D t : ℕ) (ht : D ≤ t) :
    (∑ i ∈ Finset.range D, (n + (t - i)).choose n) +
      (n + 1 + (t - D)).choose (n + 1) = (n + 1 + t).choose (n + 1) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_range_succ]
    have hD : D ≤ t := by omega
    have hpas : (n + (t - D)).choose n +
        (n + 1 + (t - (D + 1))).choose (n + 1) =
        (n + 1 + (t - D)).choose (n + 1) := by
      have hh := Nat.choose_succ_succ (n + 1 + (t - (D + 1))) n
      simp only [Nat.succ_eq_add_one] at hh
      have ha : n + 1 + (t - (D + 1)) = n + (t - D) := by omega
      have hb : n + 1 + (t - (D + 1)) + 1 = n + 1 + (t - D) := by omega
      rw [hb] at hh
      rw [ha] at hh
      simpa only [ha] using hh.symm
    rw [add_assoc, hpas]
    exact ih hD

noncomputable def principalHilbertPoly (n D : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range D, preHilbertPoly ℚ n i

lemma principalHilbertPoly_coeff (n D : ℕ) :
    (principalHilbertPoly n D).coeff n = (D : ℚ) * (n.factorial : ℚ)⁻¹ := by
  simp [principalHilbertPoly, Polynomial.coeff_sum, coeff_preHilbertPoly_self]

lemma principalHilbertPoly_degree (n D : ℕ) (hD : 0 < D) :
    (principalHilbertPoly n D).natDegree = n := by
  apply le_antisymm
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_preHilbertPoly ℚ n i).le
  · apply le_natDegree_of_ne_zero
    rw [principalHilbertPoly_coeff]
    positivity

lemma principalHilbertPoly_eventual {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K (n + 1))) (p : Polynomials K (n + 1)) (hp : p ≠ 0)
    (hX : MvPolynomial.vanishingIdeal K X = Ideal.span {p}) :
    ∃ N : ℕ, ∀ t ≥ N, (principalHilbertPoly n p.totalDegree).eval (t : ℚ) =
      (affineHilbertFunction X t : ℚ) := by
  refine ⟨p.totalDegree, ?_⟩
  intro t ht
  have hf := principal_affineHilbertFunction X p hp hX t ht
  have hs := choose_hypersurface_sum n p.totalDegree t ht
  have heval : (principalHilbertPoly n p.totalDegree).eval (t : ℚ) =
      ((∑ i ∈ Finset.range p.totalDegree, (n + (t - i)).choose n : ℕ) : ℚ) := by
    simp only [principalHilbertPoly, eval_finsetSum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ t := (Finset.mem_range.mp hi).le.trans ht
    simpa only [Nat.add_comm] using preHilbertPoly_eq_choose_sub_add (F := ℚ) n hi'
  rw [heval]
  congr 1
  omega

lemma principal_image_relation_degree {K : Type} [Field K] [Infinite K] {n : ℕ}
    (F : PolynomialMap K n (n + 1)) (d : ℕ) (hd : 0 < d)
    (hF : ∀ i, (F i).totalDegree ≤ d)
    (p : Polynomials K (n + 1)) (hp : p ≠ 0) (hpD : 0 < p.totalDegree)
    (hI : MvPolynomial.vanishingIdeal K (imageClosure F) = Ideal.span {p}) :
    p.totalDegree ≤ d ^ n := by
  let H := principalHilbertPoly n p.totalDegree
  have hH := principalHilbertPoly_degree n p.totalDegree hpD
  have hbound := imageHilbert_leading_bound F d hd hF H hH
    (principalHilbertPoly_eventual (imageClosure F) p hp hI)
  have hcoeff : H.leadingCoeff = (p.totalDegree : ℚ) * (n.factorial : ℚ)⁻¹ := by
    rw [Polynomial.leadingCoeff, show H.natDegree = n from hH]
    exact principalHilbertPoly_coeff n p.totalDegree
  rw [hcoeff] at hbound
  have hfac : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hh : (p.totalDegree : ℚ) * (n.factorial : ℚ)⁻¹ * (n.factorial : ℚ) = p.totalDegree := by field_simp
  rw [hh] at hbound
  exact_mod_cast hbound

end APSCounting893.Main
end Component_10

section Component_11

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma perron_relation_of_independent {K : Type} [Field K] [Infinite K] {n : ℕ}
    (g : Fin n → Polynomials K n) (hg : AlgebraicIndependent K g)
    (f : Polynomials K n) (d : ℕ) (hd : 0 < d)
    (hf : f.totalDegree ≤ d) (hgD : ∀ i, (g i).totalDegree ≤ d) :
    ∃ q : Polynomials K (n + 1), q ≠ 0 ∧ 0 < q.totalDegree ∧
      q.totalDegree ≤ d ^ n ∧ aeval (Fin.cons f g) q = 0 ∧
      vanishingIdeal K (imageClosure (Fin.cons f g)) = Ideal.span {q} := by
  classical
  let F : PolynomialMap K n (n + 1) := Fin.cons f g
  let I := RingHom.ker (aeval (R := K) F).toRingHom
  haveI : I.IsPrime := RingHom.ker_isPrime _
  have hI : I ≠ ⊥ := polynomial_map_kernel_ne_bot n F
  have hcontract : I.comap (rename Fin.succ) = ⊥ := by
    ext p
    change aeval F (rename Fin.succ p) = 0 ↔ p = 0
    rw [aeval_rename]
    have hcomp : F ∘ Fin.succ = g := by funext i; simp [F]
    rw [hcomp]
    constructor
    · exact hg.eq_zero_of_aeval_eq_zero p
    · rintro rfl; exact map_zero _
  obtain ⟨q, hq⟩ := mv_prime_principal_of_contract_succ_zero I hcontract
  have hq0 : q ≠ 0 := by
    intro h0
    apply hI
    rw [hq, h0]
    exact Submodule.span_eq_bot.mpr (by simp)
  have hqmem : q ∈ I := by rw [hq]; exact Ideal.subset_span (Set.mem_singleton q)
  have hqD : 0 < q.totalDegree := by
    by_contra h
    have hD : q.totalDegree = 0 := by omega
    have he : q = C (q.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hD
    have hc : q.coeff 0 ≠ 0 := by intro hc; simp [hc] at he; exact hq0 he
    have hu : IsUnit q := isUnit_iff_totalDegree_of_isReduced.mpr ⟨isUnit_iff_ne_zero.mpr hc, hD⟩
    exact Ideal.IsPrime.ne_top' (Ideal.eq_top_of_isUnit_mem I hqmem hu)
  have hvan : vanishingIdeal K (imageClosure F) = Ideal.span {q} := by
    rw [imageClosure, vanishingIdeal_zClosure, image_vanishingIdeal_eq_kernel]
    exact hq
  have hFD : ∀ i, (F i).totalDegree ≤ d := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hf
    · exact hgD j
  exact ⟨q, hq0, hqD, principal_image_relation_degree F d hd hFD q hq0 hqD hvan, hqmem, hvan⟩

end APSCounting893.Main
end Component_11

section Component_12

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma betaPolynomials_algebraicIndependent (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c) :
    AlgebraicIndependent ℂ (betaPolynomials F c) := by
  apply algebraicIndependent_iff.mpr
  intro p hp
  let q : Polynomials ℂ (F.n + 1) := aeval (normalizationPolynomials c) p
  have hsub : aeval F.F q = aeval (betaPolynomials F c) p := by
    dsimp only [q]
    rw [comp_aeval_apply]
    rfl
  have hqimage : q ∈ vanishingIdeal ℂ (imageClosure F.F) := by
    rw [imageClosure, vanishingIdeal_zClosure, image_vanishingIdeal_eq_kernel]
    exact hsub.trans hp
  have hqzero : ∀ y ∈ imageClosure F.F, eval (normalization c y) p = 0 := by
    intro y hy
    have h := hqimage y hy
    change aeval y q = 0 at h
    have he : eval y q = eval (normalization c y) p :=
      evaluation_substitution (normalizationPolynomials c) p y
    exact he ▸ h
  apply MvPolynomial.funext
  intro y
  exact hc.2.2.1 p hqzero y (Set.mem_univ y)

lemma betaPolynomials_degree_bound (F : ReducedMap) (c : Affine ℂ F.n) (i : Fin F.n) :
    (betaPolynomials F c i).totalDegree ≤ F.d := by
  apply (totalDegree_eval₂_bounded (RingHom.id ℂ) F.F F.d F.degree_bound
    (normalizationPolynomials c i)).trans
  exact (Nat.mul_le_mul_left F.d (normalizationPolynomials_degree_le c i)).trans_eq (Nat.mul_one _)

lemma normalized_coordinate_perron (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c) (i : Fin F.n) :
    ∃ q : Polynomials ℂ (F.n + 1), q ≠ 0 ∧ 0 < q.totalDegree ∧
      q.totalDegree ≤ F.d ^ F.n ∧ aeval (Fin.cons (X i) (betaPolynomials F c)) q = 0 := by
  obtain ⟨q, hq0, hqD, hqbound, hq, _⟩ := perron_relation_of_independent
    (betaPolynomials F c) (betaPolynomials_algebraicIndependent F c hc)
    (X i) F.d (by have := F.degree_ge_two; omega)
    (by simpa only [totalDegree_X] using F.degree_ge_two.trans' (by omega : 1 ≤ 2))
    (betaPolynomials_degree_bound F c)
  exact ⟨q, hq0, hqD, hqbound, hq⟩

end APSCounting893.Main
end Component_12

section Component_13

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma normalized_coordinate_relation_coefficients (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c) (i : Fin F.n) :
    ∃ p : Polynomial (Polynomials ℂ F.n), 0 < p.natDegree ∧
      p.leadingCoeff ≠ 0 ∧ p.leadingCoeff.totalDegree ≤ F.d ^ F.n ∧
      ∀ x : Affine ℂ F.n,
        Polynomial.eval (x i) (p.map (eval (evaluate (betaPolynomials F c) x))) = 0 := by
  classical
  obtain ⟨q, hq0, hqD, hqbound, hq⟩ := normalized_coordinate_perron F c hc i
  let e := MvPolynomial.finSuccEquiv ℂ F.n
  let p := e q
  have hp0 : p ≠ 0 := e.injective.ne (by simpa using hq0)
  have hpdeg : 0 < p.natDegree := by
    by_contra h
    have hd : p.natDegree = 0 := by omega
    have he : q = rename Fin.succ (p.coeff 0) := by
      apply e.injective
      rw [finSuccEquiv_rename_succ]
      exact Polynomial.eq_C_of_natDegree_eq_zero hd
    have hroot : aeval (betaPolynomials F c) (p.coeff 0) = 0 := by
      rw [he, aeval_rename] at hq
      simpa only [Function.comp_def, Fin.cons_succ] using hq
    have hz := (betaPolynomials_algebraicIndependent F c hc).eq_zero_of_aeval_eq_zero _ hroot
    apply hp0
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, hz, Polynomial.C_0]
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hdeg := totalDegree_coeff_finSuccEquiv_add_le q p.natDegree
    (show (e q).coeff p.natDegree ≠ 0 from hlc)
  refine ⟨p, hpdeg, hlc, (Nat.le_add_right _ _).trans (hdeg.trans hqbound), ?_⟩
  intro x
  have hzero : eval x (aeval (Fin.cons (X i) (betaPolynomials F c)) q) = 0 := by rw [hq, map_zero]
  have heval : eval x (aeval (Fin.cons (X i) (betaPolynomials F c)) q) =
      eval (Fin.cons (x i) (evaluate (betaPolynomials F c) x)) q := by
    change eval x (eval₂Hom C (Fin.cons (X i) (betaPolynomials F c)) q) = _
    rw [evaluation_substitution]
    congr 2
    funext j
    refine Fin.cases ?_ (fun l => ?_) j <;> simp [evaluate]
  rw [heval, eval_eq_eval_mv_eval'] at hzero
  exact hzero

lemma normalized_perron_product (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c) :
    ∃ (p : Fin F.n → Polynomial (Polynomials ℂ F.n)) (b : Polynomials ℂ F.n),
      b = ∏ i, (p i).leadingCoeff ∧ b ≠ 0 ∧ b.totalDegree ≤ F.n * F.d ^ F.n ∧
      (∀ i, 0 < (p i).natDegree) ∧
      (∀ i x, Polynomial.eval (x i) ((p i).map (eval (evaluate (betaPolynomials F c) x))) = 0) := by
  classical
  choose p hpdeg hp0 hpbound hproot using normalized_coordinate_relation_coefficients F c hc
  refine ⟨p, ∏ i, (p i).leadingCoeff, rfl, Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 i), ?_, hpdeg, hproot⟩
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i : Fin F.n, ((p i).leadingCoeff).totalDegree ≤ ∑ _i : Fin F.n, F.d ^ F.n :=
      Finset.sum_le_sum (fun i _ => hpbound i)
    _ = F.n * F.d ^ F.n := by simp

end APSCounting893.Main
end Component_13

section Component_14

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial
namespace APSCounting893.Main

lemma natDegree_eq_of_eventual_nat_eval_sandwich (p low high : Polynomial ℚ) (n : ℕ)
    (hlowdeg : low.natDegree = n) (hhighdeg : high.natDegree = n) (hlowpos : 0 < low.leadingCoeff)
    (hlow : ∃ N : ℕ, ∀ t ≥ N, low.eval (t : ℚ) ≤ p.eval (t : ℚ))
    (hhigh : ∃ N : ℕ, ∀ t ≥ N, p.eval (t : ℚ) ≤ high.eval (t : ℚ)) : p.natDegree = n := by
  have hpne : p ≠ 0 := by
    intro hpzero
    have hh := coefficient_le_of_eventual_nat_eval_le low p n hlowdeg.le (by simp [hpzero]) hlow
    have hc : low.coeff n = low.leadingCoeff := by rw [← hlowdeg, coeff_natDegree]
    rw [hc, hpzero, coeff_zero] at hh
    linarith
  apply le_antisymm
  · by_contra hn
    have hn' : n < p.natDegree := by omega
    have hlc : low.coeff p.natDegree = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hhc : high.coeff p.natDegree = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h1 := coefficient_le_of_eventual_nat_eval_le low p p.natDegree (by omega) le_rfl hlow
    have h2 := coefficient_le_of_eventual_nat_eval_le p high p.natDegree le_rfl (by omega) hhigh
    rw [hlc, coeff_natDegree] at h1
    rw [hhc, coeff_natDegree] at h2
    exact hpne (leadingCoeff_eq_zero.mp (le_antisymm h2 h1))
  · by_contra hn
    have hn' : p.natDegree < n := by omega
    have hpc : p.coeff n = 0 := coeff_eq_zero_of_natDegree_lt hn'
    have hh := coefficient_le_of_eventual_nat_eval_le low p n hlowdeg.le hn'.le hlow
    have hc : low.coeff n = low.leadingCoeff := by rw [← hlowdeg, coeff_natDegree]
    rw [hc, hpc] at hh
    linarith

end APSCounting893.Main
end Component_14

section Component_15

set_option autoImplicit false
open scoped BigOperators fwdDiff
open Polynomial
namespace APSCounting893.Main

lemma leading_factorial_integer_of_eventual_integer (p : Polynomial ℚ)
    (hp : ∃ N : ℕ, ∀ t ≥ N, ∃ z : ℤ, p.eval (t : ℚ) = (z : ℚ)) :
    ∃ z : ℤ, p.leadingCoeff * (p.natDegree.factorial : ℚ) = (z : ℚ) := by
  classical
  obtain ⟨N, hN⟩ := hp
  choose z hz using fun i : ℕ => hN (N + i) (Nat.le_add_right N i)
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1),
    ((-1 : ℤ) ^ (p.natDegree - i) * p.natDegree.choose i) * z i, ?_⟩
  have h := congrFun p.fwdDiff_iter_degree_eq_factorial (N : ℚ)
  rw [fwdDiff_iter_eq_sum_shift] at h
  have hsum : (∑ i ∈ Finset.range (p.natDegree + 1),
      ((-1 : ℤ) ^ (p.natDegree - i) * p.natDegree.choose i) •
        p.eval ((N : ℚ) + i • (1 : ℚ))) =
      ((∑ i ∈ Finset.range (p.natDegree + 1),
        ((-1 : ℤ) ^ (p.natDegree - i) * p.natDegree.choose i) * z i : ℤ) : ℚ) := by
    simp only [Int.cast_sum, Int.cast_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (N : ℚ) + i • (1 : ℚ) = ((N + i : ℕ) : ℚ) by simp, hz i]
    simp
  rw [hsum] at h
  simpa using h.symm

end APSCounting893.Main
end Component_15

section Component_16

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace APSCounting893.Main

lemma affineHilbertPolynomial_spec {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n))
    (hex : ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ t ≥ N,
      p.eval (t : ℚ) = (affineHilbertFunction X t : ℚ)) :
    ∃ N : ℕ, ∀ t ≥ N,
      (affineHilbertPolynomial X).eval (t : ℚ) = (affineHilbertFunction X t : ℚ) :=
  Classical.epsilon_spec hex

lemma reduced_image_degree_bound_of_hilbert_exists (F : ReducedMap)
    (c : Affine ℂ F.n) (hc : IsNormalization (imageClosure F.F) c)
    (hex : ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ t ≥ N,
      p.eval (t : ℚ) = (affineHilbertFunction (imageClosure F.F) t : ℚ)) :
    projectiveDegree (imageClosure F.F) ≤ F.d ^ F.n := by
  classical
  let p := affineHilbertPolynomial (imageClosure F.F)
  have hp := affineHilbertPolynomial_spec (imageClosure F.F) hex
  change ∃ N : ℕ, ∀ t ≥ N, p.eval (t : ℚ) = _ at hp
  let low := preHilbertPoly ℚ F.n 0
  let high := low.comp (C (F.d : ℚ) * X)
  have hDpos : 0 < F.d := by have := F.degree_ge_two; omega
  have hDne : (F.d : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hlin : (C (F.d : ℚ) * X).natDegree = 1 := natDegree_C_mul_X (F.d : ℚ) hDne
  have hlowdeg : low.natDegree = F.n := natDegree_preHilbertPoly _ _ _
  have hhighdeg : high.natDegree = F.n := by
    simp only [high, natDegree_comp, hlowdeg, hlin, mul_one]
  have hlowpos : 0 < low.leadingCoeff := by
    rw [show low.leadingCoeff = (F.n.factorial : ℚ)⁻¹ from leadingCoeff_preHilbertPoly _ _ _]
    positivity
  have hloweval (t : ℕ) : low.eval (t : ℚ) = ((F.n + t).choose F.n : ℚ) := by
    simpa only [low, Nat.sub_zero, Nat.add_comm] using
      preHilbertPoly_eq_choose_sub_add (F := ℚ) F.n (k := 0) (n := t) (Nat.zero_le _)
  have hhigheval (t : ℕ) : high.eval (t : ℚ) = ((F.n + F.d * t).choose F.n : ℚ) := by
    rw [eval_comp]
    have he : (C (F.d : ℚ) * X).eval (t : ℚ) = ((F.d * t : ℕ) : ℚ) := by simp
    rw [he, hloweval]
  obtain ⟨N, hN⟩ := hp
  have hlow : ∃ N : ℕ, ∀ t ≥ N, low.eval (t : ℚ) ≤ p.eval (t : ℚ) := by
    refine ⟨N, fun t ht => ?_⟩
    rw [hN t ht, hloweval]
    exact_mod_cast normalization_affineHilbert_lower _ c hc t
  have hhigh : ∃ N : ℕ, ∀ t ≥ N, p.eval (t : ℚ) ≤ high.eval (t : ℚ) := by
    refine ⟨N, fun t ht => ?_⟩
    rw [hN t ht, hhigheval]
    exact_mod_cast imageHilbert_le_choose F.F F.d t F.degree_bound
  have hpdeg := natDegree_eq_of_eventual_nat_eval_sandwich p low high F.n
    hlowdeg hhighdeg hlowpos hlow hhigh
  have hleadpos : 0 < p.leadingCoeff := by
    have hle := coefficient_le_of_eventual_nat_eval_le low p F.n hlowdeg.le hpdeg.le hlow
    rw [← hlowdeg, coeff_natDegree, hlowdeg, ← hpdeg, coeff_natDegree] at hle
    exact hlowpos.trans_le hle
  have hbound := imageHilbert_leading_bound F.F F.d hDpos F.degree_bound p hpdeg ⟨N, hN⟩
  obtain ⟨z, hz⟩ := leading_factorial_integer_of_eventual_integer p
    ⟨N, fun t ht => ⟨(affineHilbertFunction (imageClosure F.F) t : ℤ), by simpa using hN t ht⟩⟩
  have hzpos : 0 ≤ z := by
    have hh : 0 ≤ p.leadingCoeff * (p.natDegree.factorial : ℚ) := by positivity
    rw [hz] at hh
    exact_mod_cast hh
  change (p.leadingCoeff * (p.natDegree.factorial : ℚ)).num.natAbs ≤ F.d ^ F.n
  rw [hz, Rat.num_intCast]
  have hb : (z : ℚ) ≤ ((F.d ^ F.n : ℕ) : ℚ) := by
    rw [← hz, hpdeg]
    exact_mod_cast hbound
  have hb' : z ≤ (F.d ^ F.n : ℤ) := by exact_mod_cast hb
  exact_mod_cast (show (z.natAbs : ℤ) ≤ (F.d ^ F.n : ℤ) by
    rw [Int.natCast_natAbs, abs_of_nonneg hzpos]
    exact hb')

end APSCounting893.Main
end Component_16

section Component_17

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma eval_homogenize_monomial {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (z : Fin (n + 1) → K) (e : Fin n →₀ ℕ) (c : R) (d : ℕ) :
    MvPolynomial.eval₂ f z (MvPolynomial.monomial
      (Finsupp.single 0 (d - e.sum (fun _ k => k)) + e.mapDomain Fin.succ) c) =
    f c * z 0 ^ (d - e.sum (fun _ k => k)) * e.prod (fun i k => z i.succ ^ k) := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rw [Finsupp.prod_single_index (h := fun i k => z i ^ k) (pow_zero (z 0))]
  rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  ring

lemma finsupp_prod_scaled {K : Type} [Field K] {n : ℕ}
    (e : Fin n →₀ ℕ) (a : K) (x : Fin n → K) :
    e.prod (fun i k => (a * x i) ^ k) =
      a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k) := by
  classical
  rw [e.prod_fintype _ (fun _ => pow_zero _), e.prod_fintype _ (fun _ => pow_zero _),
    e.sum_fintype _ (fun _ => rfl)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

lemma eval_homogenize_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (a : K) (x : Fin n → K) :
    MvPolynomial.eval₂ f (Fin.cases a (fun i => a * x i)) (homogenizeAll d p) =
      a ^ d * MvPolynomial.eval₂ f x p := by
  classical
  rw [homogenizeAll, MvPolynomial.eval₂_sum]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval_homogenize_monomial]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [finsupp_prod_scaled]
  have hedeg : e.sum (fun _ k => k) ≤ d := (MvPolynomial.le_totalDegree he).trans hd
  have hpow : a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k) = a ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hedeg]
  calc
    f (p.coeff e) * a ^ (d - e.sum (fun _ k => k)) *
        (a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k)) =
      (a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k)) *
        (f (p.coeff e) * e.prod (fun i k => x i ^ k)) := by ring
    _ = _ := by rw [hpow]; rfl

lemma eval_homogenize_dehomogenize {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (z : Fin (n + 1) → K) (hz : z 0 ≠ 0) :
    MvPolynomial.eval₂ f z (homogenizeAll d p) =
      z 0 ^ d * MvPolynomial.eval₂ f (fun i => z i.succ / z 0) p := by
  have heq : Fin.cases (z 0) (fun i => z 0 * (z i.succ / z 0)) = z := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp [hz, mul_div_cancel₀, mul_comm]
  simpa only [heq] using eval_homogenize_scaled f p d hd (z 0) (fun i => z i.succ / z 0)

end APSCounting893.Main
end Component_17

section Component_18

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial
namespace APSCounting893.Main

noncomputable def chartHomogeneousIdeal {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    Ideal (Polynomials K (n + 1)) :=
  Ideal.span {p | ∃ d : ℕ, p.IsHomogeneous d ∧ ∀ x ∈ X, eval (Fin.cons 1 x) p = 0}

lemma chartHomogeneousIdeal_isHomogeneous {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    (chartHomogeneousIdeal X).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) := by
  apply Ideal.homogeneous_span
  rintro p ⟨d, hd, hx⟩
  exact ⟨d, hd⟩

lemma chartHomogeneousIdeal_le_vanishing {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    chartHomogeneousIdeal X ≤ vanishingIdeal K ((fun x : Affine K n => Fin.cons 1 x) '' X) := by
  apply Ideal.span_le.mpr
  rintro p ⟨d, hd, hzero⟩ y ⟨x, hx, rfl⟩
  exact hzero x hx

lemma homogeneous_mem_chartIdeal_iff {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (p : Polynomials K (n + 1)) (d : ℕ) (hd : p.IsHomogeneous d) :
    p ∈ chartHomogeneousIdeal X ↔ ∀ x ∈ X, eval (Fin.cons 1 x) p = 0 := by
  constructor
  · intro hp x hx
    exact chartHomogeneousIdeal_le_vanishing X hp (Fin.cons 1 x) ⟨x, hx, rfl⟩
  · intro hp
    exact Ideal.subset_span ⟨d, hd, hp⟩

lemma homogenizeAll_isHomogeneous {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K n) (d : ℕ) (hd : p.totalDegree ≤ d) :
    (homogenizeAll d p).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  apply MvPolynomial.isHomogeneous_monomial
  rw [map_add, Finsupp.degree_single, Finsupp.degree_mapDomain, Finsupp.degree_eq_sum,
    ← finsupp_nat_sum_eq]
  exact Nat.sub_add_cancel ((MvPolynomial.le_totalDegree he).trans hd)

lemma eval_homogenize_chart {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K n) (d : ℕ) (hd : p.totalDegree ≤ d) (x : Affine K n) :
    eval (Fin.cons 1 x) (homogenizeAll d p) = eval x p := by
  have hh := eval_homogenize_scaled (RingHom.id K) p d hd 1 x
  have he : (Fin.cons (α := fun _ : Fin (n + 1) => K) (1 : K) x) = (fun i : Fin (n + 1) => Fin.cases (1 : K) (fun j : Fin n => x j) i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [he]
  simpa using hh

end APSCounting893.Main
end Component_18

section Component_19

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial
namespace APSCounting893.Main

noncomputable def chartDehomogenize {K : Type} [Field K] {n : ℕ} :
    Polynomials K (n + 1) →ₐ[K] Polynomials K n :=
  MvPolynomial.aeval (Fin.cons 1 (fun i : Fin n => MvPolynomial.X i))

lemma chartDehomogenize_degree {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K (n + 1)) :
    (chartDehomogenize p).totalDegree ≤ p.totalDegree := by
  have h := totalDegree_eval₂_bounded (RingHom.id K)
    (Fin.cons 1 (fun i : Fin n => MvPolynomial.X i)) 1 (fun i => ?_) p
  · simpa [chartDehomogenize, MvPolynomial.aeval_def] using h
  · refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma eval_chartDehomogenize {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K (n + 1)) (x : Affine K n) :
    eval x (chartDehomogenize p) = eval (Fin.cons 1 x) p := by
  apply MvPolynomial.induction_on p
  · intro c; simp [chartDehomogenize]
  · intro p q hp hq; simpa only [map_add] using congrArg₂ (· + ·) hp hq
  · intro p i hp
    simp only [map_mul, hp]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [chartDehomogenize]

noncomputable def homogeneousChartEvaluation {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    homogeneousSubmodule (Fin (n + 1)) K d →ₗ[K] (X → K) where
  toFun p := fun x => eval (Fin.cons 1 x.val) p.val
  map_add' p q := by funext x; exact map_add (eval (Fin.cons 1 x.val)) p.val q.val
  map_smul' c p := by funext x; simp [MvPolynomial.smul_eq_C_mul]

lemma homogeneousChartEvaluation_range {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    LinearMap.range (homogeneousChartEvaluation X d) = affineFilteredPiece X d := by
  ext f
  rw [LinearMap.mem_range, mem_affineFilteredPiece]
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨chartDehomogenize p.val,
      (chartDehomogenize_degree p.val).trans p.property.totalDegree_le, ?_⟩
    funext x
    exact (eval_chartDehomogenize p.val x.val).symm
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨homogenizeAll d p, homogenizeAll_isHomogeneous p d hp⟩, ?_⟩
    funext x
    exact eval_homogenize_chart p d hp x.val

noncomputable def homogeneousChartQuotient {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    homogeneousSubmodule (Fin (n + 1)) K d →ₗ[K]
      (Polynomials K (n + 1) ⧸ chartHomogeneousIdeal X) :=
  (Ideal.Quotient.mkₐ K (chartHomogeneousIdeal X)).toLinearMap.comp
    (homogeneousSubmodule (Fin (n + 1)) K d).subtype

lemma homogeneousChart_kernels {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    LinearMap.ker (homogeneousChartQuotient X d) =
      LinearMap.ker (homogeneousChartEvaluation X d) := by
  ext p
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  change (Ideal.Quotient.mk (chartHomogeneousIdeal X) p.val = 0) ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,
    homogeneous_mem_chartIdeal_iff X p.val d p.property]
  constructor
  · intro h; funext x; exact h x.val x.property
  · intro h x hx; exact congrFun h ⟨x, hx⟩

lemma chartQuotientPiece_finrank {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    Module.finrank K (LinearMap.range (homogeneousChartQuotient X d)) =
      affineHilbertFunction X d := by
  rw [← (homogeneousChartQuotient X d).quotKerEquivRange.finrank_eq,
    homogeneousChart_kernels,
    (homogeneousChartEvaluation X d).quotKerEquivRange.finrank_eq,
    homogeneousChartEvaluation_range]
  rfl

end APSCounting893.Main
end Component_19

section Component_20

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
open PhilipponMultiplicity
namespace APSCounting893.Main

abbrev SingleChartVariable (n : ℕ) := Sigma (fun _ : Fin 1 => Fin (n + 1))

def singleChartEquiv (n : ℕ) : SingleChartVariable n ≃ Fin (n + 1) where
  toFun v := v.2
  invFun i := ⟨0, i⟩
  left_inv v := by obtain ⟨i,j⟩ := v; have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl
  right_inv i := rfl

lemma singleBlockWeight {n : ℕ} (e : SingleChartVariable n →₀ ℕ) :
    Finsupp.weight (Hilbert.blockWeight 1 (fun _ => n)) e = fun _ : Fin 1 => e.degree := by
  ext i
  have hw (v : SingleChartVariable n) : Hilbert.blockWeight 1 (fun _ => n) v i = 1 := by
    simp [Hilbert.blockWeight, show v.1 = i from Subsingleton.elim _ _]
  simp only [Finsupp.weight_apply, Finsupp.degree_eq_sum, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, hw, smul_eq_mul, mul_one]
  exact e.sum_fintype (fun _ v => v) (fun _ => rfl)

lemma singleBlockHomogeneous_iff {K : Type} [Field K] {n : ℕ}
    (p : MvPolynomial (SingleChartVariable n) K) (d : ℕ) :
    p.IsWeightedHomogeneous (Hilbert.blockWeight 1 (fun _ => n)) (fun _ => d) ↔
      p.IsHomogeneous d := by
  simp only [IsHomogeneous, IsWeightedHomogeneous, singleBlockWeight]
  constructor
  · intro h e he
    change Finsupp.weight (fun _ : SingleChartVariable n => (1 : ℕ)) e = d
    rw [← Finsupp.degree_eq_weight_one]
    exact congrFun (h he) 0
  · intro h e he; exact _root_.funext (fun _ => by
      have hh := h he
      change Finsupp.weight (fun _ : SingleChartVariable n => (1 : ℕ)) e = d at hh
      rwa [← Finsupp.degree_eq_weight_one] at hh)

lemma singleBlockComponent {K : Type} [Field K] {n : ℕ}
    (p : MvPolynomial (SingleChartVariable n) K) (d : Fin 1 → ℕ) :
    weightedHomogeneousComponent (Hilbert.blockWeight 1 (fun _ => n)) d p =
      homogeneousComponent (d 0) p := by
  classical
  have hd : d = fun _ => d 0 := funext (fun i => congrArg d (Subsingleton.elim _ _))
  ext e
  rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, singleBlockWeight, hd]
  have he : (fun _ : Fin 1 => e.degree) = (fun _ : Fin 1 => d 0) ↔ e.degree = d 0 := by
    constructor
    · intro h; exact congrFun h 0
    · intro h; simp only [h]
  simp only [he]

noncomputable def singleChartIdeal {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    Ideal (MvPolynomial (SingleChartVariable n) K) :=
  Ideal.comap (rename (singleChartEquiv n)) (chartHomogeneousIdeal X)

lemma singleChartIdeal_homogeneous {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) :
    Hilbert.IsHomogeneousIdeal K 1 (fun _ => n) (singleChartIdeal X) := by
  intro p hp d
  change rename (singleChartEquiv n)
    (weightedHomogeneousComponent (Hilbert.blockWeight 1 (fun _ => n)) d p) ∈ chartHomogeneousIdeal X
  rw [singleBlockComponent, rename_homogeneousComponent]
  exact homogeneousComponent_mem_of_mem (chartHomogeneousIdeal_isHomogeneous X) hp (d 0)

noncomputable def singleChartEvaluation {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    Hilbert.degreePiece K 1 (fun _ => n) (fun _ => d) →ₗ[K] (X → K) where
  toFun p := fun x => eval (Fin.cons 1 x.val) (rename (singleChartEquiv n) p.val)
  map_add' p q := by funext x; simp only [map_add, Submodule.coe_add, Pi.add_apply]
  map_smul' c p := by funext x; simp [MvPolynomial.smul_eq_C_mul]

lemma singleChartEvaluation_range {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    LinearMap.range (singleChartEvaluation X d) = affineFilteredPiece X d := by
  rw [← homogeneousChartEvaluation_range X d]
  ext f
  rw [LinearMap.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    have hp : p.val.IsHomogeneous d := (singleBlockHomogeneous_iff p.val d).mp p.property
    refine ⟨⟨rename (singleChartEquiv n) p.val, hp.rename_isHomogeneous⟩, rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨⟨rename (singleChartEquiv n).symm p.val, ?_⟩, ?_⟩
    · exact (singleBlockHomogeneous_iff _ _).mpr p.property.rename_isHomogeneous
    · funext x
      simp only [singleChartEvaluation, homogeneousChartEvaluation, LinearMap.coe_mk,
        AddHom.coe_mk, rename_rename, Equiv.self_comp_symm, rename_id_apply]

noncomputable def singleChartQuotient {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    Hilbert.degreePiece K 1 (fun _ => n) (fun _ => d) →ₗ[K]
      (MvPolynomial (SingleChartVariable n) K ⧸ singleChartIdeal X) :=
  (Ideal.Quotient.mkₐ K (singleChartIdeal X)).toLinearMap.comp
    (Hilbert.degreePiece K 1 (fun _ => n) (fun _ => d)).subtype

lemma singleChart_kernels {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    LinearMap.ker (singleChartQuotient X d) = LinearMap.ker (singleChartEvaluation X d) := by
  ext p
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  change (Ideal.Quotient.mk (singleChartIdeal X) p.val = 0) ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change rename (singleChartEquiv n) p.val ∈ chartHomogeneousIdeal X ↔ _
  have hp : p.val.IsHomogeneous d := (singleBlockHomogeneous_iff p.val d).mp p.property
  rw [homogeneous_mem_chartIdeal_iff X _ d hp.rename_isHomogeneous]
  constructor
  · intro h; funext x; exact h x.val x.property
  · intro h x hx; exact congrFun h ⟨x, hx⟩

lemma singleChart_hilbertFunction {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    Hilbert.hilbertFunction K 1 (fun _ => n) (singleChartIdeal X) (fun _ => d) =
      affineHilbertFunction X d := by
  have hr : LinearMap.range (singleChartQuotient X d) =
      Hilbert.quotientPiece K 1 (fun _ => n) (singleChartIdeal X) (fun _ => d) := by
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      exact Submodule.mem_map.mpr ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  change Module.finrank K _ = _
  rw [← hr, ← (singleChartQuotient X d).quotKerEquivRange.finrank_eq,
    singleChart_kernels, (singleChartEvaluation X d).quotKerEquivRange.finrank_eq,
    singleChartEvaluation_range]
  rfl

lemma affineHilbertPolynomial_exists {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) :
    ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ t ≥ N,
      p.eval (t : ℚ) = (affineHilbertFunction X t : ℚ) := by
  let M : MultiProjectiveSpace K := ⟨1, by decide, fun _ => n⟩
  obtain ⟨P, d0, hP⟩ := PhilipponMultiplicity.multigraded_hilbert_polynomial_exists K M
    (singleChartIdeal X) (singleChartIdeal_homogeneous X)
  refine ⟨MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) P, d0 0, ?_⟩
  intro t ht
  have hh := hP (fun _ => t) (fun i => by simpa only [Subsingleton.elim i 0] using ht)
  rw [singleChart_hilbertFunction] at hh
  change Polynomial.eval₂ (RingHom.id ℚ) (t : ℚ) _ = _
  rw [MvPolynomial.eval₂_const_uniqueAlgEquiv]
  exact hh

end APSCounting893.Main
end Component_20

section Component_21

set_option autoImplicit false
namespace APSCounting893.Main

lemma reduced_image_projectiveDegree_le (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c) :
    projectiveDegree (imageClosure F.F) ≤ F.d ^ F.n :=
  reduced_image_degree_bound_of_hilbert_exists F c hc
    (affineHilbertPolynomial_exists (imageClosure F.F))

end APSCounting893.Main
end Component_21

section Component_22

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace APSCounting893.Main

lemma normalized_image_hilbert_degree (F : ReducedMap)
    (c : Affine ℂ F.n) (hc : IsNormalization (imageClosure F.F) c) :
    (affineHilbertPolynomial (imageClosure F.F)).natDegree = F.n ∧
      0 < (affineHilbertPolynomial (imageClosure F.F)).leadingCoeff := by
  classical
  have hex := affineHilbertPolynomial_exists (imageClosure F.F)
  let p := affineHilbertPolynomial (imageClosure F.F)
  have hp := affineHilbertPolynomial_spec (imageClosure F.F) hex
  change ∃ N : ℕ, ∀ t ≥ N, p.eval (t : ℚ) = _ at hp
  let low := preHilbertPoly ℚ F.n 0
  let high := low.comp (C (F.d : ℚ) * X)
  have hDpos : 0 < F.d := by have := F.degree_ge_two; omega
  have hDne : (F.d : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hlin : (C (F.d : ℚ) * X).natDegree = 1 := natDegree_C_mul_X (F.d : ℚ) hDne
  have hlowdeg : low.natDegree = F.n := natDegree_preHilbertPoly _ _ _
  have hhighdeg : high.natDegree = F.n := by
    simp only [high, natDegree_comp, hlowdeg, hlin, mul_one]
  have hlowpos : 0 < low.leadingCoeff := by
    rw [show low.leadingCoeff = (F.n.factorial : ℚ)⁻¹ from leadingCoeff_preHilbertPoly _ _ _]
    positivity
  have hloweval (t : ℕ) : low.eval (t : ℚ) = ((F.n + t).choose F.n : ℚ) := by
    simpa only [low, Nat.sub_zero, Nat.add_comm] using
      preHilbertPoly_eq_choose_sub_add (F := ℚ) F.n (k := 0) (n := t) (Nat.zero_le _)
  have hhigheval (t : ℕ) : high.eval (t : ℚ) = ((F.n + F.d * t).choose F.n : ℚ) := by
    rw [eval_comp]
    have he : (C (F.d : ℚ) * X).eval (t : ℚ) = ((F.d * t : ℕ) : ℚ) := by simp
    rw [he, hloweval]
  obtain ⟨N, hN⟩ := hp
  have hlow : ∃ N : ℕ, ∀ t ≥ N, low.eval (t : ℚ) ≤ p.eval (t : ℚ) := by
    refine ⟨N, fun t ht => ?_⟩
    rw [hN t ht, hloweval]
    exact_mod_cast normalization_affineHilbert_lower _ c hc t
  have hhigh : ∃ N : ℕ, ∀ t ≥ N, p.eval (t : ℚ) ≤ high.eval (t : ℚ) := by
    refine ⟨N, fun t ht => ?_⟩
    rw [hN t ht, hhigheval]
    exact_mod_cast imageHilbert_le_choose F.F F.d t F.degree_bound
  have hpdeg := natDegree_eq_of_eventual_nat_eval_sandwich p low high F.n
    hlowdeg hhighdeg hlowpos hlow hhigh
  have hleadpos : 0 < p.leadingCoeff := by
    have hle := coefficient_le_of_eventual_nat_eval_le low p F.n hlowdeg.le hpdeg.le hlow
    rw [← hlowdeg, coeff_natDegree, hlowdeg, ← hpdeg, coeff_natDegree] at hle
    exact hlowpos.trans_le hle
  exact ⟨hpdeg, hleadpos⟩

end APSCounting893.Main
end Component_22

section Component_23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def filteredSetPullback {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (Y : Set (Affine K m)) (F : PolynomialMap K n m)
    (hmap : ∀ x ∈ X, evaluate F x ∈ Y) (t : ℕ)
    (hF : ∀ i, (F i).totalDegree ≤ 1) :
    affineFilteredPiece Y t →ₗ[K] affineFilteredPiece X t where
  toFun f := ⟨fun x => f.val ⟨evaluate F x.val, hmap x.val x.property⟩, by
    obtain ⟨p, hp, hf⟩ := (mem_affineFilteredPiece Y t f.val).mp f.property
    refine (mem_affineFilteredPiece X t _).mpr ⟨eval₂Hom C F p, ?_, ?_⟩
    · have hh := totalDegree_eval₂_bounded (RingHom.id K) F 1 hF p
      exact (show (eval₂Hom C F p).totalDegree ≤ p.totalDegree by simpa using hh).trans hp
    · funext x
      rw [hf]
      exact (evaluation_substitution F p x.val).symm⟩
  map_add' f g := rfl
  map_smul' c f := rfl

lemma filteredSetPullback_injective {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (Y : Set (Affine K m)) (F : PolynomialMap K n m)
    (hmap : ∀ x ∈ X, evaluate F x ∈ Y) (t : ℕ)
    (hF : ∀ i, (F i).totalDegree ≤ 1)
    (hsurj : ∀ y ∈ Y, ∃ x ∈ X, evaluate F x = y) :
    Function.Injective (filteredSetPullback X Y F hmap t hF) := by
  intro f g h
  apply Subtype.ext
  funext y
  obtain ⟨x, hx, hxy⟩ := hsurj y.val y.property
  have hh := congrArg (fun z : affineFilteredPiece X t => z.val ⟨x, hx⟩) h
  change f.val ⟨evaluate F x, _⟩ = g.val ⟨evaluate F x, _⟩ at hh
  simpa only [hxy] using hh

lemma affineHilbert_lower_of_linear_set_surjection {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (Y : Set (Affine K m)) (F : PolynomialMap K n m)
    (hmap : ∀ x ∈ X, evaluate F x ∈ Y) (t : ℕ)
    (hF : ∀ i, (F i).totalDegree ≤ 1)
    (hsurj : ∀ y ∈ Y, ∃ x ∈ X, evaluate F x = y) :
    affineHilbertFunction Y t ≤ affineHilbertFunction X t :=
  LinearMap.finrank_le_finrank_of_injective
    (filteredSetPullback_injective X Y F hmap t hF hsurj)

end APSCounting893.Main
end Component_23

section Component_24

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def filteredRestriction {K : Type} [Field K] {n : ℕ}
    (Y W : Set (Affine K n)) (hWY : W ⊆ Y) (t : ℕ) :
    affineFilteredPiece Y t →ₗ[K] affineFilteredPiece W t where
  toFun f := ⟨fun x => f.val ⟨x.val, hWY x.property⟩, by
    obtain ⟨p, hp, hf⟩ := (mem_affineFilteredPiece Y t f.val).mp f.property
    exact (mem_affineFilteredPiece W t _).mpr ⟨p, hp, by funext x; rw [hf]⟩⟩
  map_add' f g := rfl
  map_smul' c f := rfl

lemma filteredRestriction_surjective {K : Type} [Field K] {n : ℕ}
    (Y W : Set (Affine K n)) (hWY : W ⊆ Y) (t : ℕ) :
    Function.Surjective (filteredRestriction Y W hWY t) := by
  intro f
  obtain ⟨p, hp, hf⟩ := (mem_affineFilteredPiece W t f.val).mp f.property
  refine ⟨⟨fun x => eval x.val p, (mem_affineFilteredPiece Y t _).mpr ⟨p, hp, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact hf.symm

noncomputable def filteredCoordinateMultiple {K : Type} [Field K] {n : ℕ}
    (Y : Set (Affine K n)) (b : Polynomials K n) (E t : ℕ)
    (hbE : b.totalDegree ≤ E) (hEt : E ≤ t) :
    affineFilteredPiece Y (t - E) →ₗ[K] affineFilteredPiece Y t where
  toFun f := ⟨fun x => eval x.val b * f.val x, by
    obtain ⟨p, hp, hf⟩ := (mem_affineFilteredPiece Y (t - E) f.val).mp f.property
    refine (mem_affineFilteredPiece Y t _).mpr ⟨b * p,
      (totalDegree_mul b p).trans (by omega), ?_⟩
    funext x
    rw [hf, map_mul]⟩
  map_add' f g := by apply Subtype.ext; funext x; exact mul_add _ _ _
  map_smul' c f := by apply Subtype.ext; funext x; simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma filteredCoordinateMultiple_injective {K : Type} [Field K] {n : ℕ}
    (Y : Set (Affine K n)) (hY : IrreducibleAffine Y)
    (b : Polynomials K n) (hb : b ∉ vanishingIdeal K Y) (E t : ℕ)
    (hbE : b.totalDegree ≤ E) (hEt : E ≤ t) :
    Function.Injective (filteredCoordinateMultiple Y b E t hbE hEt) := by
  intro f g h
  obtain ⟨p, hp, hf⟩ := (mem_affineFilteredPiece Y (t - E) f.val).mp f.property
  obtain ⟨q, hq, hg⟩ := (mem_affineFilteredPiece Y (t - E) g.val).mp g.property
  have hmul : b * (p - q) ∈ vanishingIdeal K Y := by
    intro x hx
    have hh := congrArg (fun v : affineFilteredPiece Y t => v.val ⟨x, hx⟩) h
    change eval x b * f.val ⟨x, hx⟩ = eval x b * g.val ⟨x, hx⟩ at hh
    rw [hf, hg] at hh
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_mul, map_sub,
      mul_sub, sub_eq_zero] using hh
  haveI : (vanishingIdeal K Y).IsPrime := irreducibleAffine_ideal_prime hY
  have hpq := (Ideal.IsPrime.mem_or_mem (inferInstance : (vanishingIdeal K Y).IsPrime) hmul).resolve_left hb
  apply Subtype.ext
  funext x
  rw [hf, hg]
  have hh := hpq x.val x.property
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, sub_eq_zero] using hh

lemma filteredCoordinateMultiple_le_ker {K : Type} [Field K] {n : ℕ}
    (Y W : Set (Affine K n)) (hWY : W ⊆ Y) (b : Polynomials K n)
    (hbW : ∀ x ∈ W, eval x b = 0) (E t : ℕ)
    (hbE : b.totalDegree ≤ E) (hEt : E ≤ t) :
    LinearMap.range (filteredCoordinateMultiple Y b E t hbE hEt) ≤
      LinearMap.ker (filteredRestriction Y W hWY t) := by
  rintro _ ⟨f, rfl⟩
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  funext x
  change eval x.val b * f.val ⟨x.val, hWY x.property⟩ = 0
  rw [hbW x.val x.property, zero_mul]

lemma hypersurface_affineHilbert_bound {K : Type} [Field K] {n : ℕ}
    (Y W : Set (Affine K n)) (hY : IrreducibleAffine Y) (hWY : W ⊆ Y)
    (b : Polynomials K n) (hb : b ∉ vanishingIdeal K Y)
    (hbW : ∀ x ∈ W, eval x b = 0) (E t : ℕ)
    (hbE : b.totalDegree ≤ E) (hEt : E ≤ t) :
    affineHilbertFunction W t + affineHilbertFunction Y (t - E) ≤ affineHilbertFunction Y t := by
  have hh := (filteredRestriction Y W hWY t).finrank_range_add_finrank_ker
  have hr : Module.finrank K (LinearMap.range (filteredRestriction Y W hWY t)) =
      affineHilbertFunction W t := by
    rw [LinearMap.range_eq_top.mpr (filteredRestriction_surjective Y W hWY t), finrank_top]
    rfl
  rw [hr] at hh
  change affineHilbertFunction W t + _ = affineHilbertFunction Y t at hh
  have hle := Submodule.finrank_mono (filteredCoordinateMultiple_le_ker Y W hWY b hbW E t hbE hEt)
  rw [LinearMap.finrank_range_of_inj (filteredCoordinateMultiple_injective Y hY b hb E t hbE hEt)] at hle
  change affineHilbertFunction Y (t - E) ≤ _ at hle
  omega

end APSCounting893.Main
end Component_24

section Component_25

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Polynomial
namespace APSCounting893.Main

lemma totalDegree_pos_of_nonunit {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K n) (hp : p ≠ 0) (hu : ¬ IsUnit p) : 0 < p.totalDegree := by
  by_contra h
  have hD : p.totalDegree = 0 := by omega
  have he : p = MvPolynomial.C (p.coeff 0) := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hD
  have hc : p.coeff 0 ≠ 0 := by intro hc; simp [hc] at he; exact hp he
  exact hu (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mpr ⟨isUnit_iff_ne_zero.mpr hc, hD⟩)

lemma affineHilbertFunction_mono {K : Type} [Field K] {n : ℕ}
    (Y W : Set (Affine K n)) (hWY : W ⊆ Y) (t : ℕ) :
    affineHilbertFunction W t ≤ affineHilbertFunction Y t :=
  LinearMap.finrank_le_finrank_of_surjective (filteredRestriction_surjective Y W hWY t)

lemma hypersurface_projection_lower {K : Type} [Field K] [IsAlgClosed K] {m N : ℕ}
    (hN : 0 < N) (Y : Set (Affine K m)) (pi : PolynomialMap K m N)
    (hpi : ∀ i, (pi i).totalDegree ≤ 1)
    (hsurj : ∀ u : Affine K N, ∃ y ∈ Y, evaluate pi y = u)
    (b : Polynomials K N) (hb : b ≠ 0) (hbu : ¬ IsUnit b) :
    ∃ low : Polynomial ℚ, low.natDegree = N - 1 ∧ 0 < low.leadingCoeff ∧
      ∃ T : ℕ, ∀ t ≥ T, low.eval (t : ℚ) ≤
        (affineHilbertFunction {y ∈ Y | MvPolynomial.eval (evaluate pi y) b = 0} t : ℚ) := by
  classical
  obtain ⟨a, ha, hab⟩ := WfDvdMonoid.exists_irreducible_factor hbu hb
  have haD := totalDegree_pos_of_nonunit a ha.ne_zero ha.not_isUnit
  let V : Set (Affine K N) := MvPolynomial.zeroLocus K (Ideal.span {a})
  haveI : (Ideal.span ({a} : Set (Polynomials K N))).IsPrime :=
    (Ideal.span_singleton_prime ha.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp ha)
  have hV : vanishingIdeal K V = Ideal.span {a} := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus _
  let W : Set (Affine K m) := {y ∈ Y | MvPolynomial.eval (evaluate pi y) b = 0}
  let A : Set (Affine K m) := {y ∈ Y | evaluate pi y ∈ V}
  have hAV : ∀ y ∈ A, evaluate pi y ∈ V := fun y hy => hy.2
  have hsurjA : ∀ u ∈ V, ∃ y ∈ A, evaluate pi y = u := by
    intro u hu
    obtain ⟨y, hy, hpy⟩ := hsurj u
    exact ⟨y, ⟨hy, hpy ▸ hu⟩, hpy⟩
  have hAW : A ⊆ W := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    obtain ⟨r, hr⟩ := hab
    have hzero : MvPolynomial.eval (evaluate pi y) a = 0 := by
      have hh := hy.2
      change evaluate pi y ∈ MvPolynomial.zeroLocus K (Ideal.span {a}) at hh
      rw [MvPolynomial.zeroLocus_span] at hh
      simpa only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq, MvPolynomial.aeval_def,
        Algebra.algebraMap_self, MvPolynomial.eval₂_id] using hh
    rw [hr, map_mul, hzero, zero_mul]
  have hbound (t : ℕ) : affineHilbertFunction V t ≤ affineHilbertFunction W t :=
    (affineHilbert_lower_of_linear_set_surjection A V pi hAV t hpi hsurjA).trans
      (affineHilbertFunction_mono W A hAW t)
  cases N with
  | zero => omega
  | succ n =>
    let low := principalHilbertPoly n a.totalDegree
    have hlowdeg : low.natDegree = n := principalHilbertPoly_degree n a.totalDegree haD
    have hlc : low.leadingCoeff = (a.totalDegree : ℚ) * (n.factorial : ℚ)⁻¹ := by
      rw [Polynomial.leadingCoeff, hlowdeg]
      exact principalHilbertPoly_coeff n a.totalDegree
    obtain ⟨T, hT⟩ := principalHilbertPoly_eventual V a ha.ne_zero hV
    refine ⟨low, by simpa only [Nat.add_sub_cancel] using hlowdeg, ?_, T, ?_⟩
    · rw [hlc]; positivity
    · intro t ht
      rw [hT t ht]
      exact_mod_cast hbound t

end APSCounting893.Main
end Component_25

section Component_26

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial
namespace APSCounting893.Main

lemma coeff_taylor_of_natDegree_le (p : Polynomial ℚ) (a : ℚ) (n : ℕ) (hp : p.natDegree ≤ n) :
    (taylor a p).coeff n = p.coeff n := by
  by_cases he : p.natDegree = n
  · rw [← he, coeff_taylor_natDegree, coeff_natDegree]
  · have hh : p.natDegree < n := by omega
    rw [coeff_eq_zero_of_natDegree_lt (by simpa only [natDegree_taylor] using hh),
      coeff_eq_zero_of_natDegree_lt hh]

lemma coeff_taylor_below_top (p : Polynomial ℚ) (a : ℚ) (n : ℕ) (hp : p.natDegree ≤ n + 1) :
    (taylor a p).coeff n = p.coeff n + (n + 1 : ℚ) * a * p.coeff (n + 1) := by
  rw [taylor_coeff]
  have hd : (hasseDeriv n p).natDegree < 2 := (natDegree_hasseDeriv_le p n).trans_lt (by omega)
  rw [Polynomial.eval_eq_sum_range' hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one, hasseDeriv_coeff, zero_add, Nat.choose_self, Nat.cast_one, one_mul]
  have hchoose : (1 + n).choose n = n + 1 := by rw [Nat.add_comm]; exact Nat.choose_succ_self_right n
  rw [hchoose, Nat.cast_add, Nat.cast_one, Nat.add_comm 1 n]
  ring

noncomputable def hilbertDifference (p : Polynomial ℚ) (E : ℕ) : Polynomial ℚ :=
  p - taylor (-(E : ℚ)) p

lemma hilbertDifference_degree_le (p : Polynomial ℚ) (E n : ℕ) (hp : p.natDegree ≤ n + 1) :
    (hilbertDifference p E).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [hilbertDifference, coeff_sub]
  by_cases he : m = n + 1
  · subst m
    rw [coeff_taylor_of_natDegree_le p _ (n + 1) hp, sub_self]
  · have hpm : p.natDegree < m := by omega
    rw [coeff_eq_zero_of_natDegree_lt hpm,
      coeff_eq_zero_of_natDegree_lt (by simpa only [natDegree_taylor] using hpm), sub_self]

lemma hilbertDifference_coeff (p : Polynomial ℚ) (E n : ℕ) (hp : p.natDegree ≤ n + 1) :
    (hilbertDifference p E).coeff n = (n + 1 : ℚ) * E * p.coeff (n + 1) := by
  rw [hilbertDifference, coeff_sub, coeff_taylor_below_top p _ n hp]
  ring

lemma hilbertDifference_eval (p : Polynomial ℚ) (E t : ℕ) (ht : E ≤ t) :
    (hilbertDifference p E).eval (t : ℚ) = p.eval (t : ℚ) - p.eval ((t - E : ℕ) : ℚ) := by
  rw [hilbertDifference, eval_sub, taylor_apply, eval_comp]
  congr 2
  simp [Nat.cast_sub ht, sub_eq_add_neg]

end APSCounting893.Main
end Component_26

section Component_27

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace APSCounting893.Main

lemma eventual_nat_polynomial_unique (p q : Polynomial ℚ)
    (h : ∃ N : ℕ, ∀ t ≥ N, p.eval (t : ℚ) = q.eval (t : ℚ)) : p = q := by
  obtain ⟨N, hN⟩ := h
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := (fun t : ℕ => (t : ℚ)) '' Set.Ici N)
  · rintro x ⟨t, ht, rfl⟩
    exact hN t ht
  · exact (Set.Ici_infinite N).image Nat.cast_injective.injOn

lemma affineHilbertPolynomial_eq_of_eventual {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (p : Polynomial ℚ)
    (hp : ∃ N : ℕ, ∀ t ≥ N, p.eval (t : ℚ) = (affineHilbertFunction X t : ℚ)) :
    affineHilbertPolynomial X = p := by
  obtain ⟨M, hM⟩ := affineHilbertPolynomial_spec X ⟨p, hp⟩
  obtain ⟨N, hN⟩ := hp
  apply eventual_nat_polynomial_unique
  exact ⟨max M N, fun t ht => (hM t ((le_max_left M N).trans ht)).trans
    (hN t ((le_max_right M N).trans ht)).symm⟩

lemma projectiveDegree_le_of_hilbert_polynomial {K : Type} [Field K] {m : ℕ}
    (X : Set (Affine K m)) (p : Polynomial ℚ)
    (hp : ∃ N : ℕ, ∀ t ≥ N, p.eval (t : ℚ) = (affineHilbertFunction X t : ℚ))
    (B : ℕ) (hpos : 0 ≤ p.leadingCoeff)
    (hbound : p.leadingCoeff * (p.natDegree.factorial : ℚ) ≤ (B : ℚ)) :
    projectiveDegree X ≤ B := by
  obtain ⟨z, hz⟩ := leading_factorial_integer_of_eventual_integer p (by
    obtain ⟨N, hN⟩ := hp
    exact ⟨N, fun t ht => ⟨(affineHilbertFunction X t : ℤ), by simpa using hN t ht⟩⟩)
  have hzpos : 0 ≤ z := by
    have hh : 0 ≤ p.leadingCoeff * (p.natDegree.factorial : ℚ) := mul_nonneg hpos (by positivity)
    rw [hz] at hh
    exact_mod_cast hh
  rw [projectiveDegree, affineHilbertPolynomial_eq_of_eventual X p hp, hz, Rat.num_intCast]
  have hb : z ≤ (B : ℤ) := by rw [hz] at hbound; exact_mod_cast hbound
  exact_mod_cast (show (z.natAbs : ℤ) ≤ (B : ℤ) by
    rw [Int.natCast_natAbs, abs_of_nonneg hzpos]
    exact hb)

lemma projectiveDegree_cast_of_hilbert_polynomial {K : Type} [Field K] {m : ℕ}
    (X : Set (Affine K m)) (p : Polynomial ℚ)
    (hp : ∃ N : ℕ, ∀ t ≥ N, p.eval (t : ℚ) = (affineHilbertFunction X t : ℚ))
    (hpos : 0 ≤ p.leadingCoeff) :
    (projectiveDegree X : ℚ) = p.leadingCoeff * (p.natDegree.factorial : ℚ) := by
  obtain ⟨z, hz⟩ := leading_factorial_integer_of_eventual_integer p (by
    obtain ⟨N, hN⟩ := hp
    exact ⟨N, fun t ht => ⟨(affineHilbertFunction X t : ℤ), by simpa using hN t ht⟩⟩)
  have hzpos : 0 ≤ z := by
    have hh : 0 ≤ p.leadingCoeff * (p.natDegree.factorial : ℚ) := mul_nonneg hpos (by positivity)
    rw [hz] at hh
    exact_mod_cast hh
  rw [projectiveDegree, affineHilbertPolynomial_eq_of_eventual X p hp, hz, Rat.num_intCast]
  have he : (z.natAbs : ℤ) = z := by rw [Int.natCast_natAbs, abs_of_nonneg hzpos]
  calc
    (z.natAbs : ℚ) = ((z.natAbs : ℤ) : ℚ) := by simp
    _ = (z : ℚ) := congrArg (fun a : ℤ => (a : ℚ)) he

lemma projectiveDegree_empty {K : Type} [Field K] (n : ℕ) :
    projectiveDegree (∅ : Set (Affine K n)) = 0 := by
  have hzero : affineHilbertPolynomial (∅ : Set (Affine K n)) = 0 := by
    apply affineHilbertPolynomial_eq_of_eventual
    exact ⟨0, fun t ht => by
      haveI : Subsingleton (affineFilteredPiece (∅ : Set (Affine K n)) t) :=
        ⟨fun f g => Subtype.ext (funext (fun x => False.elim x.property))⟩
      simp [affineHilbertFunction, Module.finrank_zero_of_subsingleton]⟩
  simp [projectiveDegree, hzero]

end APSCounting893.Main
end Component_27

section Component_28

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace APSCounting893.Main

lemma linear_projection_hypersurface_degree_bound {K : Type} [Field K] [IsAlgClosed K]
    {m N : ℕ} (hN : 0 < N) (Y : Set (Affine K m)) (hY : IrreducibleAffine Y)
    (pi : PolynomialMap K m N) (hpi : ∀ i, (pi i).totalDegree ≤ 1)
    (hsurj : ∀ u : Affine K N, ∃ y ∈ Y, evaluate pi y = u)
    (hYdeg : (affineHilbertPolynomial Y).natDegree = N)
    (hYpos : 0 < (affineHilbertPolynomial Y).leadingCoeff)
    (b : Polynomials K N) (hb : b ≠ 0) (hbu : ¬ IsUnit b) :
    projectiveDegree {y ∈ Y | MvPolynomial.eval (evaluate pi y) b = 0} ≤
      b.totalDegree * projectiveDegree Y := by
  classical
  cases N with
  | zero => omega
  | succ n =>
    let W : Set (Affine K m) := {y ∈ Y | MvPolynomial.eval (evaluate pi y) b = 0}
    let s : Polynomials K m := MvPolynomial.eval₂Hom MvPolynomial.C pi b
    let E := b.totalDegree
    have hE : 0 < E := totalDegree_pos_of_nonunit b hb hbu
    have hsdeg : s.totalDegree ≤ E := by
      have hh := totalDegree_eval₂_bounded (RingHom.id K) pi 1 hpi b
      simpa only [RingHom.comp_id, Nat.one_mul] using hh
    have hsY : s ∉ MvPolynomial.vanishingIdeal K Y := by
      intro hs
      apply hb
      apply MvPolynomial.funext
      intro u
      obtain ⟨y, hy, hpy⟩ := hsurj u
      have hh := hs y hy
      change MvPolynomial.eval y s = 0 at hh
      rw [evaluation_substitution, hpy] at hh
      exact hh
    have hWY : W ⊆ Y := fun _ hy => hy.1
    have hsW : ∀ y ∈ W, MvPolynomial.eval y s = 0 := by
      intro y hy
      exact (evaluation_substitution pi b y).trans hy.2
    have hHF (t : ℕ) (ht : E ≤ t) :=
      hypersurface_affineHilbert_bound Y W hY hWY s hsY hsW E t hsdeg ht
    let P := affineHilbertPolynomial Y
    let H := affineHilbertPolynomial W
    let Q := hilbertDifference P E
    have hPdeg : P.natDegree = n + 1 := hYdeg
    have hPpos : 0 < P.leadingCoeff := hYpos
    obtain ⟨a, ha⟩ := affineHilbertPolynomial_spec Y (affineHilbertPolynomial_exists Y)
    obtain ⟨c, hc⟩ := affineHilbertPolynomial_spec W (affineHilbertPolynomial_exists W)
    have hQle : Q.natDegree ≤ n := hilbertDifference_degree_le P E n hPdeg.le
    have hQc : Q.coeff n = (n + 1 : ℚ) * E * P.leadingCoeff := by
      rw [hilbertDifference_coeff P E n hPdeg.le, ← hPdeg, coeff_natDegree]
    have hQcpos : 0 < Q.coeff n := by rw [hQc]; positivity
    have hQdeg : Q.natDegree = n := le_antisymm hQle (le_natDegree_of_ne_zero hQcpos.ne')
    have hhigh : ∃ T : ℕ, ∀ t ≥ T, H.eval (t : ℚ) ≤ Q.eval (t : ℚ) := by
      refine ⟨a + E + c, ?_⟩
      intro t ht
      have hEt : E ≤ t := by omega
      have h := hHF t hEt
      have h' : (affineHilbertFunction W t : ℚ) + (affineHilbertFunction Y (t - E) : ℚ) ≤
          (affineHilbertFunction Y t : ℚ) := by exact_mod_cast h
      change (affineHilbertPolynomial W).eval (t : ℚ) ≤ _
      rw [hc t (by omega)]
      rw [hilbertDifference_eval P E t hEt,
        show P.eval (t : ℚ) = _ from ha t (by omega),
        show P.eval ((t - E : ℕ) : ℚ) = _ from ha (t - E) (by omega)]
      linarith
    obtain ⟨low, hlowdeg, hlowpos, hlow⟩ := hypersurface_projection_lower
      (by omega : 0 < n + 1) Y pi hpi hsurj b hb hbu
    have hlowdeg' : low.natDegree = n := by simpa only [Nat.add_sub_cancel] using hlowdeg
    have hlowH : ∃ T : ℕ, ∀ t ≥ T, low.eval (t : ℚ) ≤ H.eval (t : ℚ) := by
      obtain ⟨T, hT⟩ := hlow
      exact ⟨T + c, fun t ht => by rw [show H.eval (t : ℚ) = _ from hc t (by omega)]; exact hT t (by omega)⟩
    have hHdeg := natDegree_eq_of_eventual_nat_eval_sandwich H low Q n hlowdeg' hQdeg hlowpos hlowH hhigh
    have hHpos : 0 ≤ H.leadingCoeff := by
      have hzero : ∃ T : ℕ, ∀ t ≥ T, (0 : Polynomial ℚ).eval (t : ℚ) ≤ H.eval (t : ℚ) := by
        refine ⟨c, fun t ht => ?_⟩
        rw [show H.eval (t : ℚ) = _ from hc t ht]
        simp
      have hh := coefficient_le_of_eventual_nat_eval_le 0 H n (by simp) hHdeg.le hzero
      simpa only [coeff_zero, ← hHdeg, coeff_natDegree] using hh
    have hcoeff := coefficient_le_of_eventual_nat_eval_le H Q n hHdeg.le hQdeg.le hhigh
    rw [← hHdeg, coeff_natDegree, hHdeg, hQc] at hcoeff
    have hYcast := projectiveDegree_cast_of_hilbert_polynomial Y P ⟨a, ha⟩ hPpos.le
    have hbound : H.leadingCoeff * (H.natDegree.factorial : ℚ) ≤
        ((E * projectiveDegree Y : ℕ) : ℚ) := by
      rw [hHdeg, Nat.cast_mul, hYcast, hPdeg, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hh := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ (n.factorial : ℚ) by positivity)
      nlinarith
    exact projectiveDegree_le_of_hilbert_polynomial W H ⟨c, hc⟩
      (E * projectiveDegree Y) hHpos hbound

end APSCounting893.Main
end Component_28

section Component_29

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma normalized_perron_exceptional_degree (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c) :
    ∃ (p : Fin F.n → Polynomial (Polynomials ℂ F.n)) (b : Polynomials ℂ F.n),
      b = ∏ i, (p i).leadingCoeff ∧ b ≠ 0 ∧ b.totalDegree ≤ F.n * F.d ^ F.n ∧
      (∀ i, 0 < (p i).natDegree) ∧
      (∀ i x, Polynomial.eval (x i) ((p i).map (eval (evaluate (betaPolynomials F c) x))) = 0) ∧
      projectiveDegree {y ∈ imageClosure F.F | eval (normalization c y) b = 0} ≤
        F.n * F.d ^ (2 * F.n) := by
  classical
  obtain ⟨p, b, hpb, hb, hbdeg, hpdeg, hroot⟩ := normalized_perron_product F c hc
  refine ⟨p, b, hpb, hb, hbdeg, hpdeg, hroot, ?_⟩
  by_cases hbu : IsUnit b
  · have hset : {y ∈ imageClosure F.F | eval (normalization c y) b = 0} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact (hbu.map (eval (normalization c y))).ne_zero hy.2
    rw [hset, projectiveDegree_empty]
    exact Nat.zero_le _
  · obtain ⟨hYdeg, hYpos⟩ := normalized_image_hilbert_degree F c hc
    have hsurj : ∀ u : Affine ℂ F.n, ∃ y ∈ imageClosure F.F, evaluate (normalizationPolynomials c) y = u := by
      intro u
      have hu : u ∈ normalization c '' imageClosure F.F := by rw [hc.2.1]; trivial
      exact hu
    have hdeg := linear_projection_hypersurface_degree_bound F.positive
      (imageClosure F.F) (irreducibleAffine_imageClosure F.F) (normalizationPolynomials c)
      (normalizationPolynomials_degree_le c) hsurj hYdeg hYpos b hb hbu
    have hYbound := reduced_image_projectiveDegree_le F c hc
    apply hdeg.trans
    calc
      b.totalDegree * projectiveDegree (imageClosure F.F) ≤
          (F.n * F.d ^ F.n) * F.d ^ F.n := Nat.mul_le_mul hbdeg hYbound
      _ = F.n * F.d ^ (2 * F.n) := by rw [two_mul, pow_add]; ring

end APSCounting893.Main
end Component_29

open APSCounting893.Main MvPolynomial
theorem solution (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c) :
    ∃ (p : Fin F.n → Polynomial (Polynomials ℂ F.n)) (b : Polynomials ℂ F.n),
      b = ∏ i, (p i).leadingCoeff ∧ b ≠ 0 ∧ b.totalDegree ≤ F.n * F.d ^ F.n ∧
      (∀ i, 0 < (p i).natDegree) ∧
      (∀ i x, Polynomial.eval (x i) ((p i).map (eval (evaluate (betaPolynomials F c) x))) = 0) ∧
      projectiveDegree {y ∈ imageClosure F.F | eval (normalization c y) b = 0} ≤
        F.n * F.d ^ (2 * F.n) := by
  exact APSCounting893.Main.normalized_perron_exceptional_degree F c hc
