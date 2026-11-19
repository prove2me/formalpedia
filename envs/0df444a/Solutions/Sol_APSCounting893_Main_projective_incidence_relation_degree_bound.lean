-- Prove2me | solution 1 for APSCounting893.Main.projective_incidence_relation_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:30:16.020581+00:00
-- url     : https://prove2.me/submissions/9562f70a-7efb-47ab-81e0-223413a2f585

import Definitions.Def_APSCounting893_Main_Geometry
import Definitions.Def_APSCounting893_Main_RandomReduction
import Definitions.Def_APSCounting893_Main_Resultant
import Mathlib
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.EssentialFiniteness
import Theorems.Thm_APSCounting893_Main_affine_section_nonvanishing_certificate
import Theorems.Thm_APSCounting893_Main_rational_incidence_relation_bounded
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_exists_coordinate_transcendence_basis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat
import Theorems.Thm_ringKrullDim_le_of_ringHom_isIntegral
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

noncomputable def genericLinearValues {E : Type} [CommRing E] {m r : ℕ} (f : Fin m → E) :
    Fin r → MvPolynomial (Fin r × Fin m) E :=
  fun i => ∑ a : Fin m, MvPolynomial.X (i,a)*MvPolynomial.C (f a)


end APSCounting893.Main
end Component_0

section Component_1
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

/-- Coordinates on the normalized incidence chart, with the pivot column first. -/
noncomputable def genericIncidenceChartValues {E : Type} [Field E] {r m : ℕ} (f : Fin m → E) :
    Fin (r+1) × Fin (m+1) → FractionRing (MvPolynomial (Fin (r+1) × Fin m) E) :=
  fun a => Fin.cases (-algebraMap _ _ (genericLinearValues f a.1))
    (fun j => algebraMap (MvPolynomial (Fin (r+1) × Fin m) E) (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E)) (MvPolynomial.X (a.1,j))) a.2

noncomputable def genericIncidenceChartHom (K : Type) {E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (f : Fin m → E) :
    MvPolynomial (Fin (r+1) × Fin (m+1)) K →ₐ[K]
      FractionRing (MvPolynomial (Fin (r+1) × Fin m) E) :=
  MvPolynomial.aeval (genericIncidenceChartValues (r := r) f)


end APSCounting893.Main
end Component_1

section Component_2
open MvPolynomial
namespace APSCounting893.Main
lemma exists_rational_incidence_relation_bounded {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (Q : MvPolynomial (Fin r) K) (hQ : Q ≠ 0)
    (P : Fin m → MvPolynomial (Fin r) K)
    (v : Fin m → FractionRing (MvPolynomial (Fin r) K))
    (hP : ∀ i, algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) (P i) =
      algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) Q * v i)
    (g : Fin r → Fin m) (hg : AlgebraicIndependent K (v ∘ g))
    (d : ℕ) (hd : 0 < d) (hdQ : Q.totalDegree ≤ d) (hdP : ∀ i, (P i).totalDegree ≤ d) :
    ∃ q : MvPolynomial (Fin (r+1) × Fin (m+1)) K,
      q ≠ 0 ∧ q.totalDegree ≤ (r+1)*d^r ∧ genericIncidenceChartHom K v q = 0 := by
  exact rational_incidence_relation_bounded Q hQ P v hP g hg d hd hdQ hdP
end APSCounting893.Main
end Component_2

section Component_3
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma coordinate_algebraic_over_ratio_field {K E σ : Type} [Field K] [Field E] [Algebra K E]
    [Fintype σ] (v : σ → E) (j : σ) (hj : v j ≠ 0)
    (p : MvPolynomial σ K) (hp : MvPolynomial.aeval v p=0)
    (hp0 : MvPolynomial.eval (0 : σ → K) p ≠ 0) :
    IsAlgebraic (IntermediateField.adjoin K (Set.range (fun i => v i / v j))) (v j) := by
  classical
  let R := IntermediateField.adjoin K (Set.range (fun i => v i / v j))
  let w : σ → R := fun i => ⟨v i / v j,IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩
  let phi : MvPolynomial σ K →+* Polynomial R := MvPolynomial.eval₂Hom
    (Polynomial.C.comp (algebraMap K R)) (fun i => Polynomial.C (w i)*Polynomial.X)
  let Q := phi p
  have hzero : (Polynomial.evalRingHom (0 : R)).comp phi = (algebraMap K R).comp (MvPolynomial.eval (0 : σ → K)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [phi]
    · intro i
      simp [phi]
  have hQ : Q ≠ 0 := by
    intro hz
    have hh := congrArg (fun f : MvPolynomial σ K →+* R => f p) hzero
    change Q.eval 0 = algebraMap K R (MvPolynomial.eval (0 : σ → K) p) at hh
    rw [hz,Polynomial.eval_zero] at hh
    apply hp0
    exact (algebraMap K R).injective (by simpa using hh.symm)
  let psi : Polynomial R →+* E := Polynomial.eval₂RingHom (algebraMap R E) (v j)
  have hpsi : psi.comp phi = (MvPolynomial.aeval v).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [phi,psi,← IsScalarTower.algebraMap_apply K R E]
    · intro i
      simp [phi,psi,w,hj]
  refine ⟨Q,hQ,?_⟩
  have hh := congrArg (fun f : MvPolynomial σ K →+* E => f p) hpsi
  change psi Q = MvPolynomial.aeval v p at hh
  rw [hp] at hh
  exact hh

end APSCounting893.Main
end Component_3

section Component_4

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
end Component_4

section Component_5
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma imageClosure_vanishingIdeal_eq_kernel {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) :
    vanishingIdeal K (imageClosure F) = RingHom.ker (MvPolynomial.aeval F).toRingHom := by
  rw [imageClosure,vanishingIdeal_zClosure,image_vanishingIdeal_eq_kernel]
  rfl

noncomputable def imageCoordinateAlgebraMap {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : CoordinateRing (imageClosure F) →ₐ[K] MvPolynomial (Fin n) K :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval F) (fun p hp => by
    rw [imageClosure_vanishingIdeal_eq_kernel] at hp
    exact hp)

lemma imageCoordinateAlgebraMap_mk {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (p : Polynomials K m) :
    imageCoordinateAlgebraMap F (Ideal.Quotient.mk (vanishingIdeal K (imageClosure F)) p) =
      MvPolynomial.aeval F p := rfl

lemma imageCoordinateAlgebraMap_injective {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : Function.Injective (imageCoordinateAlgebraMap F) := by
  apply (injective_iff_map_eq_zero (imageCoordinateAlgebraMap F).toRingHom).mpr
  intro x hx
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [imageClosure_vanishingIdeal_eq_kernel]
  change MvPolynomial.aeval F p = 0
  change imageCoordinateAlgebraMap F (Ideal.Quotient.mk _ p) = 0 at hx
  rw [imageCoordinateAlgebraMap_mk] at hx
  exact hx

lemma imageCoordinateAlgebraMap_coordinate {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (j : Fin m) :
    imageCoordinateAlgebraMap F (coordinate (imageClosure F) j) = F j := by
  change imageCoordinateAlgebraMap F (Ideal.Quotient.mk _ (MvPolynomial.X j)) = F j
  rw [imageCoordinateAlgebraMap_mk,MvPolynomial.aeval_X]

end APSCounting893.Main
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma polynomial_map_relation_nonzero_at_origin {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (h0 : (0 : Affine K m) ∉ imageClosure F) :
    ∃ p : Polynomials K m, MvPolynomial.aeval F p=0 ∧ eval (0 : Affine K m) p ≠ 0 := by
  classical
  have hex : ∃ p ∈ vanishingIdeal K (Set.range (evaluate F)), MvPolynomial.aeval (R := K) (0 : Affine K m) p ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (fun p hp => h p hp)
  obtain ⟨p,hp,hp0⟩ := hex
  refine ⟨p,?_,?_⟩
  · rw [image_vanishingIdeal_eq_kernel] at hp
    exact hp
  · simpa only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id] using hp0

lemma all_coordinates_algebraic_over_ratio_field {K E σ : Type} [Field K] [Field E] [Algebra K E]
    [Fintype σ] (v : σ → E) (j : σ) (hj : v j ≠ 0)
    (p : MvPolynomial σ K) (hp : MvPolynomial.aeval v p=0)
    (hp0 : MvPolynomial.eval (0 : σ → K) p ≠ 0) :
    ∀ i : σ, IsAlgebraic (IntermediateField.adjoin K (Set.range (fun i => v i / v j))) (v i) := by
  intro i
  let R := IntermediateField.adjoin K (Set.range (fun i => v i / v j))
  let w : R := ⟨v i/v j,IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩
  have hjalg := coordinate_algebraic_over_ratio_field v j hj p hp hp0
  have hw : IsAlgebraic R (algebraMap R E w) := isAlgebraic_algebraMap w
  have hh := hw.mul hjalg
  change IsAlgebraic R ((v i/v j)*v j) at hh
  simpa only [div_mul_cancel₀ _ hj] using hh

lemma polynomial_map_coordinates_algebraic_over_ratios {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (h0 : (0 : Affine K m) ∉ imageClosure F)
    (j : Fin m) (hj : F j ≠ 0) :
    let E := FractionRing (Polynomials K n)
    let v : Fin m → E := fun i => algebraMap (Polynomials K n) E (F i)
    ∀ i, IsAlgebraic (IntermediateField.adjoin K (Set.range (fun i => v i / v j))) (v i) := by
  classical
  let E := FractionRing (Polynomials K n)
  let v : Fin m → E := fun i => algebraMap (Polynomials K n) E (F i)
  obtain ⟨p,hp,hp0⟩ := polynomial_map_relation_nonzero_at_origin F h0
  have hvj : v j ≠ 0 := by
    simpa only [v,map_zero] using (IsFractionRing.injective (Polynomials K n) E).ne hj
  have heval : MvPolynomial.aeval (R := K) v = (IsScalarTower.toAlgHom K (Polynomials K n) E).comp (MvPolynomial.aeval F) := by
    ext i <;> simp only [MvPolynomial.aeval_C,MvPolynomial.aeval_X,AlgHom.comp_apply] <;> rfl
  have hpv : MvPolynomial.aeval v p=0 := by
    rw [heval,AlgHom.comp_apply,hp,map_zero]
  exact all_coordinates_algebraic_over_ratio_field v j hvj p hpv hp0

end APSCounting893.Main
end Component_6

section Component_7
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open IntermediateField
namespace APSCounting893.Main

lemma trdeg_lower_of_independent_algebraic_coordinates {K R E : Type}
    [Field K] [Field R] [Field E] [Algebra K R] [Algebra K E] [Algebra R E] [IsScalarTower K R E]
    {r : ℕ} (v : Fin r → E) (hv : AlgebraicIndependent K v) (halg : ∀ i, IsAlgebraic R (v i)) :
    (r : Cardinal) ≤ Algebra.trdeg K R := by
  classical
  let M := IntermediateField.adjoin R (Set.range v)
  letI : Algebra K M := ((algebraMap R M).comp (algebraMap K R)).toAlgebra
  letI : IsScalarTower K R M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower K M E := IsScalarTower.of_algebraMap_eq (fun k => by
    change algebraMap K E k = algebraMap R E (algebraMap K R k)
    exact IsScalarTower.algebraMap_apply K R E k)
  let w : Fin r → M := fun i => ⟨v i,IntermediateField.subset_adjoin R _ (Set.mem_range_self i)⟩
  letI : Algebra.IsAlgebraic R M := IntermediateField.isAlgebraic_adjoin (by
    rintro x ⟨i,rfl⟩
    exact (halg i).isIntegral)
  have hw : AlgebraicIndependent K w := by
    apply AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom K M E)
    exact hv
  have hcard := hw.cardinalMk_le_trdeg
  have heq := trdeg_add_eq K R (A := M)
  have hz : Algebra.trdeg R M = 0 := trdeg_eq_zero
  rw [hz,add_zero] at heq
  rw [← heq] at hcard
  simpa using hcard

end APSCounting893.Main
end Component_7

section Component_8
set_option autoImplicit false
set_option maxHeartbeats 400000
open Cardinal
namespace APSCounting893.Main

lemma algebraic_over_subfield_of_full_independent_algebraic_coordinates {K R E : Type}
    [Field K] [Field R] [Field E] [Algebra K R] [Algebra K E] [Algebra R E] [IsScalarTower K R E]
    {r : ℕ} (hE : Algebra.trdeg K E = (r : Cardinal))
    (v : Fin r → E) (hv : AlgebraicIndependent K v) (halg : ∀ i, IsAlgebraic R (v i)) :
    Algebra.IsAlgebraic R E := by
  have hlo := trdeg_lower_of_independent_algebraic_coordinates v hv halg
  have hhi := trdeg_le_of_injective (IsScalarTower.toAlgHom K R E) (algebraMap R E).injective
  have hR : Algebra.trdeg K R = (r : Cardinal) := le_antisymm (hhi.trans_eq hE) hlo
  have hsum := trdeg_add_eq K R (A := E)
  rw [hR,hE] at hsum
  have hz : Algebra.trdeg R E = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hsum with hbad | hgood
    · have hh := (le_max_left _ _).trans hbad
      exact False.elim (not_le_of_gt (Cardinal.nat_lt_aleph0 r) hh)
    · exact hgood
  exact trdeg_eq_zero_iff.mp hz

end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
namespace APSCounting893.Main

lemma rationalFunction_trdeg (K : Type) [Field K] (n : ℕ) :
    Algebra.trdeg K (FractionRing (MvPolynomial (Fin n) K)) = (n : Cardinal) := by
  let P := MvPolynomial (Fin n) K
  let E := FractionRing P
  letI : Algebra.IsAlgebraic P E := IsLocalization.isAlgebraic E (nonZeroDivisors P)
  have heq := trdeg_add_eq K P (A := E)
  have hz : Algebra.trdeg P E=0 := trdeg_eq_zero
  rw [hz,add_zero] at heq
  rw [MvPolynomial.trdeg_of_isDomain] at heq
  simpa only [Cardinal.mk_fin,Cardinal.lift_natCast] using heq.symm

lemma rationalFunction_trdeg_of_isFractionRing (K : Type) [Field K] (n : ℕ)
    (E : Type) [Field E] [Algebra K E] [Algebra (MvPolynomial (Fin n) K) E]
    [IsScalarTower K (MvPolynomial (Fin n) K) E] [IsFractionRing (MvPolynomial (Fin n) K) E] :
    Algebra.trdeg K E = (n : Cardinal) := by
  let P := MvPolynomial (Fin n) K
  letI : Algebra.IsAlgebraic P E := IsLocalization.isAlgebraic E (nonZeroDivisors P)
  have heq := trdeg_add_eq K P (A := E)
  have hz : Algebra.trdeg P E = 0 := trdeg_eq_zero
  rw [hz,add_zero] at heq
  rw [MvPolynomial.trdeg_of_isDomain] at heq
  simpa only [Cardinal.mk_fin,Cardinal.lift_natCast] using heq.symm

end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma exists_independent_image_coordinates {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞)) :
    ∃ g : Fin r → Fin (m+1), Function.Injective g ∧ AlgebraicIndependent ℂ (F ∘ g) := by
  classical
  let S := MvPolynomial (Fin (m+1)) ℂ
  let R := MvPolynomial (Fin n) ℂ
  let P : Ideal S := RingHom.ker (MvPolynomial.aeval F).toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨s,hind,hcard⟩ := OAI.PiExponent.FormalInterpolation.mvPolynomial_exists_coordinate_transcendence_basis P
  have hDim := OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat P
  have hP : vanishingIdeal ℂ (imageClosure F) = P := by
    rw [imageClosure,vanishingIdeal_zClosure,image_vanishingIdeal_eq_kernel]
    rfl
  change ringKrullDim (S ⧸ vanishingIdeal ℂ (imageClosure F)) = ((r : ℕ∞) : WithBot ℕ∞) at hdim
  rw [hP] at hdim
  have htr : (Algebra.trdeg ℂ (FractionRing (S ⧸ P))).toNat = r := by
    exact_mod_cast hDim.symm.trans hdim
  have hsr : s.card = r := hcard.trans htr
  let f₀ : (S ⧸ P) →ₐ[ℂ] FractionRing (S ⧸ P) := IsScalarTower.toAlgHom ℂ (S ⧸ P) _
  have he (i : s) : f₀ (Ideal.Quotient.mk P (MvPolynomial.X i.1)) =
      algebraMap S (FractionRing (S ⧸ P)) (MvPolynomial.X i.1) := by
    dsimp only [f₀]
    rw [IsScalarTower.toAlgHom_apply,IsScalarTower.algebraMap_apply S (S ⧸ P) (FractionRing (S ⧸ P))]
    rfl
  have hquot : AlgebraicIndependent ℂ (fun i : s => Ideal.Quotient.mk P (MvPolynomial.X i.1)) := by
    apply AlgebraicIndependent.of_comp f₀
    have hef : (f₀ ∘ (fun i : s => Ideal.Quotient.mk P (MvPolynomial.X i.1))) =
        fun i : s => algebraMap S (FractionRing (S ⧸ P)) (MvPolynomial.X i.1) := funext he
    rw [hef]
    exact hind
  let f : (S ⧸ P) →ₐ[ℂ] R := Ideal.Quotient.liftₐ P (MvPolynomial.aeval F) (fun p hp => hp)
  have hfapp (p : S) : f (Ideal.Quotient.mk P p) = MvPolynomial.aeval F p := rfl
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f.toRingHom).mpr
    intro x hx
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change MvPolynomial.aeval F p = 0
    change f (Ideal.Quotient.mk P p) = 0 at hx
    rw [hfapp] at hx
    exact hx
  have hindF : AlgebraicIndependent ℂ (fun i : s => F i.1) := by
    have hh := hquot.map' hf
    have hefun : (f ∘ (fun i : s => Ideal.Quotient.mk P (MvPolynomial.X i.1))) =
        fun i : s => F i.1 := by
      funext i
      change f (Ideal.Quotient.mk P (MvPolynomial.X i.1)) = F i.1
      rw [hfapp,MvPolynomial.aeval_X]
    rw [hefun] at hh
    exact hh
  let e : Fin r ≃ s := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin,Fintype.card_coe] using hsr.symm)
  refine ⟨fun i => (e i).1,Subtype.val_injective.comp e.injective,?_⟩
  exact hindF.comp e e.injective

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma rationalFunction_algebraic_over_output_ratios {r m : ℕ} (F : PolynomialMap ℂ r (m+1))
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (h0 : ¬ hasAPS F) (j : Fin (m+1)) (hj : F j ≠ 0) :
    let E := FractionRing (Polynomials ℂ r)
    let v : Fin (m+1) → E := fun i => algebraMap (Polynomials ℂ r) E (F i)
    Algebra.IsAlgebraic (IntermediateField.adjoin ℂ (Set.range (fun i => v i/v j))) E := by
  classical
  let P := Polynomials ℂ r
  let E := FractionRing P
  let v : Fin (m+1) → E := fun i => algebraMap P E (F i)
  let R := IntermediateField.adjoin ℂ (Set.range (fun i => v i/v j))
  have halg : ∀ i : Fin (m+1), IsAlgebraic R (v i) := polynomial_map_coordinates_algebraic_over_ratios F h0 j hj
  obtain ⟨g,hg,hInd⟩ := exists_independent_image_coordinates F hdim
  have hv : AlgebraicIndependent ℂ (v ∘ g) := by
    have hh := hInd.map' (f := IsScalarTower.toAlgHom ℂ P E) (IsFractionRing.injective P E)
    exact hh
  exact algebraic_over_subfield_of_full_independent_algebraic_coordinates (rationalFunction_trdeg ℂ r)
    (v ∘ g) hv (fun i => halg (g i))

end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open scoped IntermediateField.algebraAdjoinAdjoin
namespace APSCounting893.Main

lemma exists_independent_generating_subfamily {K E : Type} [Field K] [Field E] [Algebra K E]
    {m r : ℕ} (v : Fin m → E)
    (hgen : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range v)) E)
    (htrdeg : Algebra.trdeg K E = (r : Cardinal)) :
    ∃ g : Fin r → Fin m, Function.Injective g ∧ AlgebraicIndependent K (v ∘ g) := by
  classical
  let R := IntermediateField.adjoin K (Set.range v)
  let A := Algebra.adjoin K (Set.range v)
  letI : Algebra.IsAlgebraic R E := hgen
  letI : Algebra.IsAlgebraic A E := Algebra.IsAlgebraic.trans A R E
  obtain ⟨t,ht,hbasis⟩ := exists_isTranscendenceBasis_subset (R := K) (A := E) (Set.range v)
  have hfinite : t.Finite := (Set.finite_range v).subset ht
  letI : Fintype t := hfinite.fintype
  have hcard : Fintype.card t=r := by
    have hh := hbasis.cardinalMk_eq_trdeg
    rw [htrdeg,Cardinal.mk_fintype] at hh
    exact_mod_cast hh
  let e : Fin r ≃ t := Fintype.equivOfCardEq (by simp only [Fintype.card_fin,hcard])
  have hex (i : Fin r) : ∃ j : Fin m, v j=(e i).val := ht (e i).property
  choose g hg using hex
  have hind : AlgebraicIndependent K (v ∘ g) := by
    have hh := hbasis.1.comp e e.injective
    have heq : (fun i => (e i).val) = v ∘ g := by
      funext i
      exact (hg i).symm
    change AlgebraicIndependent K (fun i => (e i).val) at hh
    rw [heq] at hh
    exact hh
  refine ⟨g,?_,hind⟩
  intro i j hij
  apply hind.injective
  exact congrArg v hij

end APSCounting893.Main
end Component_12

section Component_13
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma exists_independent_output_ratios {r m : ℕ} (F : PolynomialMap ℂ r (m+1))
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (h0 : ¬ hasAPS F) (j : Fin (m+1)) (hj : F j ≠ 0) :
    let E := FractionRing (Polynomials ℂ r)
    let v : Fin (m+1) → E := fun i => algebraMap (Polynomials ℂ r) E (F i)
    ∃ g : Fin r → Fin (m+1), Function.Injective g ∧
      AlgebraicIndependent ℂ (fun i => v (g i)/v j) := by
  classical
  let E := FractionRing (Polynomials ℂ r)
  let v : Fin (m+1) → E := fun i => algebraMap (Polynomials ℂ r) E (F i)
  have hgen := rationalFunction_algebraic_over_output_ratios F hdim h0 j hj
  exact exists_independent_generating_subfamily (fun i => v i/v j) hgen (rationalFunction_trdeg ℂ r)

end APSCounting893.Main
end Component_13

section Component_14
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma independent_ratios_without_pivot {K E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (v : Fin (m+1) → E) (j : Fin (m+1)) (hj : v j ≠ 0)
    (g : Fin r → Fin (m+1)) (hg : AlgebraicIndependent K (fun i => v (g i)/v j)) :
    ∃ g' : Fin r → Fin m, AlgebraicIndependent K (fun i =>
      v ((Equiv.swap 0 j) (g' i).succ)/v j) := by
  classical
  let e : Fin (m+1) ≃ Fin (m+1) := Equiv.swap 0 j
  have hgj (i : Fin r) : g i ≠ j := by
    intro heq
    have ht := hg.transcendental i
    have hconst : v (g i)/v j=1 := by rw [heq,div_self hj]
    rw [hconst] at ht
    exact ht (by simpa only [map_one] using (isAlgebraic_algebraMap (1 : K) : IsAlgebraic K (algebraMap K E 1)))
  have hpred (i : Fin r) : e.symm (g i) ≠ 0 := by
    intro hi
    have hh := congrArg e hi
    rw [Equiv.apply_symm_apply] at hh
    have he0 : e 0=j := by simp [e]
    rw [he0] at hh
    exact hgj i hh
  let g' : Fin r → Fin m := fun i => (e.symm (g i)).pred (hpred i)
  refine ⟨g',?_⟩
  have heq : (fun i : Fin r => v ((Equiv.swap 0 j) (g' i).succ)/v j) =
      fun i => v (g i)/v j := by
    funext i
    change v (e ((e.symm (g i)).pred (hpred i)).succ)/v j = _
    rw [Fin.succ_pred,Equiv.apply_symm_apply]
  rw [heq]
  exact hg

end APSCounting893.Main
end Component_14

section Component_15
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def weightedDegreePolynomial {K σ : Type} [CommSemiring K]
    (w : σ → ℕ) : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X^(w i))

lemma weightedDegreePolynomial_monomial {K σ : Type} [CommSemiring K]
    (w : σ → ℕ) (e : σ →₀ ℕ) (c : K) :
    weightedDegreePolynomial w (MvPolynomial.monomial e c) =
      Polynomial.monomial (e.sum (fun i k => k*w i)) (MvPolynomial.monomial e c) := by
  classical
  rw [weightedDegreePolynomial,MvPolynomial.aeval_monomial]
  rw [show algebraMap K (Polynomial (MvPolynomial σ K)) c = Polynomial.C (MvPolynomial.C c) by rfl]
  simp only [mul_pow,← Polynomial.C_pow,← pow_mul]
  rw [Finsupp.prod_mul]
  have hprod : (e.prod fun i k => Polynomial.C ((MvPolynomial.X i : MvPolynomial σ K) ^ k)) =
      Polynomial.C (e.prod fun i k => (MvPolynomial.X i : MvPolynomial σ K) ^ k) := by
    unfold Finsupp.prod
    rw [map_prod]
  have hpow : (e.prod fun i k => (Polynomial.X : Polynomial (MvPolynomial σ K)) ^ (w i*k)) =
      Polynomial.X ^ (e.sum (fun i k => k*w i)) := by
    unfold Finsupp.prod Finsupp.sum
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.mul_comm _ _
  rw [hprod,hpow,← mul_assoc,← map_mul,← MvPolynomial.monomial_eq,Polynomial.C_mul_X_pow_eq_monomial]

lemma weightedDegreePolynomial_coeff_coeff {K σ : Type} [CommSemiring K]
    (w : σ → ℕ) (p : MvPolynomial σ K) (k : ℕ) (e : σ →₀ ℕ) :
    ((weightedDegreePolynomial w p).coeff k).coeff e =
      if e.sum (fun i v => v*w i) = k then p.coeff e else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [weightedDegreePolynomial_monomial,Polynomial.coeff_monomial]
    by_cases ha : a=e
    · subst a
      by_cases hk : k=e.sum (fun i k => k*w i) <;> simp [MvPolynomial.coeff_monomial,eq_comm,hk]
    · split_ifs <;> simp [MvPolynomial.coeff_monomial,ha,Ne.symm ha]
  | add p q hp hq =>
    simp only [map_add,Polynomial.coeff_add,MvPolynomial.coeff_add,hp,hq]
    split_ifs <;> simp

lemma weightedDegreePolynomial_natDegree {K σ : Type} [CommSemiring K] (w : σ → ℕ)
    (p : MvPolynomial σ K) :
    (weightedDegreePolynomial w p).natDegree = MvPolynomial.weightedTotalDegree w p := by
  classical
  let D := MvPolynomial.weightedTotalDegree w p
  have hweight (e : σ →₀ ℕ) : Finsupp.weight w e = e.sum (fun i k => k*w i) := by
    simp only [Finsupp.weight_apply,smul_eq_mul]
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    ext e
    rw [weightedDegreePolynomial_coeff_coeff,MvPolynomial.coeff_zero]
    split_ifs with he
    · by_contra hne
      have hh := Finset.le_sup (f := fun e => Finsupp.weight w e) (MvPolynomial.mem_support_iff.mpr hne)
      rw [hweight,he] at hh
      exact (not_le_of_gt hk) hh
    · rfl
  · unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro e he
    apply Polynomial.le_natDegree_of_ne_zero
    intro hz
    have hh := congrArg (fun q : MvPolynomial σ K => q.coeff e) hz
    rw [weightedDegreePolynomial_coeff_coeff,MvPolynomial.coeff_zero] at hh
    rw [hweight,if_pos rfl] at hh
    exact MvPolynomial.mem_support_iff.mp he hh

lemma weightedTotalDegree_mul_eq {K σ : Type} [CommRing K] [IsDomain K]
    (w : σ → ℕ) (p q : MvPolynomial σ K) (hp : p ≠ 0) (hq : q ≠ 0) :
    MvPolynomial.weightedTotalDegree w (p*q) =
      MvPolynomial.weightedTotalDegree w p + MvPolynomial.weightedTotalDegree w q := by
  have hinj : Function.Injective (weightedDegreePolynomial (K := K) w) := by
    intro a b h
    ext e
    have hh := congrArg (fun f : Polynomial (MvPolynomial σ K) => (f.coeff (e.sum (fun i k => k*w i))).coeff e) h
    simpa only [weightedDegreePolynomial_coeff_coeff,if_true] using hh
  rw [← weightedDegreePolynomial_natDegree, map_mul,Polynomial.natDegree_mul]
  · rw [weightedDegreePolynomial_natDegree,weightedDegreePolynomial_natDegree]
  · simpa only [map_zero] using hinj.ne hp
  · simpa only [map_zero] using hinj.ne hq

end APSCounting893.Main
end Component_15

section Component_16
set_option autoImplicit false
set_option maxHeartbeats 800000
open MvPolynomial
namespace APSCounting893.Main

noncomputable def rowDegree {K ι κ : Type} [CommSemiring K] [DecidableEq ι]
    (i : ι) (p : MvPolynomial (ι × κ) K) : ℕ :=
  MvPolynomial.weightedTotalDegree (fun a : ι × κ => if a.1=i then (1 : ℕ) else 0) p

lemma rowDegree_le_iff {K ι κ : Type} [CommSemiring K] [DecidableEq ι]
    (i : ι) (p : MvPolynomial (ι × κ) K) (d : ℕ) :
    rowDegree i p ≤ d ↔ ∀ e ∈ p.support, e.sum (fun a k => if a.1=i then k else 0) ≤ d := by
  classical
  simp only [rowDegree,MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
  congr! 3
  simp [Finsupp.weight,Finsupp.linearCombination_apply,Finsupp.sum,smul_eq_mul]

lemma totalDegree_le_sum_rowDegree {K ι κ : Type} [CommSemiring K] [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial (ι × κ) K) : p.totalDegree ≤ ∑ i, rowDegree i p := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro e he
  have hs : e.sum (fun _ k => k) = ∑ i : ι, e.sum (fun a k => if a.1=i then k else 0) := by
    unfold Finsupp.sum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp
  rw [hs]
  apply Finset.sum_le_sum
  intro i _
  exact (rowDegree_le_iff i p _).mp le_rfl e he

lemma rowDegree_mul_eq {K ι κ : Type} [CommRing K] [IsDomain K] [DecidableEq ι]
    (i : ι) (p q : MvPolynomial (ι × κ) K) (hp : p ≠ 0) (hq : q ≠ 0) :
    rowDegree i (p*q) = rowDegree i p + rowDegree i q :=
  weightedTotalDegree_mul_eq _ p q hp hq

lemma rowDegree_le_of_dvd {K ι κ : Type} [CommRing K] [IsDomain K] [DecidableEq ι]
    (i : ι) {p q : MvPolynomial (ι × κ) K} (h : p ∣ q) (hq : q ≠ 0) :
    rowDegree i p ≤ rowDegree i q := by
  obtain ⟨b,rfl⟩ := h
  rw [rowDegree_mul_eq i p b (left_ne_zero_of_mul hq) (right_ne_zero_of_mul hq)]
  exact Nat.le_add_right _ _

lemma rowDegree_rename_rows {K ι κ : Type} [CommSemiring K] [DecidableEq ι]
    (e : ι ≃ ι) (i : ι) (p : MvPolynomial (ι × κ) K) :
    rowDegree (e i) (MvPolynomial.rename (fun a : ι × κ => (e a.1,a.2)) p) = rowDegree i p := by
  have hinj : Function.Injective (fun a : ι × κ => (e a.1,a.2)) := by
    intro a b h
    apply Prod.ext
    · exact e.injective (congrArg Prod.fst h)
    · simpa only using congrArg (fun x : ι × κ => x.2) h
  unfold rowDegree
  rw [MvPolynomial.weightedTotalDegree_rename_of_injective hinj]
  congr 1
  funext a
  simp only [Function.comp_apply,Equiv.apply_eq_iff_eq]

lemma totalDegree_le_rows_bound {K ι κ : Type} [CommSemiring K] [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial (ι × κ) K) (d : ℕ) (h : ∀ i, rowDegree i p ≤ d) :
    p.totalDegree ≤ Fintype.card ι * d := by
  apply (totalDegree_le_sum_rowDegree p).trans
  exact (Finset.sum_le_sum (fun i _ => h i)).trans_eq (by simp)

end APSCounting893.Main
end Component_16

section Component_17
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def genericIncidencePolynomialValues {E : Type} [Field E] {r m : ℕ} (f : Fin m → E) :
    Fin (r+1) × Fin (m+1) → MvPolynomial (Fin (r+1) × Fin m) E :=
  fun a => Fin.cases (-genericLinearValues f a.1) (fun j => MvPolynomial.X (a.1,j)) a.2

noncomputable def genericIncidencePolynomialHom (K : Type) {E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (f : Fin m → E) :
    MvPolynomial (Fin (r+1) × Fin (m+1)) K →ₐ[K] MvPolynomial (Fin (r+1) × Fin m) E :=
  MvPolynomial.aeval (genericIncidencePolynomialValues f)

lemma genericIncidenceChartHom_eq_map {K E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (f : Fin m → E) (p : MvPolynomial (Fin (r+1) × Fin (m+1)) K) :
    genericIncidenceChartHom K f p = algebraMap _ (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E))
      (genericIncidencePolynomialHom K f p) := by
  have heq : genericIncidenceChartHom K f =
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin (r+1) × Fin m) E) _).comp (genericIncidencePolynomialHom K f) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [genericIncidenceChartHom,genericIncidencePolynomialHom,AlgHom.comp_apply,MvPolynomial.aeval_X]
    rcases a with ⟨i,j⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [genericIncidenceChartValues,genericIncidencePolynomialValues]
    · rfl
  exact AlgHom.congr_fun heq p

lemma genericIncidencePolynomialHom_rename_rows {K E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (f : Fin m → E) (e : Fin (r+1) ≃ Fin (r+1))
    (p : MvPolynomial (Fin (r+1) × Fin (m+1)) K) :
    genericIncidencePolynomialHom K f (MvPolynomial.rename (fun a => (e a.1,a.2)) p) =
      MvPolynomial.rename (fun a => (e a.1,a.2)) (genericIncidencePolynomialHom K f p) := by
  let u : Fin (r+1) × Fin (m+1) → Fin (r+1) × Fin (m+1) := fun a => (e a.1,a.2)
  let v : Fin (r+1) × Fin m → Fin (r+1) × Fin m := fun a => (e a.1,a.2)
  have heq : (genericIncidencePolynomialHom K f).comp (MvPolynomial.rename u) =
      ((MvPolynomial.rename v).restrictScalars K).comp (genericIncidencePolynomialHom K f) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply,MvPolynomial.rename_X,genericIncidencePolynomialHom,MvPolynomial.aeval_X]
    rcases a with ⟨i,j⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [genericIncidencePolynomialValues,genericLinearValues,u,v]
    · simp [genericIncidencePolynomialValues,u,v]
  exact AlgHom.congr_fun heq p

lemma generic_incidence_kernel_row_invariant {K E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (f : Fin m → E) (e : Fin (r+1) ≃ Fin (r+1))
    (p : MvPolynomial (Fin (r+1) × Fin (m+1)) K)
    (hp : genericIncidenceChartHom K f p = 0) :
    genericIncidenceChartHom K f (MvPolynomial.rename (fun a => (e a.1,a.2)) p) = 0 := by
  rw [genericIncidenceChartHom_eq_map] at hp ⊢
  have hz : genericIncidencePolynomialHom K f p = 0 :=
    (IsFractionRing.injective (MvPolynomial (Fin (r+1) × Fin m) E) (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E)))
      (by simpa only [map_zero] using hp)
  rw [genericIncidencePolynomialHom_rename_rows,hz,map_zero,map_zero]

end APSCounting893.Main
end Component_17

section Component_18
set_option autoImplicit false
set_option maxHeartbeats 500000
open MvPolynomial
namespace APSCounting893.Main

noncomputable def incidenceMatrixAt {K : Type} [Field K] {m r : ℕ}
    (j : Fin m) (z : Fin m → K) (B : Fin r × Fin m → K) : Fin r × Fin m → K :=
  fun a => z j * B a - (∑ t : Fin m, z t * B (a.1,t)) * (if a.2=j then 1 else 0)

lemma incidenceMatrixAt_annihilates {K : Type} [Field K] {m r : ℕ}
    (j : Fin m) (z : Fin m → K) (B : Fin r × Fin m → K) (i : Fin r) :
    ∑ l : Fin m, incidenceMatrixAt j z B (i,l) * z l = 0 := by
  classical
  simp only [incidenceMatrixAt,sub_mul,Finset.sum_sub_distrib,mul_assoc,← Finset.mul_sum,
    ite_mul,one_mul,zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ,ite_true]
  have hh : (∑ x : Fin m, B (i,x)*z x) = ∑ x : Fin m, z x*B (i,x) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact mul_comm _ _
  rw [hh,mul_comm,sub_self]

lemma incidenceMatrixAt_recover {K : Type} [Field K] {m r : ℕ}
    (j : Fin m) (z : Fin m → K) (hj : z j ≠ 0) (A : Fin r × Fin m → K)
    (hA : ∀ i, ∑ l : Fin m, A (i,l)*z l=0) :
    incidenceMatrixAt j z (fun a => A a / z j) = A := by
  classical
  have hsum (i : Fin r) : (∑ t : Fin m, z t*(A (i,t)/z j)) = 0 := by
    simp only [← mul_div_assoc,← Finset.sum_div]
    have hh : (∑ t : Fin m, z t*A (i,t)) = ∑ t : Fin m, A (i,t)*z t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact mul_comm _ _
    rw [hh,hA,zero_div]
  funext a
  simp only [incidenceMatrixAt,hsum,zero_mul,sub_zero]
  field_simp

noncomputable def incidencePointPolynomials {K : Type} [Field K] {m r : ℕ}
    (j : Fin m) (B : Fin r × Fin m → K) : Fin r × Fin m → MvPolynomial (Fin m) K :=
  fun a => MvPolynomial.C (B a) * MvPolynomial.X j -
    (∑ t : Fin m, MvPolynomial.C (B (a.1,t))*MvPolynomial.X t) * (if a.2=j then 1 else 0)

lemma incidencePointPolynomials_eval {K : Type} [Field K] {m r : ℕ}
    (j : Fin m) (B : Fin r × Fin m → K) (z : Fin m → K) :
    (fun a => eval z (incidencePointPolynomials j B a)) = incidenceMatrixAt j z B := by
  classical
  funext a
  by_cases ha : a.2=j <;> simp [incidencePointPolynomials,incidenceMatrixAt,ha,mul_comm]

end APSCounting893.Main
end Component_18

section Component_19
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main

lemma vanishes_on_irreducible_of_vanishes_off_hyperplane {K : Type} [Field K] {m : ℕ}
    (Y : Set (Affine K m)) (hY : IrreducibleAffine Y) (j : Fin m)
    (hj : ∃ z ∈ Y, z j ≠ 0) (p : Polynomials K m)
    (hp : ∀ z ∈ Y, z j ≠ 0 → eval z p = 0) : p ∈ vanishingIdeal K Y := by
  have hprime := irreducibleAffine_ideal_prime hY
  have hX : (MvPolynomial.X j : Polynomials K m) ∉ vanishingIdeal K Y := by
    intro hh
    obtain ⟨z,hz,hzj⟩ := hj
    apply hzj
    simpa using hh z hz
  have hprod : MvPolynomial.X j*p ∈ vanishingIdeal K Y := by
    intro z hz
    simp only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id,map_mul,MvPolynomial.eval_X]
    by_cases hh : z j=0
    · rw [hh,zero_mul]
    · rw [hp z hz hh,mul_zero]
  exact (hprime.mem_or_mem hprod).resolve_left hX

end APSCounting893.Main
end Component_19

section Component_20
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma eval_incidencePointSubstitution {K : Type} [Field K] {m r : ℕ}
    (q : MvPolynomial (Fin r × Fin m) K) (j : Fin m) (B : Fin r × Fin m → K) (z : Fin m → K) :
    eval z (MvPolynomial.aeval (incidencePointPolynomials j B) q) = eval (incidenceMatrixAt j z B) q := by
  have hh := MvPolynomial.comp_aeval_apply (incidencePointPolynomials j B) (MvPolynomial.aeval (R := K) z) q
  have hf : (fun a => MvPolynomial.aeval (R := K) z (incidencePointPolynomials j B a)) = incidenceMatrixAt j z B := by
    simpa only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id] using incidencePointPolynomials_eval j B z
  rw [hf] at hh
  simpa only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id] using hh

lemma incidence_relation_all_pivots {K : Type} [Field K] {m r : ℕ}
    (Y : Set (Affine K m)) (hY : IrreducibleAffine Y) (j : Fin m)
    (hj : ∃ z ∈ Y, z j ≠ 0) (q : MvPolynomial (Fin r × Fin m) K)
    (hq : ∀ z ∈ Y, ∀ B : Fin r × Fin m → K, eval (incidenceMatrixAt j z B) q = 0) :
    ∀ k : Fin m, ∀ z ∈ Y, ∀ B : Fin r × Fin m → K, eval (incidenceMatrixAt k z B) q = 0 := by
  classical
  intro k z hz B
  let p := MvPolynomial.aeval (incidencePointPolynomials k B) q
  have hp : p ∈ vanishingIdeal K Y := by
    apply vanishes_on_irreducible_of_vanishes_off_hyperplane Y hY j hj
    intro x hx hxj
    rw [show p = MvPolynomial.aeval (incidencePointPolynomials k B) q from rfl,eval_incidencePointSubstitution]
    let A := incidenceMatrixAt k x B
    have hA (i : Fin r) : ∑ l : Fin m, A (i,l)*x l=0 := incidenceMatrixAt_annihilates k x B i
    have hh := hq x hx (fun a => A a / x j)
    rw [incidenceMatrixAt_recover j x hxj A hA] at hh
    exact hh
  have hh := hp z hz
  simp only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id] at hh
  change eval z (MvPolynomial.aeval (incidencePointPolynomials k B) q) = 0 at hh
  rwa [eval_incidencePointSubstitution] at hh

lemma incidence_relation_vanishes_on_common_zero {K : Type} [Field K] {m r : ℕ}
    (Y : Set (Affine K m)) (hY : IrreducibleAffine Y) (j : Fin m)
    (hj : ∃ z ∈ Y, z j ≠ 0) (q : MvPolynomial (Fin r × Fin m) K)
    (hq : ∀ z ∈ Y, ∀ B : Fin r × Fin m → K, eval (incidenceMatrixAt j z B) q = 0)
    (z : Fin m → K) (hz : z ∈ Y) (hne : z ≠ 0) (A : Fin r × Fin m → K)
    (hA : ∀ i, ∑ l : Fin m, A (i,l)*z l=0) : eval A q=0 := by
  classical
  have hex : ∃ k, z k ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    funext k
    exact h k
  obtain ⟨k,hk⟩ := hex
  have hh := incidence_relation_all_pivots Y hY j hj q hq k z hz (fun a => A a / z k)
  rwa [incidenceMatrixAt_recover k z hk A hA] at hh

end APSCounting893.Main
end Component_20

section Component_21
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma incidence_raw_polynomial_zero {K : Type} [Field K] {n r m : ℕ}
    (F : Fin (m+1) → MvPolynomial (Fin n) K) (hF : F 0 ≠ 0)
    (q : MvPolynomial (Fin (r+1) × Fin (m+1)) K)
    (hq : genericIncidenceChartHom K (fun j =>
      algebraMap _ (FractionRing (MvPolynomial (Fin n) K)) (F j.succ) /
        algebraMap _ (FractionRing (MvPolynomial (Fin n) K)) (F 0)) q = 0)
    (s : K) (B : Fin (r+1) × Fin (m+1) → K) :
    MvPolynomial.aeval (fun a =>
      MvPolynomial.C (B a)*MvPolynomial.C s*F 0 -
        (∑ t : Fin (m+1), MvPolynomial.C (B (a.1,t))*MvPolynomial.C s*F t)*
          (if a.2=0 then 1 else 0)) q = 0 := by
  classical
  let A := MvPolynomial (Fin n) K
  let E := FractionRing A
  let v : Fin m → E := fun j => algebraMap A E (F j.succ)/algebraMap A E (F 0)
  let u : Fin (r+1) × Fin (m+1) → A := fun a =>
    MvPolynomial.C (B a)*MvPolynomial.C s*F 0 -
      (∑ t : Fin (m+1), MvPolynomial.C (B (a.1,t))*MvPolynomial.C s*F t)*(if a.2=0 then 1 else 0)
  let c : Fin (r+1) × Fin m → E := fun a =>
    algebraMap A E (MvPolynomial.C (s*B (a.1,a.2.succ))*F 0)
  have hQ : algebraMap A E (F 0) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A E).ne hF
  have hpoly : genericIncidencePolynomialHom K v q = 0 := by
    have hh := hq
    rw [genericIncidenceChartHom_eq_map] at hh
    exact (IsFractionRing.injective (MvPolynomial (Fin (r+1) × Fin m) E) (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E)))
      (by simpa only [map_zero] using hh)
  have hz := congrArg (MvPolynomial.eval c) hpoly
  change MvPolynomial.eval c (MvPolynomial.aeval (genericIncidencePolynomialValues v) q) = 0 at hz
  have hcoeff : (MvPolynomial.eval c).comp (algebraMap K (MvPolynomial (Fin (r+1) × Fin m) E)) = algebraMap K E := by
    ext k
    change MvPolynomial.eval c (MvPolynomial.C (algebraMap K E k)) = _
    exact MvPolynomial.eval_C _
  change MvPolynomial.eval c (MvPolynomial.eval₂Hom (algebraMap K _) (genericIncidencePolynomialValues v) q)=0 at hz
  rw [MvPolynomial.map_eval₂Hom,hcoeff] at hz
  have hvals : (fun a => MvPolynomial.eval c (genericIncidencePolynomialValues v a)) =
      fun a => algebraMap A E (u a) := by
    funext a
    rcases a with ⟨i,j⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [genericIncidencePolynomialValues,Fin.cases_zero,map_neg,genericLinearValues,map_sum,map_mul,MvPolynomial.eval_X,MvPolynomial.eval_C]
      change -(∑ j : Fin m, algebraMap A E (MvPolynomial.C (s*B (i,j.succ))*F 0) *
        (algebraMap A E (F j.succ)/algebraMap A E (F 0))) = algebraMap A E (u (i,0))
      have hterm (j : Fin m) : algebraMap A E (MvPolynomial.C (s*B (i,j.succ))*F 0) *
          (algebraMap A E (F j.succ)/algebraMap A E (F 0)) =
          algebraMap A E (MvPolynomial.C (B (i,j.succ))*MvPolynomial.C s*F j.succ) := by
        simp only [map_mul,MvPolynomial.C_mul]
        rw [div_eq_mul_inv]
        calc
          _ = algebraMap A E (MvPolynomial.C s) * algebraMap A E (MvPolynomial.C (B (i,j.succ))) * algebraMap A E (F j.succ) *
            (algebraMap A E (F 0)*(algebraMap A E (F 0))⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ hQ,mul_one]; ring
      simp_rw [hterm]
      simp only [u,ite_true,mul_one,Fin.sum_univ_succ,map_sub,map_add,map_sum,map_mul]
      ring
    · simp only [genericIncidencePolynomialValues,Fin.cases_succ,MvPolynomial.eval_X]
      change algebraMap A E (MvPolynomial.C (s*B (i,j.succ))*F 0)=algebraMap A E (u (i,j.succ))
      congr 1
      simp [u,Fin.succ_ne_zero,MvPolynomial.C_mul,mul_comm,mul_left_comm]
  rw [hvals] at hz
  have hm := MvPolynomial.map_eval₂Hom (MvPolynomial.C : K →+* A) u (algebraMap A E) q
  have hmcoeff : (algebraMap A E).comp MvPolynomial.C = algebraMap K E := by ext k; rfl
  rw [hmcoeff] at hm
  apply (IsFractionRing.injective A E)
  rw [map_zero]
  exact hm.trans hz

end APSCounting893.Main
end Component_21

section Component_22
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma incidence_raw_scaled_image_vanishes {K : Type} [Field K] {n r m : ℕ}
    (F : Fin (m+1) → MvPolynomial (Fin n) K) (hF : F 0 ≠ 0)
    (q : MvPolynomial (Fin (r+1) × Fin (m+1)) K)
    (hq : genericIncidenceChartHom K (fun j =>
      algebraMap _ (FractionRing (MvPolynomial (Fin n) K)) (F j.succ) /
        algebraMap _ (FractionRing (MvPolynomial (Fin n) K)) (F 0)) q = 0)
    (s : K) (x : Fin n → K) (B : Fin (r+1) × Fin (m+1) → K) :
    MvPolynomial.eval (incidenceMatrixAt 0 (fun i => s*MvPolynomial.eval x (F i)) B) q=0 := by
  classical
  let u : Fin (r+1) × Fin (m+1) → MvPolynomial (Fin n) K := fun a =>
    MvPolynomial.C (B a)*MvPolynomial.C s*F 0 -
      (∑ t : Fin (m+1), MvPolynomial.C (B (a.1,t))*MvPolynomial.C s*F t)*(if a.2=0 then 1 else 0)
  have hz := incidence_raw_polynomial_zero F hF q hq s B
  have hh := congrArg (MvPolynomial.eval x) hz
  change MvPolynomial.eval x (MvPolynomial.eval₂Hom MvPolynomial.C u q)=0 at hh
  rw [MvPolynomial.map_eval₂Hom] at hh
  have hcoef : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id K := by ext k; simp
  rw [hcoef] at hh
  have hpoint : (fun a => MvPolynomial.eval x (u a)) = incidenceMatrixAt 0 (fun i => s*MvPolynomial.eval x (F i)) B := by
    funext a
    by_cases ha : a.2=0 <;> simp [u,incidenceMatrixAt,ha,mul_comm,mul_left_comm,mul_assoc]
  rw [hpoint] at hh
  exact hh

lemma incidence_relation_extends_zClosure {K : Type} [Field K] {m r : ℕ}
    (Z : Set (Fin m → K)) (j : Fin m) (q : MvPolynomial (Fin r × Fin m) K)
    (hq : ∀ z ∈ Z, ∀ B : Fin r × Fin m → K, MvPolynomial.eval (incidenceMatrixAt j z B) q=0) :
    ∀ z ∈ RSCapacity.zClosure Z, ∀ B : Fin r × Fin m → K, MvPolynomial.eval (incidenceMatrixAt j z B) q=0 := by
  intro z hz B
  let p := MvPolynomial.aeval (incidencePointPolynomials j B) q
  have hp : p ∈ vanishingIdeal K Z := by
    intro y hy
    change MvPolynomial.aeval y p=0
    simp only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id]
    rw [show p=MvPolynomial.aeval (incidencePointPolynomials j B) q from rfl,eval_incidencePointSubstitution]
    exact hq y hy B
  have hp' : p ∈ vanishingIdeal K (RSCapacity.zClosure Z) := by rwa [vanishingIdeal_zClosure]
  have hh := hp' z hz
  change MvPolynomial.aeval z p=0 at hh
  simp only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id] at hh
  rw [show p=MvPolynomial.aeval (incidencePointPolynomials j B) q from rfl,eval_incidencePointSubstitution] at hh
  exact hh

end APSCounting893.Main
end Component_22

section Component_23
set_option autoImplicit false
set_option maxHeartbeats 500000
open MvPolynomial
namespace APSCounting893.Main

lemma incidenceMatrixAt_permute_columns {K : Type} [Field K] {m r : ℕ}
    (e : Fin (m+1) ≃ Fin (m+1)) (j : Fin (m+1)) (he : e 0=j)
    (z : Fin (m+1) → K) (B : Fin r × Fin (m+1) → K) :
    (fun a : Fin r × Fin (m+1) => incidenceMatrixAt j z B (a.1,e a.2)) =
      incidenceMatrixAt 0 (fun i => z (e i)) (fun a => B (a.1,e a.2)) := by
  classical
  funext a
  have hs : (∑ t : Fin (m+1), z (e t)*B (a.1,e t)) = ∑ t : Fin (m+1), z t*B (a.1,t) :=
    Equiv.sum_comp e (fun t => z t*B (a.1,t))
  have hi : e a.2=j ↔ a.2=0 := by rw [← he]; exact e.apply_eq_iff_eq
  simp only [incidenceMatrixAt,he,hs,hi]

lemma incidence_polynomial_column_permutation {K : Type} [Field K] {n r m : ℕ}
    (e : Fin (m+1) ≃ Fin (m+1)) (j : Fin (m+1)) (he : e 0=j)
    (F : Fin (m+1) → MvPolynomial (Fin n) K)
    (q : MvPolynomial (Fin r × Fin (m+1)) K) (s : K) (x : Fin n → K)
    (B : Fin r × Fin (m+1) → K) :
    MvPolynomial.eval (incidenceMatrixAt j (fun i => s*MvPolynomial.eval x (F i)) B)
      (MvPolynomial.rename (fun a : Fin r × Fin (m+1) => (a.1,e a.2)) q) =
    MvPolynomial.eval (incidenceMatrixAt 0 (fun i => s*MvPolynomial.eval x (F (e i)))
      (fun a => B (a.1,e a.2))) q := by
  rw [MvPolynomial.eval_rename]
  have hh := incidenceMatrixAt_permute_columns e j he (fun i => s*MvPolynomial.eval x (F i)) B
  change MvPolynomial.eval (fun a => incidenceMatrixAt j _ B (a.1,e a.2)) q = _
  rw [hh]

end APSCounting893.Main
end Component_23

section Component_24
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma full_dimension_incidence_raw_certificate {m r : ℕ} (F : PolynomialMap ℂ r (m+1))
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (h0 : ¬ hasAPS F) (j : Fin (m+1)) (hj : F j ≠ 0)
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ i, (F i).totalDegree ≤ d) :
    ∃ q : MvPolynomial (Fin (r+1) × Fin (m+1)) ℂ,
      q ≠ 0 ∧ q.totalDegree ≤ (r+1)*d^r ∧
      ∀ (s : ℂ) (x : Fin r → ℂ) (B : Fin (r+1) × Fin (m+1) → ℂ),
        MvPolynomial.eval (incidenceMatrixAt j (fun i => s*MvPolynomial.eval x (F i)) B) q = 0 := by
  classical
  let A := MvPolynomial (Fin r) ℂ
  let E := FractionRing A
  let w : Fin (m+1) → E := fun i => algebraMap A E (F i)
  let e : Fin (m+1) ≃ Fin (m+1) := Equiv.swap 0 j
  have he0 : e 0=j := by simp [e]
  have hQ : w j ≠ 0 := by simpa only [w,map_zero] using (IsFractionRing.injective A E).ne hj
  obtain ⟨g,hg,hgi⟩ := exists_independent_output_ratios F hdim h0 j hj
  obtain ⟨g',hg'⟩ := independent_ratios_without_pivot w j hQ g hgi
  let v : Fin m → E := fun i => w (e i.succ)/w j
  let P : Fin m → A := fun i => F (e i.succ)
  have hP (i : Fin m) : algebraMap A E (P i)=algebraMap A E (F j)*v i := by
    change w (e i.succ)=w j*(w (e i.succ)/w j)
    exact (mul_div_cancel₀ (w (e i.succ)) hQ).symm
  have hg'' : AlgebraicIndependent ℂ (v ∘ g') := hg'
  obtain ⟨q,hqn,hqd,hqv⟩ := exists_rational_incidence_relation_bounded (F j) hj P v hP g' hg'' d hd (hdeg j) (fun i => hdeg (e i.succ))
  let u : Fin (r+1) × Fin (m+1) → Fin (r+1) × Fin (m+1) := fun a => (a.1,e a.2)
  have hu : Function.Injective u := by
    intro a b h
    have h1 := congrArg (fun a : Fin (r+1) × Fin (m+1) => a.1) h
    have h2 := congrArg (fun a : Fin (r+1) × Fin (m+1) => a.2) h
    exact Prod.ext h1 (e.injective h2)
  refine ⟨MvPolynomial.rename u q,?_,(MvPolynomial.totalDegree_rename_le u q).trans hqd,?_⟩
  · simpa only [map_zero] using (MvPolynomial.rename_injective u hu).ne hqn
  · intro s x B
    rw [incidence_polynomial_column_permutation e j he0 F q s x B]
    apply incidence_raw_scaled_image_vanishes (fun i => F (e i)) (by simpa only [he0] using hj) q
    change genericIncidenceChartHom ℂ (fun i => algebraMap A E (F (e i.succ))/algebraMap A E (F (e 0))) q=0
    rw [he0]
    exact hqv

end APSCounting893.Main
end Component_24

section Component_25

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
end Component_25

section Component_26

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma projectiveRepresentative_rescaling {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ projectiveRepresentative z = a • z := by
  classical
  have hS : (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).Nonempty := by
    by_contra h
    apply hz
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let j := (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).min' hS
  have hj : z j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
  refine ⟨(z j)⁻¹, inv_ne_zero hj, ?_⟩
  rw [projectiveRepresentative, dif_pos hS]
  funext i
  simp only [div_eq_mul_inv, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

lemma projectiveRepresentative_ne_zero {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) : projectiveRepresentative z ≠ 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  exact smul_ne_zero ha hz

lemma homogenizeAll_homogeneous {R : Type} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d) :
    (homogenizeAll d p).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  apply MvPolynomial.isHomogeneous_monomial
  rw [map_add, Finsupp.degree_single, Finsupp.degree_mapDomain, Finsupp.degree_eq_sum]
  have hsum : (∑ i : Fin n, e i) = e.sum (fun _ k => k) :=
    (e.sum_fintype (fun _ k => k) (fun _ => rfl)).symm
  rw [hsum]
  exact Nat.sub_add_cancel ((MvPolynomial.le_totalDegree he).trans hd)

lemma homogeneous_eval₂_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (a : K) (z : Fin n → K) :
    MvPolynomial.eval₂ f (fun i => a * z i) p = a ^ d * MvPolynomial.eval₂ f z p := by
  classical
  conv_lhs => rw [MvPolynomial.eval₂_eq]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  change f (p.coeff e) * e.prod (fun i k => (a * z i) ^ k) =
    a ^ d * (f (p.coeff e) * e.prod (fun i k => z i ^ k))
  rw [finsupp_prod_scaled]
  have hd := hp.degree_eq_sum_deg_support he
  change d = e.sum (fun _ k => k) at hd
  rw [← hd]
  ring

lemma homogeneous_root_projectiveRepresentative {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (z : Fin n → K) (hz : z ≠ 0) (hroot : MvPolynomial.eval₂ f z p = 0) :
    MvPolynomial.eval₂ f (projectiveRepresentative z) p = 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  change MvPolynomial.eval₂ f (fun i => a * z i) p = 0
  rw [homogeneous_eval₂_scaled p d hp f a z, hroot, mul_zero]

end APSCounting893.Main
end Component_26

section Component_27
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def radialPolynomial {K : Type} [Field K] {σ : Type}
    (p : MvPolynomial σ K) (y : σ → K) : Polynomial K :=
  ∑ d ∈ Finset.range (p.totalDegree+1), Polynomial.C (eval y (homogeneousComponent d p)) * Polynomial.X^d

lemma radialPolynomial_eval {K : Type} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (y : Fin n → K) (a : K) :
    (radialPolynomial p y).eval a = eval (fun j => a*y j) p := by
  classical
  rw [radialPolynomial,Polynomial.eval_finset_sum]
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent p]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hh := homogeneous_eval₂_scaled (homogeneousComponent d p) d
    (homogeneousComponent_isHomogeneous d p) (RingHom.id K) a y
  simpa only [MvPolynomial.eval₂_id,mul_comm] using hh.symm

lemma radialPolynomial_coeff {K : Type} [Field K] {σ : Type}
    (p : MvPolynomial σ K) (y : σ → K) (d : ℕ) :
    (radialPolynomial p y).coeff d = eval y (homogeneousComponent d p) := by
  classical
  by_cases hd : d ≤ p.totalDegree
  · simp [radialPolynomial,Polynomial.coeff_C_mul_X_pow,Finset.mem_range,Nat.lt_succ_iff,hd]
  · have hh : homogeneousComponent d p = 0 := homogeneousComponent_eq_zero d p (by omega)
    simp [radialPolynomial,Polynomial.coeff_C_mul_X_pow,Finset.mem_range,Nat.lt_succ_iff,hd,hh]

lemma eval_homogeneousComponent_zero_of_scaled_zero {K : Type} [Field K] [Infinite K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (y : Fin n → K)
    (hp : ∀ a : K, eval (fun j => a*y j) p = 0) (d : ℕ) :
    eval y (homogeneousComponent d p) = 0 := by
  have hz : radialPolynomial p y = 0 := by
    apply Polynomial.funext
    intro a
    rw [radialPolynomial_eval,hp,Polynomial.eval_zero]
  rw [← radialPolynomial_coeff,hz,Polynomial.coeff_zero]

end APSCounting893.Main
end Component_27

section Component_28

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
end Component_28

section Component_29

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
end Component_29

section Component_30

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
end Component_30

section Component_31
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def scaledChart {K : Type} [Field K] {n : ℕ} (Y : Set (Affine K n)) : Set (Affine K (n+1)) :=
  {z | ∃ a : K, ∃ y ∈ Y, z = fun j => a * (Fin.cons 1 y : Fin (n+1) → K) j}

noncomputable def projectiveCone {K : Type} [Field K] {n : ℕ} (Y : Set (Affine K n)) : Set (Affine K (n+1)) :=
  zeroLocus K (chartHomogeneousIdeal Y)

lemma chartHomogeneousIdeal_eq_scaledChart_vanishing {K : Type} [Field K] [Infinite K] {n : ℕ}
    (Y : Set (Affine K n)) : chartHomogeneousIdeal Y = vanishingIdeal K (scaledChart Y) := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨d,hd,hp⟩ z ⟨a,y,hy,rfl⟩
    have hh := homogeneous_eval₂_scaled p d hd (RingHom.id K) a (Fin.cons 1 y)
    simpa only [MvPolynomial.eval₂_id,hp y hy,mul_zero,aeval_def,Algebra.algebraMap_self] using hh
  · intro p hp
    rw [← MvPolynomial.sum_homogeneousComponent p]
    apply Ideal.sum_mem
    intro d hd
    apply Ideal.subset_span
    refine ⟨d,homogeneousComponent_isHomogeneous d p,?_⟩
    intro y hy
    apply eval_homogeneousComponent_zero_of_scaled_zero p (Fin.cons 1 y)
    intro a
    exact hp _ ⟨a,y,hy,rfl⟩

lemma projectiveCone_eq_closure_scaledChart {K : Type} [Field K] [Infinite K] {n : ℕ}
    (Y : Set (Affine K n)) : projectiveCone Y = RSCapacity.zClosure (scaledChart Y) := by
  rw [projectiveCone,chartHomogeneousIdeal_eq_scaledChart_vanishing]
  rfl

lemma projectiveCone_chart_iff {K : Type} [Field K] {n : ℕ}
    (Y : Set (Affine K n)) (hY : RSCapacity.IsAlgSet Y) (y : Affine K n) :
    Fin.cons 1 y ∈ projectiveCone Y ↔ y ∈ Y := by
  constructor
  · intro hy
    rw [isAlgSet_eq_zeroLocus hY]
    intro p hp
    have hm : homogenizeAll p.totalDegree p ∈ chartHomogeneousIdeal Y := by
      apply Ideal.subset_span
      refine ⟨p.totalDegree,homogenizeAll_isHomogeneous p p.totalDegree le_rfl,?_⟩
      intro x hx
      rw [eval_homogenize_chart p p.totalDegree le_rfl]
      exact hp x hx
    have hh := hy _ hm
    simp only [aeval_def,Algebra.algebraMap_self,eval₂_id] at hh ⊢
    rwa [eval_homogenize_chart p p.totalDegree le_rfl] at hh
  · intro hy p hp
    exact chartHomogeneousIdeal_le_vanishing Y hp _ ⟨y,hy,rfl⟩

lemma scaledChart_subset_projectiveCone {K : Type} [Field K] [Infinite K] {n : ℕ}
    (Y : Set (Affine K n)) : scaledChart Y ⊆ projectiveCone Y := by
  rw [projectiveCone_eq_closure_scaledChart]
  exact zeroLocus_vanishingIdeal_le _

lemma projectiveCone_scale {K : Type} [Field K] [Infinite K] {n : ℕ}
    (Y : Set (Affine K n)) (z : Affine K (n+1)) (hz : z ∈ projectiveCone Y) (a : K) :
    (fun j => a*z j) ∈ projectiveCone Y := by
  have hle : chartHomogeneousIdeal Y ≤ RingHom.ker (eval (fun j => a*z j)) := by
    apply Ideal.span_le.mpr
    rintro p ⟨d,hd,hp⟩
    have hm : p ∈ chartHomogeneousIdeal Y := Ideal.subset_span ⟨d,hd,hp⟩
    have hh := homogeneous_eval₂_scaled p d hd (RingHom.id K) a z
    change eval (fun j => a*z j) p = 0
    have hz' : eval z p = 0 := by
      simpa only [aeval_def,Algebra.algebraMap_self,eval₂_id] using hz p hm
    simpa only [MvPolynomial.eval₂_id,hz',mul_zero] using hh
  intro p hp
  exact hle hp

end APSCounting893.Main
end Component_31

section Component_32

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
namespace APSCounting893.Main

lemma zeroLocus_prime_nonempty {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (I : Ideal (Polynomials K n)) (hI : I.IsPrime) : (zeroLocus K I).Nonempty := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI.ne_top
  obtain ⟨x, hMx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hM
  refine ⟨x, ?_⟩
  intro p hp
  have hpM := hIM hp
  rw [hMx] at hpM
  exact hpM x (Set.mem_singleton x)

lemma irreducibleAffine_zeroLocus_prime {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (I : Ideal (Polynomials K n)) (hI : I.IsPrime) : IrreducibleAffine (zeroLocus K I) := by
  letI : I.IsPrime := hI
  apply prime_ideal_irreducibleAffine (zeroLocus_prime_nonempty I hI) (isAlgSet_zeroLocus I)
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]
  exact hI

lemma affineComponent_ideal_minimal {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {C W : Set (Affine K n)} (hC : RSCapacity.IsAlgSet C) (hW : AffineComponent C W) :
    (vanishingIdeal K C).IsMinimalPrime (vanishingIdeal K W) := by
  refine ⟨⟨irreducibleAffine_ideal_prime hW.1, vanishingIdeal_anti_mono hW.2.1⟩, ?_⟩
  intro Q hQ hQW
  letI : Q.IsPrime := hQ.1
  have hWQ : W ⊆ zeroLocus K Q := by
    rw [isAlgSet_eq_zeroLocus hW.1.2.1]
    exact zeroLocus_anti_mono hQW
  have hQC : zeroLocus K Q ⊆ C := by
    rw [isAlgSet_eq_zeroLocus hC]
    exact zeroLocus_anti_mono hQ.2
  have heq := hW.2.2 (zeroLocus K Q) (irreducibleAffine_zeroLocus_prime Q hQ.1) hWQ hQC
  rw [← heq, MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]

lemma affineComponent_of_minimal {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {C : Set (Affine K n)} (hC : RSCapacity.IsAlgSet C)
    (Q : Ideal (Polynomials K n)) (hQ : (vanishingIdeal K C).IsMinimalPrime Q) :
    AffineComponent C (zeroLocus K Q) := by
  letI : Q.IsPrime := hQ.isPrime
  refine ⟨irreducibleAffine_zeroLocus_prime Q hQ.isPrime, ?_, ?_⟩
  · rw [isAlgSet_eq_zeroLocus hC]
    exact zeroLocus_anti_mono hQ.le
  · intro W hW hQW hWC
    have hIWQ : vanishingIdeal K W ≤ Q := by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) Q]
      exact vanishingIdeal_anti_mono hQW
    have hQI : Q ≤ vanishingIdeal K W := hQ.2
      ⟨irreducibleAffine_ideal_prime hW, vanishingIdeal_anti_mono hWC⟩ hIWQ
    rw [isAlgSet_eq_zeroLocus hW.2.1, hIWQ.antisymm hQI]

lemma exists_affineComponent_mem {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {C : Set (Affine K n)} (hC : RSCapacity.IsAlgSet C) {x : Affine K n} (hx : x ∈ C) :
    ∃ W, AffineComponent C W ∧ x ∈ W := by
  have hI : vanishingIdeal K C ≤ vanishingIdeal K ({x} : Set (Affine K n)) :=
    vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hx)
  obtain ⟨Q, hQ, hQx⟩ := Ideal.exists_minimalPrimes_le hI
  exact ⟨zeroLocus K Q, affineComponent_of_minimal hC Q hQ,
    fun p hp => hQx hp x (Set.mem_singleton x)⟩

lemma isAlgSet_inter {K : Type} [Field K] {n : ℕ} {A B : Set (Affine K n)}
    (hA : RSCapacity.IsAlgSet A) (hB : RSCapacity.IsAlgSet B) : RSCapacity.IsAlgSet (A ∩ B) := by
  obtain ⟨S, rfl⟩ := hA
  obtain ⟨T, rfl⟩ := hB
  refine ⟨S ∪ T, ?_⟩
  ext x
  simp only [RSCapacity.zeroSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union]
  aesop

lemma isAlgSet_preimage_evaluate {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) {A : Set (Affine K m)} (hA : RSCapacity.IsAlgSet A) :
    RSCapacity.IsAlgSet (evaluate F ⁻¹' A) := by
  obtain ⟨S, rfl⟩ := hA
  refine ⟨(eval₂Hom MvPolynomial.C F) '' S, ?_⟩
  ext x
  simp only [Set.mem_preimage, RSCapacity.zeroSet, Set.mem_setOf_eq, Set.forall_mem_image, evaluation_substitution]

lemma isAlgSet_affineLine {K : Type} [Field K] {d : ℕ}
    (base direction : Affine K d) (hdir : direction ≠ 0) : RSCapacity.IsAlgSet (affineLine base direction) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, direction i ≠ 0 := by
    by_contra h
    push Not at h
    exact hdir (funext h)
  let p : Fin d → Polynomials K d := fun j =>
    MvPolynomial.C (direction i) * (MvPolynomial.X j - MvPolynomial.C (base j)) -
      MvPolynomial.C (direction j) * (MvPolynomial.X i - MvPolynomial.C (base i))
  refine ⟨Set.range p, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩ q ⟨j, rfl⟩
    simp only [p, map_sub, map_mul, eval_C, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro x hx
    have hj (j : Fin d) : direction i * (x j - base j) - direction j * (x i - base i) = 0 := by
      simpa [p] using hx (p j) (Set.mem_range_self j)
    refine ⟨(x i - base i) / direction i, ?_⟩
    funext j
    have he : x j - base j = direction j * (x i - base i) / direction i :=
      (eq_div_iff hi).mpr (by simpa only [mul_comm] using sub_eq_zero.mp (hj j))
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -he

lemma irreducibleAffine_affineLine {K : Type} [Field K] [Infinite K] {d : ℕ}
    (base direction : Affine K d) (hdir : direction ≠ 0) : IrreducibleAffine (affineLine base direction) := by
  let F : PolynomialMap K 1 d := fun j => MvPolynomial.C (base j) +
    MvPolynomial.C (direction j) * MvPolynomial.X 0
  have hrange : Set.range (evaluate F) = affineLine base direction := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x 0, ?_⟩
      funext j
      simp [evaluate, F, mul_comm]
    · rintro ⟨t, rfl⟩
      refine ⟨fun _ => t, ?_⟩
      funext j
      simp [evaluate, F, mul_comm]
  have hcl : imageClosure F = affineLine base direction := by
    unfold imageClosure RSCapacity.zClosure
    rw [hrange, ← isAlgSet_eq_zeroLocus (isAlgSet_affineLine base direction hdir)]
  exact hcl ▸ irreducibleAffine_imageClosure F

lemma finiteMorphism_restrict {K : Type} [Field K] {n m : ℕ}
    {X W : Set (Affine K n)} (F : PolynomialMap K n m) (hfinite : FiniteMorphism X F)
    (hWX : W ⊆ X) : FiniteMorphism W F := by
  obtain ⟨s, g, hg⟩ := hfinite
  refine ⟨s, g, ?_⟩
  intro p
  obtain ⟨c, hc⟩ := hg p
  exact ⟨c, fun x hx => hc x (hWX hx)⟩

lemma finiteMorphism_image {K : Type} [Field K] [IsAlgClosed K] {n m : ℕ}
    (W : Set (Affine K n)) (hclosed : RSCapacity.IsAlgSet W)
    (F : PolynomialMap K n m) (hfinite : FiniteMorphism W F) :
    evaluate F '' W = zeroLocus K (RingHom.ker (coordinatePullback W F)) := by
  classical
  letI : Algebra (Polynomials K m) (CoordinateRing W) := coordinatePullbackAlgebra W F
  letI : Module.Finite (Polynomials K m) (CoordinateRing W) := finiteMorphism_module_finite W F hfinite
  have halg : algebraMap (Polynomials K m) (CoordinateRing W) = coordinatePullback W F := rfl
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩ p hp
    have hpI : eval₂Hom MvPolynomial.C F p ∈ vanishingIdeal K W :=
      Ideal.Quotient.eq_zero_iff_mem.mp hp
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using hpI x hx
  · intro y hy
    let P := vanishingIdeal K ({y} : Set (Affine K m))
    have hker : RingHom.ker (algebraMap (Polynomials K m) (CoordinateRing W)) ≤ P := by
      intro p hp
      rw [halg] at hp
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff y p).mpr (hy p hp)
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
      (S := CoordinateRing W) P hker
    letI : Q.IsMaximal := hQmax
    let N : Ideal (Polynomials K n) := Q.comap (Ideal.Quotient.mk (vanishingIdeal K W))
    have hNmax : N.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hNx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hNmax
    have hxW : x ∈ W := by
      rw [isAlgSet_eq_zeroLocus hclosed]
      intro p hp
      have hpN : p ∈ N := by
        change Ideal.Quotient.mk (vanishingIdeal K W) p ∈ Q
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
        exact Q.zero_mem
      rw [hNx] at hpN
      exact hpN x (Set.mem_singleton x)
    refine ⟨x, hxW, ?_⟩
    funext j
    have hpP : MvPolynomial.X j - MvPolynomial.C (y j) ∈ P := by
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    rw [← hQ] at hpP
    have hpN : eval₂Hom MvPolynomial.C F (MvPolynomial.X j - MvPolynomial.C (y j)) ∈ N := hpP
    rw [hNx] at hpN
    have hpval := hpN x (Set.mem_singleton x)
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution,
      map_sub, eval_X, eval_C, sub_eq_zero] at hpval
    exact hpval

lemma finite_dominant_component_surjective {K : Type} [Field K] [IsAlgClosed K] {n m : ℕ}
    (X : Set (Affine K n)) (hX : IrreducibleAffine X)
    (F : PolynomialMap K n m) (hfinite : FiniteMorphism X F)
    (hdom : RSCapacity.zClosure (evaluate F '' X) = Set.univ)
    (L : Set (Affine K m)) (hL : IrreducibleAffine L)
    (W : Set (Affine K n)) (hW : AffineComponent {x | x ∈ X ∧ evaluate F x ∈ L} W) :
    evaluate F '' W = L := by
  classical
  letI : (vanishingIdeal K X).IsPrime := irreducibleAffine_ideal_prime hX
  letI : (vanishingIdeal K W).IsPrime := irreducibleAffine_ideal_prime hW.1
  letI : Algebra (Polynomials K m) (CoordinateRing X) := coordinatePullbackAlgebra X F
  letI : Module.Finite (Polynomials K m) (CoordinateRing X) := finiteMorphism_module_finite X F hfinite
  have halg : algebraMap (Polynomials K m) (CoordinateRing X) = coordinatePullback X F := rfl
  letI : FaithfulSMul (Polynomials K m) (CoordinateRing X) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (coordinatePullback_injective_of_dominant X F hdom)
  have hWX : W ⊆ X := fun x hx => (hW.2.1 hx).1
  let psi : CoordinateRing X →+* CoordinateRing W :=
    Ideal.Quotient.factor (vanishingIdeal_anti_mono hWX)
  let Q : Ideal (CoordinateRing X) := RingHom.ker psi
  letI : Q.IsPrime := RingHom.ker_isPrime psi
  have hraw : Q.comap (Ideal.Quotient.mk (vanishingIdeal K X)) = vanishingIdeal K W := by
    ext p
    simp [Q, psi, Ideal.mem_comap, RingHom.mem_ker, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem]
  let P : Ideal (Polynomials K m) := vanishingIdeal K L
  letI : P.IsPrime := irreducibleAffine_ideal_prime hL
  have hP : P ≤ Q.under (Polynomials K m) := by
    intro p hp
    change (coordinatePullback X F) p ∈ Q
    have hs : eval₂Hom MvPolynomial.C F p ∈ vanishingIdeal K W := by
      intro x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using
        hp (evaluate F x) (hW.2.1 hx).2
    rw [← hraw] at hs
    exact hs
  let q : Ideal (Polynomials K m) := Q.under (Polynomials K m)
  letI : Q.LiesOver q := ⟨rfl⟩
  obtain ⟨Q0, hQ0Q, hQ0prime, hQ0over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := P) (q := q) Q hP
  letI : Q0.IsPrime := hQ0prime
  letI : Q0.LiesOver P := hQ0over
  have hQ0base : Q0.comap (coordinatePullback X F) = P := (Q0.over_def P).symm
  let J : Ideal (Polynomials K n) := Q0.comap (Ideal.Quotient.mk (vanishingIdeal K X))
  letI : J.IsPrime := Ideal.comap_isPrime _ Q0
  have hJW : J ≤ vanishingIdeal K W := (Ideal.comap_mono hQ0Q).trans_eq hraw
  have hWJ : W ⊆ zeroLocus K J := by
    rw [isAlgSet_eq_zeroLocus hW.1.2.1]
    exact zeroLocus_anti_mono hJW
  have hJC : zeroLocus K J ⊆ {x | x ∈ X ∧ evaluate F x ∈ L} := by
    intro x hx
    constructor
    · rw [isAlgSet_eq_zeroLocus hX.2.1]
      intro p hp
      have hpJ : p ∈ J := by
        change Ideal.Quotient.mk (vanishingIdeal K X) p ∈ Q0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
        exact Q0.zero_mem
      exact hx p hpJ
    · rw [isAlgSet_eq_zeroLocus hL.2.1]
      intro p hp
      have hp0 : (coordinatePullback X F) p ∈ Q0 := by
        change p ∈ Q0.comap (coordinatePullback X F)
        rw [hQ0base]
        exact hp
      have hpJ : eval₂Hom MvPolynomial.C F p ∈ J := hp0
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using hx _ hpJ
  have hWeq := hW.2.2 (zeroLocus K J) (irreducibleAffine_zeroLocus_prime J inferInstance) hWJ hJC
  have hIW : vanishingIdeal K W = J := by
    rw [← hWeq, MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]
  have hker : RingHom.ker (coordinatePullback W F) = P := by
    ext p
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk (vanishingIdeal K W) (eval₂Hom MvPolynomial.C F p) = 0 ↔ p ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem, hIW]
    change p ∈ Q0.comap (coordinatePullback X F) ↔ p ∈ P
    rw [hQ0base]
  rw [finiteMorphism_image W hW.1.2.1 F (finiteMorphism_restrict F hfinite hWX), hker]
  exact (isAlgSet_eq_zeroLocus hL.2.1).symm

end APSCounting893.Main

end Component_32

section Component_33

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
namespace APSCounting893.Main

lemma top_homogeneousComponent_ne_zero {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K n) (hp : p ≠ 0) : homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨e, he, hmax⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hp)
    (fun e => e.sum (fun _ a => a))
  have hd : e.degree = p.totalDegree := by simpa [Finsupp.degree, Finsupp.sum, totalDegree] using hmax.symm
  intro h
  have hc := congrArg (MvPolynomial.coeff e) h
  rw [coeff_homogeneousComponent, if_pos hd, coeff_zero] at hc
  exact (mem_support_iff.mp he) hc

lemma homogeneous_eval_scale {K : Type} [Field K] {n D : ℕ}
    (p : Polynomials K n) (hp : p.IsHomogeneous D) (a : K) (x : Affine K n) :
    eval (fun i => a * x i) p = a ^ D * eval x p := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hd : ∑ i : Fin n, e i = D := by
    have hs : (∑ i ∈ e.support, e i) = ∑ i : Fin n, e i := by
      exact e.sum_fintype (fun _ b => b) (fun _ => rfl)
    exact hs.symm.trans (hp.degree_eq_sum_deg_support he).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

noncomputable def normalizationParameter {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K (n + 1)) : Polynomials K n :=
  eval₂Hom MvPolynomial.C (Fin.lastCases 1 MvPolynomial.X) (homogeneousComponent p.totalDegree p)

lemma normalizationParameter_ne_zero {K : Type} [Field K] [Infinite K] {n : ℕ}
    (p : Polynomials K (n + 1)) (hp : p ≠ 0) : normalizationParameter p ≠ 0 := by
  classical
  let H := homogeneousComponent p.totalDegree p
  have hH : H ≠ 0 := top_homogeneousComponent_ne_zero p hp
  have hprod : H * MvPolynomial.X (Fin.last n) ≠ 0 := mul_ne_zero hH (X_ne_zero _)
  obtain ⟨w, hw⟩ : ∃ w : Affine K (n + 1), eval w (H * MvPolynomial.X (Fin.last n)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hprod
    apply MvPolynomial.funext
    intro w
    simpa only [map_zero] using h w
  rw [map_mul, eval_X] at hw
  have hwH := left_ne_zero_of_mul hw
  have hwl := right_ne_zero_of_mul hw
  let c : Affine K n := fun i => w i.castSucc / w (Fin.last n)
  have hv : evaluate (Fin.lastCases (1 : Polynomials K n) MvPolynomial.X) c =
      fun i => (w (Fin.last n))⁻¹ * w i := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [evaluate, hwl]
    · simp [evaluate, c, div_eq_mul_inv, mul_comm]
  have hval : eval c (normalizationParameter p) ≠ 0 := by
    unfold normalizationParameter
    rw [evaluation_substitution, hv, homogeneous_eval_scale _ (homogeneousComponent_isHomogeneous _ _)]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hwl)) hwH
  intro h
  exact hval (by rw [h, map_zero])

lemma coeff_prod_sum_of_natDegree_le {A ι : Type} [CommRing A]
    (s : Finset ι) (f : ι → Polynomial A) (d : ι → ℕ)
    (hd : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (hd i (Finset.mem_insert_self _ _))]
    · rw [ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))]
    · exact (Polynomial.natDegree_prod_le s f).trans (Finset.sum_le_sum (fun j hj => hd j (Finset.mem_insert_of_mem hj)))

lemma natDegree_eval₂_of_linear {K A : Type} [CommRing K] [CommRing A] {N : ℕ}
    (f : K →+* A) (g : Fin N → Polynomial A) (hg : ∀ i, (g i).natDegree ≤ 1)
    (p : Polynomials K N) :
    (eval₂Hom (Polynomial.C.comp f) g p).natDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  rw [eval₂Hom_monomial, Finsupp.prod_pow]
  apply Polynomial.natDegree_mul_le.trans
  simp only [RingHom.comp_apply, Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hg i))))
  have he' : e.degree ≤ p.totalDegree := by
    simpa [Finsupp.degree_apply, Finsupp.sum] using (le_totalDegree he)
  simpa only [mul_one, ← Finsupp.degree_eq_sum] using he' 

lemma coeff_eval₂_monomial_of_linear {K A : Type} [CommRing K] [CommRing A] {N D : ℕ}
    (f : K →+* A) (g : Fin N → Polynomial A) (hg : ∀ i, (g i).natDegree ≤ 1)
    (e : Fin N →₀ ℕ) (c : K) (he : e.degree ≤ D) :
    (eval₂Hom (Polynomial.C.comp f) g (MvPolynomial.monomial e c)).coeff D =
      if e.degree = D then f c * ∏ i : Fin N, (g i).coeff 1 ^ e i else 0 := by
  classical
  rw [eval₂Hom_monomial, Finsupp.prod_pow]
  simp only [RingHom.comp_apply, Polynomial.coeff_C_mul]
  have hbound : (∏ i : Fin N, g i ^ e i).natDegree ≤ e.degree := by
    apply (Polynomial.natDegree_prod_le _ _).trans
    apply le_trans (Finset.sum_le_sum (fun i _ =>
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hg i))))
    simp [Finsupp.degree_eq_sum]
  split_ifs with heq
  · have hcoeff := coeff_prod_sum_of_natDegree_le Finset.univ (fun i : Fin N => g i ^ e i)
      (fun i => e i) (fun i _ => Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (e i) (hg i)))
    have hpows (i : Fin N) : (g i ^ e i).coeff (e i) = (g i).coeff 1 ^ e i := by
      simpa using (Polynomial.coeff_pow_of_natDegree_le (m := e i) (hg i))
    rw [← heq, Finsupp.degree_eq_sum, hcoeff]
    simp only [hpows]
  · have hlt : (∏ i : Fin N, g i ^ e i).natDegree < D := hbound.trans_lt (lt_of_le_of_ne he heq)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]

lemma coeff_eval₂_linear_top {K A : Type} [CommRing K] [CommRing A] {N D : ℕ}
    (f : K →+* A) (g : Fin N → Polynomial A) (hg : ∀ i, (g i).natDegree ≤ 1)
    (p : Polynomials K N) (hp : p.totalDegree ≤ D) :
    (eval₂Hom (Polynomial.C.comp f) g p).coeff D =
      eval₂Hom f (fun i => (g i).coeff 1) (homogeneousComponent D p) := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, homogeneousComponent_apply, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  have hd0 : e.degree ≤ p.totalDegree := by
    simpa [Finsupp.degree_apply, Finsupp.sum] using le_totalDegree he
  have hd : e.degree ≤ D := hd0.trans hp
  rw [coeff_eval₂_monomial_of_linear f g hg e _ hd]
  split_ifs
  · rw [eval₂Hom_monomial, Finsupp.prod_pow]
  · rfl

noncomputable def normalizationLinearForms {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) : Fin (n + 1) → Polynomial (Polynomials K n) :=
  Fin.lastCases Polynomial.X (fun i => Polynomial.C (MvPolynomial.X i) +
    Polynomial.C (MvPolynomial.C (c i)) * Polynomial.X)

lemma normalizationLinearForms_degree {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) (i : Fin (n + 1)) : (normalizationLinearForms c i).natDegree ≤ 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [normalizationLinearForms]
  · simp only [normalizationLinearForms, Fin.lastCases_castSucc]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simp)

noncomputable def normalizationShear {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) (p : Polynomials K (n + 1)) : Polynomial (Polynomials K n) :=
  eval₂Hom (Polynomial.C.comp MvPolynomial.C) (normalizationLinearForms c) p

lemma normalizationShear_top_coeff {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) (p : Polynomials K (n + 1)) :
    (normalizationShear c p).coeff p.totalDegree = MvPolynomial.C (eval c (normalizationParameter p)) := by
  rw [normalizationShear, coeff_eval₂_linear_top MvPolynomial.C _ (normalizationLinearForms_degree c) _ le_rfl]
  have heq : eval₂Hom MvPolynomial.C (fun i => (normalizationLinearForms c i).coeff 1) =
      MvPolynomial.C.comp (eval (Fin.lastCases 1 c)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [normalizationLinearForms]
      · simp [normalizationLinearForms]
  rw [heq, RingHom.comp_apply]
  have hv : evaluate (Fin.lastCases (1 : Polynomials K n) MvPolynomial.X) c = Fin.lastCases 1 c := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [evaluate]
  rw [normalizationParameter, evaluation_substitution, hv]

lemma normalizationShear_unit_leadingCoeff {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) (p : Polynomials K (n + 1))
    (hc : eval c (normalizationParameter p) ≠ 0) :
    IsUnit (normalizationShear c p).leadingCoeff := by
  have hcoef : (normalizationShear c p).coeff p.totalDegree ≠ 0 := by
    rw [normalizationShear_top_coeff]
    simpa only [map_zero] using (MvPolynomial.C_injective (Fin n) K).ne hc
  have hdegree : (normalizationShear c p).natDegree = p.totalDegree :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_eval₂_of_linear MvPolynomial.C _ (normalizationLinearForms_degree c) p) hcoef
  rw [Polynomial.leadingCoeff, hdegree, normalizationShear_top_coeff]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

lemma normalizationShear_eval {n : ℕ} (Y : Set (Affine ℂ (n + 1)))
    (c : Affine ℂ n) (p : Polynomials ℂ (n + 1)) :
    (normalizationShear c p).eval₂ (coordinatePullback Y (normalizationPolynomials c))
      (coordinate Y (Fin.last n)) = Ideal.Quotient.mk (vanishingIdeal ℂ Y) p := by
  let phi := Polynomial.eval₂RingHom (coordinatePullback Y (normalizationPolynomials c))
    (coordinate Y (Fin.last n))
  have heq : phi.comp (eval₂Hom (Polynomial.C.comp MvPolynomial.C) (normalizationLinearForms c)) =
      Ideal.Quotient.mk (vanishingIdeal ℂ Y) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [phi, coordinatePullback]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [phi, normalizationLinearForms, coordinate]
      · simp [phi, normalizationLinearForms, coordinatePullback, normalizationPolynomials, coordinate]
  exact RingHom.congr_fun heq p

lemma normalization_last_integral {n : ℕ} (Y : Set (Affine ℂ (n + 1)))
    (c : Affine ℂ n) (p : Polynomials ℂ (n + 1)) (hp : p ∈ vanishingIdeal ℂ Y)
    (hc : eval c (normalizationParameter p) ≠ 0) :
    letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
    IsIntegral (Polynomials ℂ n) (coordinate Y (Fin.last n)) := by
  classical
  letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
  let q := normalizationShear c p
  have hu : IsUnit q.leadingCoeff := normalizationShear_unit_leadingCoeff c p hc
  have hzero : q.eval₂ (coordinatePullback Y (normalizationPolynomials c))
      (coordinate Y (Fin.last n)) = 0 :=
    (normalizationShear_eval Y c p).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  refine ⟨hu.unit⁻¹.val • q, Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hu, ?_⟩
  change Polynomial.eval₂ (coordinatePullback Y (normalizationPolynomials c))
    (coordinate Y (Fin.last n)) (hu.unit⁻¹.val • q) = 0
  rw [Polynomial.eval₂_smul, hzero, mul_zero]

lemma normalization_adjoin_last_eq_top {n : ℕ} (Y : Set (Affine ℂ (n + 1))) (c : Affine ℂ n) :
    letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
    Algebra.adjoin (Polynomials ℂ n) ({coordinate Y (Fin.last n)} : Set (CoordinateRing Y)) = ⊤ := by
  classical
  letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
  have halg : algebraMap (Polynomials ℂ n) (CoordinateRing Y) = coordinatePullback Y (normalizationPolynomials c) := rfl
  let S := Algebra.adjoin (Polynomials ℂ n) ({coordinate Y (Fin.last n)} : Set (CoordinateRing Y))
  have hz : coordinate Y (Fin.last n) ∈ S := Algebra.subset_adjoin (Set.mem_singleton _)
  have hvar (i : Fin (n + 1)) : coordinate Y i ∈ S := by
    refine Fin.lastCases hz (fun j => ?_) i
    have h := S.add_mem (S.algebraMap_mem (MvPolynomial.X j))
      (S.mul_mem (S.algebraMap_mem (MvPolynomial.C (c j))) hz)
    simpa [halg, coordinatePullback, coordinate, normalizationPolynomials] using h
  apply top_unique
  intro b hb
  clear hb
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [halg, coordinatePullback] using S.algebraMap_mem (MvPolynomial.C a)
  | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
  | mul_X p i hp => simpa only [map_mul, coordinate, S] using S.mul_mem hp (hvar i)

lemma normalization_module_finite {n : ℕ} (Y : Set (Affine ℂ (n + 1)))
    (c : Affine ℂ n) (p : Polynomials ℂ (n + 1)) (hp : p ∈ vanishingIdeal ℂ Y)
    (hc : eval c (normalizationParameter p) ≠ 0) :
    letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
    Module.Finite (Polynomials ℂ n) (CoordinateRing Y) := by
  classical
  letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
  let S := Algebra.adjoin (Polynomials ℂ n) ({coordinate Y (Fin.last n)} : Set (CoordinateRing Y))
  letI : Module.Finite (Polynomials ℂ n) S :=
    Algebra.finite_adjoin_simple_of_isIntegral (normalization_last_integral Y c p hp hc)
  apply Module.Finite.of_surjective S.val.toLinearMap
  intro b
  have hS : S = ⊤ := normalization_adjoin_last_eq_top Y c
  have hb : b ∈ S := by rw [hS]; trivial
  exact ⟨⟨b, hb⟩, rfl⟩

lemma module_finite_finiteMorphism {K : Type} [Field K] {n m : ℕ}
    (Y : Set (Affine K n)) (F : PolynomialMap K n m) :
    letI : Algebra (Polynomials K m) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
    Module.Finite (Polynomials K m) (CoordinateRing Y) → FiniteMorphism Y F := by
  classical
  letI : Algebra (Polynomials K m) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
  intro hfinite
  letI := hfinite
  have halg : algebraMap (Polynomials K m) (CoordinateRing Y) = coordinatePullback Y F := rfl
  obtain ⟨s, g, hgen⟩ := Module.Finite.exists_fin (R := Polynomials K m) (M := CoordinateRing Y)
  choose representatives hrep using fun i => Ideal.Quotient.mk_surjective (g i)
  refine ⟨s, representatives, ?_⟩
  intro p
  have hp : Ideal.Quotient.mk (vanishingIdeal K Y) p ∈ Submodule.span (Polynomials K m) (Set.range g) := by
    rw [hgen]; trivial
  obtain ⟨coefficients, hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun (Polynomials K m)).mp hp
  refine ⟨coefficients, ?_⟩
  have hz : p - ∑ i : Fin s, eval₂Hom MvPolynomial.C F (coefficients i) * representatives i ∈
      vanishingIdeal K Y := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_sum]
    apply sub_eq_zero.mpr
    have h := hcoeff.symm
    simpa only [Algebra.smul_def, halg, coordinatePullback, RingHom.comp_apply, map_mul, hrep] using h
  intro x hx
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, map_sum, map_mul,
    evaluation_substitution, sub_eq_zero] using hz x hx

lemma coordinatePullback_injective_of_finite_dimension {K : Type} [Field K] {a n : ℕ}
    (Y : Set (Affine K a)) (F : PolynomialMap K a n)
    (hdim : RSCapacity.algDim Y = ((n : ℕ∞) : WithBot ℕ∞))
    (hfinite : letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
      Module.Finite (Polynomials K n) (CoordinateRing Y)) :
    Function.Injective (coordinatePullback Y F) := by
  classical
  letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
  letI : Module.Finite (Polynomials K n) (CoordinateRing Y) := hfinite
  let f : Polynomials K n →+* CoordinateRing Y := algebraMap (Polynomials K n) (CoordinateRing Y)
  have hf : f.IsIntegral := Algebra.IsIntegral.isIntegral
  have hdimBound := ringKrullDim_le_of_ringHom_isIntegral f.kerLift hf.kerLift
  have hdimBase : ringKrullDim (Polynomials K n) = ((n : ℕ∞) : WithBot ℕ∞) := by simp [Polynomials]
  change ringKrullDim (CoordinateRing Y) = ((n : ℕ∞) : WithBot ℕ∞) at hdim
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨r, hr, hrne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hquot := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (RingHom.ker f))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hrne)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hbad := (add_le_add hdimBound le_rfl).trans hquot
  rw [hdim, hdimBase] at hbad
  have hn : n + 1 ≤ n := by exact_mod_cast hbad
  omega

lemma vanishingIdeal_ne_bot_of_codimension_one {K : Type} [Field K] {n : ℕ}
    (Y : Set (Affine K (n + 1)))
    (hdim : RSCapacity.algDim Y = ((n : ℕ∞) : WithBot ℕ∞)) : vanishingIdeal K Y ≠ ⊥ := by
  intro h
  change ringKrullDim (Polynomials K (n + 1) ⧸ vanishingIdeal K Y) = ((n : ℕ∞) : WithBot ℕ∞) at hdim
  rw [h, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)] at hdim
  have hn : n + 1 = n := by exact_mod_cast (by simpa [Polynomials] using hdim :
    (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞))
  omega

lemma module_finite_coordinatesIntegral {K : Type} [Field K] {a n : ℕ}
    (Y : Set (Affine K a)) (hY : IrreducibleAffine Y) (F : PolynomialMap K a n)
    (hfinite : letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
      Module.Finite (Polynomials K n) (CoordinateRing Y)) : CoordinatesIntegral Y F := by
  classical
  letI : (vanishingIdeal K Y).IsPrime := irreducibleAffine_ideal_prime hY
  letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
  letI : Module.Finite (Polynomials K n) (CoordinateRing Y) := hfinite
  have halg : algebraMap (Polynomials K n) (CoordinateRing Y) = coordinatePullback Y F := rfl
  intro j
  obtain ⟨p, hp, hroot⟩ := Algebra.IsIntegral.isIntegral (R := Polynomials K n) (coordinate Y j)
  have hd : 0 < p.natDegree := by
    by_contra h
    have hp1 := Polynomial.eq_one_of_monic_natDegree_zero hp (Nat.eq_zero_of_not_pos h)
    simpa [hp1] using hroot
  refine ⟨p.natDegree, hd, fun i => p.coeff i.val, ?_⟩
  intro x hx
  let ex : CoordinateRing Y →+* K := Ideal.Quotient.lift (vanishingIdeal K Y)
    (MvPolynomial.eval x) (fun q hq => by
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hq x hx)
  have hcomp : ex.comp (algebraMap (Polynomials K n) (CoordinateRing Y)) = eval (evaluate F x) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [ex, halg, coordinatePullback]
    · intro i; simp [ex, halg, coordinatePullback, evaluate]
  have hz : ex (coordinate Y j) = x j := by simp [ex, coordinate]
  have hpoint : Polynomial.eval₂ (eval (evaluate F x)) (x j) p = 0 := by
    have h := congrArg ex hroot
    rw [Polynomial.hom_eval₂, hcomp, hz, map_zero] at h
    exact h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hpoint
  rw [← Fin.sum_univ_eq_sum_range] at hpoint
  simpa only [add_comm] using hpoint

end APSCounting893.Main

open APSCounting893.Main

theorem normalization_internal_solution (n : ℕ) (hn : 0 < n) (Y : Set (Affine ℂ (n + 1)))
    (hirr : IrreducibleAffine Y)
    (hdim : RSCapacity.algDim Y = ((n : ℕ∞) : WithBot ℕ∞)) :
    ∃ O : Set (Affine ℂ n), O.Nonempty ∧ RelativeOpen Set.univ O ∧
      ∀ c ∈ O, IsNormalization Y c := by
  classical
  obtain ⟨p, hp, hpne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (vanishingIdeal_ne_bot_of_codimension_one Y hdim)
  let P := normalizationParameter p
  have hP : P ≠ 0 := normalizationParameter_ne_zero p hpne
  let O : Set (Affine ℂ n) := {c | eval c P ≠ 0}
  have hO : O.Nonempty := by
    by_contra h
    apply hP
    apply MvPolynomial.funext
    intro c
    have hc : eval c P = 0 := by
      by_contra hc
      exact h ⟨c, hc⟩
    simpa only [map_zero] using hc
  refine ⟨O, hO, ?_, ?_⟩
  · refine ⟨Set.subset_univ _, ⟨{P}, ?_⟩⟩
    ext c
    simp [O, RSCapacity.zeroSet]
  · intro c hc
    have hc' : eval c (normalizationParameter p) ≠ 0 := hc
    have hmodule := normalization_module_finite Y c p hp hc'
    have hfin := module_finite_finiteMorphism Y (normalizationPolynomials c) hmodule
    have hinj := coordinatePullback_injective_of_finite_dimension Y (normalizationPolynomials c) hdim hmodule
    have hsurj : normalization c '' Y = Set.univ := by
      change evaluate (normalizationPolynomials c) '' Y = Set.univ
      rw [finiteMorphism_image Y hirr.2.1 _ hfin,
        (RingHom.injective_iff_ker_eq_bot _).mp hinj, zeroLocus_bot]
      rfl
    refine ⟨hfin, hsurj, ?_, module_finite_coordinatesIntegral Y hirr (normalizationPolynomials c) hmodule⟩
    intro f hf y hy
    obtain ⟨x, hx, hxy⟩ := (Set.ext_iff.mp hsurj y).mpr (Set.mem_univ y)
    exact hxy ▸ hf x hx
end Component_33

section Component_34
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def composePolynomialMap {K : Type} [Field K] {n m r : ℕ}
    (F : PolynomialMap K n m) (G : PolynomialMap K m r) : PolynomialMap K n r :=
  fun j => MvPolynomial.eval₂Hom MvPolynomial.C F (G j)

lemma evaluate_composePolynomialMap {K : Type} [Field K] {n m r : ℕ}
    (F : PolynomialMap K n m) (G : PolynomialMap K m r) (x : Affine K n) :
    evaluate (composePolynomialMap F G) x = evaluate G (evaluate F x) := by
  funext j
  exact evaluation_substitution F (G j) x

lemma finiteMorphism_compose {K : Type} [Field K] {n m r : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) (G : PolynomialMap K m r)
    (hF : FiniteMorphism X F) (hG : FiniteMorphism (evaluate F '' X) G) :
    FiniteMorphism X (composePolynomialMap F G) := by
  classical
  obtain ⟨s,a,ha⟩ := hF
  obtain ⟨t,b,hb⟩ := hG
  let E : Fin (s*t) ≃ Fin s × Fin t := finProdFinEquiv.symm
  refine ⟨s*t,fun z => a (E z).1 * MvPolynomial.eval₂Hom MvPolynomial.C F (b (E z).2),?_⟩
  intro f
  obtain ⟨A,hA⟩ := ha f
  have hB (i : Fin s) := hb (A i)
  choose B hB using hB
  refine ⟨fun z => B (E z).1 (E z).2,?_⟩
  intro x hx
  have hFx : evaluate F x ∈ evaluate F '' X := ⟨x,hx,rfl⟩
  rw [hA x hx]
  calc
    (∑ i, eval (evaluate F x) (A i) * eval x (a i)) =
        ∑ i, (∑ j, eval (evaluate G (evaluate F x)) (B i j) * eval (evaluate F x) (b j)) * eval x (a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hB i _ hFx]
    _ = ∑ i : Fin s, ∑ j : Fin t,
        eval (evaluate (composePolynomialMap F G) x) (B i j) *
          eval x (a i * eval₂Hom MvPolynomial.C F (b j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [evaluate_composePolynomialMap,map_mul,evaluation_substitution]
      ring
    _ = ∑ z : Fin (s*t), eval (evaluate (composePolynomialMap F G) x) (B (E z).1 (E z).2) *
          eval x (a (E z).1 * eval₂Hom MvPolynomial.C F (b (E z).2)) := by
      have he := Equiv.sum_comp E (fun z : Fin s × Fin t =>
        eval (evaluate (composePolynomialMap F G) x) (B z.1 z.2) *
          eval x (a z.1 * eval₂Hom MvPolynomial.C F (b z.2)))
      simpa only [Fintype.sum_prod_type] using he.symm

end APSCounting893.Main
end Component_34

section Component_35
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def conePolynomialMap {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) : PolynomialMap K (n+1) (m+1) :=
  Fin.cons (MvPolynomial.X 0) (fun i => MvPolynomial.X 0 * MvPolynomial.rename Fin.succ (F i))

lemma conePolynomialMap_eval {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (a : K) (x : Affine K n) :
    evaluate (conePolynomialMap F) (Fin.cons a x) = fun j => a * (Fin.cons 1 (evaluate F x) : Fin (m+1) → K) j := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [evaluate,conePolynomialMap]
  · simp [evaluate,conePolynomialMap,MvPolynomial.eval_rename,Function.comp_def]

lemma scaledChart_range_eq_conePolynomialMap_range {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) : scaledChart (Set.range (evaluate F)) = Set.range (evaluate (conePolynomialMap F)) := by
  ext z
  constructor
  · rintro ⟨a,y,⟨x,rfl⟩,rfl⟩
    exact ⟨Fin.cons a x,conePolynomialMap_eval F a x⟩
  · rintro ⟨x,rfl⟩
    refine ⟨x 0,evaluate F (fun i => x i.succ),Set.mem_range_self _,?_⟩
    have hx : Fin.cons (x 0) (fun i => x i.succ) = x := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [← conePolynomialMap_eval,hx]

lemma scaledChart_closure_vanishing {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) :
    vanishingIdeal K (scaledChart (imageClosure F)) = vanishingIdeal K (scaledChart (Set.range (evaluate F))) := by
  apply le_antisymm
  · apply vanishingIdeal_anti_mono
    rintro z ⟨a,y,hy,rfl⟩
    exact ⟨a,y,zeroLocus_vanishingIdeal_le _ hy,rfl⟩
  · intro p hp z
    rintro ⟨a,y,hy,rfl⟩
    let P : PolynomialMap K m (m+1) := Fin.cons (MvPolynomial.C a)
      (fun j => MvPolynomial.C a * MvPolynomial.X j)
    have hP (y : Affine K m) : evaluate P y = fun j => a*(Fin.cons 1 y : Fin (m+1) → K) j := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [P,evaluate]
    have hvan : MvPolynomial.aeval P p ∈ vanishingIdeal K (Set.range (evaluate F)) := by
      intro y hy
      have hh := hp _ (show (fun j => a*(Fin.cons 1 y : Fin (m+1) → K) j) ∈ scaledChart (Set.range (evaluate F)) from ⟨a,y,hy,rfl⟩)
      rw [← hP] at hh
      exact (evaluation_substitution P p y).trans hh
    have hh := hy _ hvan
    rw [← hP]
    exact (evaluation_substitution P p y).symm.trans hh

lemma projectiveCone_imageClosure {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : projectiveCone (imageClosure F) = imageClosure (conePolynomialMap F) := by
  rw [projectiveCone,chartHomogeneousIdeal_eq_scaledChart_vanishing,scaledChart_closure_vanishing,
    scaledChart_range_eq_conePolynomialMap_range]
  rfl

lemma projectiveCone_image_irreducible {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : IrreducibleAffine (projectiveCone (imageClosure F)) := by
  rw [projectiveCone_imageClosure]
  exact irreducibleAffine_imageClosure _

end APSCounting893.Main
end Component_35

section Component_36
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma prime_quotient_dimension_lower_of_independent {m r : ℕ}
    (P : Ideal (MvPolynomial (Fin (m+1)) ℂ)) [P.IsPrime]
    (v : Fin r → MvPolynomial (Fin (m+1)) ℂ ⧸ P) (hv : AlgebraicIndependent ℂ v) :
    ((r : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin (m+1)) ℂ ⧸ P) := by
  classical
  let A := MvPolynomial (Fin (m+1)) ℂ ⧸ P
  let L := FractionRing A
  letI : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors A)
  letI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ A L
  let f : A →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ A L
  have hfield := hv.map' (f := f) (IsFractionRing.injective A L)
  have hcard := hfield.cardinalMk_le_trdeg
  have hfinite := trdeg_lt_aleph0 ℂ L
  have hnat := Cardinal.toNat_le_toNat hcard hfinite
  have hn : r ≤ (Algebra.trdeg ℂ L).toNat := by simpa using hnat
  rw [OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat P]
  exact_mod_cast hn

end APSCounting893.Main
end Component_36

section Component_37
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma prime_quotient_dimension_mono {m n : ℕ}
    (P : Ideal (MvPolynomial (Fin (m+1)) ℂ)) [P.IsPrime]
    (Q : Ideal (MvPolynomial (Fin (n+1)) ℂ)) [Q.IsPrime]
    (f : (MvPolynomial (Fin (m+1)) ℂ ⧸ P) →ₐ[ℂ] (MvPolynomial (Fin (n+1)) ℂ ⧸ Q))
    (hf : Function.Injective f) :
    ringKrullDim (MvPolynomial (Fin (m+1)) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin (n+1)) ℂ ⧸ Q) := by
  classical
  let A := MvPolynomial (Fin (m+1)) ℂ ⧸ P
  let B := MvPolynomial (Fin (n+1)) ℂ ⧸ Q
  let L := FractionRing A
  let M := FractionRing B
  let g : A →ₐ[ℂ] M := (IsScalarTower.toAlgHom ℂ B M).comp f
  have hg : Function.Injective g := (IsFractionRing.injective B M).comp hf
  let h : L →ₐ[ℂ] M := IsFractionRing.liftAlgHom hg
  have hh := trdeg_le_of_injective h h.injective
  letI : Algebra.EssFiniteType B M := Algebra.EssFiniteType.of_isLocalization M (nonZeroDivisors B)
  letI : Algebra.EssFiniteType ℂ M := Algebra.EssFiniteType.comp ℂ B M
  have hnat := Cardinal.toNat_le_toNat hh (trdeg_lt_aleph0 ℂ M)
  rw [OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat P,
    OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat Q]
  exact_mod_cast hnat

end APSCounting893.Main
end Component_37

section Component_38
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma aeval_composePolynomialMap {K : Type} [Field K] {n m t : ℕ}
    (F : PolynomialMap K n m) (P : PolynomialMap K m t) (p : Polynomials K t) :
    MvPolynomial.aeval F (MvPolynomial.aeval P p) = MvPolynomial.aeval (composePolynomialMap F P) p := by
  have hh : composePolynomialMap F P = fun i => MvPolynomial.aeval F (P i) := by
    funext i
    simp only [composePolynomialMap,aeval_def,MvPolynomial.algebraMap_eq]
    rfl
  rw [hh]
  exact MvPolynomial.comp_aeval_apply P (MvPolynomial.aeval F) p

noncomputable def polynomialImageCoordinateMap {K : Type} [Field K] [Infinite K] {n m t : ℕ}
    (F : PolynomialMap K n m) (P : PolynomialMap K m t) :
    CoordinateRing (imageClosure (composePolynomialMap F P)) →ₐ[K] CoordinateRing (imageClosure F) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ K _).comp (MvPolynomial.aeval P)) (by
    intro p hp
    change Ideal.Quotient.mk (vanishingIdeal K (imageClosure F)) (MvPolynomial.aeval P p) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [imageClosure_vanishingIdeal_eq_kernel]
    change MvPolynomial.aeval F (MvPolynomial.aeval P p) = 0
    rw [aeval_composePolynomialMap]
    rw [imageClosure_vanishingIdeal_eq_kernel] at hp
    exact hp)

lemma polynomialImageCoordinateMap_injective {K : Type} [Field K] [Infinite K] {n m t : ℕ}
    (F : PolynomialMap K n m) (P : PolynomialMap K m t) :
    Function.Injective (polynomialImageCoordinateMap F P) := by
  apply (injective_iff_map_eq_zero (polynomialImageCoordinateMap F P).toRingHom).mpr
  intro x hx
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [imageClosure_vanishingIdeal_eq_kernel]
  change MvPolynomial.aeval (composePolynomialMap F P) p = 0
  rw [← aeval_composePolynomialMap]
  have hh : Ideal.Quotient.mk (vanishingIdeal K (imageClosure F)) (MvPolynomial.aeval P p) = 0 := hx
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hh
  rw [imageClosure_vanishingIdeal_eq_kernel] at hm
  exact hm

lemma image_dimension_compose_le {n m t : ℕ}
    (F : PolynomialMap ℂ n (m+1)) (P : PolynomialMap ℂ (m+1) (t+1)) :
    RSCapacity.algDim (imageClosure (composePolynomialMap F P)) ≤ RSCapacity.algDim (imageClosure F) := by
  let I := vanishingIdeal ℂ (imageClosure (composePolynomialMap F P))
  let J := vanishingIdeal ℂ (imageClosure F)
  letI : I.IsPrime := irreducibleAffine_ideal_prime (irreducibleAffine_imageClosure _)
  letI : J.IsPrime := irreducibleAffine_ideal_prime (irreducibleAffine_imageClosure _)
  exact prime_quotient_dimension_mono I J (polynomialImageCoordinateMap F P) (polynomialImageCoordinateMap_injective F P)

lemma polynomialImage_maps_closure {K : Type} [Field K] {n m t : ℕ}
    (F : PolynomialMap K n m) (P : PolynomialMap K m t) :
    evaluate P '' imageClosure F ⊆ imageClosure (composePolynomialMap F P) := by
  rintro y ⟨x,hx,rfl⟩ p hp
  have hvan : MvPolynomial.aeval P p ∈ vanishingIdeal K (Set.range (evaluate F)) := by
    intro z hz
    obtain ⟨u,rfl⟩ := hz
    have hh := hp (evaluate (composePolynomialMap F P) u) (Set.mem_range_self u)
    rw [evaluate_composePolynomialMap] at hh
    exact (evaluation_substitution P p (evaluate F u)).trans hh
  have hh := hx (MvPolynomial.aeval P p) hvan
  exact (evaluation_substitution P p x).symm.trans hh

end APSCounting893.Main
end Component_38

section Component_39
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma cone_output_nonzero_of_origin_excluded {K : Type} [Field K] [Infinite K] {m : ℕ}
    (Y : Set (Affine K m)) (hY : RSCapacity.IsAlgSet Y) (h0 : (0 : Affine K m) ∉ Y)
    (z : Affine K (m+1)) (hz : z ∈ projectiveCone Y) (hne : z ≠ 0) :
    (fun j : Fin m => z j.succ) ≠ 0 := by
  intro hout
  have hz0 : z 0 ≠ 0 := by
    intro hz0
    apply hne
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact hz0
    · exact congrFun hout j
  have hscaled := projectiveCone_scale Y z hz (z 0)⁻¹
  have hpoint : (fun j => (z 0)⁻¹*z j) = (Fin.cons 1 (0 : Affine K m) : Affine K (m+1)) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [hz0]
    · simp [congrFun hout j]
  rw [hpoint] at hscaled
  exact h0 ((projectiveCone_chart_iff Y hY 0).mp hscaled)

end APSCounting893.Main
end Component_39

section Component_40
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def outputConePolynomialMap {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) : PolynomialMap K (n+1) m :=
  fun i => MvPolynomial.X 0 * MvPolynomial.rename Fin.succ (F i)

noncomputable def coneOutputCoordinates {K : Type} [Field K] (m : ℕ) : PolynomialMap K (m+1) m :=
  fun i => MvPolynomial.X i.succ

lemma coneOutputCoordinates_evaluate {K : Type} [Field K] {m : ℕ} (z : Affine K (m+1)) :
    evaluate (coneOutputCoordinates m) z = fun i => z i.succ := by
  funext i
  simp [evaluate,coneOutputCoordinates]

lemma outputConePolynomialMap_eq_compose {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) : composePolynomialMap (conePolynomialMap F) (coneOutputCoordinates m) =
      outputConePolynomialMap F := by
  funext i
  simp [composePolynomialMap,coneOutputCoordinates,conePolynomialMap,outputConePolynomialMap]

lemma outputConePolynomialMap_eval {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (a : K) (x : Affine K n) :
    evaluate (outputConePolynomialMap F) (Fin.cons a x) = fun j => a*evaluate F x j := by
  funext i
  simp [outputConePolynomialMap,evaluate,MvPolynomial.eval_rename,Function.comp_def]

lemma cone_output_mem_outputConeClosure {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (z : Affine K (m+1)) (hz : z ∈ projectiveCone (imageClosure F)) :
    (fun i => z i.succ) ∈ imageClosure (outputConePolynomialMap F) := by
  rw [projectiveCone_imageClosure] at hz
  have hh := polynomialImage_maps_closure (conePolynomialMap F) (coneOutputCoordinates m)
    ⟨z,hz,rfl⟩
  rw [outputConePolynomialMap_eq_compose,coneOutputCoordinates_evaluate] at hh
  exact hh

lemma outputConeClosure_coordinate_nonzero {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (j : Fin m) (hF : F j ≠ 0) :
    ∃ y ∈ imageClosure (outputConePolynomialMap F), y j ≠ 0 := by
  have hex : ∃ x : Affine K n, eval x (F j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hF
    apply MvPolynomial.funext
    intro x
    simpa only [map_zero] using h x
  obtain ⟨x,hx⟩ := hex
  refine ⟨evaluate F x,?_,hx⟩
  apply zeroLocus_vanishingIdeal_le _
  refine ⟨Fin.cons 1 x,?_⟩
  simpa only [one_mul] using outputConePolynomialMap_eval F 1 x

end APSCounting893.Main
end Component_40

section Component_41
set_option autoImplicit false
set_option maxHeartbeats 600000
open MvPolynomial
namespace APSCounting893.Main

lemma full_dimension_incidence_cone_certificate {m r : ℕ} (F : PolynomialMap ℂ r (m+1))
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (h0 : ¬ hasAPS F) (j : Fin (m+1)) (hj : F j ≠ 0)
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ i, (F i).totalDegree ≤ d) :
    ∃ q : MvPolynomial (Fin (r+1) × Fin (m+1)) ℂ,
      q ≠ 0 ∧ q.totalDegree ≤ (r+1)*d^r ∧
      ∀ z ∈ imageClosure (outputConePolynomialMap F), ∀ B : Fin (r+1) × Fin (m+1) → ℂ,
        MvPolynomial.eval (incidenceMatrixAt j z B) q=0 := by
  obtain ⟨q,hqn,hqd,hq⟩ := full_dimension_incidence_raw_certificate F hdim h0 j hj d hd hdeg
  refine ⟨q,hqn,hqd,?_⟩
  apply incidence_relation_extends_zClosure (Set.range (evaluate (outputConePolynomialMap F))) j q
  intro z hz B
  obtain ⟨x,rfl⟩ := hz
  have hx : x=Fin.cons (x 0) (fun i => x i.succ) := by ext i; exact Fin.cases rfl (fun i => rfl) i
  rw [hx,outputConePolynomialMap_eval]
  exact hq (x 0) (fun i => x i.succ) B

end APSCounting893.Main
end Component_41

section Component_42
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma imageClosure_postcompose_congr {K : Type} [Field K] [Infinite K] {n a m t : ℕ}
    (F : PolynomialMap K n m) (G : PolynomialMap K a m) (P : PolynomialMap K m t)
    (h : imageClosure F = imageClosure G) :
    imageClosure (composePolynomialMap F P) = imageClosure (composePolynomialMap G P) := by
  have hI := congrArg (vanishingIdeal K) h
  rw [imageClosure_vanishingIdeal_eq_kernel,imageClosure_vanishingIdeal_eq_kernel] at hI
  have hk : RingHom.ker (MvPolynomial.aeval (R := K) (composePolynomialMap F P)).toRingHom =
      RingHom.ker (MvPolynomial.aeval (R := K) (composePolynomialMap G P)).toRingHom := by
    ext p
    change MvPolynomial.aeval (R := K) (composePolynomialMap F P) p = 0 ↔ MvPolynomial.aeval (R := K) (composePolynomialMap G P) p = 0
    rw [← aeval_composePolynomialMap,← aeval_composePolynomialMap]
    exact SetLike.ext_iff.mp hI (MvPolynomial.aeval P p)
  unfold imageClosure RSCapacity.zClosure
  rw [image_vanishingIdeal_eq_kernel,image_vanishingIdeal_eq_kernel]
  exact congrArg (zeroLocus K) hk

end APSCounting893.Main
end Component_42

section Component_43
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace APSCounting893.Main

lemma outputConeClosure_congr {K : Type} [Field K] [Infinite K] {n a m : ℕ}
    (F : PolynomialMap K n m) (G : PolynomialMap K a m) (h : imageClosure F=imageClosure G) :
    imageClosure (outputConePolynomialMap F)=imageClosure (outputConePolynomialMap G) := by
  have hcone : imageClosure (conePolynomialMap F)=imageClosure (conePolynomialMap G) := by
    rw [← projectiveCone_imageClosure,← projectiveCone_imageClosure,h]
  have hh := imageClosure_postcompose_congr (conePolynomialMap F) (conePolynomialMap G) (coneOutputCoordinates m) hcone
  rw [outputConePolynomialMap_eq_compose,outputConePolynomialMap_eq_compose] at hh
  exact hh

end APSCounting893.Main
end Component_43

section Component_44
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main
lemma totalDegree_eval₂_bounded_general {K L σ : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (g : Fin n → MvPolynomial σ L) (D : ℕ)
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
end Component_44

section Component_45
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main
lemma parameterMap_totalDegree_le {n r : ℕ} (p : SectionParameter n r) (i : Fin n) :
    (parameterMap p i).totalDegree ≤ 1 := by
  classical
  unfold parameterMap
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
end APSCounting893.Main
end Component_45

section Component_46
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def coefficientFunctional {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (φ : E →ₗ[K] K) (p : MvPolynomial σ E) : MvPolynomial σ K :=
  AddMonoidAlgebra.map φ.toAddMonoidHom p

lemma coefficientFunctional_coeff {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (φ : E →ₗ[K] K) (p : MvPolynomial σ E) (e : σ →₀ ℕ) :
    (coefficientFunctional φ p).coeff e = φ (p.coeff e) := rfl

lemma coefficientFunctional_degree_le {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (φ : E →ₗ[K] K) (p : MvPolynomial σ E) :
    (coefficientFunctional φ p).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro e he
  apply MvPolynomial.le_totalDegree
  apply MvPolynomial.mem_support_iff.mpr
  intro h
  have hq := MvPolynomial.mem_support_iff.mp he
  rw [coefficientFunctional_coeff,h,map_zero] at hq
  exact hq rfl

lemma coefficientFunctional_sum_monomials {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (φ : E →ₗ[K] K) (p : MvPolynomial σ E) :
    coefficientFunctional φ p = ∑ e ∈ p.support, MvPolynomial.monomial e (φ (p.coeff e)) := by
  classical
  apply MvPolynomial.ext
  intro e
  rw [coefficientFunctional_coeff,MvPolynomial.coeff_sum]
  by_cases he : e ∈ p.support
  · simp [MvPolynomial.coeff_monomial,he]
  · have hzero := MvPolynomial.notMem_support_iff.mp he
    simp [MvPolynomial.coeff_monomial,he,hzero]

lemma coefficientFunctional_eval {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (φ : E →ₗ[K] K) (p : MvPolynomial σ E) (x : σ → K) :
    MvPolynomial.eval x (coefficientFunctional φ p) =
      φ (MvPolynomial.eval (fun j => algebraMap K E (x j)) p) := by
  classical
  rw [coefficientFunctional_sum_monomials]
  conv_rhs => rw [MvPolynomial.eval_eq]
  simp only [MvPolynomial.eval_sum,MvPolynomial.eval_monomial,map_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hmul : p.coeff e * e.prod (fun j k => algebraMap K E (x j)^k) =
      (e.prod (fun j k => x j^k)) • p.coeff e := by
    rw [Algebra.smul_def,map_finsuppProd]
    simp only [map_pow]
    exact mul_comm _ _
  change φ (p.coeff e) * e.prod (fun j k => x j^k) =
    φ (p.coeff e * e.prod (fun j k => algebraMap K E (x j)^k))
  rw [hmul,map_smul,smul_eq_mul,mul_comm]

lemma exists_base_coefficient_certificate {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (p : MvPolynomial σ E) (hp : p ≠ 0) :
    ∃ q : MvPolynomial σ K, q ≠ 0 ∧ q.totalDegree ≤ p.totalDegree ∧
      ∀ x : σ → K, MvPolynomial.eval x q ≠ 0 →
        MvPolynomial.eval (fun j => algebraMap K E (x j)) p ≠ 0 := by
  classical
  have hex : ∃ e, p.coeff e ≠ 0 := by
    by_contra hh
    push_neg at hh
    apply hp
    ext e
    exact hh e
  obtain ⟨e,he⟩ := hex
  obtain ⟨φ,hφ⟩ := Module.Projective.exists_dual_eq_one K he
  refine ⟨coefficientFunctional φ p,?_,coefficientFunctional_degree_le φ p,?_⟩
  · intro h
    have hh := congrArg (MvPolynomial.coeff e) h
    rw [coefficientFunctional_coeff,hφ,MvPolynomial.coeff_zero] at hh
    exact one_ne_zero hh
  · intro x hx hpx
    rw [coefficientFunctional_eval,hpx,map_zero] at hx
    exact hx rfl

lemma exists_base_point_eval_ne_zero {K E σ : Type} [Field K] [Infinite K] [Field E] [Algebra K E]
    (p : MvPolynomial σ E) (hp : p ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval (fun j => algebraMap K E (x j)) p ≠ 0 := by
  classical
  obtain ⟨q,hq,hdegree,hgood⟩ := exists_base_coefficient_certificate (K := K) p hp
  have hex : ∃ x : σ → K, MvPolynomial.eval x q ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hq
    apply MvPolynomial.funext
    intro x
    simpa only [map_zero] using hh x
  obtain ⟨x,hx⟩ := hex
  exact ⟨x,hgood x hx⟩

end APSCounting893.Main
end Component_46

section Component_47
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma projective_incidence_relation_degree_bound_proof
    {n m r : ℕ} (F : PolynomialMap ℂ n m)
    (hr : 0 < r) (hrm : r < m)
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (h0 : ¬ hasAPS F) (j : Fin m) (hj : F j ≠ 0) :
    ∃ q : MvPolynomial (Fin (r+1) × Fin m) ℂ,
      q ≠ 0 ∧ q.totalDegree ≤ (r+1)*(inputDegree F)^r ∧
      ∀ z ∈ imageClosure (fun i : Fin m => MvPolynomial.X (0 : Fin (n+1)) * MvPolynomial.rename Fin.succ (F i)),
        ∀ B : Fin (r+1) × Fin m → ℂ,
          eval (fun a => z j*B a - (∑ t : Fin m, z t*B (a.1,t))*(if a.2=j then 1 else 0)) q = 0 := by
  classical
  cases m with
  | zero => exact (Nat.not_lt_zero r hrm).elim
  | succ m =>
    obtain ⟨q,hq,hqdeg,hgood⟩ := affine_section_nonvanishing_certificate F hrm hdim
    obtain ⟨s,hs⟩ := exists_base_point_eval_ne_zero (K := ℚ) q hq
    let s' : ReductionLabels n (m+1) r → ℚ := Sum.elim s (fun _ => 0)
    have heval : eval (fun a => (s' (Sum.inl a) : ℂ)) q ≠ 0 := by
      simpa only [s',Sum.elim_inl,eq_ratCast] using hs
    obtain ⟨hparam,hclosure⟩ := hgood s' heval
    let p := parameterMap (selectedSectionParameter s')
    let G := composePolynomialMap p F
    have hGdim : RSCapacity.algDim (imageClosure G) = ((r : ℕ∞) : WithBot ℕ∞) := by
      rw [show imageClosure G=imageClosure F from hclosure]
      exact hdim
    have hG0 : ¬ hasAPS G := by
      change ¬ (0 ∈ imageClosure G)
      rw [show imageClosure G=imageClosure F from hclosure]
      exact h0
    have hGj : G j ≠ 0 := by
      intro hzero
      have hk := congrArg (vanishingIdeal ℂ) hclosure
      rw [imageClosure_vanishingIdeal_eq_kernel,imageClosure_vanishingIdeal_eq_kernel] at hk
      have hX : MvPolynomial.X j ∈ RingHom.ker (MvPolynomial.aeval (R := ℂ) G).toRingHom := by
        change MvPolynomial.aeval (R := ℂ) G (MvPolynomial.X j)=0
        rw [MvPolynomial.aeval_X,hzero]
      change RingHom.ker (MvPolynomial.aeval (R := ℂ) G).toRingHom = RingHom.ker (MvPolynomial.aeval (R := ℂ) F).toRingHom at hk
      rw [hk] at hX
      change MvPolynomial.aeval (R := ℂ) F (MvPolynomial.X j)=0 at hX
      rw [MvPolynomial.aeval_X] at hX
      exact hj hX
    have hGdeg (i : Fin (m+1)) : (G i).totalDegree ≤ inputDegree F := by
      have hh := totalDegree_eval₂_bounded_general (RingHom.id ℂ) p 1
        (parameterMap_totalDegree_le (selectedSectionParameter s')) (F i)
      have hh' : (G i).totalDegree ≤ (F i).totalDegree := by
        simpa only [G,composePolynomialMap,RingHom.comp_id,one_mul] using hh
      exact hh'.trans ((Finset.le_sup (f := fun a => (F a).totalDegree) (Finset.mem_univ i)).trans (le_max_right _ _))
    obtain ⟨Q,hQ,hQdeg,hQgood⟩ := full_dimension_incidence_cone_certificate G hGdim hG0 j hGj
      (inputDegree F) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) hGdeg
    refine ⟨Q,hQ,hQdeg,?_⟩
    intro z hz B
    have hcone := outputConeClosure_congr G F hclosure
    have hzG : z ∈ imageClosure (outputConePolynomialMap G) := by
      rw [hcone]
      exact hz
    exact hQgood z hzG B

end APSCounting893.Main
end Component_47

open APSCounting893.Main
open MvPolynomial
theorem solution
    {n m r : ℕ} (F : PolynomialMap ℂ n m)
    (hr : 0 < r) (hrm : r < m)
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (h0 : ¬ hasAPS F) (j : Fin m) (hj : F j ≠ 0) :
    ∃ q : MvPolynomial (Fin (r+1) × Fin m) ℂ,
      q ≠ 0 ∧ q.totalDegree ≤ (r+1)*(inputDegree F)^r ∧
      ∀ z ∈ imageClosure (fun i : Fin m => MvPolynomial.X (0 : Fin (n+1)) * MvPolynomial.rename Fin.succ (F i)),
        ∀ B : Fin (r+1) × Fin m → ℂ,
          eval (fun a => z j*B a - (∑ t : Fin m, z t*B (a.1,t))*(if a.2=j then 1 else 0)) q = 0 := by
  exact projective_incidence_relation_degree_bound_proof F hr hrm hdim h0 j hj
