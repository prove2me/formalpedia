-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
-- name    : Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:08.947248+00:00
-- url     : https://prove2.me/theorems/b7892b67-3403-4cfd-9804-82aa23478a6d
-- title:
--   Is Graded Map Linear Combination
-- statement:
--   Definitions and structural lemmas for Is Graded Map Linear Combination, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one


set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
namespace GlobalTheory
open GradedHilbert
section Internal
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
theorem grProj_sum (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (T : Finset ℤ) (v : ℤ → M)
    (hv : ∀ j ∈ T, v j ∈ ℳ j) {n : ℤ} (hn : n ∈ T) : proj ℳ n (∑ j ∈ T, v j) = v n := by
  rw [map_sum, Finset.sum_eq_single n (fun j hj h => proj_of_mem_ne ℳ (hv j hj) h)
    (fun h => absurd hn h), proj_of_mem ℳ (hv n hn)]
theorem exists_sum_grProj (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (m : M) :
    ∃ T : Finset ℤ, ∑ j ∈ T, proj ℳ j m = m := by
  classical
  exact ⟨_, DirectSum.sum_support_decompose ℳ m⟩
theorem isInternal_of_sum_eq_zero (ℳ : ℤ → Submodule R M)
    (h₁ : ∀ (T : Finset ℤ) (v : ℤ → M), (∀ j ∈ T, v j ∈ ℳ j) → ∑ j ∈ T, v j = 0 →
      ∀ j ∈ T, v j = 0) (h₂ : ∀ m, m ∈ ⨆ j, ℳ j) : IsInternal ℳ :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top ℳ).2
    ⟨(iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero ℳ).2 h₁, eq_top_iff.2 fun m _ => h₂ m⟩
end Internal
section Poly
variable (ι : Type*) (R : Type*) [CommRing R]
def polyGrading : ℤ → Submodule R (MvPolynomial ι R) :=
  weightedHomogeneousSubmodule R (fun _ : ι => (1 : ℤ))
instance polyGrading.gradedAlgebra : GradedAlgebra (polyGrading ι R) :=
  weightedGradedAlgebra R (fun _ : ι => (1 : ℤ))
variable {ι R}
theorem weight_one_int (a : ι →₀ ℕ) :
    Finsupp.weight (fun _ : ι => (1 : ℤ)) a = (a.degree : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]
theorem mem_polyGrading_iff {p : MvPolynomial ι R} {n : ℤ} :
    p ∈ polyGrading ι R n ↔ ∀ a, coeff a p ≠ 0 → (a.degree : ℤ) = n := by
  simp only [polyGrading, mem_weightedHomogeneousSubmodule, IsWeightedHomogeneous, weight_one_int]
theorem mem_polyGrading_natCast {p : MvPolynomial ι R} {d : ℕ} :
    p ∈ polyGrading ι R d ↔ p.IsHomogeneous d := by
  simp only [mem_polyGrading_iff, IsHomogeneous, IsWeightedHomogeneous, Nat.cast_inj,
    Finsupp.degree_eq_weight_one]
  rfl
variable (ι R) in

theorem polyGrading_of_neg {n : ℤ} (hn : n < 0) : polyGrading ι R n = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  ext a
  by_contra h
  have := mem_polyGrading_iff.1 hp a h
  omega
end Poly
section Module
variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
variable (ι) in

abbrev PolyGradedSMul (ℳ : ℤ → Submodule R M) : Prop :=
  SetLike.GradedSMul (polyGrading ι R) ℳ
theorem grSMul_mem (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {p : MvPolynomial ι R} {d n : ℤ}
    {m : M} (hp : p ∈ polyGrading ι R d) (hm : m ∈ ℳ n) : p • m ∈ ℳ (n + d) := by
  rw [add_comm]
  exact SetLike.GradedSMul.smul_mem hp hm
theorem polyGradedSMul_of_X_smul_mem [IsScalarTower R (MvPolynomial ι R) M]
    (ℳ : ℤ → Submodule R M)
    (hX : ∀ (i : ι) (n : ℤ), ∀ m ∈ ℳ n, (X i : MvPolynomial ι R) • m ∈ ℳ (n + 1)) :
    PolyGradedSMul ι ℳ where
  smul_mem d n p m hp hm := by
    rcases lt_or_ge d 0 with hd | hd
    · rw [polyGrading_of_neg ι R hd, Submodule.mem_bot] at hp
      rw [hp, zero_smul]
      exact zero_mem _
    · lift d to ℕ using hd
      rw [vadd_eq_add, add_comm]
      exact smul_mem_of_isHomogeneous ℳ hX (mem_polyGrading_natCast.1 hp) n m hm
def IsGradedMap (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N)
    (f : M →ₗ[MvPolynomial ι R] N) : Prop :=
  ∀ ⦃n : ℤ⦄ ⦃m : M⦄, m ∈ ℳ n → f m ∈ 𝒩 n
namespace IsGradedMap
variable {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {𝒬 : ℤ → Submodule R P}
variable (ι ℳ 𝒩) in

theorem zero : IsGradedMap ℳ 𝒩 (0 : M →ₗ[MvPolynomial ι R] N) := fun _ _ _ => zero_mem _
theorem add {f g : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (hg : IsGradedMap ℳ 𝒩 g) :
    IsGradedMap ℳ 𝒩 (f + g) := fun _ _ h => add_mem (hf h) (hg h)
variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) P]
def piece {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) : ℳ n →ₗ[R] 𝒩 n :=
  (f.restrictScalars R).restrict fun _ h => hf h
@[simp]
theorem coe_piece {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) (m : ℳ n) :
    (hf.piece n m : N) = f m := rfl
variable [Decomposition ℳ] [Decomposition 𝒩]
theorem proj_apply {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) (m : M) :
    proj 𝒩 n (f m) = f (proj ℳ n m) := by
  simpa using proj_map ℳ 𝒩 (f.restrictScalars R) 0 (fun n m hm => by simpa using hf hm) n m
theorem exists_mem_of_mem_range {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) {n : ℤ}
    {y : N} (hy : y ∈ 𝒩 n) (h : y ∈ LinearMap.range f) : ∃ m ∈ ℳ n, f m = y := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨proj ℳ n m, proj_mem _ _ _, by rw [← hf.proj_apply, proj_of_mem _ hy]⟩
theorem symm {e : M ≃ₗ[MvPolynomial ι R] N} (he : IsGradedMap ℳ 𝒩 e.toLinearMap) :
    IsGradedMap 𝒩 ℳ e.symm.toLinearMap := fun n y hy => by
  obtain ⟨m, hm, rfl⟩ := he.exists_mem_of_mem_range hy (e.surjective y)
  simpa using hm
end IsGradedMap
def grShift (ℳ : ℤ → Submodule R M) (d : ℤ) : ℤ → Submodule R M := fun n => ℳ (n + d)
@[simp]
theorem grShift_apply (ℳ : ℤ → Submodule R M) (d n : ℤ) : grShift ℳ d n = ℳ (n + d) := rfl
@[simp]
theorem grShift_zero (ℳ : ℤ → Submodule R M) : grShift ℳ 0 = ℳ := by
  funext n; simp
instance grShift.polyGradedSMul (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] (d : ℤ) :
    PolyGradedSMul ι (grShift ℳ d) where
  smul_mem e n p m hp hm := by
    have := grSMul_mem ℳ hp hm
    rwa [grShift_apply, vadd_eq_add, show e + n + d = n + d + e by ring]
instance grShift.decomposition (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (d : ℤ) :
    Decomposition (grShift ℳ d) :=
  IsInternal.chooseDecomposition _ <| isInternal_of_sum_eq_zero _
    (fun T v hv h j hj => by
      have := congrArg (proj ℳ (j + d)) h
      rwa [map_sum, Finset.sum_eq_single j
        (fun i hi e => proj_of_mem_ne ℳ (hv i hi) (by omega)) (fun e => absurd hj e),
        proj_of_mem ℳ (hv j hj), map_zero] at this)
    fun m => by
      induction m using Decomposition.inductionOn ℳ with
      | zero => exact zero_mem _
      | @homogeneous n m => exact Submodule.mem_iSup_of_mem (n - d) (by simp)
      | add a b ha hb => exact add_mem ha hb
variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
def grSub (ℳ : ℤ → Submodule R M) (K : Submodule (MvPolynomial ι R) M) :
    ℤ → Submodule R K := fun n => (ℳ n).comap (K.subtype.restrictScalars R)
@[simp]
theorem mem_grSub {ℳ : ℤ → Submodule R M} {K : Submodule (MvPolynomial ι R) M} {n : ℤ}
    {m : K} : m ∈ grSub ℳ K n ↔ (m : M) ∈ ℳ n := Iff.rfl
def grQuot (ℳ : ℤ → Submodule R M) (K : Submodule (MvPolynomial ι R) M) :
    ℤ → Submodule R (M ⧸ K) := fun n => (ℳ n).map (K.mkQ.restrictScalars R)
theorem mem_grQuot {ℳ : ℤ → Submodule R M} {K : Submodule (MvPolynomial ι R) M} {n : ℤ}
    {y : M ⧸ K} : y ∈ grQuot ℳ K n ↔ ∃ m ∈ ℳ n, Submodule.Quotient.mk m = y := Iff.rfl
instance grSub.polyGradedSMul (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    (K : Submodule (MvPolynomial ι R) M) : PolyGradedSMul ι (grSub ℳ K) where
  smul_mem _ _ _ _ hp hm := SetLike.GradedSMul.smul_mem (B := ℳ) hp hm
instance grQuot.polyGradedSMul (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    (K : Submodule (MvPolynomial ι R) M) : PolyGradedSMul ι (grQuot ℳ K) where
  smul_mem := by
    rintro d n p _ hp ⟨m, hm, rfl⟩
    exact ⟨p • m, SetLike.GradedSMul.smul_mem (B := ℳ) hp hm, rfl⟩
theorem isInternal_grSub (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    {K : Submodule (MvPolynomial ι R) M} (hK : K.IsHomogeneous ℳ) :
    IsInternal (grSub ℳ K) :=
  isInternal_of_sum_eq_zero _
    (fun T v hv h j hj => Subtype.ext <| by
      have e := grProj_sum ℳ T (fun i => (v i : M)) hv hj
      rw [← e, ← Submodule.coe_sum, h]
      simp)
    fun m => by
      obtain ⟨T, hT⟩ := exists_sum_grProj ℳ (m : M)
      have : m = ∑ j ∈ T, (⟨proj ℳ j m, hK j m.2⟩ : K) := Subtype.ext (by simp [hT])
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j (proj_mem ℳ j m)
theorem isInternal_grQuot (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    {K : Submodule (MvPolynomial ι R) M} (hK : K.IsHomogeneous ℳ) :
    IsInternal (grQuot ℳ K) :=
  isInternal_of_sum_eq_zero _
    (fun T v hv h j hj => by
      choose! w hw e using fun i hi => mem_grQuot.1 (hv i hi)
      have h' : ∑ i ∈ T, w i ∈ K := by
        rw [← Submodule.Quotient.mk_eq_zero, ← h, ← Finset.sum_congr rfl e]
        exact map_sum K.mkQ _ _
      have := hK j h'
      rw [← GradedHilbert.proj_apply, grProj_sum ℳ T w hw hj] at this
      rw [← e j hj, Submodule.Quotient.mk_eq_zero]
      exact this)
    fun y => by
      obtain ⟨m, rfl⟩ := K.mkQ_surjective y
      induction m using Decomposition.inductionOn ℳ with
      | zero => rw [map_zero]; exact zero_mem _
      | @homogeneous n m => exact Submodule.mem_iSup_of_mem n ⟨m, m.2, rfl⟩
      | add a b ha hb => rw [map_add]; exact add_mem ha hb
@[instance_reducible]
def grSubDecomposition (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    {K : Submodule (MvPolynomial ι R) M} (hK : K.IsHomogeneous ℳ) :
    Decomposition (grSub ℳ K) :=
  (isInternal_grSub ℳ hK).chooseDecomposition _
@[instance_reducible]
def grQuotDecomposition (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    {K : Submodule (MvPolynomial ι R) M} (hK : K.IsHomogeneous ℳ) :
    Decomposition (grQuot ℳ K) :=
  (isInternal_grQuot ℳ hK).chooseDecomposition _
instance grSub.decomposition (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [PolyGradedSMul ι ℳ] (K : HomogeneousSubmodule (polyGrading ι R) ℳ) :
    Decomposition (grSub ℳ K.toSubmodule) := grSubDecomposition ℳ K.isHomogeneous
instance grQuot.decomposition (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [PolyGradedSMul ι ℳ] (K : HomogeneousSubmodule (polyGrading ι R) ℳ) :
    Decomposition (grQuot ℳ K.toSubmodule) := grQuotDecomposition ℳ K.isHomogeneous
end Module
section Pi
variable {ι : Type*} {R : Type*} [CommRing R] {κ : Type*}
  {M : κ → Type*} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
  [∀ k, Module (MvPolynomial ι R) (M k)]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
def grPi (ℳ : ∀ k, ℤ → Submodule R (M k)) : ℤ → Submodule R (∀ k, M k) :=
  fun n => Submodule.pi Set.univ fun k => ℳ k n
@[simp]
theorem mem_grPi {ℳ : ∀ k, ℤ → Submodule R (M k)} {n : ℤ} {m : ∀ k, M k} :
    m ∈ grPi ℳ n ↔ ∀ k, m k ∈ ℳ k n := by
  simp [grPi, Submodule.mem_pi]
instance grPi.polyGradedSMul (ℳ : ∀ k, ℤ → Submodule R (M k))
    [∀ k, PolyGradedSMul ι (ℳ k)] : PolyGradedSMul ι (grPi ℳ) where
  smul_mem _ _ _ _ hp hm := mem_grPi.2 fun k =>
    SetLike.GradedSMul.smul_mem (B := ℳ k) hp (mem_grPi.1 hm k)
instance grPi.decomposition [Finite κ] (ℳ : ∀ k, ℤ → Submodule R (M k))
    [∀ k, Decomposition (ℳ k)] : Decomposition (grPi ℳ) :=
  IsInternal.chooseDecomposition _ <| isInternal_of_sum_eq_zero _
    (fun T v hv h j hj => funext fun k => by
      have e := grProj_sum (ℳ k) T (fun i => v i k) (fun i hi => mem_grPi.1 (hv i hi) k) hj
      rw [← e, ← Finset.sum_apply, h]
      simp)
    fun m => by
      classical
      have := Fintype.ofFinite κ
      rw [← Finset.univ_sum_single m]
      refine Submodule.sum_mem _ fun k _ => ?_
      induction m k using Decomposition.inductionOn (ℳ k) with
      | zero => rw [Pi.single_zero]; exact zero_mem _
      | @homogeneous n x =>
        refine Submodule.mem_iSup_of_mem n (mem_grPi.2 fun j => ?_)
        by_cases h : j = k
        · subst h; simp
        · rw [Pi.single_eq_of_ne h]; exact zero_mem _
      | add a b ha hb => rw [Pi.single_add]; exact add_mem ha hb
variable (ι R) in

abbrev grFree (d : κ → ℤ) : ℤ → Submodule R (κ → MvPolynomial ι R) :=
  grPi fun k => grShift (polyGrading ι R) (-d k)
end Pi
section Family
variable {ι : Type*} {R : Type*} [CommRing R]
  {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
  {B : ℤ → Type*} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
def OperatorsCommute (x : ι → ∀ n, A n →ₗ[R] A (n + 1)) : Prop :=
  ∀ (i j : ι) (n : ℤ) (a : A n), x i (n + 1) (x j n a) = x j (n + 1) (x i n a)
@[nolint unusedArguments]
def GrSum {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (_ : OperatorsCommute x) : Type _ := ⨁ n, A n
namespace GrSum
variable {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
  {y : ι → ∀ n, B n →ₗ[R] B (n + 1)} (hy : OperatorsCommute y)
instance : AddCommGroup (GrSum hx) := inferInstanceAs (AddCommGroup (⨁ n, A n))
instance : Module R (GrSum hx) := inferInstanceAs (Module R (⨁ n, A n))
def equivDirectSum : GrSum hx ≃ₗ[R] ⨁ n, A n := LinearEquiv.refl R _
def of (n : ℤ) : A n →ₗ[R] GrSum hx := DirectSum.lof R ℤ A n
def component (n : ℤ) : GrSum hx →ₗ[R] A n := DirectSum.component R ℤ A n
@[simp]
theorem component_of (n : ℤ) (a : A n) : component hx n (of hx n a) = a :=
  DirectSum.component.lof_self R n a
theorem component_of_ne {n k : ℤ} (h : k ≠ n) (a : A k) : component hx n (of hx k a) = 0 :=
  (DirectSum.component.of R n k a).trans (dif_neg h)
theorem of_injective (n : ℤ) : Function.Injective (of hx n) :=
  Function.LeftInverse.injective (component_of hx n)
theorem lhom_ext {N : Type*} [AddCommGroup N] [Module R N] {f g : GrSum hx →ₗ[R] N}
    (h : ∀ n a, f (of hx n a) = g (of hx n a)) : f = g :=
  DirectSum.linearMap_ext R fun n => LinearMap.ext (h n)
def desc {N : Type*} [AddCommGroup N] [Module R N] (φ : ∀ n, A n →ₗ[R] N) : GrSum hx →ₗ[R] N :=
  DirectSum.toModule R ℤ N φ
@[simp]
theorem desc_of {N : Type*} [AddCommGroup N] [Module R N] (φ : ∀ n, A n →ₗ[R] N) (n : ℤ)
    (a : A n) : desc hx φ (of hx n a) = φ n a :=
  DirectSum.toModule_lof R n a
def op (i : ι) : Module.End R (GrSum hx) := desc hx fun n => of hx (n + 1) ∘ₗ x i n
@[simp]
theorem op_of (i : ι) (n : ℤ) (a : A n) : op hx i (of hx n a) = of hx (n + 1) (x i n a) :=
  desc_of hx _ n a
theorem commute_op (i j : ι) : Commute (op hx i) (op hx j) :=
  lhom_ext hx fun n a => by simp [hx i j n a]
instance : Module (MvPolynomial ι R) (GrSum hx) :=
  Module.compHom (GrSum hx) (Wick.commEval R (op hx) (commute_op hx)).toRingHom
theorem smul_def (p : MvPolynomial ι R) (m : GrSum hx) :
    p • m = Wick.commEval R (op hx) (commute_op hx) p m := rfl
instance : IsScalarTower R (MvPolynomial ι R) (GrSum hx) where
  smul_assoc r p m := by rw [smul_def, smul_def, map_smul]; rfl
theorem X_smul (i : ι) (m : GrSum hx) : (X i : MvPolynomial ι R) • m = op hx i m := by
  rw [smul_def, Wick.commEval_X]
@[simp]
theorem X_smul_of (i : ι) (n : ℤ) (a : A n) :
    (X i : MvPolynomial ι R) • of hx n a = of hx (n + 1) (x i n a) := by
  rw [X_smul, op_of]
def grading : ℤ → Submodule R (GrSum hx) := fun n => LinearMap.range (of hx n)
theorem mem_grading {n : ℤ} {m : GrSum hx} : m ∈ grading hx n ↔ ∃ a, of hx n a = m := Iff.rfl
def pieceEquiv (n : ℤ) : A n ≃ₗ[R] grading hx n := LinearEquiv.ofInjective _ (of_injective hx n)
@[simp]
theorem coe_pieceEquiv (n : ℤ) (a : A n) : (pieceEquiv hx n a : GrSum hx) = of hx n a := rfl
instance : PolyGradedSMul ι (grading hx) :=
  polyGradedSMul_of_X_smul_mem _ (by
    rintro i n _ ⟨a, rfl⟩
    exact ⟨_, (X_smul_of hx i n a).symm⟩)
instance : Decomposition (grading hx) :=
  IsInternal.chooseDecomposition _ <| isInternal_of_sum_eq_zero _
    (fun T v hv h j hj => by
      choose! a ha using fun i hi => (mem_grading hx).1 (hv i hi)
      have := congrArg (component hx j) h
      rw [← Finset.sum_congr rfl ha, map_sum, Finset.sum_eq_single j
        (fun i _ e => component_of_ne hx e _) (fun e => absurd hj e), component_of,
        map_zero] at this
      rw [← ha j hj, this, map_zero])
    fun m => by
      induction m using DirectSum.induction_on with
      | zero => exact zero_mem _
      | of n a => exact Submodule.mem_iSup_of_mem n ⟨a, rfl⟩
      | add a b ha hb => exact add_mem ha hb
variable {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
def lift (φ : ∀ n, A n →ₗ[R] N)
    (hφ : ∀ i n a, φ (n + 1) (x i n a) = (X i : MvPolynomial ι R) • φ n a) :
    GrSum hx →ₗ[MvPolynomial ι R] N where
  toFun := desc hx φ
  map_add' := map_add _
  map_smul' p m := by
    have hX (i : ι) : desc hx φ ∘ₗ mul (GrSum hx) (X i : MvPolynomial ι R) =
        mul N (X i : MvPolynomial ι R) ∘ₗ desc hx φ := lhom_ext hx fun n a => by simp [hφ]
    rw [RingHom.id_apply]
    induction p using MvPolynomial.induction_on generalizing m with
    | C a => rw [← MvPolynomial.algebraMap_eq, algebraMap_smul, algebraMap_smul, map_smul]
    | add p q hp hq => rw [add_smul, add_smul, map_add, hp, hq]
    | mul_X p i hp =>
      rw [mul_smul, mul_smul, hp]
      exact congrArg _ congr($(hX i) m)
@[simp]
theorem lift_of (φ : ∀ n, A n →ₗ[R] N) (hφ) (n : ℤ) (a : A n) :
    lift hx φ hφ (of hx n a) = φ n a := desc_of hx φ n a
def map (φ : ∀ n, A n →ₗ[R] B n) (hφ : ∀ i n a, φ (n + 1) (x i n a) = y i n (φ n a)) :
    GrSum hx →ₗ[MvPolynomial ι R] GrSum hy :=
  lift hx (fun n => of hy n ∘ₗ φ n) fun i n a => by simp [hφ]
end GrSum
end Family
end GlobalTheory


