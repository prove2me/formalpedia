-- Prove2me | solution 1 for AlgebraicGeometry.AdmissibleAlgebra.isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_of_ringEquiv_tensorProduct_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/cf788cf7-bb8a-5ef2-be7e-0eede1e439e1

import Mathlib
import Theorems.Thm_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_sub_tmul_mem_span_pow_of_flat
import Theorems.Thm_AlgebraicGeometry_AdmissibleAlgebra_fixedPoints_isAdicComplete_and_finite_and_finiteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_of_ringEquiv_tensorProduct_quotient

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open TensorProduct

namespace C3Alg

theorem mem_fixedPoints_subalgebra_iff {A B : Type} [CommSemiring A] [Semiring B] [Algebra A B]
    {G : Type} [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] (x : B) :
    x ∈ FixedPoints.subalgebra A B G ↔ ∀ g : G, g • x = x := Iff.rfl

theorem smodEq_span_pow_top_iff {R : Type} [CommRing R] (a : R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ Ideal.span {a ^ n} := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

theorem pow_mul_eq_zero_imp {R : Type} [CommRing R] (t : R) (htf : ∀ x : R, t * x = 0 → x = 0) :
    ∀ (n : ℕ) (x : R), t ^ n * x = 0 → x = 0 := by
  intro n
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [pow_succ, mul_assoc] at hx
    exact htf x (ih _ hx)

theorem smul_mem_span_pow {S R : Type} [CommRing S] [CommRing R] [Algebra S R]
    {G : Type} [Group G] [MulSemiringAction G R] [SMulCommClass G S R] (t : S) (k : ℕ) (g : G)
    {y : R} (hy : y ∈ Ideal.span {(algebraMap S R t) ^ k}) : g • y ∈ Ideal.span {(algebraMap S R t) ^ k} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [smul_mul', smul_pow', smul_algebraMap]
  exact Ideal.mem_span_singleton'.mpr ⟨g • c, rfl⟩

theorem coe_mem_span_pow_iff {S R : Type} [CommRing S] [CommRing R] [Algebra S R]
    (G : Type) [Group G] [MulSemiringAction G R] [SMulCommClass G S R] (t : S)
    (htf : ∀ x : R, algebraMap S R t * x = 0 → x = 0) (n : ℕ) (x : ↥(FixedPoints.subalgebra S R G)) :
    (x : R) ∈ Ideal.span {(algebraMap S R t) ^ n} ↔
      x ∈ Ideal.span {(algebraMap S ↥(FixedPoints.subalgebra S R G) t) ^ n} := by
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hx
    have hrfix : ∀ g : G, g • r = r := fun g => by
      have hgx : g • (x : R) = x := (mem_fixedPoints_subalgebra_iff (A := S) (x : R)).mp x.2 g
      have h1 : (algebraMap S R t) ^ n * (g • r - r) = 0 := by
        rw [mul_sub, sub_eq_zero]
        have := congrArg (fun y : R => g • y) hr
        simp only [smul_mul', smul_pow', smul_algebraMap, hgx] at this
        rw [mul_comm] at this hr
        rw [this, hr]
      exact sub_eq_zero.mp (pow_mul_eq_zero_imp (algebraMap S R t) htf n _ h1)
    refine Ideal.mem_span_singleton'.mpr ⟨⟨r, (mem_fixedPoints_subalgebra_iff (A := S) r).mpr hrfix⟩, ?_⟩
    apply Subtype.ext
    show r * ((algebraMap S ↥(FixedPoints.subalgebra S R G) t : ↥(FixedPoints.subalgebra S R G)) : R) ^ n = (x : R)
    rw [Subalgebra.coe_algebraMap, hr]
  · intro hx
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hx
    rw [← hr]
    refine Ideal.mem_span_singleton'.mpr ⟨(r : R), ?_⟩
    show (r : R) * (algebraMap S R t) ^ n = ((r * (algebraMap S ↥(FixedPoints.subalgebra S R G) t) ^ n :  ↥(FixedPoints.subalgebra S R G)) : R)
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap]

theorem fixedPoints_isAdicComplete {S R : Type} [CommRing S] [CommRing R] [Algebra S R]
    (G : Type) [Group G] [MulSemiringAction G R] [SMulCommClass G S R] (t : S)
    (hc : IsAdicComplete (Ideal.span {algebraMap S R t}) R)
    (htf : ∀ x : R, algebraMap S R t * x = 0 → x = 0) :
    IsAdicComplete (Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R G) t}) ↥(FixedPoints.subalgebra S R G) where
  haus' x hx := by
    apply Subtype.ext
    refine IsHausdorff.haus hc.toIsHausdorff _ (fun n => ?_)
    rw [smodEq_span_pow_top_iff, sub_zero]
    have := hx n
    rw [smodEq_span_pow_top_iff, sub_zero] at this
    exact (coe_mem_span_pow_iff G t htf n x).mpr this
  prec' f hf := by
    have hf' : ∀ {m n : ℕ}, m ≤ n →
        (f m : R) ≡ (f n : R) [SMOD ((Ideal.span {algebraMap S R t}) ^ m • ⊤ : Submodule R R)] := by
      intro m n hmn
      rw [smodEq_span_pow_top_iff, ← AddSubgroupClass.coe_sub]
      apply (coe_mem_span_pow_iff G t htf m _).mpr
      have h := hf hmn
      rwa [smodEq_span_pow_top_iff] at h
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete hf'
    have hLfix : ∀ g : G, g • L = L := fun g => by
      rw [← sub_eq_zero]
      refine IsHausdorff.haus hc.toIsHausdorff _ (fun n => ?_)
      rw [smodEq_span_pow_top_iff, sub_zero]
      have hn := hL n
      rw [smodEq_span_pow_top_iff] at hn
      have hfix : g • (f n : R) = f n := (mem_fixedPoints_subalgebra_iff (A := S) (f n : R)).mp (f n).2 g
      have hrew : g • L - L = -(g • ((f n : R) - L)) + ((f n : R) - L) := by
        rw [smul_sub, hfix]; ring
      rw [hrew]
      exact Ideal.add_mem _ ((Ideal.neg_mem_iff _).mpr (smul_mem_span_pow t n g hn)) hn
    refine ⟨⟨L, (mem_fixedPoints_subalgebra_iff (A := S) L).mpr hLfix⟩, fun n => ?_⟩
    rw [smodEq_span_pow_top_iff]
    apply (coe_mem_span_pow_iff G t htf n _).mp
    rw [AddSubgroupClass.coe_sub]
    have hn := hL n
    rwa [smodEq_span_pow_top_iff] at hn

section Action

variable {𝒪 : Type} [CommRing 𝒪] {R : Type} [CommRing R] [Algebra 𝒪 R]
  {G : Type} [Group G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R]

def smulLinear (g : G) : R →ₗ[↥(FixedPoints.subalgebra 𝒪 R G)] R where
  toFun r := g • r
  map_add' x y := smul_add g x y
  map_smul' a r := by
    simp only [Algebra.smul_def, smul_mul', RingHom.id_apply]
    congr 1
    exact a.2 g

@[scoped simp] theorem smulLinear_apply (g : G) (r : R) : smulLinear (𝒪 := 𝒪) g r = g • r := rfl

variable (A' : Type) [CommRing A'] [Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A']

noncomputable def ρ (g : G) :
    R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A' →+ R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A' :=
  ((smulLinear (𝒪 := 𝒪) g).rTensor A').toAddMonoidHom

theorem ρ_tmul (g : G) (r : R) (s : A') :
    (ρ (𝒪 := 𝒪) (R := R) (G := G) A' g) (r ⊗ₜ s) = (g • r) ⊗ₜ s := rfl

end Action

theorem mem_span_pow_of_tmul_mem {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {R : Type} [CommRing R] [Algebra 𝒪 R]
    {G : Type} [Group G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R]
    (hinv : ∀ k : ℕ, ∀ x : ↥(FixedPoints.subalgebra 𝒪 R G),
      (x : R) ∈ Ideal.span {(algebraMap 𝒪 R π) ^ k} → x ∈ Ideal.span {(algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π) ^ k})
    (A' : Type) [CommRing A'] [Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A'] [Module.Flat ↥(FixedPoints.subalgebra 𝒪 R G) A']
    (m : ℕ) (w : A')
    (h : (1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w ∈
      Ideal.span {(algebraMap 𝒪 R π ^ m) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) :
    w ∈ Ideal.span {algebraMap ↥(FixedPoints.subalgebra 𝒪 R G) A'
      (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π) ^ m} := by
  classical

  obtain ⟨IA, hIA⟩ : ∃ IA : Ideal ↥(FixedPoints.subalgebra 𝒪 R G),
      IA = Ideal.span {(algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π) ^ m} := ⟨_, rfl⟩
  obtain ⟨IR, hIR⟩ : ∃ IR : Ideal R, IR = Ideal.span {(algebraMap 𝒪 R π) ^ m} := ⟨_, rfl⟩
  have hπA : (algebraMap ↥(FixedPoints.subalgebra 𝒪 R G) R) (algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π) =
      algebraMap 𝒪 R π := rfl

  have hle : IA ≤ IR.comap (Algebra.ofId ↥(FixedPoints.subalgebra 𝒪 R G) R) := by
    rw [hIA, hIR, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    show (algebraMap ↥(FixedPoints.subalgebra 𝒪 R G) R) ((algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π) ^ m) ∈ _
    rw [map_pow, hπA]
    exact Ideal.subset_span rfl
  let jq : (↥(FixedPoints.subalgebra 𝒪 R G) ⧸ IA) →ₐ[↥(FixedPoints.subalgebra 𝒪 R G)] (R ⧸ IR) :=
    Ideal.quotientMapₐ IR (Algebra.ofId ↥(FixedPoints.subalgebra 𝒪 R G) R) hle
  have hjq : ∀ a : ↥(FixedPoints.subalgebra 𝒪 R G), jq (Ideal.Quotient.mk IA a) = Ideal.Quotient.mk IR (a : R) :=
    fun a => rfl
  have hinj : Function.Injective jq.toLinearMap := by
    intro u v huv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective v
    change jq (Ideal.Quotient.mk IA a) = jq (Ideal.Quotient.mk IA a') at huv
    rw [hjq, hjq, Ideal.Quotient.eq, ← AddSubgroupClass.coe_sub, hIR] at huv
    exact Ideal.Quotient.eq.mpr (hIA ▸ hinv m _ huv)
  have hinj' := Module.Flat.rTensor_preserves_injective_linearMap (M := A') jq.toLinearMap hinj

  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp h
  let Φ : R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A' →ₐ[↥(FixedPoints.subalgebra 𝒪 R G)] (R ⧸ IR) ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A' :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ ↥(FixedPoints.subalgebra 𝒪 R G) IR) (AlgHom.id ↥(FixedPoints.subalgebra 𝒪 R G) A')
  have hΦ : (Ideal.Quotient.mk IR 1) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w = (0 : (R ⧸ IR) ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') := by
    have h1 : Φ ((1 : R) ⊗ₜ w) = (Ideal.Quotient.mk IR 1) ⊗ₜ w := rfl
    have hπ0 : Ideal.Quotient.mk IR (algebraMap 𝒪 R π ^ m) = 0 := by
      rw [hIR]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    have h2 : Φ ((algebraMap 𝒪 R π ^ m) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')) = 0 := by
      have : Φ ((algebraMap 𝒪 R π ^ m) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')) =
          (Ideal.Quotient.mk IR (algebraMap 𝒪 R π ^ m)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A') := rfl
      rw [this, hπ0, TensorProduct.zero_tmul]
    rw [← h1, ← hz, map_mul, h2, mul_zero]
  have h0 : (jq.toLinearMap.rTensor A') ((Ideal.Quotient.mk IA 1) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w) = (jq.toLinearMap.rTensor A') 0 := by
    rw [LinearMap.rTensor_tmul, map_zero, AlgHom.toLinearMap_apply, hjq]
    exact hΦ
  have h1 : (Ideal.Quotient.mk IA 1) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w = 0 := hinj' h0
  have h2 : (Submodule.Quotient.mk ((1 : ↥(FixedPoints.subalgebra 𝒪 R G)) • w) : A' ⧸ (IA • ⊤ : Submodule ↥(FixedPoints.subalgebra 𝒪 R G) A')) = 0 := by
    rw [← TensorProduct.quotTensorEquivQuotSMul_mk_tmul, h1, LinearEquiv.map_zero]
  rw [one_smul, Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, hIA,
    Ideal.map_span, Set.image_singleton, map_pow] at h2
  exact h2

end C3Alg
p2m_reactivate "P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_of_ringEquiv_tensorProduct_quotient.C3Alg"

namespace C3Alg

section Lift

variable {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {R : Type} [CommRing R] [Algebra 𝒪 R]
  {G : Type} [Group G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R]
  {S : Type} [CommRing S] [Algebra 𝒪 S]
  {A' : Type} [CommRing A'] [Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A']
  {R' : Type} [CommRing R'] [Algebra S R'] [MulSemiringAction G R'] [SMulCommClass G S R']
  (τ : ∀ n : ℕ, ((R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') ⧸ Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) ≃+* (R' ⧸ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)}))

theorem hIpow (n : ℕ) : (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) ^ (n + 1) = Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)} := Ideal.span_singleton_pow _ _

noncomputable def lvlMap (n : ℕ) : (R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') →+* R' ⧸ (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) ^ (n + 1) :=
  (Ideal.quotEquivOfEq (hIpow (S := S) (R' := R') π n).symm).toRingHom.comp ((τ n).toRingHom.comp (Ideal.Quotient.mk _))

theorem lvlMap_apply (n : ℕ) (z : (R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A')) (y : R') (h : τ n (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y) :
    lvlMap π τ n z = Ideal.Quotient.mk _ y := by
  show Ideal.quotEquivOfEq (hIpow (S := S) (R' := R') π n).symm (τ n (Ideal.Quotient.mk _ z)) = _
  rw [h, Ideal.quotEquivOfEq_mk]

theorem strictMono_succ : StrictMono (fun n : ℕ => n + 1) := fun _ _ h => Nat.add_lt_add_right h 1

theorem lvlMap_compat
    (hτ_succ : ∀ (n : ℕ) (z : (R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A')) (y : R'),
      τ (n + 1) (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y → τ n (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y)
    {m : ℕ} :
    (Ideal.Quotient.factorPow (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) (strictMono_succ.monotone m.le_succ)).comp (lvlMap π τ (m + 1)) =
      lvlMap π τ m := by
  refine RingHom.ext fun z => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (τ (m + 1) (Ideal.Quotient.mk _ z))
  rw [RingHom.comp_apply, lvlMap_apply π τ (m + 1) z y hy.symm, lvlMap_apply π τ m z y (hτ_succ m z y hy.symm)]
  exact Ideal.Quotient.factor_mk _ _

variable (hR'c : IsAdicComplete (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) R')
  (hτ_succ : ∀ (n : ℕ) (z : (R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A')) (y : R'),
    τ (n + 1) (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y → τ n (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y)

noncomputable def ι : (R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') →+* R' :=
  haveI := hR'c
  IsAdicComplete.StrictMono.liftRingHom (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) strictMono_succ (lvlMap π τ) (lvlMap_compat π τ hτ_succ)

include hR'c hτ_succ in
theorem ι_sub_mem (n : ℕ) (z : (R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A')) (y : R') (h : τ n (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y) :
    ι π τ hR'c hτ_succ z - y ∈ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)} := by
  haveI := hR'c
  rw [← hIpow (S := S) (R' := R') π n, ← Ideal.Quotient.eq]
  have := IsAdicComplete.StrictMono.mk_liftRingHom (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) strictMono_succ (lvlMap π τ)
    (lvlMap_compat π τ hτ_succ) (n := n) z
  rw [lvlMap_apply π τ n z y h] at this
  exact this

include hR'c hτ_succ in
theorem τ_mk (n : ℕ) (z : (R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A')) : τ n (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ (ι π τ hR'c hτ_succ z) := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (τ n (Ideal.Quotient.mk _ z))
  rw [← hy]
  exact (Ideal.Quotient.eq.mpr (ι_sub_mem π τ hR'c hτ_succ n z y hy.symm)).symm

include hR'c hτ_succ in
theorem ι_mem (n : ℕ) (u : (R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A')) (hu : u ∈ Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) : ι π τ hR'c hτ_succ u ∈ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  rw [map_mul]
  apply Ideal.mul_mem_left
  have h00 : Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) ((algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have h0 : τ n (Ideal.Quotient.mk _ ((algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A'))) = Ideal.Quotient.mk _ 0 := by
    rw [h00, (τ n).map_zero, (Ideal.Quotient.mk _).map_zero]
  have := ι_sub_mem π τ hR'c hτ_succ n _ 0 h0
  rwa [sub_zero] at this

theorem eq_zero_of_forall_mem (hR'c : IsAdicComplete (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) R') (u : R')
    (hu : ∀ n : ℕ, u ∈ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)}) : u = 0 := by
  refine IsHausdorff.haus hR'c.toIsHausdorff u (fun k => ?_)
  rw [smodEq_span_pow_top_iff, sub_zero]
  cases k with
  | zero => rw [pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top
  | succ n => exact hu n

set_option maxHeartbeats 1600000 in

theorem τ_ρ
    (hτ_smul : ∀ (n : ℕ) (g : G) (x : R) (w : A') (y : R'),
      τ n (Ideal.Quotient.mk _ (x ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ y →
      τ n (Ideal.Quotient.mk _ ((g • x) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ (g • y))
    (n : ℕ) (g : G) : ∀ (z : (R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A')) (y : R'), τ n (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y →
      τ n (Ideal.Quotient.mk _ ((ρ (𝒪 := 𝒪) (R := R) (G := G) A' g) z)) = Ideal.Quotient.mk _ (g • y) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
    intro y h
    rw [(Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')})).map_zero, (τ n).map_zero] at h
    rw [(ρ (𝒪 := 𝒪) (R := R) (G := G) A' g).map_zero, (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')})).map_zero, (τ n).map_zero]
    have hy : y ∈ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)} := Ideal.Quotient.eq_zero_iff_mem.mp h.symm
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr (smul_mem_span_pow _ _ g hy)).symm
  | tmul x w =>
    intro y h
    rw [ρ_tmul]
    exact hτ_smul n g x w y h
  | add z₁ z₂ h₁ h₂ =>
    intro y h
    obtain ⟨y₁, hy₁⟩ := Ideal.Quotient.mk_surjective (τ n (Ideal.Quotient.mk _ z₁))
    have hsum : τ n (Ideal.Quotient.mk _ z₁) + τ n (Ideal.Quotient.mk _ z₂) = Ideal.Quotient.mk _ y := by
      rw [← (τ n).map_add, ← (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')})).map_add]; exact h
    have h₂' : τ n (Ideal.Quotient.mk _ z₂) = Ideal.Quotient.mk _ (y - y₁) := by
      rw [(Ideal.Quotient.mk (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)})).map_sub, ← hsum, ← hy₁, add_sub_cancel_left]
    have e1 := h₁ y₁ hy₁.symm
    have e2 := h₂ (y - y₁) h₂'
    rw [(ρ (𝒪 := 𝒪) (R := R) (G := G) A' g).map_add, (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')})).map_add, (τ n).map_add, e1, e2,
      ← (Ideal.Quotient.mk (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)})).map_add, smul_sub, add_sub_cancel]

variable (hτ_smul : ∀ (n : ℕ) (g : G) (x : R) (w : A') (y : R'),
      τ n (Ideal.Quotient.mk _ (x ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ y →
      τ n (Ideal.Quotient.mk _ ((g • x) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ (g • y))

include hR'c hτ_succ hτ_smul in
theorem smul_ι_one_tmul (w : A') (g : G) :
    g • ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w) = ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem π hR'c _ (fun n => ?_)
  have h1 := τ_mk π τ hR'c hτ_succ n ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)
  have h2 := τ_ρ π τ hτ_smul n g _ _ h1
  rw [ρ_tmul, smul_one] at h2
  have h3 := Ideal.Quotient.eq.mp (h1.symm.trans h2)
  rw [← neg_sub]
  exact (Ideal.neg_mem_iff _).mpr h3

noncomputable def j : A' →+* ↥(FixedPoints.subalgebra S R' G) where
  toFun w := ⟨ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w),
    (mem_fixedPoints_subalgebra_iff (A := S) _).mpr (smul_ι_one_tmul π τ hR'c hτ_succ hτ_smul w)⟩
  map_one' := Subtype.ext (by
    show ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')) = 1
    rw [← Algebra.TensorProduct.one_def, map_one])
  map_mul' w₁ w₂ := Subtype.ext (by
    show ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (w₁ * w₂)) =
      ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w₁) * ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w₂)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul])
  map_zero' := Subtype.ext (by
    show ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (0 : A')) = 0
    rw [TensorProduct.tmul_zero, map_zero])
  map_add' w₁ w₂ := Subtype.ext (by
    show ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (w₁ + w₂)) =
      ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w₁) + ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w₂)
    rw [TensorProduct.tmul_add, map_add])

theorem coe_j (w : A') : ((j π τ hR'c hτ_succ hτ_smul w : ↥(FixedPoints.subalgebra S R' G)) : R') = ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w) := rfl

include hR'c hτ_succ hτ_smul in
theorem j_σ (σ : S →+* A')
    (hτ_σ : ∀ (n : ℕ) (s : S),
      τ n (Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] σ s)) = Ideal.Quotient.mk _ (algebraMap S R' s)) (s : S) :
    j π τ hR'c hτ_succ hτ_smul (σ s) = algebraMap S ↥(FixedPoints.subalgebra S R' G) s := by
  apply Subtype.ext
  rw [coe_j, Subalgebra.coe_algebraMap, ← sub_eq_zero]
  exact eq_zero_of_forall_mem π hR'c _ (fun n => ι_sub_mem π τ hR'c hτ_succ n _ _ (hτ_σ n s))

end Lift
p2m_reactivate "P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_of_ringEquiv_tensorProduct_quotient.C3Alg"

end C3Alg
p2m_reactivate "P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_of_ringEquiv_tensorProduct_quotient.C3Alg"

set_option maxHeartbeats 1600000 in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    (hRc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (hRtf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0)
    (hRft : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}))
    (G : Type) [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R]

    (S : Type) [CommRing S] [Algebra 𝒪 S]
    (A' : Type) [CommRing A'] [Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A'] [Module.Flat ↥(FixedPoints.subalgebra 𝒪 R G) A']
    (σ : S →+* A')
    (hσ : ∀ o : 𝒪, σ (algebraMap 𝒪 S o) =
      algebraMap ↥(FixedPoints.subalgebra 𝒪 R G) A' (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o))

    (R' : Type) [CommRing R'] [Algebra S R'] [MulSemiringAction G R'] [SMulCommClass G S R']
    (hR'c : IsAdicComplete (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) R')
    (hR'tf : ∀ x : R', algebraMap S R' (algebraMap 𝒪 S π) * x = 0 → x = 0)
    (τ : ∀ n : ℕ, ((R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') ⧸
        Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) ≃+*
      (R' ⧸ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)}))
    (hτ_succ : ∀ (n : ℕ) (z : R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') (y : R'),
      τ (n + 1) (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y → τ n (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y)
    (hτ_smul : ∀ (n : ℕ) (g : G) (x : R) (w : A') (y : R'),
      τ n (Ideal.Quotient.mk _ (x ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ y →
      τ n (Ideal.Quotient.mk _ ((g • x) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ (g • y))
    (hτ_σ : ∀ (n : ℕ) (s : S),
      τ n (Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] σ s)) = Ideal.Quotient.mk _ (algebraMap S R' s)) :
    IsAdicComplete (Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) (algebraMap 𝒪 S π)}) ↥(FixedPoints.subalgebra S R' G) ∧
    ∃ α : ∀ n : ℕ, (A' ⧸ Ideal.span {σ (algebraMap 𝒪 S π) ^ (n + 1)}) ≃+*
        (↥(FixedPoints.subalgebra S R' G) ⧸ Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) (algebraMap 𝒪 S π) ^ (n + 1)}),
      (∀ (n : ℕ) (w : A') (x : ↥(FixedPoints.subalgebra S R' G)),
        α (n + 1) (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ x → α n (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ x) ∧
      (∀ (n : ℕ) (w : A') (x : ↥(FixedPoints.subalgebra S R' G)),
        α n (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ x →
        τ n (Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ (x : R')) ∧
      (∀ (n : ℕ) (s : S),
        α n (Ideal.Quotient.mk _ (σ s)) = Ideal.Quotient.mk _ (algebraMap S ↥(FixedPoints.subalgebra S R' G) s)) := by
  classical
  refine ⟨C3Alg.fixedPoints_isAdicComplete (S := S) (R := R') G (algebraMap 𝒪 S π) hR'c hR'tf, ?_⟩

  have hQ1 := AlgebraicGeometry.AdmissibleAlgebra.fixedPoints_isAdicComplete_and_finite_and_finiteType
    𝒪 hdvr π hπ hcomplete R hRc hRtf hRft G
  obtain ⟨-, -, -, hinv⟩ := hQ1
  have hALG := AlgebraicGeometry.AdmissibleAlgebra.exists_forall_sub_tmul_mem_span_pow_of_flat
    𝒪 hdvr π hπ hcomplete R hRc hRtf hRft G
  obtain ⟨e, he⟩ := hALG
  have hρ : ∀ (g : G) (r : R) (s : A'), (C3Alg.ρ (𝒪 := 𝒪) (R := R) (G := G) A' g) (r ⊗ₜ s) = (g • r) ⊗ₜ s :=
    fun g r s => C3Alg.ρ_tmul (𝒪 := 𝒪) (R := R) (G := G) A' g r s

  have hι := C3Alg.ι_sub_mem π τ hR'c hτ_succ
  have hι' := C3Alg.τ_mk π τ hR'c hτ_succ
  have hιI := C3Alg.ι_mem π τ hR'c hτ_succ
  have hτG := C3Alg.τ_ρ π τ hτ_smul
  have hj := C3Alg.coe_j π τ hR'c hτ_succ hτ_smul
  have hjσ := C3Alg.j_σ π τ hR'c hτ_succ hτ_smul σ hτ_σ

  have hle : ∀ n : ℕ, Ideal.span {σ (algebraMap 𝒪 S π) ^ (n + 1)} ≤ (Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) (algebraMap 𝒪 S π) ^ (n + 1)}).comap (C3Alg.j π τ hR'c hτ_succ hτ_smul) := fun n => by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow, hjσ]
    exact Ideal.subset_span rfl
  have hmemT : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra S R' G)), x ∈ Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) (algebraMap 𝒪 S π) ^ (n + 1)} ↔ (x : R') ∈ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)} :=
    fun n x => (C3Alg.coe_mem_span_pow_iff G (algebraMap 𝒪 S π) hR'tf (n + 1) x).symm
  have hσπ : σ (algebraMap 𝒪 S π) = algebraMap ↥(FixedPoints.subalgebra 𝒪 R G) A' (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π) := hσ π
  have hαh_iff : ∀ (n : ℕ) (w : A') (x : ↥(FixedPoints.subalgebra S R' G)),
      Ideal.quotientMap _ (C3Alg.j π τ hR'c hτ_succ hτ_smul) (hle n) (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ x ↔
        C3Alg.ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w) - (x : R') ∈ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)} := by
    intro n w x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, hmemT, AddSubgroupClass.coe_sub, hj]

  have hinjα : ∀ n : ℕ, Function.Injective (Ideal.quotientMap _ (C3Alg.j π τ hR'c hτ_succ hτ_smul) (hle n)) := by
    intro n u v huv
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [Ideal.Quotient.eq]
    rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.eq, ← map_sub, hmemT, hj] at huv
    have h1 : τ n (Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (w - w'))) = 0 := by
      rw [hι', Ideal.Quotient.eq_zero_iff_mem]; exact huv
    have h2 : Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (w - w')) = 0 :=
      (τ n).injective (by rw [h1, (τ n).map_zero])
    have h3 := C3Alg.mem_span_pow_of_tmul_mem π hinv A' (n + 1) (w - w') (Ideal.Quotient.eq_zero_iff_mem.mp h2)
    rwa [← hσπ] at h3

  have hsurjα : ∀ n : ℕ, Function.Surjective (Ideal.quotientMap _ (C3Alg.j π τ hR'c hτ_succ hτ_smul) (hle n)) := by
    intro n v
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective v
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((τ (n + e)).symm (Ideal.Quotient.mk _ (x : R')))
    have hz' : τ (n + e) (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ (x : R') := by
      rw [hz, RingEquiv.apply_symm_apply]
    have hzG : ∀ g : G, (C3Alg.ρ (𝒪 := 𝒪) (R := R) (G := G) A' g) z - z ∈
        Ideal.span {(algebraMap 𝒪 R π ^ (n + 1 + e)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')} := by
      intro g
      have h1 := hτG (n + e) g z (x : R') hz'
      have hgx : g • (x : R') = x := (C3Alg.mem_fixedPoints_subalgebra_iff (A := S) (x : R')).mp x.2 g
      rw [hgx, ← hz'] at h1
      have h2 := Ideal.Quotient.eq.mp ((τ (n + e)).injective h1)
      rwa [Nat.add_right_comm n e 1] at h2
    obtain ⟨w, hw⟩ := he A' (C3Alg.ρ (𝒪 := 𝒪) (R := R) (G := G) A') hρ (n + 1) z hzG
    refine ⟨Ideal.Quotient.mk _ w, ?_⟩
    rw [hαh_iff]
    have h1 : C3Alg.ι π τ hR'c hτ_succ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w) - (x : R') =
        -(C3Alg.ι π τ hR'c hτ_succ (z - (1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) + (C3Alg.ι π τ hR'c hτ_succ z - (x : R')) := by
      rw [map_sub]; abel
    rw [h1]
    refine Ideal.add_mem _ ((Ideal.neg_mem_iff _).mpr (hιI n _ hw)) ?_
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (by omega)) (hι (n + e) z _ hz')

  refine ⟨fun n => RingEquiv.ofBijective _ ⟨hinjα n, hsurjα n⟩, ?_, ?_, ?_⟩
  · intro n w x h
    have h' := (hαh_iff (n + 1) w x).mp h
    exact (hαh_iff n w x).mpr (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (by omega)) h')
  · intro n w x h
    have h' := (hαh_iff n w x).mp h
    exact (hι' n _).trans (Ideal.Quotient.eq.mpr h')
  · intro n s
    show Ideal.quotientMap _ (C3Alg.j π τ hR'c hτ_succ hτ_smul) (hle n) (Ideal.Quotient.mk _ (σ s)) = _
    rw [Ideal.quotientMap_mk, hjσ]

end S_AlgebraicGeometry_AdmissibleAlgebra_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_of_ringEquiv_tensorProduct_quotient
end P2MW
export P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_of_ringEquiv_tensorProduct_quotient (solution)
