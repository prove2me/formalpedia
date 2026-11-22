-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete
-- name    : Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:16:13.730591+00:00
-- url     : https://prove2.me/theorems/4a16b72a-a30a-4d3e-bf04-a803fdb79a8e
-- title:
--   Is Local Ring Of Complete
-- statement:
--   Definitions and structural lemmas for Is Local Ring Of Complete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/IsLocalRingOfComplete.lean

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace Formalism.L2.G.IntCl
theorem ideal_smul_top_le_comap_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (g : M →ₗ[R] N) :
    (J • ⊤ : Submodule R M) ≤ (J • ⊤ : Submodule R N).comap g :=
  Submodule.smul_le.mpr fun r hr m _ => by
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
theorem sModEq_ideal_smul_top_map {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (g : M →ₗ[R] N) {x y : M}
    (h : x ≡ y [SMOD (J • ⊤ : Submodule R M)]) : g x ≡ g y [SMOD (J • ⊤ : Submodule R N)] := by
  rw [SModEq.sub_mem] at h ⊢
  rw [← map_sub]
  exact ideal_smul_top_le_comap_smul_top J g h
theorem precomplete_equiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (e : M ≃ₗ[R] N) [IsPrecomplete I M] : IsPrecomplete I N := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete I M).prec (f := fun n => e.symm (f n))
    (fun hmn => sModEq_ideal_smul_top_map _ e.symm.toLinearMap (hf hmn))
  refine ⟨e L, fun n => ?_⟩
  have := sModEq_ideal_smul_top_map _ e.toLinearMap (hL n)
  simpa using this
theorem mem_ideal_smul_top_pi_iff' {R : Type*} [CommRing R] {n : ℕ} (J : Ideal R) (x : Fin n → R) :
    x ∈ (J • ⊤ : Submodule R (Fin n → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on (p := fun y : Fin n → R => y i ∈ J) hx ?_ ?_
    · intro r hr y _
      simpa using J.mul_mem_right (y i) hr
    · intro y z hy hz
      simpa using J.add_mem hy hz
  · intro h
    rw [pi_eq_sum_univ x]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem_smul (h i) Submodule.mem_top
theorem isPrecomplete_fin_pi {R : Type*} [CommRing R] (J : Ideal R) [IsPrecomplete J R] (n : ℕ) :
    IsPrecomplete J (Fin n → R) := by
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ L : R, ∀ k, f k i ≡ L [SMOD (J ^ k • ⊤ : Submodule R R)] := fun i =>
    (inferInstance : IsPrecomplete J R).prec (f := fun k => f k i) fun {a b} hab => by
      have h := hf hab
      rw [SModEq.sub_mem, mem_ideal_smul_top_pi_iff'] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      simpa using h i
  choose L hL using hc
  refine ⟨L, fun k => ?_⟩
  rw [SModEq.sub_mem, mem_ideal_smul_top_pi_iff']
  intro i
  have h := hL i k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  simpa using h
theorem isLocalRing_of_complete {B : Type*} [CommRing B] [IsDedekindDomain B] (I : Ideal B)
    (hI : I ≠ ⊥) [IsAdicComplete I B] : IsLocalRing B := by
  have hjac : ∀ P : Ideal B, P.IsMaximal → I ≤ P := fun P hP =>
    (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hP⟩)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal B
  refine IsLocalRing.of_unique_max_ideal ⟨P, hP, fun Q hQ => ?_⟩
  by_contra hne
  have hIP := hjac P hP
  have hIQ := hjac Q hQ
  have hI0 : (I : Ideal B) ≠ 0 := hI
  have hPu : ¬ IsUnit P := by
    rw [Ideal.isUnit_iff]
    exact hP.ne_top
  obtain ⟨a, K, hPK, hIeq⟩ := WfDvdMonoid.max_power_factor' hI0 hPu
  have hPK' : ¬ K ≤ P := fun h => hPK (Ideal.dvd_iff_le.mpr h)
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hIeq
    exact hPK' (hIeq ▸ hIP)
  have hKQ : K ≤ Q := by
    have hle : P ^ a * K ≤ Q := hIeq ▸ hIQ
    rcases (Ideal.IsPrime.mul_le hQ.isPrime).mp hle with h | h
    · haveI := hQ.isPrime
      exact absurd (hP.eq_of_le hQ.ne_top (Ideal.IsPrime.le_of_pow_le h)).symm hne
    · exact h
  have hsup : P ⊔ K = ⊤ :=
    hP.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hPK' (by rw [h]; exact le_sup_right))
  have hcop : P ^ a ⊔ K = ⊤ := Ideal.pow_sup_eq_top hsup
  have hone : (1 : B) ∈ P ^ a ⊔ K := by
    rw [hcop]
    exact Submodule.mem_top
  obtain ⟨j, hj, k, hk, hjk⟩ := Submodule.mem_sup.mp hone
  have hIle1 : I ≤ P ^ a := by
    rw [hIeq]
    exact Ideal.mul_le.mpr fun r hr s _ => (P ^ a).mul_mem_right s hr
  have hIle2 : I ≤ K := by
    rw [hIeq]
    exact Ideal.mul_le.mpr fun r _ s hs => K.mul_mem_left r hs
  have hPa_ne : P ^ a ≠ ⊤ := fun h => hP.ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self ha))
  have hK_ne : K ≠ ⊤ := fun h => hQ.ne_top (top_le_iff.mp (h ▸ hKQ))
  let f : B[X] := X ^ 2 - X
  have hfe : ∀ y : B, f.eval y = y ^ 2 - y := fun y => by simp [f]
  have hmon : f.Monic :=
    (monic_X_pow 2).sub_of_left (by rw [degree_X, degree_X_pow]; norm_num)
  have hev : f.eval k ∈ I := by
    have h' : f.eval k = -(j * k) := by
      rw [hfe]
      linear_combination k * hjk
    rw [h', hIeq]
    exact neg_mem (Ideal.mul_mem_mul hj hk)
  have hder : IsUnit (Ideal.Quotient.mk I (f.derivative.eval k)) := by
    have hd : f.derivative.eval k = 2 * k - 1 := by
      simp only [f, derivative_sub, derivative_X_sq, derivative_X, eval_sub, eval_mul, eval_C,
        eval_X, eval_one]
    rw [hd]
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (2 * k - 1)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    have h4 : (2 * k - 1) * (2 * k - 1) - 1 = 4 * f.eval k := by
      rw [hfe]
      ring
    rw [h4]
    exact I.mul_mem_left 4 hev
  obtain ⟨x, hx, hxk⟩ := HenselianRing.is_henselian f hmon k hev hder
  have hx2 : x * (x - 1) = 0 := by
    have h0 : f.eval x = 0 := hx
    rw [hfe] at h0
    linear_combination h0
  rcases mul_eq_zero.mp hx2 with h0 | h1
  · apply hPa_ne
    rw [Ideal.eq_top_iff_one, ← hjk]
    refine (P ^ a).add_mem hj (hIle1 ?_)
    have hkx : k = -(x - k) := by
      rw [h0]
      ring
    rw [hkx]
    exact I.neg_mem hxk
  · apply hK_ne
    rw [Ideal.eq_top_iff_one, ← hjk]
    refine K.add_mem (hIle2 ?_) hk
    have hxj : x - k = j := by
      linear_combination h1 - hjk
    rw [← hxj]
    exact hxk
section Main
open IsLocalRing
variable (A K L : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
  [IsScalarTower A K L]
include K
theorem algL_injective : Function.Injective (algebraMap A L) := by
  rw [IsScalarTower.algebraMap_eq A K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
theorem alg_injective : Function.Injective (algebraMap A (integralClosure A L)) := by
  have h := algL_injective A K L
  rw [IsScalarTower.algebraMap_eq A (integralClosure A L) L, RingHom.coe_comp] at h
  exact h.of_comp
theorem dedekind : IsDedekindDomain (integralClosure A L) :=
  integralClosure.isDedekindDomain A K L
theorem finite : Module.Finite A (integralClosure A L) :=
  IsIntegralClosure.finite (A := A) (K := K) (L := L) (C := integralClosure A L)
theorem free : Module.Free A (integralClosure A L) := by
  have : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).mpr (algL_injective A K L)
  exact IsIntegralClosure.module_free (A := A) (K := K) (L := L) (C := integralClosure A L)
theorem map_ne_bot : (maximalIdeal A).map (algebraMap A (integralClosure A L)) ≠ ⊥ := by
  rw [Ne, Ideal.map_eq_bot_iff_of_injective (alg_injective A K L)]
  exact IsDiscreteValuationRing.not_a_field A
theorem complete_map (hC : IsAdicComplete (maximalIdeal A) A) :
    IsAdicComplete ((maximalIdeal A).map (algebraMap A (integralClosure A L))) (integralClosure A L) := by
  have := finite A K L
  have := free A K L
  rw [IsAdicComplete.map_algebraMap_iff]
  have : IsPrecomplete (maximalIdeal A) (Fin (Module.finrank A (integralClosure A L)) → A) :=
    isPrecomplete_fin_pi _ _
  exact { toIsHausdorff := inferInstance,
          toIsPrecomplete := precomplete_equiv _
            (Module.finBasis A (integralClosure A L)).equivFun.symm }
theorem isLocalRing (hC : IsAdicComplete (maximalIdeal A) A) : IsLocalRing (integralClosure A L) := by
  have := dedekind A K L
  have := complete_map A K L hC
  exact isLocalRing_of_complete _ (map_ne_bot A K L)
theorem not_isField : ¬ IsField (integralClosure A L) := by
  intro h
  have hA : IsField A :=
    (Algebra.IsIntegral.isField_iff_isField (alg_injective A K L)).mpr h
  exact IsDiscreteValuationRing.not_a_field A (IsLocalRing.isField_iff_maximalIdeal_eq.mp hA)
theorem isDVR (hC : IsAdicComplete (maximalIdeal A) A) : IsDiscreteValuationRing (integralClosure A L) := by
  have := dedekind A K L
  have := isLocalRing A K L hC
  exact ((IsDiscreteValuationRing.TFAE (integralClosure A L) (not_isField A K L)).out 2 0).mp
    (dedekind A K L)
end Main
end Formalism.L2.G.IntCl


