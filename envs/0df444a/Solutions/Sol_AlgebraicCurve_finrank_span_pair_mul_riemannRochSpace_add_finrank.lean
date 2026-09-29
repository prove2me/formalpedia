-- Prove2me | solution 1 for AlgebraicCurve.finrank_span_pair_mul_riemannRochSpace_add_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8b450d35-3eda-5511-a4c5-65ae3f4f487c

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finrank_span_pair_mul_riemannRochSpace_add_finrank

set_option autoImplicit false

namespace P2MBrick

open Submodule AlgebraicCurve

theorem ord_neg' {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (x : F) :
    w.ord (-x) = w.ord x := by
  simp only [Place.ord, Valuation.map_neg]

theorem mul_mem_riemannRochSpace_add {K F : Type*} [Field K] [Field F] [Algebra K F]
    {A B : Divisor K F} {f g : F} (hf : f ∈ riemannRochSpace A) (hg : g ∈ riemannRochSpace B) :
    f * g ∈ riemannRochSpace (A + B) := by
  rw [mem_riemannRochSpace_iff] at hf hg ⊢
  intro w
  rcases eq_or_ne f 0 with rfl | hf0
  · left; rw [zero_mul]
  rcases eq_or_ne g 0 with rfl | hg0
  · left; rw [mul_zero]
  right
  rw [Place.ord_mul _ hf0 hg0, Finsupp.add_apply, neg_add]
  exact add_le_add ((hf w).resolve_left hf0) ((hg w).resolve_left hg0)

end P2MBrick

open Submodule AlgebraicCurve P2MBrick in

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (L M : AlgebraicCurve.Divisor K F) {f₁ f₂ : F} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (h₁ : ∀ w : AlgebraicCurve.Place K F, 0 ≤ w.ord f₁ + L w)
    (h₂ : ∀ w : AlgebraicCurve.Place K F, 0 ≤ w.ord f₂ + L w)
    (hbpf : ∀ w : AlgebraicCurve.Place K F, w.ord f₁ + L w = 0 ∨ w.ord f₂ + L w = 0)
    [FiniteDimensional K ↥(AlgebraicCurve.riemannRochSpace M)] :
    Module.finrank K ↥(Submodule.span K {f₁, f₂} * AlgebraicCurve.riemannRochSpace M)
        + Module.finrank K ↥(AlgebraicCurve.riemannRochSpace (M - L))
      = 2 * Module.finrank K ↥(AlgebraicCurve.riemannRochSpace M) ∧
    Submodule.span K {f₁, f₂} * AlgebraicCurve.riemannRochSpace M ≤ AlgebraicCurve.riemannRochSpace (M + L) := by
  classical
  set LM : Submodule K F := riemannRochSpace M with hLM
  have hf₁L : f₁ ∈ riemannRochSpace L := mem_riemannRochSpace_iff.mpr fun w => Or.inr (by linarith [h₁ w])
  have hf₂L : f₂ ∈ riemannRochSpace L := mem_riemannRochSpace_iff.mpr fun w => Or.inr (by linarith [h₂ w])

  have hle : span K {f₁, f₂} * LM ≤ riemannRochSpace (M + L) := by
    rw [mul_le]
    intro m hm n hn
    obtain ⟨α, β, rfl⟩ := mem_span_pair.mp hm
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
    refine add_mem (smul_mem _ α ?_) (smul_mem _ β ?_)
    · rw [mul_comm]; exact mul_mem_riemannRochSpace_add hn hf₁L
    · rw [mul_comm]; exact mul_mem_riemannRochSpace_add hn hf₂L
  refine ⟨?_, hle⟩

  let Φ : (↥LM × ↥LM) →ₗ[K] F :=
    (LinearMap.mulRight K f₁).comp (LM.subtype.comp (LinearMap.fst K ↥LM ↥LM))
      + (LinearMap.mulRight K f₂).comp (LM.subtype.comp (LinearMap.snd K ↥LM ↥LM))
  have hΦ : ∀ ab : ↥LM × ↥LM, Φ ab = (ab.1 : F) * f₁ + (ab.2 : F) * f₂ := fun _ => rfl

  have hrange : LinearMap.range Φ = span K {f₁, f₂} * LM := by
    apply le_antisymm
    · rintro _ ⟨ab, rfl⟩
      rw [hΦ]
      refine add_mem ?_ ?_
      · exact mul_mem_mul_rev (subset_span (Set.mem_insert f₁ {f₂})) ab.1.2
      · exact mul_mem_mul_rev (subset_span (Set.mem_insert_of_mem f₁ (Set.mem_singleton f₂))) ab.2.2
    · rw [mul_le]
      intro m hm n hn
      obtain ⟨α, β, rfl⟩ := mem_span_pair.mp hm
      refine ⟨(⟨α • n, LM.smul_mem α hn⟩, ⟨β • n, LM.smul_mem β hn⟩), ?_⟩
      rw [hΦ]
      simp only [Algebra.smul_def]
      ring

  have hc₂ : ∀ c ∈ riemannRochSpace (M - L), c * f₂ ∈ LM := by
    intro c hc
    have := mul_mem_riemannRochSpace_add hc hf₂L
    rwa [sub_add_cancel] at this
  have hc₁ : ∀ c ∈ riemannRochSpace (M - L), -(c * f₁) ∈ LM := by
    intro c hc
    apply Submodule.neg_mem
    have := mul_mem_riemannRochSpace_add hc hf₁L
    rwa [sub_add_cancel] at this
  let ψ : ↥(riemannRochSpace (M - L)) →ₗ[K] ↥(LinearMap.ker Φ) :=
    { toFun := fun c => ⟨(⟨(c : F) * f₂, hc₂ c c.2⟩, ⟨-((c : F) * f₁), hc₁ c c.2⟩), by
        rw [LinearMap.mem_ker, hΦ]; simp only; ring⟩
      map_add' := fun c c' => by
        apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext <;>
          simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add] <;> ring
      map_smul' := fun r c => by
        apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext <;>
          simp only [Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Algebra.smul_def] <;>
          ring }
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro c c' h
      have h1 : (c : F) * f₂ = (c' : F) * f₂ :=
        congrArg (fun z : ↥(LinearMap.ker Φ) => ((z : ↥LM × ↥LM).1 : F)) h
      exact Subtype.ext (mul_right_cancel₀ hf₂ h1)
    · rintro ⟨⟨a, b⟩, hab⟩
      rw [LinearMap.mem_ker, hΦ] at hab
      have hc : (a : F) * f₂⁻¹ ∈ riemannRochSpace (M - L) := by
        rw [mem_riemannRochSpace_iff]
        intro w
        rcases eq_or_ne (a : F) 0 with ha0 | ha0
        · left; rw [ha0, zero_mul]
        right
        have hb0 : (b : F) ≠ 0 := by
          intro hb0
          apply ha0
          have : (a : F) * f₁ = 0 := by rw [hb0, zero_mul, add_zero] at hab; exact hab
          exact (mul_eq_zero.mp this).resolve_right hf₁
        have ha := (mem_riemannRochSpace_iff.mp a.2 w).resolve_left ha0
        have hb := (mem_riemannRochSpace_iff.mp b.2 w).resolve_left hb0
        have hord : w.ord (a : F) + w.ord f₁ = w.ord (b : F) + w.ord f₂ := by
          have h' : (a : F) * f₁ = -((b : F) * f₂) := by linear_combination hab
          have := congrArg w.ord h'
          rwa [Place.ord_mul _ ha0 hf₁, P2MBrick.ord_neg', Place.ord_mul _ hb0 hf₂] at this
        rw [Place.ord_mul _ ha0 (inv_ne_zero hf₂), Place.ord_inv, Finsupp.sub_apply]
        rcases hbpf w with hw | hw
        · linarith
        · linarith
      refine ⟨⟨(a : F) * f₂⁻¹, hc⟩, ?_⟩
      apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext
      · show (a : F) * f₂⁻¹ * f₂ = a
        rw [inv_mul_cancel_right₀ hf₂]
      · show -((a : F) * f₂⁻¹ * f₁) = b
        field_simp
        linear_combination -hab
  have hker : Module.finrank K ↥(LinearMap.ker Φ) = Module.finrank K ↥(riemannRochSpace (M - L)) :=
    (LinearEquiv.ofBijective ψ hψbij).finrank_eq.symm
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hrange, hker, Module.finrank_prod] at hrn
  omega

end S_AlgebraicCurve_finrank_span_pair_mul_riemannRochSpace_add_finrank
end P2MW
export P2MW.S_AlgebraicCurve_finrank_span_pair_mul_riemannRochSpace_add_finrank (solution)
