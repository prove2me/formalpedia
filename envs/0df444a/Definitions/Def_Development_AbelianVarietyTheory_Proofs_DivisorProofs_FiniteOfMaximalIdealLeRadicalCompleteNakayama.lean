-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfMaximalIdealLeRadicalCompleteNakayama
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfMaximalIdealLeRadicalCompleteNakayama
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:31:18.24879+00:00
-- url     : https://prove2.me/theorems/cd28a4dd-ee3f-4897-8a96-3ae6061e03cf
-- title:
--   Finite Of Maximal Ideal Le Radical Complete Nakayama
-- statement:
--   Definitions and structural lemmas for Finite Of Maximal Ideal Le Radical Complete Nakayama, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfMaximalIdealLeRadicalCompleteNakayama.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_FormalIsogeny_finite_of_finite_quotient_map
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X


set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory.CompleteNakayamaLocal
theorem exists_fg_sup_pow_eq_top {B R : Type} [CommRing B] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra B R]
    (hres : Module.Finite B (R ⧸ maximalIdeal R)) (n : ℕ) :
    ∃ P : Submodule B R, P.FG ∧ P ⊔ (maximalIdeal R ^ n).restrictScalars B = ⊤ := by
  obtain ⟨T, hT⟩ := (Module.Finite.fg_top (R := B) (M := R ⧸ maximalIdeal R))
  choose lift hlift using fun x : R ⧸ maximalIdeal R => Ideal.Quotient.mk_surjective x

  have hTop : Submodule.span B (lift '' (T : Set _)) ⊔ (maximalIdeal R).restrictScalars B = ⊤ := by
    rw [eq_top_iff]
    intro r _
    have hr : Ideal.Quotient.mk (maximalIdeal R) r ∈ Submodule.span B (T : Set _) := by
      rw [hT]; trivial
    have hmap : Submodule.span B (T : Set (R ⧸ maximalIdeal R)) =
        (Submodule.span B (lift '' (T : Set _))).map
          (Ideal.Quotient.mkₐ B (maximalIdeal R)).toLinearMap := by
      rw [Submodule.map_span, ← Set.image_comp]
      congr 1
      ext x
      simp [hlift]
    rw [hmap] at hr
    obtain ⟨t, ht, hte⟩ := hr
    have hu : r - t ∈ maximalIdeal R := by
      rw [← Ideal.Quotient.eq]
      simpa using hte.symm
    rw [Submodule.mem_sup]
    exact ⟨t, ht, r - t, hu, by ring⟩
  induction n with
  | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
  | succ n ih =>
    obtain ⟨P, hP, hPtop⟩ := ih
    obtain ⟨gens, hgens⟩ := (IsNoetherian.noetherian (maximalIdeal R ^ n) : (maximalIdeal R ^ n).FG)
    let G : Set R := Set.image2 (· * ·) (lift '' (T : Set _)) (gens : Set R)
    have hGf : G.Finite := ((T.finite_toSet.image _).image2 _ gens.finite_toSet)
    refine ⟨P ⊔ Submodule.span B G, hP.sup (Submodule.fg_def.2 ⟨G, hGf, rfl⟩), ?_⟩

    have key : ∀ y ∈ maximalIdeal R ^ n, ∀ r : R,
        r * y ∈ Submodule.span B G ⊔ (maximalIdeal R ^ (n + 1)).restrictScalars B := by
      intro y hy
      rw [← hgens] at hy
      induction hy using Submodule.span_induction with
      | mem g hg =>
        intro r
        have hr : r ∈ (⊤ : Submodule B R) := trivial
        rw [← hTop, Submodule.mem_sup] at hr
        obtain ⟨t, ht, u, hu, rfl⟩ := hr
        rw [add_mul]
        refine Submodule.add_mem_sup ?_ ?_
        · have : t * g ∈ (Submodule.span B (lift '' (T : Set _))).map (LinearMap.mulRight B g) :=
            ⟨t, ht, rfl⟩
          rw [Submodule.map_span] at this
          refine Submodule.span_mono ?_ this
          rintro _ ⟨s, hs, rfl⟩
          exact ⟨s, hs, g, hg, rfl⟩
        · show u * g ∈ maximalIdeal R ^ (n + 1)
          rw [pow_succ']
          exact Ideal.mul_mem_mul hu (hgens ▸ Submodule.subset_span hg)
      | zero => intro r; simp
      | add a b _ _ ha hb => intro r; rw [mul_add]; exact Submodule.add_mem _ (ha r) (hb r)
      | smul s a _ ha => intro r; rw [smul_eq_mul, ← mul_assoc]; exact ha (r * s)
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (⊤ : Submodule B R) := trivial
    rw [← hPtop, Submodule.mem_sup] at hx
    obtain ⟨p, hp, y, hy, rfl⟩ := hx
    have hy' := key y hy 1
    rw [one_mul, Submodule.mem_sup] at hy'
    obtain ⟨a, ha, c, hc, rfl⟩ := hy'
    rw [Submodule.mem_sup]
    refine ⟨p + a, Submodule.add_mem_sup hp ha, c, hc, by ring⟩
theorem finite_of_maximalIdeal_le_radical : ∀ (B R : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R),
    IsAdicComplete (maximalIdeal B) B → IsLocalHom ψ →
    maximalIdeal R ≤ ((maximalIdeal B).map ψ).radical → ((residue R).comp ψ).Finite →
    ψ.Finite := by
  intro B R _ _ _ _ _ _ ψ hB hψ hrad hres
  letI : Algebra B R := ψ.toAlgebra
  set J : Ideal R := (maximalIdeal B).map (algebraMap B R) with hJdef
  have hJm : J ≤ maximalIdeal R := by
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (mem_maximalIdeal x).1 hx (isUnit_of_map_unit ψ x h)
  haveI : IsHausdorff J R := ⟨fun x hx => IsHausdorff.haus (I := maximalIdeal R) inferInstance x
    fun n => (hx n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJm n))⟩
  obtain ⟨e, he⟩ : ∃ e, maximalIdeal R ^ e ≤ J :=
    Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hres' : Module.Finite B (R ⧸ maximalIdeal R) := hres
  obtain ⟨P, hP, hPtop⟩ := exists_fg_sup_pow_eq_top hres' e
  haveI : Module.Finite B (R ⧸ J) := by
    refine ⟨?_⟩
    have : (⊤ : Submodule B (R ⧸ J)) = P.map (Ideal.Quotient.mkₐ B J).toLinearMap := by
      refine le_antisymm ?_ le_top
      rintro z -
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hx : x ∈ (⊤ : Submodule B R) := trivial
      rw [← hPtop, Submodule.mem_sup] at hx
      obtain ⟨p, hp, y, hy, rfl⟩ := hx
      refine ⟨p, hp, ?_⟩
      show Ideal.Quotient.mk J p = Ideal.Quotient.mk J (p + y)
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 (he hy), add_zero]
    rw [this]
    exact hP.map _
  exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal B)
example : ∀ (B R : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → IsLocalHom ψ → maximalIdeal R ≤ ((maximalIdeal B).map ψ).radical → ((residue R).comp ψ).Finite → ψ.Finite := finite_of_maximalIdeal_le_radical
end GlobalTheory.CompleteNakayamaLocal


