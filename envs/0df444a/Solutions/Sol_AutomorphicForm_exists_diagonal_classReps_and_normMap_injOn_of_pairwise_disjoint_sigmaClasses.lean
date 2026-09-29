-- Prove2me | solution 1 for AutomorphicForm.exists_diagonal_classReps_and_normMap_injOn_of_pairwise_disjoint_sigmaClasses
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4ffce83d-28de-5a96-a96b-20c833f3c280

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_diagonal_classReps_and_normMap_injOn_of_pairwise_disjoint_sigmaClasses

set_option autoImplicit false
open scoped Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hgenK : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K))
    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)})
    (hΔcov : {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} ⊆
      ⋃ t ∈ Δ, {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) :
    ∃ (ΔK : Set (GL (Fin 2) K)) (n : GL (Fin 2) L → GL (Fin 2) K),
      (∀ t ∈ ΔK, (t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1) ∧
      (∀ t ∈ ΔK, ∀ t' ∈ ΔK, t ≠ t' →
        Disjoint {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
            t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)}
          {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
            t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)}) ∧
      ({δ : GL (Fin 2) K | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
          LT.TwistedNorm.normClassMap hgenK (LT.TwistedNorm.SigmaConjClasses.mk (1 : K ≃ₐ[K] K) δ) = ConjClasses.mk γ} ⊆
        ⋃ t ∈ ΔK, {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
            t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)}) ∧
      (∀ t ∈ Δ, n t ∈ ΔK ∧
        (n t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (n t : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
        (n t : Matrix (Fin 2) (Fin 2) K) 0 0 = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧
        (n t : Matrix (Fin 2) (Fin 2) K) 1 1 = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ∧
      (∀ t ∈ Δ, ∀ t' ∈ Δ, n t = n t' → t = t') ∧
      (∀ γ ∈ ΔK, (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈
          Set.range (Algebra.norm K : L → K) → ∃ t ∈ Δ, n t = γ) := by
  classical
  obtain ⟨hL1, -, hL3⟩ :=
    LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal (K := K) (L := L) hgen
  obtain ⟨-, hK2, hK3⟩ :=
    LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal (K := K) (L := K) hgenK
  have hnorm : ∀ x : K, Algebra.norm K x = x := fun x => by rw [Algebra.norm_self, MonoidHom.id_apply]
  have hNdiv : ∀ a b : L, b ≠ 0 → Algebra.norm K (a / b) = Algebra.norm K a / Algebra.norm K b := by
    intro a b hb
    rw [eq_div_iff (Algebra.norm_ne_zero_iff.mpr hb), ← map_mul, div_mul_eq_mul_div, mul_div_assoc, div_self hb, mul_one]

  have e00 : ∀ u v : Kˣ, ((diagUnits2 u v : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = (u : K) := fun _ _ => rfl
  have e11 : ∀ u v : Kˣ, ((diagUnits2 u v : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = (v : K) := fun _ _ => rfl
  have e10 : ∀ u v : Kˣ, ((diagUnits2 u v : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := fun _ _ => rfl
  have e01 : ∀ u v : Kˣ, ((diagUnits2 u v : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := fun _ _ => rfl

  let clsK : GL (Fin 2) K → Set (GL (Fin 2) K) := fun t => {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
      t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)}
  let goodK : GL (Fin 2) K → Prop := fun t =>
      ((t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) ∧
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1

  have hent : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
    intro t ht
    have hdet : ((t : Matrix (Fin 2) (Fin 2) L)).det ≠ 0 := (t.isUnit.map Matrix.detMonoidHom).ne_zero
    rw [Matrix.det_fin_two, (hΔd t ht).1, mul_zero, sub_zero] at hdet
    exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩
  have hNz : ∀ t ∈ Δ, Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := fun t ht =>
    ⟨Algebra.norm_ne_zero_iff.mpr (hent t ht).1, Algebra.norm_ne_zero_iff.mpr (hent t ht).2⟩

  let n : GL (Fin 2) L → GL (Fin 2) K := fun t =>
    if h : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ 0 ∧ Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0
    then diagUnits2 (Units.mk0 _ h.1) (Units.mk0 _ h.2) else 1
  have hn : ∀ t (ht : t ∈ Δ), n t = diagUnits2 (Units.mk0 _ (hNz t ht).1) (Units.mk0 _ (hNz t ht).2) := by
    intro t ht
    simp only [n, dif_pos (hNz t ht)]
  have hn00 : ∀ t ∈ Δ, ((n t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) := by
    intro t ht; rw [hn t ht, e00]; rfl
  have hn11 : ∀ t ∈ Δ, ((n t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) := by
    intro t ht; rw [hn t ht, e11]; rfl
  have hn10 : ∀ t ∈ Δ, ((n t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    intro t ht; rw [hn t ht, e10]
  have hn01 : ∀ t ∈ Δ, ((n t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    intro t ht; rw [hn t ht, e01]
  have hngood : ∀ t ∈ Δ, goodK (n t) := by
    intro t ht
    refine ⟨⟨hn10 t ht, hn01 t ht⟩, ?_⟩
    rw [hn00 t ht, hn11 t ht, hnorm, ← hNdiv _ _ (hent t ht).2]
    exact (hΔd t ht).2.2

  have hcls_inj : ∀ t ∈ Δ, ∀ t' ∈ Δ, clsK (n t') = clsK (n t) → t' = t := by
    intro t ht t' ht' h
    by_contra hne
    have hdis := hΔdisj t ht t' ht' (Ne.symm hne)
    have h3 := ((hK3 (n t) (n t') (hngood t ht).1 (hngood t' ht').1).2).mp h
    rw [hn00 t ht, hn11 t ht, hn00 t' ht', hn11 t' ht'] at h3
    simp only [hnorm] at h3
    obtain ⟨ζ', hζ', hcase⟩ := h3
    have hIeq : {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} =
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} := by
      refine ((hL3 t t' ⟨(hΔd t ht).1, (hΔd t ht).2.1⟩ ⟨(hΔd t' ht').1, (hΔd t' ht').2.1⟩).2).mpr ?_
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨(t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 0 0,
          div_ne_zero (hent t' ht').1 (hent t ht).1, Or.inl ?_⟩
        have hNζ : Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 0 0) = ζ' := by
          rw [hNdiv _ _ (hent t ht).1, h1, mul_div_cancel_right₀ _ (hNz t ht).1]
        rw [hNζ]
        exact ⟨h1, h2⟩
      · refine ⟨(t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1,
          div_ne_zero (hent t' ht').1 (hent t ht).2, Or.inr ?_⟩
        have hNζ : Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = ζ' := by
          rw [hNdiv _ _ (hent t ht).2, h1, mul_div_cancel_right₀ _ (hNz t ht).2]
        rw [hNζ]
        exact ⟨h1, h2⟩
    have hne' := ((hL3 t t' ⟨(hΔd t ht).1, (hΔd t ht).2.1⟩ ⟨(hΔd t' ht').1, (hΔd t' ht').2.1⟩).1).mpr hIeq
    rw [Set.inter_comm] at hne'
    exact (Set.disjoint_iff_inter_eq_empty.mp hdis ▸ hne') |>.ne_empty rfl

  let SS : Set (Set (GL (Fin 2) K)) := {s | ∃ t, goodK t ∧ clsK t = s}
  have hSS : ∀ s : SS, ∃ t, goodK t ∧ clsK t = (s : Set (GL (Fin 2) K)) := fun s => s.2
  choose dflt hdflt using hSS
  let pick : SS → GL (Fin 2) K := fun s =>
    if h : ∃ t ∈ Δ, clsK (n t) = (s : Set (GL (Fin 2) K)) then n h.choose else dflt s
  have hpick : ∀ s : SS, goodK (pick s) ∧ clsK (pick s) = (s : Set (GL (Fin 2) K)) := by
    intro s
    by_cases h : ∃ t ∈ Δ, clsK (n t) = (s : Set (GL (Fin 2) K))
    · simp only [pick, dif_pos h]
      exact ⟨hngood _ h.choose_spec.1, h.choose_spec.2⟩
    · simp only [pick, dif_neg h]
      exact hdflt s
  refine ⟨Set.range pick, n, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(hpick s).1.1.1, (hpick s).1.1.2, (hpick s).1.2⟩
  · rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩ hne
    have hss : (s : Set (GL (Fin 2) K)) ≠ s' := fun h => hne (by rw [Subtype.ext h])
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne'
    have h := ((hK3 (pick s') (pick s) (hpick s').1.1 (hpick s).1.1).1).mp hne'
    exact hss (by rw [← (hpick s).2, ← (hpick s').2]; exact h)
  · intro δ hδ
    obtain ⟨t, htd, htN, ht⟩ := hK2 δ hδ
    have hs : clsK t ∈ SS := ⟨t, ⟨htd, htN⟩, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨pick ⟨_, hs⟩, ⟨⟨_, hs⟩, rfl⟩, ?_⟩
    show δ ∈ clsK (pick ⟨clsK t, hs⟩)
    rw [(hpick ⟨_, hs⟩).2]
    exact ht
  · intro t ht
    have hs : clsK (n t) ∈ SS := ⟨n t, hngood t ht, rfl⟩
    have hex : ∃ t' ∈ Δ, clsK (n t') = clsK (n t) := ⟨t, ht, rfl⟩
    have hp : pick ⟨clsK (n t), hs⟩ = n t := by
      simp only [pick, dif_pos hex]
      rw [hcls_inj t ht _ hex.choose_spec.1 hex.choose_spec.2]
    exact ⟨⟨⟨clsK (n t), hs⟩, hp⟩, hn10 t ht, hn01 t ht, hn00 t ht, hn11 t ht⟩
  · intro t ht t' ht' h
    exact hcls_inj t' ht' t ht (by rw [h])
  · rintro _ ⟨s, rfl⟩ hr
    by_cases h : ∃ t ∈ Δ, clsK (n t) = (s : Set (GL (Fin 2) K))
    · refine ⟨h.choose, h.choose_spec.1, ?_⟩
      simp only [pick, dif_pos h]
    · exfalso
      apply h
      obtain ⟨w, hw⟩ := hr

      have hg := (hpick s).1
      have hdet : (((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det ≠ 0 :=
        ((pick s).isUnit.map Matrix.detMonoidHom).ne_zero
      rw [Matrix.det_fin_two, hg.1.1, mul_zero, sub_zero] at hdet
      have hγ00 : ((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
      have hγ11 : ((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
      have hr1 : Algebra.norm K w ≠ 1 := by
        rw [hw, ← hnorm (((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 / ((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1)]
        exact hg.2
      have hw0 : w ≠ 0 := Algebra.norm_ne_zero_iff.mp (by rw [hw]; exact div_ne_zero hγ00 hγ11)

      let δ₀ : GL (Fin 2) L := diagUnits2 (Units.mk0 w hw0) 1
      have d00 : ((δ₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = w := rfl
      have d11 : ((δ₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := rfl
      have d10 : ((δ₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := rfl
      have d01 : ((δ₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := rfl
      have hself : δ₀ ∈ {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} :=
        ⟨1, by simp⟩
      have hhyp := hL1 δ₀ ⟨d10, d01⟩ (by rw [d00, d11, div_one]; exact hr1) hself
      obtain ⟨t, ht, hδt⟩ := Set.mem_iUnion₂.mp (hΔcov hhyp)
      have hIeq := ((hL3 t δ₀ ⟨(hΔd t ht).1, (hΔd t ht).2.1⟩ ⟨d10, d01⟩).1).mp ⟨δ₀, hself, hδt⟩
      obtain ⟨ζ, hζ, hcase⟩ := ((hL3 t δ₀ ⟨(hΔd t ht).1, (hΔd t ht).2.1⟩ ⟨d10, d01⟩).2).mp hIeq
      rw [d00, d11, map_one] at hcase
      have hw' : ((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
          Algebra.norm K w * ((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 := by
        rw [hw, div_mul_eq_mul_div, mul_div_assoc, div_self hγ11, mul_one]
      refine ⟨t, ht, ?_⟩
      refine (((hK3 (pick s) (n t) hg.1 (hngood t ht).1).2).mpr ?_).trans (hpick s).2
      rw [hn00 t ht, hn11 t ht]
      simp only [hnorm]
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) / ((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1,
          div_ne_zero (hNz t ht).2 hγ11, Or.inl ⟨?_, ?_⟩⟩
        · rw [div_mul_eq_mul_div, eq_div_iff hγ11]
          linear_combination (-(Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1))) * hw' +
            (-(Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) * ((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1)) * h1 +
            (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) * ((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1) * h2
        · rw [div_mul_eq_mul_div, mul_div_assoc, div_self hγ11, mul_one]
      · refine ⟨Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) / ((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1,
          div_ne_zero (hNz t ht).1 hγ11, Or.inr ⟨?_, ?_⟩⟩
        · rw [div_mul_eq_mul_div, mul_div_assoc, div_self hγ11, mul_one]
        · rw [div_mul_eq_mul_div, eq_div_iff hγ11]
          linear_combination (-(Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0))) * hw' +
            (-(Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) * ((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1)) * h1 +
            (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) * ((pick s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1) * h2

end S_AutomorphicForm_exists_diagonal_classReps_and_normMap_injOn_of_pairwise_disjoint_sigmaClasses
end P2MW
export P2MW.S_AutomorphicForm_exists_diagonal_classReps_and_normMap_injOn_of_pairwise_disjoint_sigmaClasses (solution)
