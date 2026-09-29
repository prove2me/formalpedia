-- Prove2me | solution 1 for AlgebraicCurve.transcendental_and_finiteDimensional_adjoin_of_valuations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3aee0dbc-9f73-590c-9622-cd24b29d5197

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_transcendental_and_finiteDimensional_adjoin_of_valuations

set_option autoImplicit false

open scoped WithZero Classical

namespace P2mKcRecognition

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def lSpace (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    (m : Multiset (Valuation F ℤᵐ⁰)) : Submodule K F where
  carrier := {g | ∀ v ∈ V, v g ≤ WithZero.exp ((m.count v : ℕ) : ℤ)}
  add_mem' {a b} ha hb := fun v hv => (Valuation.map_add v a b).trans (max_le (ha v hv) (hb v hv))
  zero_mem' := fun v _ => by simp
  smul_mem' c {g} hg := fun v hv => by
    rw [Algebra.smul_def, map_mul]
    by_cases hc : c = 0
    · simp [hc]
    · rw [hK v hv c hc, one_mul]; exact hg v hv

theorem mem_lSpace_iff (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    (m : Multiset (Valuation F ℤᵐ⁰)) (g : F) :
    g ∈ lSpace V hK m ↔ ∀ v ∈ V, v g ≤ WithZero.exp ((m.count v : ℕ) : ℤ) := Iff.rfl

theorem lSpace_zero_le (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    (hconst : ∀ f : F, (∀ v ∈ V, v f ≤ 1) → f ∈ Set.range (algebraMap K F)) :
    lSpace V hK 0 ≤ Submodule.span K {(1 : F)} := by
  intro g hg
  obtain ⟨c, rfl⟩ := hconst g (fun v hv => by simpa using hg v hv)
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ c (Submodule.subset_span rfl)

theorem lSpace_cons_le (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    (hres : ∀ v ∈ V, ∀ f : F, v f = 1 → ∃ c : K, v (f - algebraMap K F c) < 1)
    (m : Multiset (Valuation F ℤᵐ⁰)) (v₀ : Valuation F ℤᵐ⁰) :
    lSpace V hK (v₀ ::ₘ m) = lSpace V hK m ∨
      ∃ g₀ ∈ lSpace V hK (v₀ ::ₘ m), lSpace V hK (v₀ ::ₘ m) = lSpace V hK m ⊔ Submodule.span K {g₀} := by
  classical
  have hle : lSpace V hK m ≤ lSpace V hK (v₀ ::ₘ m) := fun g hg v hv =>
    (hg v hv).trans (by
      rw [WithZero.exp_le_exp]
      exact_mod_cast Multiset.count_le_count_cons v v₀ m)
  by_cases heq : lSpace V hK (v₀ ::ₘ m) ≤ lSpace V hK m
  · exact Or.inl (le_antisymm heq hle)
  · right
    obtain ⟨g₀, hg₀, hg₀'⟩ := Set.not_subset.1 heq
    refine ⟨g₀, hg₀, le_antisymm ?_ (sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).2 hg₀))⟩
    intro g hg

    have hv₀ : v₀ ∈ V := by
      by_contra hv₀
      apply hg₀'
      intro v hv
      have hne : v ≠ v₀ := fun h => hv₀ (h ▸ hv)
      have := hg₀ v hv
      rwa [Multiset.count_cons_of_ne hne] at this
    set n : ℤ := ((m.count v₀ : ℕ) : ℤ) with hn
    have hcount : (((v₀ ::ₘ m).count v₀ : ℕ) : ℤ) = n + 1 := by
      rw [Multiset.count_cons_self]; push_cast; rw [hn]
    have hg₀v : v₀ g₀ = WithZero.exp (n + 1) := by
      apply le_antisymm
      · have := hg₀ v₀ hv₀; rwa [hcount] at this
      · by_contra hlt
        push Not at hlt
        apply hg₀'
        intro v hv
        by_cases hvv : v = v₀
        · subst hvv

          rcases eq_or_ne (v g₀) 0 with h0 | h0
          · rw [h0]; exact zero_le'
          · rw [← WithZero.exp_log h0] at hlt ⊢
            rw [WithZero.exp_lt_exp] at hlt
            rw [WithZero.exp_le_exp]
            omega
        · have := hg₀ v hv
          rwa [Multiset.count_cons_of_ne hvv] at this

    by_cases hgm : g ∈ lSpace V hK m
    · exact Submodule.mem_sup_left hgm
    · have hgv : v₀ g = WithZero.exp (n + 1) := by
        apply le_antisymm
        · have := hg v₀ hv₀; rwa [hcount] at this
        · by_contra hlt
          push Not at hlt
          apply hgm
          intro v hv
          by_cases hvv : v = v₀
          · subst hvv
            rcases eq_or_ne (v g) 0 with h0 | h0
            · rw [h0]; exact zero_le'
            · rw [← WithZero.exp_log h0] at hlt ⊢
              rw [WithZero.exp_lt_exp] at hlt
              rw [WithZero.exp_le_exp]
              omega
          · have := hg v hv
            rwa [Multiset.count_cons_of_ne hvv] at this
      have hg₀ne : g₀ ≠ 0 := fun h => by rw [h, map_zero] at hg₀v; exact WithZero.exp_ne_zero hg₀v.symm

      have hquot : v₀ (g / g₀) = 1 := by
        rw [map_div₀, hgv, hg₀v, div_self (WithZero.exp_ne_zero)]
      obtain ⟨c, hc⟩ := hres v₀ hv₀ (g / g₀) hquot

      have hdiff : g - c • g₀ ∈ lSpace V hK m := by
        intro v hv
        by_cases hvv : v = v₀
        · subst hvv
          have hmul : g - c • g₀ = (g / g₀ - algebraMap K F c) * g₀ := by
            rw [Algebra.smul_def, sub_mul, div_mul_cancel₀ _ hg₀ne]
          rw [hmul, map_mul, hg₀v]

          have hlt : v (g / g₀ - algebraMap K F c) ≤ WithZero.exp (-1 : ℤ) := by
            rcases eq_or_ne (v (g / g₀ - algebraMap K F c)) 0 with h0 | h0
            · rw [h0]; exact zero_le'
            · rw [← WithZero.exp_log h0] at hc ⊢
              rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hc
              rw [WithZero.exp_le_exp]
              omega
          calc v (g / g₀ - algebraMap K F c) * WithZero.exp (n + 1)
              ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (n + 1) := mul_le_mul_left hlt _
            _ = WithZero.exp n := by rw [← WithZero.exp_add]; congr 1; ring
        · have h1 := hg v hv
          have h2 := hg₀ v hv
          rw [Multiset.count_cons_of_ne hvv] at h1 h2
          refine (Valuation.map_sub v _ _).trans (max_le h1 ?_)
          rw [Algebra.smul_def, map_mul]
          by_cases hc0 : c = 0
          · simp [hc0]
          · rw [hK v hv c hc0, one_mul]; exact h2
      have : g = (g - c • g₀) + c • g₀ := by abel
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hdiff)
        (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.subset_span rfl)))

theorem finite_and_finrank_lSpace_le (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    (hres : ∀ v ∈ V, ∀ f : F, v f = 1 → ∃ c : K, v (f - algebraMap K F c) < 1)
    (hconst : ∀ f : F, (∀ v ∈ V, v f ≤ 1) → f ∈ Set.range (algebraMap K F))
    (m : Multiset (Valuation F ℤᵐ⁰)) :
    Module.Finite K (lSpace V hK m) ∧ Module.finrank K (lSpace V hK m) ≤ Multiset.card m + 1 := by
  induction m using Multiset.induction with
  | empty =>
    have hle := lSpace_zero_le V hK hconst
    haveI : Module.Finite K (Submodule.span K {(1 : F)}) := inferInstance
    refine ⟨Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle), ?_⟩
    rw [Multiset.card_zero, zero_add]
    exact (Submodule.finrank_mono hle).trans ((finrank_span_le_card ({(1 : F)} : Set F)).trans (by simp))
  | cons v₀ m ih =>
    obtain ⟨hfin, hrank⟩ := ih
    rcases lSpace_cons_le V hK hres m v₀ with h | ⟨g₀, -, h⟩
    · rw [h, Multiset.card_cons]
      exact ⟨hfin, hrank.trans (by omega)⟩
    · rw [h, Multiset.card_cons]
      haveI := hfin
      haveI : Module.Finite K (Submodule.span K {g₀}) := inferInstance
      refine ⟨inferInstance, ?_⟩
      calc Module.finrank K ↥(lSpace V hK m ⊔ Submodule.span K {g₀})
          ≤ Module.finrank K (lSpace V hK m) + Module.finrank K (Submodule.span K {g₀}) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
        _ ≤ (Multiset.card m + 1) + 1 := add_le_add hrank
            ((finrank_span_le_card ({g₀} : Set F)).trans (by simp))

theorem lSpace_mono (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    {m m' : Multiset (Valuation F ℤᵐ⁰)} (h : m ≤ m') : lSpace V hK m ≤ lSpace V hK m' := fun g hg v hv =>
  (hg v hv).trans (by
    rw [WithZero.exp_le_exp]
    exact_mod_cast Multiset.count_le_of_le v h)

theorem mul_mem_lSpace (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    {m m' : Multiset (Valuation F ℤᵐ⁰)} {g g' : F} (hg : g ∈ lSpace V hK m) (hg' : g' ∈ lSpace V hK m') :
    g * g' ∈ lSpace V hK (m + m') := fun v hv => by
  rw [map_mul, Multiset.count_add, Nat.cast_add, WithZero.exp_add]
  exact mul_le_mul' (hg v hv) (hg' v hv)

theorem pow_mem_lSpace (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    {m : Multiset (Valuation F ℤᵐ⁰)} {g : F} (hg : g ∈ lSpace V hK m) (i : ℕ) :
    g ^ i ∈ lSpace V hK (i • m) := by
  induction i with
  | zero => intro v hv; simp
  | succ i ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_lSpace V hK ih hg

theorem exists_mem_lSpace (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    (hfin : ∀ f : F, f ≠ 0 → {v ∈ V | 1 < v f}.Finite) (g : F) :
    ∃ m : Multiset (Valuation F ℤᵐ⁰), g ∈ lSpace V hK m := by
  by_cases hg : g = 0
  · exact ⟨0, fun v hv => by simp [hg]⟩
  refine ⟨∑ w ∈ (hfin g hg).toFinset, (WithZero.log (w g)).toNat • ({w} : Multiset (Valuation F ℤᵐ⁰)),
    fun v hv => ?_⟩
  by_cases hlt : 1 < v g
  · have hvS : v ∈ (hfin g hg).toFinset := by rw [Set.Finite.mem_toFinset]; exact ⟨hv, hlt⟩
    have hcount : (WithZero.log (v g)).toNat ≤
        Multiset.count v (∑ w ∈ (hfin g hg).toFinset, (WithZero.log (w g)).toNat • ({w} : Multiset _)) := by
      have hle : (WithZero.log (v g)).toNat • ({v} : Multiset (Valuation F ℤᵐ⁰)) ≤
          ∑ w ∈ (hfin g hg).toFinset, (WithZero.log (w g)).toNat • ({w} : Multiset _) :=
        Finset.single_le_sum (f := fun w => (WithZero.log (w g)).toNat • ({w} : Multiset (Valuation F ℤᵐ⁰)))
          (fun w _ => bot_le) hvS
      have := Multiset.count_le_of_le v hle
      rwa [Multiset.count_nsmul, Multiset.count_singleton_self, mul_one] at this
    have h0 : v g ≠ 0 := ne_of_gt (lt_trans zero_lt_one hlt)
    calc v g = WithZero.exp (WithZero.log (v g)) := (WithZero.exp_log h0).symm
      _ ≤ WithZero.exp (((WithZero.log (v g)).toNat : ℕ) : ℤ) := by
          rw [WithZero.exp_le_exp]; exact Int.self_le_toNat _
      _ ≤ _ := by rw [WithZero.exp_le_exp]; exact_mod_cast hcount
  · push Not at hlt
    refine hlt.trans ?_
    generalize (∑ w ∈ (hfin g hg).toFinset, (WithZero.log (w g)).toNat • ({w} : Multiset (Valuation F ℤᵐ⁰))) = M
    have h1 : (1 : ℤᵐ⁰) = WithZero.exp (0 : ℤ) := WithZero.exp_zero.symm
    rw [h1, WithZero.exp_le_exp]
    positivity

theorem linearIndependent_pow_of_transcendental {f : F} (htr : Transcendental K f) (k : ℕ) :
    LinearIndependent K (fun i : Fin k => f ^ (i : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hp : Polynomial.aeval f (∑ j : Fin k, Polynomial.monomial (j : ℕ) (g j)) = 0 := by
    rw [map_sum]
    simpa [Polynomial.aeval_monomial, Algebra.smul_def] using hg
  have hp0 := (transcendental_iff.1 htr) _ hp
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff (i : ℕ)) hp0
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single i (fun j _ hji => if_neg (fun h => hji (Fin.ext h))) (fun h => absurd (Finset.mem_univ i) h),
    if_pos rfl] at hcoeff
  exact hcoeff

theorem v_le_one_of_isIntegral (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    {v : Valuation F ℤᵐ⁰} (hv : v ∈ V) {f : F} (hf : IsIntegral K f) : v f ≤ 1 := by

  have hmem : ∀ c : K, algebraMap K F c ∈ v.integer := fun c => by
    rw [Valuation.mem_integer_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (hK v hv c hc).le
  let φ : K →+* v.integer := (algebraMap K F).codRestrict v.integer.toSubsemiring hmem
  have hint : IsIntegral v.integer f := by
    obtain ⟨p, hp, hpf⟩ := hf
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (↥v.integer) F).comp φ = algebraMap K F := RingHom.ext fun _ => rfl
    rw [hcomp]
    exact hpf
  exact (Valuation.integer.integers v).mem_of_integral hint

theorem transcendental_and_finiteDimensional (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    (hres : ∀ v ∈ V, ∀ f : F, v f = 1 → ∃ c : K, v (f - algebraMap K F c) < 1)
    (hfin : ∀ f : F, f ≠ 0 → {v ∈ V | 1 < v f}.Finite)
    (hconst : ∀ f : F, (∀ v ∈ V, v f ≤ 1) → f ∈ Set.range (algebraMap K F))
    (f : F) (hf : f ∉ Set.range (algebraMap K F)) :
    Transcendental K f ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({f} : Set F)) F := by

  have htr : Transcendental K f := by
    intro halg
    exact hf (hconst f fun v hv => v_le_one_of_isIntegral V hK hv halg.isIntegral)
  refine ⟨htr, ?_⟩

  obtain ⟨mf, hmf⟩ := exists_mem_lSpace V hK hfin f
  set d := Multiset.card mf with hd
  have hfmem : f ∈ IntermediateField.adjoin K ({f} : Set F) := IntermediateField.mem_adjoin_simple_self K f

  have hrank : Module.rank ↥(IntermediateField.adjoin K ({f} : Set F)) F ≤ d := by
    apply rank_le
    intro s hs
    by_contra hsd
    push Not at hsd
    choose m hm using exists_mem_lSpace V hK hfin
    set ms : Multiset (Valuation F ℤᵐ⁰) := ∑ g ∈ s, m g with hms
    set C := Multiset.card ms with hC
    set k := C + 1 with hk

    have hmem : ∀ p : Fin (k + 1) × ↥s, f ^ (p.1 : ℕ) * (p.2 : F) ∈ lSpace V hK (k • mf + ms) := fun p => by
      have h1 : f ^ (p.1 : ℕ) ∈ lSpace V hK (k • mf) :=
        lSpace_mono V hK (nsmul_le_nsmul_left (bot_le (a := mf)) (Nat.lt_succ_iff.1 p.1.2)) (pow_mem_lSpace V hK hmf p.1)
      have h2 : (p.2 : F) ∈ lSpace V hK ms :=
        lSpace_mono V hK (Finset.single_le_sum (f := m) (fun w _ => bot_le) p.2.2) (hm p.2)
      exact mul_mem_lSpace V hK h1 h2

    have hb : LinearIndependent K
        (fun i : Fin (k + 1) => (⟨f, hfmem⟩ : ↥(IntermediateField.adjoin K ({f} : Set F))) ^ (i : ℕ)) := by
      apply LinearIndependent.of_comp ((IntermediateField.adjoin K ({f} : Set F)).val.toLinearMap)
      exact linearIndependent_pow_of_transcendental htr (k + 1)
    have hli : LinearIndependent K (fun p : Fin (k + 1) × ↥s => f ^ (p.1 : ℕ) * (p.2 : F)) := by
      have := linearIndependent_smul hb hs
      exact this
    have hli' : LinearIndependent K
        (fun p : Fin (k + 1) × ↥s => (⟨f ^ (p.1 : ℕ) * (p.2 : F), hmem p⟩ : ↥(lSpace V hK (k • mf + ms)))) :=
      LinearIndependent.of_comp (lSpace V hK (k • mf + ms)).subtype hli
    obtain ⟨hLfin, hLrank⟩ := finite_and_finrank_lSpace_le V hK hres hconst (k • mf + ms)
    haveI := hLfin
    have hcard := hli'.fintype_card_le_finrank
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at hcard
    rw [Multiset.card_add, Multiset.card_nsmul, ← hd, ← hC] at hLrank
    have : (k + 1) * s.card ≤ k * d + C + 1 := hcard.trans hLrank
    rw [hk] at this
    nlinarith
  exact Module.rank_lt_aleph0_iff.1 (hrank.trans_lt (Cardinal.natCast_lt_aleph0))

end P2mKcRecognition

open P2mKcRecognition in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    (hres : ∀ v ∈ V, ∀ f : F, v f = 1 → ∃ c : K, v (f - algebraMap K F c) < 1)
    (hfin : ∀ f : F, f ≠ 0 → {v ∈ V | 1 < v f}.Finite)
    (hconst : ∀ f : F, (∀ v ∈ V, v f ≤ 1) → f ∈ Set.range (algebraMap K F))
    (f : F) (hf : f ∉ Set.range (algebraMap K F)) :
    Transcendental K f ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({f} : Set F)) F :=
  transcendental_and_finiteDimensional V hK hres hfin hconst f hf

end S_AlgebraicCurve_transcendental_and_finiteDimensional_adjoin_of_valuations
end P2MW
export P2MW.S_AlgebraicCurve_transcendental_and_finiteDimensional_adjoin_of_valuations (solution)
