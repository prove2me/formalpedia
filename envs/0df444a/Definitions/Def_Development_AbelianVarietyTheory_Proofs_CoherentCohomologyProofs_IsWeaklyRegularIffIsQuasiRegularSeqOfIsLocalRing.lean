-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:51.318421+00:00
-- url     : https://prove2.me/theorems/0ae79ce0-c59a-4af6-bd22-2ef7609f05d5
-- title:
--   Is Weakly Regular Iff Is Quasi Regular Seq Of Is Local Ring
-- statement:
--   Definitions and structural lemmas for Is Weakly Regular Iff Is Quasi Regular Seq Of Is Local Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_isQuasiRegularSeq_comp_equiv_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence
namespace GlobalTheory
section Split
variable {ι : Type*}
noncomputable def MonoDeg.mulVar (i : ι) {a : ℕ} (γ : MonoDeg ι a) : MonoDeg ι (a + 1) :=
  ⟨γ.1 + Finsupp.single i 1, by simp [γ.2]⟩
theorem MonoDeg.mulVar_injective (i : ι) (a : ℕ) :
    Function.Injective (MonoDeg.mulVar i : MonoDeg ι a → MonoDeg ι (a + 1)) :=
  fun _ _ h => Subtype.ext (add_right_cancel (congrArg Subtype.val h))
noncomputable def MonoDeg.toOption {a : ℕ} (β : MonoDeg ι a) : MonoDeg (Option ι) a :=
  ⟨β.1.mapDomain some, by simp [Finsupp.degree_mapDomain, β.2]⟩
noncomputable def MonoDeg.optionEquiv (ι : Type*) (a : ℕ) :
    MonoDeg ι (a + 1) ⊕ MonoDeg (Option ι) a ≃ MonoDeg (Option ι) (a + 1) :=
  Equiv.ofBijective (Sum.elim MonoDeg.toOption (MonoDeg.mulVar none)) <| by
    have hne : ∀ (β : MonoDeg ι (a + 1)) (γ : MonoDeg (Option ι) a),
        β.toOption ≠ MonoDeg.mulVar none γ := by
      intro β γ h
      have := DFunLike.congr_fun (congrArg Subtype.val h) none
      simp only [MonoDeg.toOption, MonoDeg.mulVar] at this
      rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp)] at this
      simp at this
    constructor
    · refine Function.Injective.sumElim ?_ (MonoDeg.mulVar_injective _ _) hne
      intro β β' h
      exact Subtype.ext (Finsupp.mapDomain_injective (Option.some_injective _)
        (congrArg Subtype.val h))
    · rintro ⟨α, hα⟩
      by_cases h0 : α none = 0
      · have h1 : α.some.mapDomain some = α := by
          ext o
          cases o with
          | none => rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp), h0]
          | some i => rw [Finsupp.mapDomain_apply (Option.some_injective _), Finsupp.some_apply]
        refine ⟨Sum.inl ⟨α.some, ?_⟩, Subtype.ext h1⟩
        rw [← hα, ← h1, Finsupp.degree_mapDomain, h1]
      · have h1 : α - Finsupp.single none 1 + Finsupp.single none 1 = α :=
          tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero h0))
        refine ⟨Sum.inr ⟨α - Finsupp.single none 1, ?_⟩, Subtype.ext h1⟩
        rw [← h1, map_add, Finsupp.degree_single] at hα
        omega
variable {R : Type*} [CommRing R]
theorem monoVal_mulVar (f : ι → R) (i : ι) {a : ℕ} (γ : MonoDeg ι a) :
    monoVal f (MonoDeg.mulVar i γ).1 = f i * monoVal f γ.1 := by
  simp [MonoDeg.mulVar, monoVal_add, mul_comm]
theorem monoVal_toOption (f : Option ι → R) {a : ℕ} (β : MonoDeg ι a) :
    monoVal f β.toOption.1 = monoVal (f ∘ some) β.1 :=
  Finsupp.prod_mapDomain_index_inj (Option.some_injective _)
variable [Finite ι] {M : Type*} [AddCommGroup M] [Module R M]
theorem sum_monoVal_smul_option (f : Option ι → R) (a : ℕ) (c : MonoDeg (Option ι) (a + 1) → M) :
    ∑ α, monoVal f α.1 • c α = ∑ β : MonoDeg ι (a + 1), monoVal (f ∘ some) β.1 • c β.toOption +
      f none • ∑ γ : MonoDeg (Option ι) a, monoVal f γ.1 • c (MonoDeg.mulVar none γ) := by
  rw [← (MonoDeg.optionEquiv ι a).sum_comp, Fintype.sum_sum_type, Finset.smul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_
  · rw [← monoVal_toOption]
    rfl
  · rw [smul_smul, ← monoVal_mulVar]
    rfl
theorem mem_pow_smul_iff (f : ι → R) (a : ℕ) (N : Submodule R M) (x : M) :
    x ∈ Ideal.span (Set.range f) ^ a • N ↔
      ∃ c : MonoDeg ι a → M, (∀ α, c α ∈ N) ∧ ∑ α, monoVal f α.1 • c α = x := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m hm
      rw [span_range_pow_eq_span_monoVal, Ideal.mem_span_range_iff_exists_fun] at hr
      obtain ⟨b, rfl⟩ := hr
      exact ⟨fun α => b α • m, fun α => N.smul_mem _ hm,
        by simp [Finset.sum_smul, mul_comm, smul_smul]⟩
    · rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      exact ⟨c + d, fun α => N.add_mem (hc α) (hd α), by simp [Finset.sum_add_distrib]⟩
  · rintro ⟨c, hc, rfl⟩
    exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem_smul (monoVal_mem_pow f α) (hc α)
theorem sum_monoVal_smul_mem_pow_succ (f : ι → R) {a : ℕ} {c : MonoDeg ι a → M}
    (hc : ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) :
    ∑ α, monoVal f α.1 • c α ∈ (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M) := by
  rw [pow_succ, mul_smul]
  exact (mem_pow_smul_iff f a _ _).mpr ⟨c, hc, rfl⟩
theorem isQuasiRegularSeq_iff_eq_zero (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ (a : ℕ) (c : MonoDeg ι a → M), ∑ α, monoVal f α.1 • c α = 0 →
      ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) := by
  refine ⟨fun h a c hc => h a c (by rw [hc]; exact zero_mem _), fun h a c hc α => ?_⟩
  rw [pow_succ, mul_smul] at hc
  obtain ⟨d, hd, hdc⟩ := (mem_pow_smul_iff f a _ _).mp hc
  have := h a (c - d) (by simp [smul_sub, Finset.sum_sub_distrib, hdc]) α
  simpa using Submodule.add_mem _ this (hd α)
end Split
section Step
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
theorem mem_pow_of_regular {f : ι → R} (h : IsQuasiRegularSeq M f) {x : R}
    (hx : IsSMulRegular (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) x) (a : ℕ) (m : M)
    (hm : x • m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M)) :
    m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) := by
  induction a with
  | zero => simp
  | succ a ih =>
    obtain ⟨c, rfl⟩ := (mem_pow_smul_top_iff f a m).mp (ih (powGr.pow_succ_smul_le _ M a hm))
    refine sum_monoVal_smul_mem_pow_succ f fun α => ?_
    have := h a (fun α => x • c α) (by
      simpa only [Finset.smul_sum, smul_comm x] using hm) α
    rw [← Submodule.Quotient.mk_eq_zero] at this ⊢
    exact hx.right_eq_zero_of_smul this
theorem IsQuasiRegularSeq.option {f : Option ι → R} (h : IsQuasiRegularSeq M (f ∘ some))
    (hx : IsSMulRegular (M ⧸ (Ideal.span (Set.range (f ∘ some)) • ⊤ : Submodule R M)) (f none)) :
    IsQuasiRegularSeq M f := by
  have hJI : Ideal.span (Set.range (f ∘ some)) ≤ Ideal.span (Set.range f) :=
    Ideal.span_mono (Set.range_comp_subset_range _ _)
  intro a
  induction a with
  | zero =>
    intro c hc α
    have hs : ∀ β : MonoDeg (Option ι) 0, β.1 = 0 := fun β =>
      (Finsupp.degree_eq_zero_iff _).mp β.2
    rw [Finset.sum_eq_single α (fun β _ hβ => absurd (Subtype.ext ((hs β).trans (hs α).symm)) hβ)
      (by simp), hs α] at hc
    simpa using hc
  | succ a ih =>
    suffices key : ∀ c : MonoDeg (Option ι) (a + 1) → M, ∑ α, monoVal f α.1 • c α = 0 →
        ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) by
      intro c hc α
      rw [pow_succ, mul_smul] at hc
      obtain ⟨d, hd, hdc⟩ := (mem_pow_smul_iff f _ _ _).mp hc
      have := key (c - d) (by simp [smul_sub, Finset.sum_sub_distrib, hdc]) α
      simpa using Submodule.add_mem _ this (hd α)
    intro c hc α
    rw [sum_monoVal_smul_option] at hc
    have hH : ∑ γ : MonoDeg (Option ι) a, monoVal f γ.1 • c (MonoDeg.mulVar none γ) ∈
        (Ideal.span (Set.range (f ∘ some)) ^ (a + 1) • ⊤ : Submodule R M) := by
      refine mem_pow_of_regular h hx _ _ ?_
      rw [eq_neg_of_add_eq_zero_right hc, neg_mem_iff]
      exact (mem_pow_smul_top_iff _ _ _).mpr ⟨_, rfl⟩
    obtain ⟨β | γ, rfl⟩ := (MonoDeg.optionEquiv ι a).surjective α
    · obtain ⟨d, hd⟩ := (mem_pow_smul_top_iff _ _ _).mp hH
      have := (isQuasiRegularSeq_iff_eq_zero _).mp h (a + 1)
        (fun β => c β.toOption + f none • d β) (by
          rw [← hc, ← hd, Finset.smul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun β _ => by rw [smul_add, smul_comm (f none)]) β
      exact (Submodule.add_mem_iff_left _
        (Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_range_self none))
          Submodule.mem_top)).mp
          (Submodule.smul_mono_left hJI this)
    · exact ih (fun γ => c (MonoDeg.mulVar none γ))
        (Submodule.smul_mono_left (Ideal.pow_right_mono hJI _) hH) γ
end Step
section Main
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
theorem ofList_ofFn_eq_span_range {n : ℕ} (f : Fin n → R) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  rw [Ideal.ofList]
  congr 1
  ext x
  simp [List.mem_ofFn']
theorem isQuasiRegularSeq_of_isWeaklyRegular {n : ℕ} {f : Fin n → R}
    (h : IsWeaklyRegular M (List.ofFn f)) : IsQuasiRegularSeq M f := by
  induction n with
  | zero =>
    intro a c hc α
    have hs : ∀ β : MonoDeg (Fin 0) a, β.1 = 0 := fun β => Subsingleton.elim _ _
    obtain rfl : a = 0 := by rw [← α.2, hs α, map_zero]
    rw [Finset.sum_eq_single α (fun β _ hβ => absurd (Subtype.ext ((hs β).trans (hs α).symm)) hβ)
      (by simp), hs α] at hc
    simpa using hc
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, isWeaklyRegular_append_iff,
      isWeaklyRegular_singleton_iff, ofList_ofFn_eq_span_range] at h
    rw [← isQuasiRegularSeq_comp_equiv_iff f finSuccEquivLast.symm]
    have h1 : (f ∘ finSuccEquivLast.symm) ∘ some = fun i : Fin n => f i.castSucc := by
      funext i
      simp
    have h2 : (f ∘ finSuccEquivLast.symm) none = f (Fin.last n) := by simp
    refine IsQuasiRegularSeq.option (f := f ∘ finSuccEquivLast.symm) ?_ ?_
    · rw [h1]
      exact ih h.1
    · rw [h1, h2]
      exact h.2
example : IsQuasiRegularSeq ℤ ![(2 : ℤ)] :=
  isQuasiRegularSeq_of_isWeaklyRegular (by
    simpa using IsSMulRegular.of_ne_zero (M := ℤ) (two_ne_zero (α := ℤ)))
end Main
end GlobalTheory


