-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSMulRegularQuotIffMemNonZeroDivisors
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSMulRegularQuotIffMemNonZeroDivisors
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:54.097473+00:00
-- url     : https://prove2.me/theorems/5b6f8883-7f94-4b41-84b2-ea0bc8f27400
-- title:
--   Is SMul Regular Quot Iff Mem Non Zero Divisors
-- statement:
--   Definitions and structural lemmas for Is SMul Regular Quot Iff Mem Non Zero Divisors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSMulRegularQuotIffMemNonZeroDivisors.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Theorems.Thm_GlobalTheory_fintypeCard_degree_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
section Regular
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {M : Type*} [AddCommGroup M] [Module R M]
  {f : ι → R}
theorem IsQuasiRegularSeq.isSMulRegular_powGr (h : IsQuasiRegularSeq M f) {x : R}
    (hx : IsSMulRegular (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) x) (a : ℕ) :
    IsSMulRegular (powGr (Ideal.span (Set.range f)) M a) x := by
  intro y z hyz
  obtain ⟨c, rfl⟩ := (h.powGrEquiv a).surjective y
  obtain ⟨d, rfl⟩ := (h.powGrEquiv a).surjective z
  have key : ∀ c, x • h.powGrEquiv a c = h.powGrEquiv a (x • c) := fun c =>
    ((h.powGrEquiv a).map_smul (Ideal.Quotient.mk _ x) c).symm.trans (by
      congr 1)
  simp only [key] at hyz
  have := (h.powGrEquiv a).injective hyz
  congr 1
  exact funext fun α => hx (congrFun this α)
theorem IsQuasiRegularSeq.mem_pow_smul_top_of_smul_mem (h : IsQuasiRegularSeq M f) {x : R}
    (hx : IsSMulRegular (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) x) (a : ℕ) {m : M}
    (hm : x • m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M)) :
    m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 := ih (powGr.pow_succ_smul_le _ M a hm)
    have h2 : x • powGr.mk _ M a ⟨m, h1⟩ = 0 := by
      rw [← map_smul, powGr.mk_eq_zero]
      exact hm
    exact (powGr.mk_eq_zero _).mp ((h.isSMulRegular_powGr hx a).right_eq_zero_of_smul h2)
theorem IsQuasiRegularSeq.isSMulRegular_quot_pow (h : IsQuasiRegularSeq M f) {x : R}
    (hx : IsSMulRegular (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) x) (a : ℕ) :
    IsSMulRegular (M ⧸ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M)) x := by
  refine IsSMulRegular.of_right_eq_zero_of_smul fun m hm => ?_
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
  exact (Submodule.Quotient.mk_eq_zero _).mpr (h.mem_pow_smul_top_of_smul_mem hx a hm)
theorem isSMulRegular_quot_smul_top_iff (J : Ideal R) (x : R) :
    IsSMulRegular (R ⧸ (J • ⊤ : Submodule R R)) x ↔ IsSMulRegular (R ⧸ J) x := by
  rw [show (J • ⊤ : Submodule R R) = J by simp]
theorem isSMulRegular_quot_iff_mem_nonZeroDivisors (J : Ideal R) (x : R) :
    IsSMulRegular (R ⧸ J) x ↔ Ideal.Quotient.mk J x ∈ nonZeroDivisors (R ⧸ J) := by
  rw [← isRegular_iff_mem_nonZeroDivisors, ← isLeftRegular_iff_isRegular, isLeftRegular_iff]
  exact (isSMulRegular_algebraMap_iff (R ⧸ J)).symm
theorem IsQuasiRegularSeq.isSMulRegular_powGr_self (h : IsQuasiRegularSeq R f) {x : R}
    (hx : IsSMulRegular (R ⧸ Ideal.span (Set.range f)) x) (a : ℕ) :
    IsSMulRegular (powGr (Ideal.span (Set.range f)) R a) x :=
  h.isSMulRegular_powGr ((isSMulRegular_quot_smul_top_iff _ x).mpr hx) a
theorem IsQuasiRegularSeq.isSMulRegular_quot_pow_self (h : IsQuasiRegularSeq R f) {x : R}
    (hx : IsSMulRegular (R ⧸ Ideal.span (Set.range f)) x) (a : ℕ) :
    IsSMulRegular (R ⧸ Ideal.span (Set.range f) ^ a) x :=
  (isSMulRegular_quot_smul_top_iff _ x).mp
    (h.isSMulRegular_quot_pow ((isSMulRegular_quot_smul_top_iff _ x).mpr hx) a)
theorem IsQuasiRegularSeq.mem_pow_of_mul_mem (h : IsQuasiRegularSeq R f) {x : R}
    (hx : IsSMulRegular (R ⧸ Ideal.span (Set.range f)) x) (a : ℕ) {y : R}
    (hy : x * y ∈ Ideal.span (Set.range f) ^ a) : y ∈ Ideal.span (Set.range f) ^ a := by
  simpa using h.mem_pow_smul_top_of_smul_mem ((isSMulRegular_quot_smul_top_iff _ x).mpr hx) a
    (m := y) (by simpa using hy)
theorem IsQuasiRegularSeq.comap_map_pow (h : IsQuasiRegularSeq R f) (T : Submonoid R)
    (hT : ∀ t ∈ T, IsSMulRegular (R ⧸ Ideal.span (Set.range f)) t)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S] (a : ℕ) :
    ((Ideal.span (Set.range f) ^ a).map (algebraMap R S)).comap (algebraMap R S) =
      Ideal.span (Set.range f) ^ a := by
  refine le_antisymm (fun y hy => ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap, IsLocalization.algebraMap_mem_map_algebraMap_iff T] at hy
  obtain ⟨t, ht, hty⟩ := hy
  exact h.mem_pow_of_mul_mem (hT t ht) a hty
end Regular
section Prime
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {f : ι → R}
theorem isSMulRegular_quot_of_notMem {P : Ideal R} [P.IsPrime] {x : R} (hx : x ∉ P) :
    IsSMulRegular (R ⧸ P) x :=
  (isSMulRegular_quot_iff_mem_nonZeroDivisors P x).mpr
    (mem_nonZeroDivisors_of_ne_zero fun h => hx (Ideal.Quotient.eq_zero_iff_mem.mp h))
theorem IsQuasiRegularSeq.mem_pow_of_mul_mem_of_notMem (h : IsQuasiRegularSeq R f)
    [(Ideal.span (Set.range f)).IsPrime] {x y : R} (hx : x ∉ Ideal.span (Set.range f)) (a : ℕ)
    (hy : x * y ∈ Ideal.span (Set.range f) ^ a) : y ∈ Ideal.span (Set.range f) ^ a :=
  h.mem_pow_of_mul_mem (isSMulRegular_quot_of_notMem hx) a hy
theorem radical_pow_of_isPrime (P : Ideal R) [hP : P.IsPrime] {a : ℕ} (ha : a ≠ 0) :
    (P ^ a).radical = P := by
  rw [Ideal.radical_pow P ha, hP.radical]
theorem IsQuasiRegularSeq.isPrimary_pow (h : IsQuasiRegularSeq R f)
    [hI : (Ideal.span (Set.range f)).IsPrime] {a : ℕ} (ha : a ≠ 0) :
    (Ideal.span (Set.range f) ^ a).IsPrimary := by
  rw [Ideal.isPrimary_iff, radical_pow_of_isPrime _ ha]
  refine ⟨fun ht => hI.ne_top (top_le_iff.mp (ht ▸ Ideal.pow_le_self ha)), fun {x y} hxy => ?_⟩
  rw [or_iff_not_imp_right]
  exact fun hy => h.mem_pow_of_mul_mem_of_notMem hy a (mul_comm x y ▸ hxy)
variable (S : Type*) [CommRing S] [Algebra R S]
theorem IsQuasiRegularSeq.comap_map_pow_atPrime (h : IsQuasiRegularSeq R f)
    [(Ideal.span (Set.range f)).IsPrime] [IsLocalization.AtPrime S (Ideal.span (Set.range f))]
    (a : ℕ) : ((Ideal.span (Set.range f) ^ a).map (algebraMap R S)).comap (algebraMap R S) =
      Ideal.span (Set.range f) ^ a :=
  h.comap_map_pow (Ideal.span (Set.range f)).primeCompl
    (fun _ ht => isSMulRegular_quot_of_notMem ht) S a
theorem IsQuasiRegularSeq.comap_maximalIdeal_pow (h : IsQuasiRegularSeq R f)
    [(Ideal.span (Set.range f)).IsPrime] [IsLocalRing S]
    [IsLocalization.AtPrime S (Ideal.span (Set.range f))] (a : ℕ) :
    (IsLocalRing.maximalIdeal S ^ a).comap (algebraMap R S) = Ideal.span (Set.range f) ^ a := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span (Set.range f)) S, ← Ideal.map_pow,
    h.comap_map_pow_atPrime S a]
theorem IsQuasiRegularSeq.algebraMap_mem_maximalIdeal_pow_iff (h : IsQuasiRegularSeq R f)
    [(Ideal.span (Set.range f)).IsPrime] [IsLocalRing S]
    [IsLocalization.AtPrime S (Ideal.span (Set.range f))] (a : ℕ) (y : R) :
    algebraMap R S y ∈ IsLocalRing.maximalIdeal S ^ a ↔ y ∈ Ideal.span (Set.range f) ^ a := by
  rw [← h.comap_maximalIdeal_pow S a, Ideal.mem_comap]
end Prime
section Free
abbrev MonoDegLE (ι : Type*) (k : ℕ) : Type _ := {α : ι →₀ ℕ // α.degree ≤ k}
instance MonoDegLE.finite (ι : Type*) [Finite ι] (k : ℕ) : Finite (MonoDegLE ι k) :=
  (Finsupp.finite_of_degree_le (σ := ι) k).to_subtype
noncomputable instance MonoDegLE.fintype (ι : Type*) [Finite ι] (k : ℕ) :
    Fintype (MonoDegLE ι k) :=
  Fintype.ofFinite _
theorem MonoDegLE.card (ι : Type*) [Fintype ι] (k : ℕ) :
    Fintype.card (MonoDegLE ι k) = (k + Fintype.card ι).choose (Fintype.card ι) :=
  fintypeCard_degree_le ι k
theorem MonoDegLE.sum_eq_sum_range {ι N : Type*} [Finite ι] [AddCommMonoid N] (k : ℕ)
    (g : (ι →₀ ℕ) → N) :
    ∑ α : MonoDegLE ι k, g α.1 = ∑ a ∈ Finset.range (k + 1), ∑ α : MonoDeg ι a, g α.1 := by
  classical
  have h1 := Finset.sum_subtype (p := fun α : ι →₀ ℕ => α.degree ≤ k)
    (F := MonoDegLE.fintype ι k) (Finsupp.finite_of_degree_le (σ := ι) k).toFinset (by simp) g
  rw [← h1, ← Finset.sum_fiberwise_of_maps_to (t := Finset.range (k + 1)) (g := Finsupp.degree)
    (by simp [Nat.lt_succ_iff])]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_subtype _ (fun α => ?_) g
  rw [Finset.mem_range] at ha
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  omega
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {M : Type*} [AddCommGroup M] [Module R M]
theorem IsQuasiRegularSeq.eq_zero_of_sum_range_mem {f : ι → R} (h : IsQuasiRegularSeq M f)
    (c : (ι →₀ ℕ) → M)
    (hc : ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) → c α = 0) (n : ℕ)
    (hn : ∑ a ∈ Finset.range n, ∑ α : MonoDeg ι a, monoVal f α.1 • c α.1 ∈
      (Ideal.span (Set.range f) ^ n • ⊤ : Submodule R M)) :
    ∀ α, α.degree < n → c α = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ] at hn
    have htop : ∑ α : MonoDeg ι n, monoVal f α.1 • c α.1 ∈
        (Ideal.span (Set.range f) ^ n • ⊤ : Submodule R M) :=
      (mem_pow_smul_top_iff f n _).mpr ⟨_, rfl⟩
    have hlow := ih ((Submodule.add_mem_iff_left _ htop).mp (powGr.pow_succ_smul_le _ M n hn))
    rw [Finset.sum_eq_zero, zero_add] at hn
    · intro α hα
      rcases (Nat.lt_succ_iff_lt_or_eq).mp hα with hα | hα
      · exact hlow α hα
      · exact hc α (h n (fun β => c β.1) hn ⟨α, hα⟩)
    · intro a ha
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [hlow α.1 (α.2.symm ▸ Finset.mem_range.mp ha), smul_zero]
theorem exists_sub_sum_range_mem (f : ι → R) {N : Type*} (s : N → M)
    (hs : ∀ m, ∃ y, m - s y ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) (n : ℕ) (m : M) :
    ∃ c : (ι →₀ ℕ) → N, m - ∑ a ∈ Finset.range n, ∑ α : MonoDeg ι a, monoVal f α.1 • s (c α.1) ∈
      (Ideal.span (Set.range f) ^ n • ⊤ : Submodule R M) := by
  induction n with
  | zero => exact ⟨fun _ => (hs 0).choose, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := (mem_pow_smul_top_iff f n _).mp hc
    choose e he using fun α => hs (d α)
    refine ⟨fun β => if hβ : β.degree = n then e ⟨β, hβ⟩ else c β, ?_⟩
    have h1 : ∑ a ∈ Finset.range n, ∑ α : MonoDeg ι a,
        monoVal f α.1 • s (if hβ : α.1.degree = n then e ⟨α.1, hβ⟩ else c α.1) =
        ∑ a ∈ Finset.range n, ∑ α : MonoDeg ι a, monoVal f α.1 • s (c α.1) := by
      refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun α _ => ?_
      rw [dif_neg (α.2.trans_ne (Finset.mem_range.mp ha).ne)]
    have h2 : ∑ α : MonoDeg ι n,
        monoVal f α.1 • s (if hβ : α.1.degree = n then e ⟨α.1, hβ⟩ else c α.1) =
        ∑ α : MonoDeg ι n, monoVal f α.1 • s (e α) :=
      Finset.sum_congr rfl fun α _ => by rw [dif_pos α.2]
    rw [Finset.sum_range_succ, h1, h2, ← sub_sub, ← hd, ← Finset.sum_sub_distrib, pow_succ,
      mul_smul]
    refine Submodule.sum_mem _ fun α _ => ?_
    rw [← smul_sub]
    exact Submodule.smul_mem_smul (monoVal_mem_pow f α) (he α)
variable {A : Type*} [CommRing A] [Algebra A R] [Module A M] [IsScalarTower A R M]
  {N : Type*} [AddCommGroup N] [Module A N]
noncomputable def monoLEToQuotPow (f : ι → R) (s : N →ₗ[A] M) (k : ℕ) :
    (MonoDegLE ι k → N) →ₗ[A] M ⧸ (Ideal.span (Set.range f) ^ (k + 1) • ⊤ : Submodule R M) :=
  (Submodule.mkQ _).restrictScalars A ∘ₗ ∑ α : MonoDegLE ι k,
    (LinearMap.lsmul R M (monoVal f α.1)).restrictScalars A ∘ₗ s ∘ₗ LinearMap.proj α
theorem monoLEToQuotPow_apply (f : ι → R) (s : N →ₗ[A] M) (k : ℕ) (c : MonoDegLE ι k → N) :
    monoLEToQuotPow f s k c = Submodule.Quotient.mk (∑ α, monoVal f α.1 • s (c α)) := by
  simp only [monoLEToQuotPow, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, LinearMap.proj_apply,
    Submodule.mkQ_apply]
theorem monoLEToQuotPow_single [DecidableEq ι] (f : ι → R) (s : N →ₗ[A] M) (k : ℕ)
    (α : MonoDegLE ι k) (y : N) :
    monoLEToQuotPow f s k (Pi.single α y) = Submodule.Quotient.mk (monoVal f α.1 • s y) := by
  rw [monoLEToQuotPow_apply, Finset.sum_eq_single α]
  · rw [Pi.single_eq_same]
  · intro β _ h
    rw [Pi.single_eq_of_ne h, map_zero, smul_zero]
  · simp
theorem monoLEToQuotPow_surjective (f : ι → R) (s : N →ₗ[A] M)
    (hs : Function.Surjective fun y =>
      (Submodule.Quotient.mk (s y) : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)))
    (k : ℕ) : Function.Surjective (monoLEToQuotPow f s k) := by
  intro m
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  obtain ⟨c, hc⟩ := exists_sub_sum_range_mem f s (fun m => by
    obtain ⟨y, hy⟩ := hs (Submodule.Quotient.mk m)
    exact ⟨y, (Submodule.Quotient.eq _).mp hy.symm⟩) (k + 1) m
  refine ⟨fun α => c α.1, ?_⟩
  rw [monoLEToQuotPow_apply, MonoDegLE.sum_eq_sum_range k fun α => monoVal f α • s (c α), eq_comm,
    Submodule.Quotient.eq]
  exact hc
theorem IsQuasiRegularSeq.monoLEToQuotPow_injective {f : ι → R} (h : IsQuasiRegularSeq M f)
    (s : N →ₗ[A] M)
    (hs : Function.Injective fun y =>
      (Submodule.Quotient.mk (s y) : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)))
    (k : ℕ) : Function.Injective (monoLEToQuotPow f s k) := by
  have hs0 : ∀ y, s y ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) → y = 0 := fun y hy =>
    hs (by simpa using hy)
  rw [injective_iff_map_eq_zero]
  intro c hc
  let c' : (ι →₀ ℕ) → N := fun β => if hβ : β.degree ≤ k then c ⟨β, hβ⟩ else 0
  have hc' : ∀ α : MonoDegLE ι k, c α = c' α.1 := fun α => by simp only [c', dif_pos α.2]
  rw [monoLEToQuotPow_apply, Submodule.Quotient.mk_eq_zero] at hc
  simp only [hc'] at hc
  rw [MonoDegLE.sum_eq_sum_range k fun α => monoVal f α • s (c' α)] at hc
  have := h.eq_zero_of_sum_range_mem (fun α => s (c' α))
    (fun α hα => by rw [hs0 _ hα, map_zero]) (k + 1) hc
  funext α
  refine hs0 _ ?_
  rw [hc', this α.1 (Nat.lt_succ_of_le α.2)]
  exact zero_mem _
noncomputable def IsQuasiRegularSeq.quotPowEquiv {f : ι → R} (h : IsQuasiRegularSeq M f)
    (s : N →ₗ[A] M)
    (hs : Function.Bijective fun y =>
      (Submodule.Quotient.mk (s y) : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)))
    (k : ℕ) :
    (MonoDegLE ι k → N) ≃ₗ[A] M ⧸ (Ideal.span (Set.range f) ^ (k + 1) • ⊤ : Submodule R M) :=
  LinearEquiv.ofBijective (monoLEToQuotPow f s k)
    ⟨h.monoLEToQuotPow_injective s hs.1 k, monoLEToQuotPow_surjective f s hs.2 k⟩
theorem mk_linearCombination (P : Submodule R M) {κ : Type*} (m : κ → M) :
    (fun y : κ →₀ A => (Submodule.Quotient.mk (Finsupp.linearCombination A m y) : M ⧸ P)) =
      Finsupp.linearCombination A fun j => (Submodule.Quotient.mk (m j) : M ⧸ P) :=
  funext fun y => Finsupp.apply_linearCombination A (P.mkQ.restrictScalars A) m y
theorem monoLEToQuotPow_comp_basis (f : ι → R) {κ : Type*} (m : κ → M) (k : ℕ) :
    monoLEToQuotPow f (Finsupp.linearCombination A m) k ∘
      (Pi.basis fun _ : MonoDegLE ι k => Finsupp.basisSingleOne (R := A) (ι := κ)).reindex
        (Equiv.sigmaEquivProd _ _) =
      fun p : MonoDegLE ι k × κ => Submodule.Quotient.mk (monoVal f p.1.1 • m p.2) := by
  classical
  funext p
  simp [monoLEToQuotPow_single]
theorem IsQuasiRegularSeq.linearIndependent_monoVal_smul {f : ι → R} (h : IsQuasiRegularSeq M f)
    {κ : Type*} {m : κ → M}
    (hm : LinearIndependent A fun j =>
      (Submodule.Quotient.mk (m j) : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)))
    (k : ℕ) :
    LinearIndependent A fun p : MonoDegLE ι k × κ =>
      (Submodule.Quotient.mk (monoVal f p.1.1 • m p.2) :
        M ⧸ (Ideal.span (Set.range f) ^ (k + 1) • ⊤ : Submodule R M)) := by
  have hs : Function.Injective fun y : κ →₀ A =>
      (Submodule.Quotient.mk (Finsupp.linearCombination A m y) :
        M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) := by
    rw [mk_linearCombination]
    exact hm
  have h1 := ((Pi.basis fun _ : MonoDegLE ι k => Finsupp.basisSingleOne (R := A) (ι := κ)).reindex
    (Equiv.sigmaEquivProd _ _)).linearIndependent.map' _
    (LinearMap.ker_eq_bot.mpr (h.monoLEToQuotPow_injective _ hs k))
  rwa [monoLEToQuotPow_comp_basis] at h1
theorem span_monoVal_smul_eq_top (f : ι → R) {κ : Type*} {m : κ → M}
    (hm : Submodule.span A (Set.range fun j =>
      (Submodule.Quotient.mk (m j) : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M))) = ⊤)
    (k : ℕ) :
    Submodule.span A (Set.range fun p : MonoDegLE ι k × κ =>
      (Submodule.Quotient.mk (monoVal f p.1.1 • m p.2) :
        M ⧸ (Ideal.span (Set.range f) ^ (k + 1) • ⊤ : Submodule R M))) = ⊤ := by
  have hs : Function.Surjective fun y : κ →₀ A =>
      (Submodule.Quotient.mk (Finsupp.linearCombination A m y) :
        M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) := by
    rwa [mk_linearCombination, ← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  have h1 := congrArg (Submodule.map (monoLEToQuotPow f (Finsupp.linearCombination A m) k))
    ((Pi.basis fun _ : MonoDegLE ι k => Finsupp.basisSingleOne (R := A) (ι := κ)).reindex
      (Equiv.sigmaEquivProd _ _)).span_eq
  rwa [Submodule.map_top, LinearMap.range_eq_top.mpr (monoLEToQuotPow_surjective f _ hs k),
    Submodule.map_span, ← Set.range_comp, monoLEToQuotPow_comp_basis] at h1
noncomputable def IsQuasiRegularSeq.quotPowBasis {f : ι → R} (h : IsQuasiRegularSeq M f)
    {κ : Type*} (b : Module.Basis κ A (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)))
    (m : κ → M) (hm : ∀ j, Submodule.Quotient.mk (m j) = b j) (k : ℕ) :
    Module.Basis (MonoDegLE ι k × κ) A
      (M ⧸ (Ideal.span (Set.range f) ^ (k + 1) • ⊤ : Submodule R M)) :=
  Module.Basis.mk
    (h.linearIndependent_monoVal_smul (m := m) (by simpa only [hm] using b.linearIndependent) k)
    (span_monoVal_smul_eq_top f (m := m) (by simpa only [hm] using b.span_eq) k).ge
@[simp] theorem IsQuasiRegularSeq.quotPowBasis_apply {f : ι → R} (h : IsQuasiRegularSeq M f)
    {κ : Type*} (b : Module.Basis κ A (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)))
    (m : κ → M) (hm : ∀ j, Submodule.Quotient.mk (m j) = b j) (k : ℕ) (p : MonoDegLE ι k × κ) :
    h.quotPowBasis b m hm k p = Submodule.Quotient.mk (monoVal f p.1.1 • m p.2) :=
  Module.Basis.mk_apply _ _ _
end Free
section FreeRing
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {f : ι → R}
  {A : Type*} [CommRing A] [Algebra A R]
variable (A) in

noncomputable def quotSMulTopEquivQuotOver (J : Ideal R) :
    (R ⧸ (J • ⊤ : Submodule R R)) ≃ₗ[A] R ⧸ J :=
  (Submodule.quotEquivOfEq (J • ⊤ : Submodule R R) J (by simp)).restrictScalars A
@[simp] theorem quotSMulTopEquivQuotOver_mk (J : Ideal R) (x : R) :
    quotSMulTopEquivQuotOver A J (Submodule.Quotient.mk x) = Ideal.Quotient.mk J x := rfl
noncomputable def IsQuasiRegularSeq.quotPowBasisSelf (h : IsQuasiRegularSeq R f)
    {κ : Type*} (b : Module.Basis κ A (R ⧸ Ideal.span (Set.range f)))
    (r : κ → R) (hr : ∀ j, Ideal.Quotient.mk _ (r j) = b j) (k : ℕ) :
    Module.Basis (MonoDegLE ι k × κ) A (R ⧸ Ideal.span (Set.range f) ^ (k + 1)) :=
  (h.quotPowBasis (b.map (quotSMulTopEquivQuotOver A _).symm) r (fun j => by
    rw [Module.Basis.map_apply, LinearEquiv.eq_symm_apply, quotSMulTopEquivQuotOver_mk, hr]) k).map
    (quotSMulTopEquivQuotOver A _)
theorem IsQuasiRegularSeq.nonempty_basis_quot_pow_self {ι : Type*} [Fintype ι] {f : ι → R}
    (h : IsQuasiRegularSeq R f) {d : ℕ} (b : Module.Basis (Fin d) A (R ⧸ Ideal.span (Set.range f)))
    (k : ℕ) :
    Nonempty (Module.Basis (Fin (d * (k + Fintype.card ι).choose (Fintype.card ι))) A
      (R ⧸ Ideal.span (Set.range f) ^ (k + 1))) := by
  choose r hr using fun j => Ideal.Quotient.mk_surjective (b j)
  refine ⟨(h.quotPowBasisSelf b r hr k).reindex (Fintype.equivFinOfCardEq ?_)⟩
  rw [Fintype.card_prod, MonoDegLE.card, Fintype.card_fin, mul_comm]
end FreeRing
universe u v
theorem IsQuasiRegularSeq.powers {R : Type u} [CommRing R] {n : ℕ} {f : Fin n → R}
    (h : IsQuasiRegularSeq R f) :
    (∀ x : R, IsSMulRegular (R ⧸ Ideal.span (Set.range f)) x → ∀ a : ℕ,
      IsSMulRegular (powGr (Ideal.span (Set.range f)) R a) x ∧
        IsSMulRegular (R ⧸ Ideal.span (Set.range f) ^ a) x) ∧
    (∀ [(Ideal.span (Set.range f)).IsPrime] (a : ℕ),
      (a ≠ 0 → (Ideal.span (Set.range f) ^ a).IsPrimary ∧
        (Ideal.span (Set.range f) ^ a).radical = Ideal.span (Set.range f)) ∧
      ((Ideal.span (Set.range f) ^ a).map
          (algebraMap R (Localization.AtPrime (Ideal.span (Set.range f))))).comap
        (algebraMap R (Localization.AtPrime (Ideal.span (Set.range f)))) =
          Ideal.span (Set.range f) ^ a ∧
      ∀ y : R, algebraMap R (Localization.AtPrime (Ideal.span (Set.range f))) y ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span (Set.range f))) ^ a ↔
        y ∈ Ideal.span (Set.range f) ^ a) ∧
    (∀ (A : Type v) [CommRing A] [Algebra A R] (d k : ℕ),
      Nonempty (Module.Basis (Fin d) A (R ⧸ Ideal.span (Set.range f))) →
      Nonempty (Module.Basis (Fin (d * (k + n).choose n)) A
        (R ⧸ Ideal.span (Set.range f) ^ (k + 1)))) := by
  refine ⟨fun x hx a => ⟨h.isSMulRegular_powGr_self hx a, h.isSMulRegular_quot_pow_self hx a⟩,
    fun a => ⟨fun ha => ⟨h.isPrimary_pow ha, radical_pow_of_isPrime _ ha⟩,
      h.comap_map_pow_atPrime _ a, h.algebraMap_mem_maximalIdeal_pow_iff _ a⟩, ?_⟩
  rintro A _ _ d k ⟨b⟩
  have := h.nonempty_basis_quot_pow_self b k
  rwa [Fintype.card_fin] at this
example : (MvPolynomial.idealOfVars (Fin 2) ℤ ^ 3).IsPrimary := by
  have : (Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ))).IsPrime := by
    have hk : Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) =
        RingHom.ker MvPolynomial.constantCoeff := by
      ext p
      rw [← pow_one (Ideal.span _), RingHom.mem_ker]
      refine (MvPolynomial.mem_pow_idealOfVars_iff' _ _).trans ?_
      simp [Finsupp.degree_eq_zero_iff, MvPolynomial.constantCoeff_eq]
    rw [hk]
    exact RingHom.ker_isPrime _
  exact (isQuasiRegularSeq_X (R := ℤ) (Fin 2)).isPrimary_pow (by norm_num)
example : Nonempty (Module.Basis (Fin 6) ℤ
    (MvPolynomial (Fin 2) ℤ ⧸ MvPolynomial.idealOfVars (Fin 2) ℤ ^ 3)) := by
  have hk : Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) =
      RingHom.ker (MvPolynomial.aeval (R := ℤ) fun _ : Fin 2 => (0 : ℤ)) := by
    ext p
    rw [← pow_one (Ideal.span _), RingHom.mem_ker]
    refine (MvPolynomial.mem_pow_idealOfVars_iff' _ _).trans ?_
    simp [Finsupp.degree_eq_zero_iff, MvPolynomial.constantCoeff_eq]
  have e := (Ideal.quotientEquivAlgOfEq ℤ hk).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := MvPolynomial.aeval (R := ℤ) fun _ : Fin 2 => (0 : ℤ))
      fun z => ⟨MvPolynomial.C z, by simp⟩)
  exact (isQuasiRegularSeq_X (R := ℤ) (Fin 2)).powers.2.2 ℤ 1 2
    ⟨(Module.Basis.singleton (Fin 1) ℤ).map e.symm.toLinearEquiv⟩
end GlobalTheory


