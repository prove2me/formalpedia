-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationExists
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:09.170676+00:00
-- url     : https://prove2.me/theorems/a5362d4f-cf67-4ae7-b4fd-29c1e12ea367
-- title:
--   PPrime Filtration Exists
-- statement:
--   Definitions and structural lemmas for PPrime Filtration Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationExists.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
section Length
variable {R : Type*} [CommRing R] {L : Type*} [AddCommGroup L] [Module R L]
abbrev colonIdeal (A : Submodule R L) (y : L) : Ideal R :=
  A.comap (LinearMap.toSpanSingleton R L y)
theorem mem_colonIdeal {A : Submodule R L} {y : L} {r : R} : r ∈ colonIdeal A y ↔ r • y ∈ A := by
  simp [colonIdeal]
end Length
namespace GradedPMod
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  (𝓜 : GradedPMod S N M) [DirectSum.Decomposition 𝓜.piece]
def IsGradedSub (A : Submodule (Poly S N) M) : Prop :=
  ∀ m ∈ A, ∀ c, (DirectSum.decompose 𝓜.piece m c : M) ∈ A
variable {𝓜}
theorem decompose_smul_eq {g : M} {e : ℤ} (hg : g ∈ 𝓜.piece e) (r : Poly S N) (c : ℤ) :
    (DirectSum.decompose 𝓜.piece (r • g) c : M) =
      ∑ i ∈ Finset.range (r.totalDegree + 1),
        if e + (i : ℤ) = c then homogeneousComponent i r • g else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent r]
  rw [Finset.sum_smul, DirectSum.decompose_sum]
  rw [DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm := 𝓜.smul_mem i e _ g (homogeneousComponent_isHomogeneous i r) hg
  split_ifs with h
  · subst h; exact DirectSum.decompose_of_mem_same _ hm
  · exact DirectSum.decompose_of_mem_ne _ hm h
theorem decompose_smul_add {g : M} {e : ℤ} (hg : g ∈ 𝓜.piece e) (r : Poly S N) (d : ℕ) :
    (DirectSum.decompose 𝓜.piece (r • g) (e + d) : M) = homogeneousComponent d r • g := by
  rw [decompose_smul_eq hg]
  simp only [add_right_inj, Nat.cast_inj, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero d r (by omega), zero_smul]
theorem isGradedSub_bot : 𝓜.IsGradedSub ⊥ := by
  intro m hm c
  rw [(Submodule.mem_bot _).mp hm, DirectSum.decompose_zero]
  exact Submodule.zero_mem _
theorem isGradedSub_sup_span {A : Submodule (Poly S N) M} (hA : 𝓜.IsGradedSub A) {g : M} {e : ℤ}
    (hg : g ∈ 𝓜.piece e) : 𝓜.IsGradedSub (A ⊔ Submodule.span (Poly S N) {g}) := by
  intro m hm c
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, decompose_smul_eq hg]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (hA a ha c)) (Submodule.sum_mem _ fun i _ => ?_)
  split_ifs
  · exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g))
  · exact Submodule.zero_mem _
theorem homogeneousComponent_mem_colonIdeal {A : Submodule (Poly S N) M} (hA : 𝓜.IsGradedSub A)
    {g : M} {e : ℤ} (hg : g ∈ 𝓜.piece e) {r : Poly S N} (hr : r ∈ colonIdeal A g) (d : ℕ) :
    homogeneousComponent d r ∈ colonIdeal A g := by
  rw [mem_colonIdeal, ← decompose_smul_add hg]
  exact hA _ (mem_colonIdeal.mp hr) _
theorem exists_homogeneous_notMem {A : Submodule (Poly S N) M} (hne : A ≠ ⊤) :
    ∃ (g : M) (e : ℤ), g ∈ 𝓜.piece e ∧ g ∉ A := by
  classical
  by_contra! h
  apply hne
  rw [eq_top_iff]
  intro m _
  rw [← DirectSum.sum_support_decompose 𝓜.piece m]
  exact Submodule.sum_mem _ fun c _ => h _ c (SetLike.coe_mem _)
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem exists_isPrime_colonIdeal [IsNoetherianRing S] {A : Submodule (Poly S N) M}
    (hA : 𝓜.IsGradedSub A) (hne : A ≠ ⊤) :
    ∃ ge : M × ℤ, ge.1 ∈ 𝓜.piece ge.2 ∧ (colonIdeal A ge.1).IsPrime ∧
      ∀ p ∈ colonIdeal A ge.1, ∀ d : ℕ, homogeneousComponent d p ∈ colonIdeal A ge.1 := by
  obtain ⟨g0, e0, hg0, hg0A⟩ := exists_homogeneous_notMem (𝓜 := 𝓜) hne
  obtain ⟨I, ⟨g, e, hg, hgA, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian (Poly S N) (Poly S N))
      {I | ∃ (g : M) (e : ℤ), g ∈ 𝓜.piece e ∧ g ∉ A ∧ I = colonIdeal A g}
      ⟨_, g0, e0, hg0, hg0A, rfl⟩
  refine ⟨(g, e), hg, ?_, fun p hp d => homogeneousComponent_mem_colonIdeal hA hg hp d⟩
  refine Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
    (𝒜 := homogeneousSubmodule (Fin (N + 1)) S) ?_ ?_ ?_
  · intro i r hr
    change (decomposition.decompose' r i : Poly S N) ∈ _
    rw [decomposition.decompose'_apply]
    exact homogeneousComponent_mem_colonIdeal hA hg hr i
  · intro htop
    apply hgA
    have h1 : (1 : Poly S N) ∈ colonIdeal A g := htop ▸ Submodule.mem_top
    simpa [mem_colonIdeal] using h1
  · rintro a b ⟨i, ha⟩ ⟨j, hb⟩ hab
    by_contra! hn
    obtain ⟨ha', hb'⟩ := hn
    have hag : a • g ∈ 𝓜.piece (e + i) :=
      𝓜.smul_mem i e a g ((mem_homogeneousSubmodule _ _).mp ha) hg
    have hagA : a • g ∉ A := fun h => ha' (mem_colonIdeal.mpr h)
    have hle : colonIdeal A g ≤ colonIdeal A (a • g) := fun p hp => by
      rw [mem_colonIdeal] at hp ⊢
      rw [smul_comm]
      exact A.smul_mem a hp
    have heq : colonIdeal A g = colonIdeal A (a • g) := by
      by_contra hne'
      exact hmax _ ⟨_, _, hag, hagA, rfl⟩ (lt_of_le_of_ne hle hne')
    apply hb'
    rw [heq, mem_colonIdeal, smul_smul, mul_comm]
    exact mem_colonIdeal.mp hab
variable (𝓜)
open Classical in

def primeFiltNext [IsNoetherianRing S] (A : Submodule (Poly S N) M) : M × ℤ :=
  if h : 𝓜.IsGradedSub A ∧ A ≠ ⊤ then Classical.choose (exists_isPrime_colonIdeal h.1 h.2) else (0, 0)
theorem primeFiltNext_mem [IsNoetherianRing S] (A : Submodule (Poly S N) M) :
    (𝓜.primeFiltNext A).1 ∈ 𝓜.piece (𝓜.primeFiltNext A).2 := by
  unfold primeFiltNext
  split_ifs with h
  · exact (Classical.choose_spec (exists_isPrime_colonIdeal h.1 h.2)).1
  · exact Submodule.zero_mem _
theorem primeFiltNext_spec [IsNoetherianRing S] {A : Submodule (Poly S N) M}
    (hA : 𝓜.IsGradedSub A) (hne : A ≠ ⊤) :
    (colonIdeal A (𝓜.primeFiltNext A).1).IsPrime ∧
      ∀ p ∈ colonIdeal A (𝓜.primeFiltNext A).1, ∀ d : ℕ,
        homogeneousComponent d p ∈ colonIdeal A (𝓜.primeFiltNext A).1 := by
  unfold primeFiltNext
  rw [dif_pos ⟨hA, hne⟩]
  exact (Classical.choose_spec (exists_isPrime_colonIdeal hA hne)).2
def primeFiltSeq [IsNoetherianRing S] : ℕ → Submodule (Poly S N) M
  | 0 => ⊥
  | k + 1 => primeFiltSeq k ⊔ Submodule.span (Poly S N) {(𝓜.primeFiltNext (primeFiltSeq k)).1}
theorem primeFiltSeq_isGradedSub [IsNoetherianRing S] (k : ℕ) :
    𝓜.IsGradedSub (𝓜.primeFiltSeq k) := by
  induction k with
  | zero => exact isGradedSub_bot
  | succ k ih => exact isGradedSub_sup_span ih (𝓜.primeFiltNext_mem _)
theorem exists_primeFiltSeq_eq_top [IsNoetherianRing S] [Module.Finite (Poly S N) M] :
    ∃ n, 𝓜.primeFiltSeq n = ⊤ := by
  have hmono : Monotone 𝓜.primeFiltSeq := monotone_nat_of_le_succ fun k => le_sup_left
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian (Poly S N) M) ⟨𝓜.primeFiltSeq, hmono⟩
  refine ⟨n, by_contra fun hne => ?_⟩
  have hp := (𝓜.primeFiltNext_spec (𝓜.primeFiltSeq_isGradedSub n) hne).1
  apply hp.ne_top
  rw [Ideal.eq_top_iff_one, mem_colonIdeal, one_smul]
  have h1 : (𝓜.primeFiltNext (𝓜.primeFiltSeq n)).1 ∈ 𝓜.primeFiltSeq (n + 1) :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have h2 : 𝓜.primeFiltSeq n = 𝓜.primeFiltSeq (n + 1) := hn (n + 1) (Nat.le_succ n)
  rwa [← h2] at h1
open Classical in

def primeFilt [IsNoetherianRing S] [Module.Finite (Poly S N) M] : PrimeFilt 𝓜 where
  n := Nat.find 𝓜.exists_primeFiltSeq_eq_top
  step i := 𝓜.primeFiltSeq i
  gen k := (𝓜.primeFiltNext (𝓜.primeFiltSeq k)).1
  deg k := (𝓜.primeFiltNext (𝓜.primeFiltSeq k)).2
  prime k := colonIdeal (𝓜.primeFiltSeq k) (𝓜.primeFiltNext (𝓜.primeFiltSeq k)).1
  step_zero := rfl
  step_last := Nat.find_spec 𝓜.exists_primeFiltSeq_eq_top
  step_succ k := rfl
  gen_mem k := 𝓜.primeFiltNext_mem _
  mem_prime k p := mem_colonIdeal
  isPrime k := (𝓜.primeFiltNext_spec (𝓜.primeFiltSeq_isGradedSub k)
    (Nat.find_min 𝓜.exists_primeFiltSeq_eq_top k.2)).1
  isHomogeneous k := (𝓜.primeFiltNext_spec (𝓜.primeFiltSeq_isGradedSub k)
    (Nat.find_min 𝓜.exists_primeFiltSeq_eq_top k.2)).2
  ann_le k p hp := by
    rw [mem_colonIdeal, (Module.mem_annihilator.mp hp)]
    exact Submodule.zero_mem _
end GradedPMod
namespace PrimeFilt
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  {𝓜 : GradedPMod S N M}
end PrimeFilt
end
end GroundTheory.Heights₂.Heights.Kleiman


