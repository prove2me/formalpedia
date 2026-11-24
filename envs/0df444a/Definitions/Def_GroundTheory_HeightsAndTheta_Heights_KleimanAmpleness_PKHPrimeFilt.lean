-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:45.020227+00:00
-- url     : https://prove2.me/theorems/83202855-7735-45c3-80a0-508da9d9ea91
-- title:
--   PKHPrime Filt
-- statement:
--   Definitions and structural lemmas for PKHPrime Filt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
namespace KHPrimeFilt
section Weight
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] (ι : K → Type)
  [∀ k, Fintype (ι k)]
def blockWeight : (Σ k, ι k) → Lex (K → ℕ) := fun p => toLex (Pi.single p.1 1)
variable {ι}
theorem ofLex_weight (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    ofLex (Finsupp.weight (blockWeight ι) d) k = ∑ i, d ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intros; simp)]
  change (∑ p : (Σ k, ι k), d p • (Pi.single p.1 1 : K → ℕ)) k = _
  rw [Finset.sum_apply, Fintype.sum_sigma]
  simp [Pi.single_apply]
theorem isMultiHomog_of_isWeightedHomogeneous {f : MRingOver S ι} {b : Lex (K → ℕ)}
    (h : IsWeightedHomogeneous (blockWeight ι) f b) : IsMultiHomog f (ofLex b) := by
  intro d hd k
  rw [← ofLex_weight, h (mem_support_iff.mp hd)]
end Weight
section Module
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} [DirectSum.Decomposition 𝓜]
def shift (e : K → ℤ) (b : Lex (K → ℕ)) : K → ℤ := e + fun k => (ofLex b k : ℤ)
theorem shift_injective (e : K → ℤ) : Function.Injective (shift e) := by
  intro a b h
  apply ofLex.injective
  funext k
  have := congrFun h k
  simp only [shift, Pi.add_apply, add_right_inj, Nat.cast_inj] at this
  exact this
abbrev colon (A : Submodule (MRingOver S ι) M) (g : M) : Ideal (MRingOver S ι) :=
  A.comap (LinearMap.toSpanSingleton (MRingOver S ι) M g)
theorem mem_colon {A : Submodule (MRingOver S ι) M} {g : M} {p : MRingOver S ι} :
    p ∈ colon A g ↔ p • g ∈ A := by
  simp [colon]
variable (𝓜) in

def IsGradedSub (A : Submodule (MRingOver S ι) M) : Prop :=
  ∀ m ∈ A, ∀ c, (DirectSum.decompose 𝓜 m c : M) ∈ A
theorem decompose_smul (hgr : IsMGraded S ι 𝓜) {g : M} {e : K → ℤ} (hg : g ∈ 𝓜 e)
    (r : MRingOver S ι) (b : Lex (K → ℕ)) :
    (DirectSum.decompose 𝓜 (r • g) (shift e b) : M) =
      weightedHomogeneousComponent (blockWeight ι) b r • g := by
  classical
  conv_lhs => rw [← r.support_sum_monomial_coeff]
  rw [Finset.sum_smul, DirectSum.decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum,
    weightedHomogeneousComponent_apply, Finset.sum_smul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hm : monomial d (coeff d r) • g ∈ 𝓜 (shift e (Finsupp.weight (blockWeight ι) d)) :=
    hgr.2 _ e _ g (isMultiHomog_of_isWeightedHomogeneous
      (isWeightedHomogeneous_monomial _ _ _ rfl)) hg
  split_ifs with h
  · rw [← h]
    exact DirectSum.decompose_of_mem_same _ hm
  · exact DirectSum.decompose_of_mem_ne _ hm fun h' => h (shift_injective e h')
theorem exists_homogeneous_notMem {A : Submodule (MRingOver S ι) M} (hne : A ≠ ⊤) :
    ∃ (g : M) (e : K → ℤ), g ∈ 𝓜 e ∧ g ∉ A := by
  classical
  by_contra! h
  apply hne
  rw [eq_top_iff]
  intro m _
  rw [← DirectSum.sum_support_decompose 𝓜 m]
  exact Submodule.sum_mem _ fun c _ => h _ c (SetLike.coe_mem _)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
abbrev lexDecEq : DecidableEq (Lex (K → ℕ)) := LinearOrder.toDecidableEq
attribute [local instance 2000] lexDecEq
theorem colon_isHomogeneous (hgr : IsMGraded S ι 𝓜) {A : Submodule (MRingOver S ι) M}
    (hA : IsGradedSub 𝓜 A) {g : M} {e : K → ℤ} (hg : g ∈ 𝓜 e) :
    (colon A g).IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι)) := by
  intro b r hr
  change ((weightedDecomposition S (blockWeight ι)).decompose' r b : MRingOver S ι) ∈ _
  rw [weightedDecomposition.decompose'_apply, mem_colon, ← decompose_smul hgr hg]
  exact hA _ (mem_colon.mp hr) _
theorem exists_prime_colon [IsNoetherianRing S] (hgr : IsMGraded S ι 𝓜)
    {A : Submodule (MRingOver S ι) M} (hA : IsGradedSub 𝓜 A) (hne : A ≠ ⊤) :
    ∃ ge : M × (K → ℤ), ge.1 ∈ 𝓜 ge.2 ∧ (colon A ge.1).IsPrime ∧
      (colon A ge.1).IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι)) := by
  obtain ⟨g0, e0, hg0, hg0A⟩ := exists_homogeneous_notMem (𝓜 := 𝓜) hne
  obtain ⟨I, ⟨g, e, hg, hgA, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr
      (inferInstance : IsNoetherian (MRingOver S ι) (MRingOver S ι))
      {I | ∃ (g : M) (e : K → ℤ), g ∈ 𝓜 e ∧ g ∉ A ∧ I = colon A g} ⟨_, g0, e0, hg0, hg0A, rfl⟩
  have hhom := colon_isHomogeneous hgr hA hg
  refine ⟨(g, e), hg, ?_, hhom⟩
  refine hhom.isPrime_of_homogeneous_mem_or_mem ?_ ?_
  · intro htop
    apply hgA
    have h1 : (1 : MRingOver S ι) ∈ colon A g := htop ▸ Submodule.mem_top
    simpa [mem_colon] using h1
  · rintro a b ⟨i, ha⟩ ⟨j, hb⟩ hab
    by_contra! hn
    obtain ⟨ha', hb'⟩ := hn
    have hag : a • g ∈ 𝓜 (shift e i) :=
      hgr.2 _ e a g (isMultiHomog_of_isWeightedHomogeneous
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mp ha)) hg
    have hagA : a • g ∉ A := fun h => ha' (mem_colon.mpr h)
    have hle : colon A g ≤ colon A (a • g) := fun p hp => by
      rw [mem_colon] at hp ⊢
      rw [smul_comm]
      exact A.smul_mem a hp
    have heq : colon A g = colon A (a • g) := by
      by_contra hne'
      exact hmax _ ⟨_, _, hag, hagA, rfl⟩ (lt_of_le_of_ne hle hne')
    apply hb'
    rw [heq, mem_colon, smul_smul, mul_comm]
    exact mem_colon.mp hab
variable (ι 𝓜)
open Classical in

def next [IsNoetherianRing S] (A : Submodule (MRingOver S ι) M) : M × (K → ℤ) :=
  if h : IsMGraded S ι 𝓜 ∧ IsGradedSub 𝓜 A ∧ A ≠ ⊤ then
    Classical.choose (exists_prime_colon h.1 h.2.1 h.2.2) else (0, 0)
def seq [IsNoetherianRing S] : ℕ → Submodule (MRingOver S ι) M
  | 0 => ⊥
  | j + 1 => seq j ⊔ Submodule.span (MRingOver S ι) {(next ι 𝓜 (seq j)).1}
def gen [IsNoetherianRing S] (j : ℕ) : M := (next ι 𝓜 (seq ι 𝓜 j)).1
variable {ι 𝓜}
end Module
end KHPrimeFilt
end GroundTheory.Heights₂.Heights.Kleiman


