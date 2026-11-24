-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
-- name    : GroundTheory_AutomorphicForms_SmoothRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:33.501243+00:00
-- url     : https://prove2.me/theorems/1b886608-9022-4176-9b9f-f801e3deaafe
-- title:
--   Smooth Rep
-- statement:
--   Definitions and structural lemmas for Smooth Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Theorems.Thm_GroundTheory_Automorphic_exists_compactOpenSubgroup_normalized

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Set Filter Topology
section General
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)
noncomputable def stabilizerOf (v : V) : Subgroup G :=
  @_root_.UpperTheory.Reformulated.B.StabilizerOf.stabilizerOf G _ V _ _ ρ v
variable {ρ} in
theorem mem_stabilizerOf {v : V} {g : G} : g ∈ stabilizerOf ρ v ↔ ρ g v = v := Iff.rfl
def fixedVectors (H : Subgroup G) : Submodule ℂ V where
  carrier := {v | ∀ h ∈ H, ρ h v = v}
  add_mem' {v w} hv hw h hh := by simp [hv h hh, hw h hh]
  zero_mem' h _ := map_zero _
  smul_mem' c v hv h hh := by simp [hv h hh]
abbrev coinvariantsKer (H : Subgroup G) : Submodule ℂ V :=
  Representation.Coinvariants.ker (ρ.comp H.subtype)
variable {ρ} in
theorem sub_mem_coinvariantsKer {H : Subgroup G} {h : G} (hh : h ∈ H) (v : V) :
    ρ h v - v ∈ coinvariantsKer ρ H :=
  Representation.Coinvariants.sub_mem_ker (ρ := ρ.comp H.subtype) ⟨h, hh⟩ v
theorem map_mem_fixedVectors {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (f : Representation.IntertwiningMap ρ σ) {H : Subgroup G} {v : V}
    (hv : v ∈ fixedVectors ρ H) : f v ∈ fixedVectors σ H := fun h hh => by
  rw [← f.isIntertwining, hv h hh]
def fixedMap {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (f : Representation.IntertwiningMap ρ σ) (H : Subgroup G) :
    fixedVectors ρ H →ₗ[ℂ] fixedVectors σ H :=
  f.toLinearMap.restrict fun _ hv => map_mem_fixedVectors ρ f hv
section CosetSum
variable (K N : Subgroup G)
def cosetSum : Module.End ℂ V :=
  ∑ᶠ q : K ⧸ N.subgroupOf K, ρ ((Quotient.out q : K) : G)
variable {K N}
theorem cosetSum_apply [Fintype (K ⧸ N.subgroupOf K)] (v : V) :
    cosetSum ρ K N v = ∑ q : K ⧸ N.subgroupOf K, ρ ((Quotient.out q : K) : G) v := by
  rw [cosetSum, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
theorem act_eq_of_mk_eq {v : V} (hv : v ∈ fixedVectors ρ N) {a b : K}
    (h : (a : K ⧸ N.subgroupOf K) = b) : ρ (a : G) v = ρ (b : G) v := by
  rw [QuotientGroup.eq] at h
  have hab : ρ ((a⁻¹ * b : K) : G) v = v := hv _ (Subgroup.mem_subgroupOf.1 h)
  calc ρ (a : G) v = ρ (a : G) (ρ ((a⁻¹ * b : K) : G) v) := by rw [hab]
    _ = ρ (b : G) v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
theorem cosetSum_mem_fixedVectors (hnorm : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    [Fintype (K ⧸ N.subgroupOf K)] {v : V} (hv : v ∈ fixedVectors ρ N) :
    cosetSum ρ K N v ∈ fixedVectors ρ K := by
  have : (N.subgroupOf K).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (by simpa using hnorm g g.2 n hn)⟩
  intro k hk
  rw [cosetSum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft ((⟨k, hk⟩ : K) : K ⧸ N.subgroupOf K)) _ _ fun q => ?_
  rw [← Module.End.mul_apply, ← map_mul]
  have := act_eq_of_mk_eq ρ hv (a := ⟨k, hk⟩ * Quotient.out q)
    (b := Quotient.out (((⟨k, hk⟩ : K) : K ⧸ N.subgroupOf K) * q)) (by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq'])
  simpa using this
theorem cosetSum_apply_act (hnorm : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    [Fintype (K ⧸ N.subgroupOf K)] {u : V} (hu : u ∈ fixedVectors ρ N) {k : G} (hk : k ∈ K) :
    cosetSum ρ K N (ρ k u) = cosetSum ρ K N u := by
  have : (N.subgroupOf K).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (by simpa using hnorm g g.2 n hn)⟩
  rw [cosetSum_apply, cosetSum_apply]
  refine Fintype.sum_equiv (Equiv.mulRight ((⟨k, hk⟩ : K) : K ⧸ N.subgroupOf K)) _ _ fun q => ?_
  rw [← Module.End.mul_apply, ← map_mul]
  have := act_eq_of_mk_eq ρ hu (a := Quotient.out q * ⟨k, hk⟩)
    (b := Quotient.out (q * ((⟨k, hk⟩ : K) : K ⧸ N.subgroupOf K))) (by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq'])
  simpa using this
theorem cosetSum_of_mem [Fintype (K ⧸ N.subgroupOf K)] {v : V} (hv : v ∈ fixedVectors ρ K) :
    cosetSum ρ K N v = (Fintype.card (K ⧸ N.subgroupOf K) : ℂ) • v := by
  rw [cosetSum_apply, Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun q _ => hv _ (Quotient.out q).2
end CosetSum
variable [TopologicalSpace G]
def IsSmooth : Prop := ∀ v : V, IsOpen (stabilizerOf ρ v : Set G)
variable [IsTopologicalGroup G]
def smoothVectors : Submodule ℂ V where
  carrier := {v | IsOpen (stabilizerOf ρ v : Set G)}
  add_mem' {v w} hv hw := by
    refine Subgroup.isOpen_mono (H₁ := stabilizerOf ρ v ⊓ stabilizerOf ρ w) ?_ ?_
    · intro g hg
      simp [mem_stabilizerOf, mem_stabilizerOf.1 (Subgroup.mem_inf.1 hg).1,
        mem_stabilizerOf.1 (Subgroup.mem_inf.1 hg).2]
    · rw [Subgroup.coe_inf]
      exact hv.inter hw
  zero_mem' := by
    have : (stabilizerOf ρ (0 : V) : Set G) = univ := by
      ext g
      simp [mem_stabilizerOf]
    simp only [Set.mem_ofPred_eq, this, isOpen_univ]
  smul_mem' c v hv := Subgroup.isOpen_mono (H₁ := stabilizerOf ρ v)
    (fun g hg => by simp [mem_stabilizerOf, mem_stabilizerOf.1 hg]) hv
variable {ρ} in
theorem mem_smoothVectors {v : V} : v ∈ smoothVectors ρ ↔ IsOpen (stabilizerOf ρ v : Set G) :=
  Iff.rfl
theorem smooth_apply_mem {v : V} (hv : v ∈ smoothVectors ρ) (g : G) :
    ρ g v ∈ smoothVectors ρ := by
  rw [mem_smoothVectors] at hv ⊢
  apply Subgroup.isOpen_of_mem_nhds (g := 1) _
  have hc : Continuous fun x : G => g⁻¹ * x * g := by fun_prop
  have h1 : (fun x : G => g⁻¹ * x * g) ⁻¹' (stabilizerOf ρ v : Set G) ∈ 𝓝 (1 : G) :=
    (hv.preimage hc).mem_nhds (by simp)
  refine mem_of_superset h1 fun x hx => ?_
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_stabilizerOf] at hx ⊢
  conv_rhs => rw [← hx]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group
def smoothPart : Representation ℂ G (smoothVectors ρ) :=
  ρ.subrepresentation (smoothVectors ρ) fun g _ hv => smooth_apply_mem ρ hv g
@[simp]
theorem coe_smoothPart_apply (g : G) (v : smoothVectors ρ) :
    ((smoothPart ρ g v : smoothVectors ρ) : V) = ρ g v := rfl
def IsAdmissible : Prop :=
  IsSmooth ρ ∧ ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
    FiniteDimensional ℂ (fixedVectors ρ K)
end General
section LocallyProfinite
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
section Average
variable {K : Subgroup G}
theorem exists_normal_subgroup (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ N : Subgroup G, IsOpen (N : Set G) ∧ N ≤ K ∧ (N : Set G) ⊆ U ∧
      (∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) ∧ Finite (K ⧸ N.subgroupOf K) := by
  obtain ⟨N, -, hNU, hnorm⟩ := exists_compactOpenSubgroup_normalized hKc
    (inter_mem hU (hKo.mem_nhds (one_mem K)))
  refine ⟨N, N.isOpen, fun x hx => (hNU hx).2, fun x hx => (hNU hx).1, hnorm, ?_⟩
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  refine Subgroup.quotient_finite_of_isOpen _ ?_
  rw [Subgroup.coe_subgroupOf]
  exact N.isOpen.preimage continuous_subtype_val
end Average
section Decomposition
variable {ρ} {K : Subgroup G}
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem exists_nhds_cosetSum_eq_zero (hρ : IsSmooth ρ) {x : V} (hx : x ∈ coinvariantsKer ρ K) :
    ∃ U ∈ 𝓝 (1 : G), ∀ N : Subgroup G, (N : Set G) ⊆ U →
      (∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) → ∀ _ : Fintype (K ⧸ N.subgroupOf K),
        cosetSum ρ K N x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨k, u⟩, rfl⟩ := hx
    refine ⟨stabilizerOf ρ u, (hρ u).mem_nhds (one_mem _), fun N hNU hnorm _ => ?_⟩
    have hu : u ∈ fixedVectors ρ N := fun n hn => hNU hn
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, map_sub]
    rw [cosetSum_apply_act ρ hnorm hu k.2, sub_self]
  | zero => exact ⟨univ, univ_mem, fun _ _ _ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, hU₁, h₁⟩ := hx
    obtain ⟨U₂, hU₂, h₂⟩ := hy
    refine ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, fun N hNU hnorm hfin => ?_⟩
    rw [map_add, h₁ N (hNU.trans inter_subset_left) hnorm hfin,
      h₂ N (hNU.trans inter_subset_right) hnorm hfin, add_zero]
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun N hNU hnorm hfin => by rw [map_smul, h N hNU hnorm hfin, smul_zero]⟩
theorem disjoint_fixedVectors_coinvariantsKer (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) : Disjoint (fixedVectors ρ K) (coinvariantsKer ρ K) := by
  rw [Submodule.disjoint_def]
  intro w hw hw'
  obtain ⟨U, hU, hUw⟩ := exists_nhds_cosetSum_eq_zero hρ hw'
  obtain ⟨N, -, -, hNU, hnorm, hfin⟩ := exists_normal_subgroup hKc hKo hU
  have := Fintype.ofFinite (K ⧸ N.subgroupOf K)
  have h := hUw N hNU hnorm inferInstance
  rw [cosetSum_of_mem ρ hw] at h
  exact (smul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
theorem codisjoint_fixedVectors_coinvariantsKer (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) : Codisjoint (fixedVectors ρ K) (coinvariantsKer ρ K) := by
  rw [codisjoint_iff, eq_top_iff]
  intro v _
  obtain ⟨N, -, hNK, hNU, hnorm, hfin⟩ := exists_normal_subgroup hKc hKo ((hρ v).mem_nhds
    (one_mem (stabilizerOf ρ v)))
  have := Fintype.ofFinite (K ⧸ N.subgroupOf K)
  have hv : v ∈ fixedVectors ρ N := fun n hn => hNU hn
  set n : ℂ := (Fintype.card (K ⧸ N.subgroupOf K) : ℂ)
  have hn : n ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine Submodule.mem_sup.2 ⟨n⁻¹ • cosetSum ρ K N v,
    Submodule.smul_mem _ _ (cosetSum_mem_fixedVectors ρ hnorm hv), v - n⁻¹ • cosetSum ρ K N v,
    ?_, add_sub_cancel _ _⟩
  have heq : v - n⁻¹ • cosetSum ρ K N v =
      n⁻¹ • ∑ q : K ⧸ N.subgroupOf K, (v - ρ ((Quotient.out q : K) : G) v) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← cosetSum_apply, smul_sub,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [heq]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
  rw [← neg_sub]
  exact Submodule.neg_mem _ (sub_mem_coinvariantsKer (Quotient.out q).2 v)
theorem isCompl_fixedVectors_coinvariantsKer (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) : IsCompl (fixedVectors ρ K) (coinvariantsKer ρ K) :=
  ⟨disjoint_fixedVectors_coinvariantsKer hρ hKc hKo,
    codisjoint_fixedVectors_coinvariantsKer hρ hKc hKo⟩
variable (ρ) in

def fixedProj (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    V →ₗ[ℂ] fixedVectors ρ K :=
  Submodule.projectionOnto _ _ (isCompl_fixedVectors_coinvariantsKer hρ hKc hKo)
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo
end Decomposition
section Exactness
variable {W X : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
  {ρ} {σ : Representation ℂ G W} {τ : Representation ℂ G X} {K : Subgroup G}
end Exactness
end LocallyProfinite
end GroundTheory.Automorphic


