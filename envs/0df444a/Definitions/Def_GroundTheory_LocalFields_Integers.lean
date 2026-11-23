-- Prove2me | Definitions.Def_GroundTheory_LocalFields_Integers
-- name    : GroundTheory_LocalFields_Integers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:13.895917+00:00
-- url     : https://prove2.me/theorems/413063d4-61b2-42e4-ade2-58941110b354
-- title:
--   Integers
-- statement:
--   Definitions and structural lemmas for Integers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Integers.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel
section Algebraic
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]
abbrev ramificationIndex : ℕ := (IsLocalRing.maximalIdeal 𝒪[L]).ramificationIdx 𝒪[K]
abbrev residueDegree : ℕ := (IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg 𝒪[K]
end Algebraic
section Topological
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
instance t2Space : T2Space L := by
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  infer_instance
variable [FiniteDimensional K L]
theorem exists_basis_coord_bound : ∃ a : K, a ≠ 0 ∧ ∀ x : L, valuation L x ≤ 1 →
    ∀ i, valuation K ((Module.finBasis K L).repr x i / a) ≤ 1 := by
  let := normedField K
  have := normedField_completeSpace K
  let b := Module.finBasis K L
  let e := b.equivFun.toContinuousLinearEquiv
  have hc : IsCompact (e '' {x : L | valuation L x ≤ 1}) :=
    (IsNonarchimedeanLocalField.isCompact_closedBall L 1).image e.continuous
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hc.isBounded
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm K (max r 1)
  have ha0 : 0 < ‖a‖ := lt_of_lt_of_le zero_lt_one (le_max_right r 1) |>.trans ha
  refine ⟨a, norm_pos_iff.1 ha0, fun x hx i => ?_⟩
  have h1 : ‖e x‖ ≤ r := by simpa using hr ⟨x, hx, rfl⟩
  have h2 : ‖b.repr x i‖ ≤ r := (norm_le_pi_norm (e x) i).trans h1
  have h3 : ‖b.repr x i / a‖ ≤ ‖(1 : K)‖ := by
    rw [norm_div, norm_one, div_le_one ha0]
    exact h2.trans ((le_max_left r 1).trans ha.le)
  have := (normedField_norm_le_norm_iff K _ _).1 h3
  rwa [(valuation K).vle_iff_le, map_one] at this
theorem finite_integer : Module.Finite 𝒪[K] 𝒪[L] := by
  obtain ⟨a, ha, hb⟩ := exists_basis_coord_bound K L
  let b := Module.finBasis K L
  let N : Submodule 𝒪[K] L := Submodule.span 𝒪[K] (Set.range fun i => a • b i)
  have hN : N.FG := Submodule.fg_span (Set.finite_range _)
  have : IsNoetherian 𝒪[K] N := isNoetherian_of_fg_of_noetherian N hN
  have hmem : ∀ x : 𝒪[L], (x : L) ∈ N := by
    intro x
    have hx : valuation L (x : L) ≤ 1 := x.2
    rw [← b.sum_repr (x : L)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc := hb x hx i
    have : b.repr x i • b i = (⟨b.repr x i / a, hc⟩ : 𝒪[K]) • (a • b i) := by
      rw [← algebraMap_smul K (⟨_, hc⟩ : 𝒪[K]) (a • b i), smul_smul]
      congr 1
      exact (div_mul_cancel₀ _ ha).symm
    rw [this]
    exact N.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : 𝒪[L] →ₗ[𝒪[K]] N :=
    LinearMap.codRestrict N ((IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L).toLinearMap) fun x => hmem x
  refine Module.Finite.of_injective f fun x y h => ?_
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'
instance : Module.Finite 𝒪[K] 𝒪[L] := finite_integer K L
theorem free_integer : Module.Free 𝒪[K] 𝒪[L] := Module.free_of_finite_type_torsion_free'
instance : Module.Free 𝒪[K] 𝒪[L] := free_integer K L
theorem isIntegral_iff (x : L) : IsIntegral 𝒪[K] x ↔ valuation L x ≤ 1 := by
  constructor
  · intro hx
    have h2 : IsIntegral 𝒪[L] x := hx.tower_top
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact y.2
  · intro hx
    have : IsIntegral 𝒪[K] (⟨x, hx⟩ : 𝒪[L]) := Algebra.IsIntegral.isIntegral _
    exact this.map (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L)
instance isIntegralClosure : IsIntegralClosure 𝒪[L] 𝒪[K] L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    rw [isIntegral_iff]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
theorem primesOver_eq : (IsLocalRing.maximalIdeal 𝒪[K]).primesOver 𝒪[L] =
    {IsLocalRing.maximalIdeal 𝒪[L]} := by
  ext P
  constructor
  · rintro ⟨hP, hl⟩
    have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (IsLocalRing.maximalIdeal 𝒪[K])
    exact IsLocalRing.eq_maximalIdeal this
  · rintro rfl
    exact ⟨inferInstance, inferInstance⟩
instance uniquePrimesOver : Unique ((IsLocalRing.maximalIdeal 𝒪[K]).primesOver 𝒪[L]) where
  default := ⟨IsLocalRing.maximalIdeal 𝒪[L], inferInstance, inferInstance⟩
  uniq P := Subtype.ext (Set.mem_singleton_iff.1 ((Set.ext_iff.1 (primesOver_eq K L) P.1).1 P.2))
end Topological
section Tower
variable (K L M : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Field M] [ValuativeRel M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
variable [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
instance isScalarTower_integer : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
  IsScalarTower.of_algebraMap_eq fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply K L M (x : K))
end Tower
end GroundTheory.LocalField


