-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
-- name    : GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:22.781064+00:00
-- url     : https://prove2.me/theorems/b16f520f-ec09-4665-b8d5-bf503b976f6f
-- title:
--   Lattice
-- statement:
--   Definitions and structural lemmas for Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Lattice.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Theorems.Thm_GroundTheory_Arith_Toric_hull_inf_halfspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
section Comb
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
theorem hull_basis_neg_eq_top {ι : Type*} (b : Basis ι 𝕜 E) :
    hull 𝕜 (Set.range b ∪ Set.range (fun i => -b i)) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have key : ∀ y ∈ Submodule.span 𝕜 (Set.range b),
      y ∈ hull 𝕜 (Set.range b ∪ Set.range (fun i => -b i)) ∧
        -y ∈ hull 𝕜 (Set.range b ∪ Set.range (fun i => -b i)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨subset_hull (Or.inl ⟨i, rfl⟩), subset_hull (Or.inr ⟨i, rfl⟩)⟩
    | zero => simp
    | add y z _ _ hy hz =>
      exact ⟨add_mem hy.1 hz.1, by rw [neg_add]; exact add_mem hy.2 hz.2⟩
    | smul c y _ hy =>
      rcases le_total 0 c with hc | hc
      · exact ⟨smul_mem _ hc hy.1, by rw [← smul_neg]; exact smul_mem _ hc hy.2⟩
      · refine ⟨?_, ?_⟩
        · rw [← neg_neg c, neg_smul, ← smul_neg]; exact smul_mem _ (neg_nonneg.2 hc) hy.2
        · rw [← neg_smul]; exact smul_mem _ (neg_nonneg.2 hc) hy.1
  exact (key x (by rw [b.span_eq]; exact Submodule.mem_top)).1
end Comb
section Integral
variable {L E : Type*} [AddCommGroup L] [AddCommGroup E] [Module ℝ E]
def IsRationalPolyhedral (ι : L →ₗ[ℤ] E) (σ : PointedCone ℝ E) : Prop :=
  ∃ S : Finset L, hull ℝ (ι '' S) = σ
theorem hull_image_inf_halfspace_int [DecidableEq L] (ι : L →ₗ[ℤ] E) (T : Finset L)
    (g : Dual ℝ E) (gL : L →ₗ[ℤ] ℤ) (hg : ∀ l, g (ι l) = gL l) :
    hull ℝ (ι '' T) ⊓ (positive ℝ ℝ).comap g =
      hull ℝ (ι '' ↑(T.filter (fun t => 0 ≤ gL t) ∪
        ((T ×ˢ T).filter (fun st => 0 < gL st.1 ∧ gL st.2 < 0)).image
          (fun st => gL st.1 • st.2 - gL st.2 • st.1))) := by
  classical
  have h := hull_inf_halfspace (𝕜 := ℝ) (T.image ι) g
  rw [Finset.coe_image] at h
  rw [h]
  have hcomb : ∀ a b, g (ι a) • ι b - g (ι b) • ι a = ι (gL a • b - gL b • a) := by
    intro a b
    simp [hg, map_sub, Int.cast_smul_eq_zsmul]
  congr 1
  ext y
  simp only [Finset.coe_union, Finset.coe_filter, Finset.coe_image, Set.mem_union,
    Set.mem_ofPred_eq, Set.mem_image, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro (⟨⟨a, ha, rfl⟩, hga⟩ | ⟨s, t, ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, h1, h2⟩, rfl⟩)
    · rw [hg] at hga
      exact ⟨a, Or.inl ⟨ha, by exact_mod_cast hga⟩, rfl⟩
    · rw [hg] at h1 h2
      refine ⟨gL a • b - gL b • a, Or.inr ⟨a, b, ⟨⟨ha, hb⟩, by exact_mod_cast h1,
        by exact_mod_cast h2⟩, rfl⟩, (hcomb a b).symm⟩
  · rintro ⟨l, (⟨hl, hgl⟩ | ⟨a, b, ⟨⟨ha, hb⟩, h1, h2⟩, rfl⟩), rfl⟩
    · exact Or.inl ⟨⟨l, hl, rfl⟩, by rw [hg]; exact_mod_cast hgl⟩
    · refine Or.inr ⟨ι a, ι b, ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, by rw [hg]; exact_mod_cast h1,
        by rw [hg]; exact_mod_cast h2⟩, hcomb a b⟩
def latticePoints (ι : L →ₗ[ℤ] E) (τ : PointedCone ℝ E) : AddSubmonoid L :=
  τ.toAddSubmonoid.comap ι.toAddMonoidHom
@[simp]
theorem mem_latticePoints {ι : L →ₗ[ℤ] E} {τ : PointedCone ℝ E} {m : L} :
    m ∈ latticePoints ι τ ↔ ι m ∈ τ := Iff.rfl
end Integral
section Lattice
variable (N : Type*) [AddCommGroup N]
def toRealSpan : N →ₗ[ℤ] ℝ ⊗[ℤ] N := TensorProduct.mk ℤ ℝ N 1
def toRealDual : Dual ℤ N →ₗ[ℤ] Dual ℝ (ℝ ⊗[ℤ] N) := Module.Dual.baseChange ℝ
variable {N}
theorem toRealSpan_apply (n : N) : toRealSpan N n = (1 : ℝ) ⊗ₜ n := rfl
@[simp]
theorem toRealDual_apply_toRealSpan (m : Dual ℤ N) (n : N) :
    toRealDual N m (toRealSpan N n) = (m n : ℝ) := by
  simp [toRealDual, toRealSpan_apply, Module.Dual.baseChange_apply_tmul]
theorem toRealDual_dualBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι ℤ N) (j : ι) :
    toRealDual N (e.dualBasis j) = (e.baseChange ℝ).dualBasis j := by
  refine (e.baseChange ℝ).ext fun i => ?_
  rw [Basis.dualBasis_apply_self, Basis.baseChange_apply, ← toRealSpan_apply,
    toRealDual_apply_toRealSpan, Basis.dualBasis_apply_self]
  split_ifs <;> simp
variable [Module.Free ℤ N] [Module.Finite ℤ N]
theorem isRationalPolyhedral_top_dual :
    IsRationalPolyhedral (toRealDual N) (⊤ : PointedCone ℝ (Dual ℝ (ℝ ⊗[ℤ] N))) := by
  classical
  let e := Module.Free.chooseBasis ℤ N
  refine ⟨Finset.univ.image e.dualBasis ∪ Finset.univ.image (fun j => -e.dualBasis j), ?_⟩
  have h1 : (toRealDual N ∘ e.dualBasis) = (e.baseChange ℝ).dualBasis :=
    funext fun j => toRealDual_dualBasis e j
  have h2 : (toRealDual N ∘ fun j => -e.dualBasis j) = fun j => -(e.baseChange ℝ).dualBasis j :=
    funext fun j => by simp only [Function.comp_apply, map_neg, toRealDual_dualBasis]
  rw [← hull_basis_neg_eq_top (e.baseChange ℝ).dualBasis, Finset.coe_union, Finset.coe_image,
    Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.image_univ, Set.image_union,
    ← Set.range_comp, ← Set.range_comp, h1, h2]
theorem IsRationalPolyhedral.dual {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) :
    IsRationalPolyhedral (toRealDual N) (dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ : Set (ℝ ⊗[ℤ] N))) := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  rw [dual_hull]
  induction S using Finset.induction_on with
  | empty => simpa using isRationalPolyhedral_top_dual
  | insert n S _ ih =>
    obtain ⟨T, hT⟩ := ih
    rw [Finset.coe_insert, Set.image_insert_eq, dual_insert, dual_singleton, inf_comm, ← hT,
      hull_image_inf_halfspace_int (toRealDual N) T _ (Dual.eval ℤ N n) (fun m => by simp)]
    exact ⟨_, rfl⟩
end Lattice
section Duality
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
end Duality
section Operations
variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]
end Operations
section Gordan
variable {N : Type*} [AddCommGroup N]
def dualMonoid (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) : AddSubmonoid (Dual ℤ N) :=
  latticePoints (toRealDual N) (dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ : Set (ℝ ⊗[ℤ] N)))
variable [Module.Free ℤ N] [Module.Finite ℤ N]
end Gordan
end GroundTheory.Arith.Toric


