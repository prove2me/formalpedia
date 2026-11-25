-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_RatIntUnifDiscrete
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_RatIntUnifDiscrete
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:03:10.384283+00:00
-- url     : https://prove2.me/theorems/bfba0b9f-799c-4df3-bd09-0b73b8c0865e
-- title:
--   Rat Int Unif Discrete
-- statement:
--   Definitions and structural lemmas for Rat Int Unif Discrete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/RatIntUnifDiscrete.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.TB
open NumberField
structure NormFam (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] where
  N : (K →+* ℂ) → V → ℝ
  nonneg : ∀ σ v, 0 ≤ N σ v
  eq_zero : ∀ σ v, N σ v = 0 → v = 0
  smul : ∀ σ (a : K) v, N σ (a • v) = ‖σ a‖ * N σ v
  add : ∀ σ v w, N σ (v + w) ≤ N σ v + N σ w
section Defs
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V]
def ProdLower (Nf : NormFam K V) (M : Submodule (𝓞 K) V) (A : ℝ) : Prop :=
  ∀ f ∈ M, f ≠ 0 → -A ≤ ∑ σ : K →+* ℂ, Real.log (Nf.N σ f)
def UnifDiscrete (Nf : NormFam K V) (M : Submodule (𝓞 K) V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ f ∈ M, (∀ σ, Nf.N σ f < ε) → f = 0
end Defs
def DiscOfProdLowerSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (Nf : NormFam K V) (M : Submodule (𝓞 K) V) (A : ℝ),
    ProdLower Nf M A → UnifDiscrete Nf M
def FGOfDiscSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    (Nf : NormFam K V) (M : Submodule (𝓞 K) V),
    UnifDiscrete Nf M → M.FG
def IsLatticeOfDiscSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    (Nf : NormFam K V) (M : Submodule (𝓞 K) V),
    UnifDiscrete Nf M → Submodule.span K (M : Set V) = ⊤ → Submodule.IsLattice K M
theorem rat_emb_apply (σ : ℚ →+* ℂ) (q : ℚ) : σ q = (q : ℂ) := eq_ratCast σ q
noncomputable def ratNormFam : NormFam ℚ ℚ where
  N σ v := ‖σ v‖
  nonneg _ _ := norm_nonneg _
  eq_zero σ v h := by simpa using h
  smul σ a v := by rw [smul_eq_mul, map_mul, norm_mul]
  add σ v w := by rw [map_add]; exact norm_add_le _ _
noncomputable def ratInt : Submodule (𝓞 ℚ) ℚ := Submodule.span (𝓞 ℚ) {1}
theorem mem_ratInt {f : ℚ} (hf : f ∈ ratInt) : ∃ n : ℤ, f = n := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hf
  have hi : IsIntegral ℤ (a : ℚ) := RingOfIntegers.isIntegral_coe a
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  refine ⟨n, ?_⟩
  rw [Algebra.smul_def, mul_one]
  simpa using hn.symm
theorem ratInt_prodLower : ProdLower ratNormFam ratInt 0 := by
  intro f hf hf0
  obtain ⟨n, rfl⟩ := mem_ratInt hf
  have hn : n ≠ 0 := by exact_mod_cast hf0
  rw [neg_zero]
  refine Finset.sum_nonneg fun σ _ => Real.log_nonneg ?_
  show 1 ≤ ‖σ (n : ℚ)‖
  rw [rat_emb_apply, Rat.cast_intCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hn
theorem ratInt_unifDiscrete : UnifDiscrete ratNormFam ratInt := by
  refine ⟨1, one_pos, fun f hf hsmall => ?_⟩
  obtain ⟨n, rfl⟩ := mem_ratInt hf
  have h := hsmall (Rat.castHom ℂ)
  change ‖(Rat.castHom ℂ) (n : ℚ)‖ < 1 at h
  rw [rat_emb_apply, Rat.cast_intCast, Complex.norm_intCast] at h
  have h' : |n| < 1 := by exact_mod_cast h
  have : n = 0 := by rwa [Int.abs_lt_one_iff] at h'
  simp [this]
theorem ratInt_span : Submodule.span ℚ (ratInt : Set ℚ) = ⊤ := by
  have h1 : (1 : ℚ) ∈ ratInt := Submodule.subset_span (Set.mem_singleton 1)
  rw [Submodule.eq_top_iff']
  intro x
  have := Submodule.smul_mem (Submodule.span ℚ (ratInt : Set ℚ)) x (Submodule.subset_span h1)
  simpa using this
example (h1 : DiscOfProdLowerSt) (h2 : FGOfDiscSt) (h3 : IsLatticeOfDiscSt) :
    UnifDiscrete ratNormFam ratInt ∧ ratInt.FG ∧ Submodule.IsLattice ℚ ratInt :=
  ⟨h1 ℚ ℚ ratNormFam ratInt 0 ratInt_prodLower, h2 ℚ ℚ ratNormFam ratInt ratInt_unifDiscrete,
    h3 ℚ ℚ ratNormFam ratInt ratInt_unifDiscrete ratInt_span⟩
end ReciprocityTheory.ChartRestriction.G.TB


