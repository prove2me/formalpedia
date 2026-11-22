-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
-- name    : Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:38.259226+00:00
-- url     : https://prove2.me/theorems/eb6bbab6-fd92-4933-aebc-d49df14c6590
-- title:
--   Algebra Map Mem Maximal Ideal Pow Iff
-- statement:
--   Definitions and structural lemmas for Algebra Map Mem Maximal Ideal Pow Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
def plEquiv (K : Type) [Field K] [NumberField K] :
    HeightOneSpectrum (𝓞 K) ≃ Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K where
  toFun w := ⟨w.asIdeal, w.isMaximal⟩
  invFun p := ⟨p.1, p.2.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
  left_inv _ := rfl
  right_inv _ := rfl
@[simp] theorem plEquiv_val (w : HeightOneSpectrum (𝓞 K)) : (plEquiv K w).1 = w.asIdeal := rfl
@[simp] theorem plEquiv_symm_asIdeal (p : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K) :
    ((plEquiv K).symm p).asIdeal = p.1 := rfl
def prW (w : HeightOneSpectrum (𝓞 K)) : ℕ := Ideal.absNorm (w.asIdeal.under ℤ)
def eW (w : HeightOneSpectrum (𝓞 K)) : ℕ := w.asIdeal.ramificationIdx ℤ
def lW (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ) / (Module.finrank ℚ K : ℝ)
def IsUnifW (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) : Prop := ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2
abbrev Ow (w : HeightOneSpectrum (𝓞 K)) : Type := Localization.AtPrime w.asIdeal
instance owDVR (w : HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (Ow w) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) w.ne_bot _
def owToK (w : HeightOneSpectrum (𝓞 K)) : Ow w →+* K :=
  IsLocalization.lift (M := w.asIdeal.primeCompl) (g := algebraMap (𝓞 K) K) (fun y => by
    refine IsUnit.mk0 _ ?_
    intro h
    have h0 : (y : 𝓞 K) = 0 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [h, map_zero]
    exact y.2 (h0 ▸ w.asIdeal.zero_mem))
instance owAlgebra (w : HeightOneSpectrum (𝓞 K)) : Algebra (Ow w) K := (owToK w).toAlgebra
instance owTower (w : HeightOneSpectrum (𝓞 K)) : IsScalarTower (𝓞 K) (Ow w) K :=
  IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq _ x).symm)
instance owFrac (w : HeightOneSpectrum (𝓞 K)) : IsFractionRing (Ow w) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization w.asIdeal.primeCompl (Ow w) K
section Mod
variable (w : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module K V]
@[reducible] def owModule : Module (Ow w) V := Module.compHom V (algebraMap (Ow w) K)
scoped instance (priority := 90) owModuleInst : Module (Ow w) V := owModule w V
scoped instance owTowerK : IsScalarTower (Ow w) K V :=
  ⟨fun r a x => by
    show (r • a) • x = algebraMap (Ow w) K r • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩
scoped instance owTowerO [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] :
    IsScalarTower (𝓞 K) (Ow w) V :=
  ⟨fun r s x => by
    show algebraMap (Ow w) K (r • s) • x = r • (algebraMap (Ow w) K s • x)
    rw [Algebra.smul_def, map_mul, mul_smul, ← IsScalarTower.algebraMap_apply, algebraMap_smul]⟩
end Mod
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def atW (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) : Submodule (Ow w) V :=
  Submodule.span (Ow w) (L : Set V)
def scalW (w : HeightOneSpectrum (𝓞 K)) (c : K) (L : Submodule (𝓞 K) V) : Submodule (Ow w) V :=
  (atW w L).map ((c • (LinearMap.id : V →ₗ[K] V)).restrictScalars (Ow w))
def lenW (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : ℕ∞ :=
  Module.length (Ow w) (atW w A ⧸ (atW w B).comap (atW w A).subtype)
def lidxW (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : ℤ :=
  ((lenW w A (A ⊓ B)).toNat : ℤ) - ((lenW w B (A ⊓ B)).toNat : ℤ)
def lenUW (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : ℚ :=
  ((lenW w A B).toNat : ℚ) / (eW w : ℚ)
def lidxUW (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : ℚ :=
  (lidxW w A B : ℚ) / (eW w : ℚ)
theorem mk'_smul (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (t : w.asIdeal.primeCompl) (x : V) :
    (t : 𝓞 K) • ((IsLocalization.mk' (Ow w) a t) • x) = a • x := by
  rw [← algebraMap_smul (Ow w) (t : 𝓞 K), smul_smul, IsLocalization.mk'_spec', algebraMap_smul]
theorem mem_atW_iff {w : HeightOneSpectrum (𝓞 K)} {L : Submodule (𝓞 K) V} {x : V} :
    x ∈ atW w L ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ L := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hx⟩
    | zero => exact ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hx⟩ := hx
      obtain ⟨t, ht, hy⟩ := hy
      refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_⟩
      have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
        rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
      rw [e]
      exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
    | smul r x _ hx =>
      obtain ⟨s, hs, hx⟩ := hx
      obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq w.asIdeal.primeCompl r
      refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs t.2, ?_⟩
      rw [mul_smul, mk'_smul, smul_comm]
      exact L.smul_mem a hx
  · rintro ⟨s, hs, hx⟩
    have h1 : x = (IsLocalization.mk' (Ow w) (1 : 𝓞 K) (⟨s, hs⟩ : w.asIdeal.primeCompl)) • (s • x) := by
      rw [smul_comm]
      have := mk'_smul w 1 (⟨s, hs⟩ : w.asIdeal.primeCompl) x
      rw [one_smul] at this
      exact this.symm
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
@[simp] theorem atW_bot (w : HeightOneSpectrum (𝓞 K)) : atW w (⊥ : Submodule (𝓞 K) V) = ⊥ := by
  simp [atW]
@[simp] theorem atW_top (w : HeightOneSpectrum (𝓞 K)) : atW w (⊤ : Submodule (𝓞 K) V) = ⊤ := by
  simp [atW]
@[reducible] def rlocModule (V : Type) [AddCommGroup V] [Module K V] (p : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K) :
    Module (Formalism.LFunctionChainParameters.slopeLatticeData.Rloc p) V := owModule ((plEquiv K).symm p) V
theorem algebraMap_ow_injective (w : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (algebraMap (Ow w) K) := IsFractionRing.injective (Ow w) K
theorem mem_range_ow_iff (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ (algebraMap (Ow w) K).range ↔ w.valuation K x ≤ 1 := by
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq w.asIdeal.primeCompl r
    have h1 : algebraMap (Ow w) K (IsLocalization.mk' (Ow w) a t) * algebraMap (𝓞 K) K (t : 𝓞 K)
        = algebraMap (𝓞 K) K a := by
      rw [IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K, ← map_mul, IsLocalization.mk'_spec,
        ← IsScalarTower.algebraMap_apply]
    have h2 := congrArg (w.valuation K) h1
    rw [map_mul, (w.valuation_eq_one_iff_notMem (K := K)).2 t.2, mul_one] at h2
    rw [h2]
    exact w.valuation_le_one a
  · intro hx
    obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    refine ⟨IsLocalization.mk' (Ow w) n d, ?_⟩
    have hd : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
      intro h0
      have : (d : 𝓞 K) = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
      exact d.2 (this ▸ w.asIdeal.zero_mem)
    apply mul_right_cancel₀ hd
    rw [h, IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K, ← map_mul, IsLocalization.mk'_spec,
      ← IsScalarTower.algebraMap_apply]
theorem maximalIdeal_ow (w : HeightOneSpectrum (𝓞 K)) :
    IsLocalRing.maximalIdeal (Ow w) = w.asIdeal.map (algebraMap (𝓞 K) (Ow w)) :=
  (Localization.AtPrime.map_eq_maximalIdeal).symm
theorem algebraMap_mem_maximalIdeal_pow_iff (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (n : ℕ) :
    algebraMap (𝓞 K) (Ow w) a ∈ IsLocalRing.maximalIdeal (Ow w) ^ n ↔ a ∈ w.asIdeal ^ n := by
  rw [maximalIdeal_ow, ← Ideal.map_pow]
  constructor
  · intro h
    obtain ⟨⟨b, s⟩, hbs⟩ := (IsLocalization.mem_map_algebraMap_iff w.asIdeal.primeCompl (Ow w)).1 h
    have h1 : a * (s : 𝓞 K) = (b : 𝓞 K) :=
      IsLocalization.injective (Ow w) w.asIdeal.primeCompl_le_nonZeroDivisors (by simpa using hbs)
    have h2 : (s : 𝓞 K) * a ∈ w.asIdeal ^ n := by rw [mul_comm, h1]; exact b.2
    exact (Ideal.IsPrime.mul_mem_pow w.asIdeal h2).resolve_left s.2
  · exact Ideal.mem_map_of_mem _
scoped instance owTorsionFree (w : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module K V] :
    Module.IsTorsionFree (Ow w) V :=
  Module.IsTorsionFree.of_smul_eq_zero (fun r x h => by
    change algebraMap (Ow w) K r • x = 0 at h
    rcases smul_eq_zero.1 h with h | h
    · left
      exact algebraMap_ow_injective w (by rw [h, map_zero])
    · exact Or.inr h)
theorem mem_atW_one_iff (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ atW w (1 : Submodule (𝓞 K) K) ↔ w.valuation K x ≤ 1 := by
  rw [← mem_range_ow_iff]
  constructor
  · intro hx
    obtain ⟨s, hs, hx'⟩ := mem_atW_iff.1 hx
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 hx'
    refine ⟨IsLocalization.mk' (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl), ?_⟩
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      intro h0
      have : s = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
      exact hs (this ▸ w.asIdeal.zero_mem)
    apply mul_right_cancel₀ hs0
    have e : algebraMap (𝓞 K) K s = algebraMap (Ow w) K (algebraMap (𝓞 K) (Ow w) s) :=
      IsScalarTower.algebraMap_apply _ _ _ _
    have h4 : IsLocalization.mk' (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl) * algebraMap (𝓞 K) (Ow w) s =
        algebraMap (𝓞 K) (Ow w) a := IsLocalization.mk'_spec (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl)
    calc algebraMap (Ow w) K (IsLocalization.mk' (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl)) *
          algebraMap (𝓞 K) K s
        = algebraMap (Ow w) K (IsLocalization.mk' (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl) *
          algebraMap (𝓞 K) (Ow w) s) := by rw [e, map_mul]
      _ = algebraMap (𝓞 K) K a := by rw [h4, ← IsScalarTower.algebraMap_apply]
      _ = x * algebraMap (𝓞 K) K s := by rw [ha, Algebra.smul_def, mul_comm]
  · rintro ⟨r, rfl⟩
    have : algebraMap (Ow w) K r = r • (1 : K) := by rw [Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.one_le.1 le_rfl))
section Restrict
variable (w : HeightOneSpectrum (𝓞 K)) (Q : Type) [AddCommGroup Q] [Module (Ow w) Q] [Module (𝓞 K) Q]
  [IsScalarTower (𝓞 K) (Ow w) Q]
end Restrict
abbrev idLat (I : Ideal (𝓞 K)) : Submodule (𝓞 K) K := IsLocalization.coeSubmodule K I
theorem mem_atW_idLat_pow_iff (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) (r : Ow w) :
    algebraMap (Ow w) K r ∈ atW w (idLat (w.asIdeal ^ n)) ↔ r ∈ IsLocalRing.maximalIdeal (Ow w) ^ n := by
  constructor
  · intro h
    obtain ⟨s, hs, hx⟩ := mem_atW_iff.1 h
    obtain ⟨a, ha, hax⟩ := (IsLocalization.mem_coeSubmodule K _).1 hx
    have h1 : algebraMap (𝓞 K) (Ow w) a = algebraMap (𝓞 K) (Ow w) s * r := by
      apply algebraMap_ow_injective w
      rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hax,
        Algebra.smul_def]
    have h2 : algebraMap (𝓞 K) (Ow w) s * r ∈ IsLocalRing.maximalIdeal (Ow w) ^ n :=
      h1 ▸ (algebraMap_mem_maximalIdeal_pow_iff w a n).2 ha
    have hu : IsUnit (algebraMap (𝓞 K) (Ow w) s) :=
      IsLocalization.map_units (Ow w) (⟨s, hs⟩ : w.asIdeal.primeCompl)
    exact (Ideal.unit_mul_mem_iff_mem _ hu).1 h2
  · intro h
    rw [maximalIdeal_ow, ← Ideal.map_pow] at h
    obtain ⟨⟨b, s⟩, hbs⟩ := (IsLocalization.mem_map_algebraMap_iff w.asIdeal.primeCompl (Ow w)).1 h
    refine mem_atW_iff.2 ⟨s, s.2, (IsLocalization.mem_coeSubmodule K _).2 ⟨b, b.2, ?_⟩⟩
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K,
      IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K, ← map_mul, mul_comm]
    exact congrArg _ hbs.symm
theorem lenW_one_pow (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    lenW w (1 : Submodule (𝓞 K) K) (idLat (w.asIdeal ^ n)) = n := by
  unfold lenW
  rw [← IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := Ow w) n]
  have hmem : ∀ r : Ow w, algebraMap (Ow w) K r ∈ atW w (1 : Submodule (𝓞 K) K) := fun r =>
    (mem_atW_one_iff w _).2 ((mem_range_ow_iff w _).1 ⟨r, rfl⟩)
  let f : Ow w →ₗ[Ow w] atW w (1 : Submodule (𝓞 K) K) :=
    (Algebra.linearMap (Ow w) K).codRestrict _ hmem
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact algebraMap_ow_injective w (congrArg Subtype.val hab)
    · rintro ⟨x, hx⟩
      obtain ⟨r, rfl⟩ := (mem_range_ow_iff w x).2 ((mem_atW_one_iff w x).1 hx)
      exact ⟨r, rfl⟩
  refine (LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ (LinearEquiv.ofBijective f hf) ?_)).symm
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (mem_atW_idLat_pow_iff w n r).2 hr
  · intro hx
    obtain ⟨r, rfl⟩ := hf.2 x
    exact ⟨r, (mem_atW_idLat_pow_iff w n r).1 hx, rfl⟩
theorem nonempty_places (K : Type) [Field K] [NumberField K] : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨(plEquiv K).symm ⟨m, hm⟩⟩
example : ∃ w : HeightOneSpectrum (𝓞 ℚ), lenW w (1 : Submodule (𝓞 ℚ) ℚ) (idLat (w.asIdeal ^ 3)) = 3 := by
  obtain ⟨w⟩ := nonempty_places ℚ
  exact ⟨w, lenW_one_pow w 3⟩
end Formalism.L2.Col


