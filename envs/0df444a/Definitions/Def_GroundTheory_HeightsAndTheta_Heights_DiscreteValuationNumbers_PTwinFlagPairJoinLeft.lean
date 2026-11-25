-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairJoinLeft
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairJoinLeft
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:30.175664+00:00
-- url     : https://prove2.me/theorems/7d40f087-b777-40fa-843c-5c6d3f051a6a
-- title:
--   PTwin Flag Pair Join Left
-- statement:
--   Definitions and structural lemmas for PTwin Flag Pair Join Left, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinLeft.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerLast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_joinCoord_assocVar_b75e0e1aca5e

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
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart chartMon IsGradedFrame IsUnitOn FlagPair IsPull
  IsVertDiv mcIdeal assocDeg assocVar joinCoord_assocVar)
namespace FlagPairJoinLeft
section Charts
variable {Ω : Type*} [Field Ω] {K K' K₂ : Type} [Fintype K] [Fintype K'] [Fintype K₂]
  {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
def lowChart (s : ∀ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => s (.inl k)
  | .inr k => s (.inr (.inl k))
def wChart (s : ∀ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) : ∀ k, ι₂ k :=
  fun k => s (.inr (.inr k))
def combChart (t : ∀ k : K ⊕ K', Sum.elim ι ι' k) (u : ∀ k, ι₂ k) :
    ∀ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k
  | .inl k => t (.inl k)
  | .inr (.inl k) => t (.inr k)
  | .inr (.inr k) => u k
theorem lowChart_combChart (t : ∀ k : K ⊕ K', Sum.elim ι ι' k) (u : ∀ k, ι₂ k) :
    lowChart (combChart t u) = t := by
  funext k
  rcases k with k | k <;> rfl
theorem wChart_combChart (t : ∀ k : K ⊕ K', Sum.elim ι ι' k) (u : ∀ k, ι₂ k) :
    wChart (combChart t u) = u :=
  rfl
theorem mseg_assoc (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (s : ∀ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) :
    mseg (joinCoord x (joinCoord z w)) s = mseg (joinCoord x z) (lowChart s) * mseg w (wChart s) := by
  simp only [mseg, Fintype.prod_sum_type, mul_assoc]
  rfl
theorem mseg_low_ne (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    {s : ∀ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k} (hs : mseg (joinCoord x (joinCoord z w)) s ≠ 0) :
    mseg (joinCoord x z) (lowChart s) ≠ 0 := by
  rw [mseg_assoc] at hs
  exact left_ne_zero_of_mul hs
theorem chartMon_assoc (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (s : ∀ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) (a : K ⊕ K' → ℤ) :
    chartMon (joinCoord x (joinCoord z w)) s (assocDeg (K₂ := K₂) a) = chartMon (joinCoord x z) (lowChart s) a := by
  simp only [chartMon, Fintype.prod_sum_type, assocDeg, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero,
    Finset.prod_const_one, mul_one]
  rfl
variable (O : Type*) [CommRing O] [Algebra O Ω]
theorem chartRing_le (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (s : ∀ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) (hs : mseg (joinCoord x (joinCoord z w)) s ≠ 0) :
    chartRing O (mseg (joinCoord x z)) (lowChart s) ≤ chartRing O (mseg (joinCoord x (joinCoord z w))) s := by
  have hw : mseg w (wChart s) ≠ 0 := by
    rw [mseg_assoc] at hs
    exact right_ne_zero_of_mul hs
  unfold chartRing
  apply Algebra.adjoin_le
  rintro _ ⟨t, rfl⟩
  have h : mseg (joinCoord x z) t / mseg (joinCoord x z) (lowChart s) =
      mseg (joinCoord x (joinCoord z w)) (combChart t (wChart s)) / mseg (joinCoord x (joinCoord z w)) s := by
    rw [mseg_assoc x z w (combChart t (wChart s)), mseg_assoc x z w s, lowChart_combChart, wChart_combChart,
      mul_div_mul_right _ _ hw]
  simp only
  rw [h]
  exact div_mem_chartRing (o := O) _ _ _
end Charts
section Lattices
variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {V : Type*} [AddCommGroup V] [Module Ω V]
def satLat (R : Subalgebra O Ω) (L : AddSubgroup V) (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) (f : Ω) (hf : f ∈ R) :
    AddSubgroup V where
  carrier := {e | ∃ n : ℕ, f ^ n • e ∈ L}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro e₁ e₂ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
    refine ⟨n₁ + n₂, ?_⟩
    have h : f ^ (n₁ + n₂) • (e₁ + e₂) = f ^ n₂ • (f ^ n₁ • e₁) + f ^ n₁ • (f ^ n₂ • e₂) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n₂ n₁]
    rw [h]
    exact L.add_mem (hL _ (R.pow_mem hf _) _ h₁) (hL _ (R.pow_mem hf _) _ h₂)
  neg_mem' := by
    rintro e ⟨n, h⟩
    exact ⟨n, by rw [smul_neg]; exact L.neg_mem h⟩
def coordLat (R : Subalgebra O Ω) (f : Ω) (hf : f ∈ R) {N : ℕ} (b : Fin N → V) : AddSubgroup V where
  carrier := {e | ∃ a : Fin N → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q}
  zero_mem' := ⟨0, fun q => ⟨0, by simp⟩, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a₁, h₁, rfl⟩ ⟨a₂, h₂, rfl⟩
    refine ⟨a₁ + a₂, fun q => ?_, by simp [add_smul, Finset.sum_add_distrib]⟩
    obtain ⟨n₁, hn₁⟩ := h₁ q
    obtain ⟨n₂, hn₂⟩ := h₂ q
    refine ⟨n₁ + n₂, ?_⟩
    have h : f ^ (n₁ + n₂) * (a₁ + a₂) q = f ^ n₂ * (f ^ n₁ * a₁ q) + f ^ n₁ * (f ^ n₂ * a₂ q) := by
      simp only [Pi.add_apply, pow_add]
      ring
    rw [h]
    exact R.add_mem (R.mul_mem (R.pow_mem hf _) hn₁) (R.mul_mem (R.pow_mem hf _) hn₂)
  neg_mem' := by
    rintro _ ⟨a, h, rfl⟩
    refine ⟨-a, fun q => ?_, by simp [neg_smul, Finset.sum_neg_distrib]⟩
    obtain ⟨n, hn⟩ := h q
    exact ⟨n, by simpa [Pi.neg_apply, mul_neg] using R.neg_mem hn⟩
end Lattices
section Bundles
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K K' K₂ : Type} [Fintype K] [Fintype K'] [Fintype K₂] {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] [∀ k, Fintype (ι₂ k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
theorem lat_le (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω) {E : ChartBundle O (mseg x) N V}
    {EF : ChartBundle O (mseg (joinCoord x z)) N V} {EB : ChartBundle O (mseg (joinCoord x (joinCoord z w))) N V}
    (hF : IsPull O x z E EF) (hB : IsPull O x (joinCoord z w) E EB)
    (s : ∀ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) (hs : mseg (joinCoord x (joinCoord z w)) s ≠ 0) :
    EF.lat (lowChart s) ≤ EB.lat s := by
  rw [hF _ (mseg_low_ne x z w hs), hB s hs]
  apply AddSubgroup.closure_mono
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact ⟨a, chartRing_le O x z w s hs ha, e, he, rfl⟩
theorem isGradedFrame_assoc (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    {E : ChartBundle O (mseg x) N V} {EF : ChartBundle O (mseg (joinCoord x z)) N V}
    {EB : ChartBundle O (mseg (joinCoord x (joinCoord z w))) N V}
    (hF : IsPull O x z E EF) (hB : IsPull O x (joinCoord z w) E EB)
    {Vs : Fin (N + 1) → Submodule Ω V} {m : Fin N → K ⊕ K' → ℤ} {gen : Fin N → V}
    (h : IsGradedFrame O (joinCoord x z) EF Vs m gen) :
    IsGradedFrame O (joinCoord x (joinCoord z w)) EB Vs (fun i => assocDeg (K₂ := K₂) (m i)) gen := by
  intro s hs
  have hle := chartRing_le O x z w s hs
  have hlat := lat_le O x z w hF hB s hs
  obtain ⟨k, f, c, hf, hc, hsum, hl⟩ := h _ (mseg_low_ne x z w hs)
  refine ⟨k, f, c, fun l => hle (hf l), fun l => hle (hc l), hsum, fun l => ?_⟩
  obtain ⟨b, hli, hspan, hiff, hwl⟩ := hl l
  refine ⟨b, hli, hspan, fun e => ?_, fun i => ?_⟩
  · have hgen : EB.lat s ≤ coordLat O (chartRing O (mseg (joinCoord x (joinCoord z w))) s) (f l) (hle (hf l)) b := by
      rw [hB s hs, AddSubgroup.closure_le]
      rintro _ ⟨a, ha, e', he', rfl⟩
      have he'F : e' ∈ EF.lat (lowChart s) := by
        rw [hF _ (mseg_low_ne x z w hs)]
        exact AddSubgroup.subset_closure ⟨1, one_mem _, e', he', (one_smul _ _).symm⟩
      obtain ⟨a', ha', rfl⟩ := (hiff e').1 ⟨0, by simpa using he'F⟩
      refine ⟨fun q => a * a' q, fun q => ?_, ?_⟩
      · obtain ⟨n, hn⟩ := ha' q
        exact ⟨n, by rw [mul_left_comm]; exact Subalgebra.mul_mem _ ha (hle hn)⟩
      · simp [Finset.smul_sum, smul_smul]
    constructor
    · rintro ⟨n, hn⟩
      by_cases hf0 : f l = 0
      · have he : e ∈ Submodule.span Ω (Set.range b) := by
          rw [hspan]
          exact Submodule.mem_top
        obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
        exact ⟨a, fun q => ⟨1, by simp [hf0]⟩, rfl⟩
      · have hfn : f l ^ n ≠ 0 := pow_ne_zero _ hf0
        obtain ⟨a, ha, he⟩ := hgen hn
        refine ⟨fun q => a q / f l ^ n, fun q => ?_, ?_⟩
        · obtain ⟨n', hn'⟩ := ha q
          refine ⟨n' + n, ?_⟩
          have h' : f l ^ (n' + n) * (a q / f l ^ n) = f l ^ n' * a q := by
            rw [pow_add]
            field_simp
          rw [h']
          exact hn'
        · calc e = (f l ^ n)⁻¹ • (f l ^ n • e) := by rw [smul_smul, inv_mul_cancel₀ hfn, one_smul]
            _ = ∑ q, (a q / f l ^ n) • b q := by
              rw [he, Finset.smul_sum]
              simp_rw [smul_smul, div_eq_inv_mul]
    · rintro ⟨a, ha, rfl⟩
      have hS : ∀ q, a q • b q ∈ satLat O (chartRing O (mseg (joinCoord x (joinCoord z w))) s) (EB.lat s)
          (EB.stable s) (f l) (hle (hf l)) := by
        intro q
        obtain ⟨n, hn⟩ := ha q
        have hsingle : ∀ q', ∃ n : ℕ, f l ^ n * (Pi.single q (1 : Ω) : Fin N → Ω) q' ∈
            chartRing O (mseg (joinCoord x z)) (lowChart s) := by
          intro q'
          refine ⟨0, ?_⟩
          rw [pow_zero, one_mul]
          by_cases hq : q' = q
          · subst hq
            simp
          · simp [hq]
        obtain ⟨m', hm'⟩ := (hiff (b q)).2 ⟨Pi.single q 1, hsingle, by simp [Pi.single_apply, ite_smul]⟩
        refine ⟨n + m', ?_⟩
        have h' : f l ^ (n + m') • (a q • b q) = (f l ^ n * a q) • (f l ^ m' • b q) := by
          rw [smul_smul, smul_smul]
          congr 1
          ring
        rw [h']
        exact EB.stable s _ hn _ (hlat hm')
      exact AddSubgroup.sum_mem _ fun q _ => hS q
  · obtain ⟨u, ⟨hu0, ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩, hmem⟩ := hwl i
    refine ⟨u, ⟨hu0, ⟨n₁, hle hn₁⟩, ⟨n₂, hle hn₂⟩⟩, ?_⟩
    rw [chartMon_assoc]
    exact hmem
end Bundles
section Forms
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
theorem aeval_assoc (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) O) :
    aeval (joinCoord x (joinCoord z w)) (rename (assocVar ι₂) f) = aeval (joinCoord x z) f := by
  have h : joinCoord x (joinCoord z w) ∘ assocVar ι₂ = joinCoord x z := funext (joinCoord_assocVar x z w)
  rw [aeval_rename, h]
theorem assocDeg_sub (a b : K ⊕ K' → ℤ) :
    assocDeg (K₂ := K₂) (a - b) = assocDeg (K₂ := K₂) a - assocDeg (K₂ := K₂) b := by
  funext k
  rcases k with k | k | k <;> simp [assocDeg]
end Forms
section Pairs
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K K' K₂ : Type} [Fintype K] [Fintype K'] [Fintype K₂] {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] [∀ k, Fintype (ι₂ k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
def assocFlagPair (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    {E E' : ChartBundle O (mseg x) N V} {EF E'F : ChartBundle O (mseg (joinCoord x z)) N V}
    {EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord z w))) N V}
    (hF : IsPull O x z E EF) (hF' : IsPull O x z E' E'F)
    (hB : IsPull O x (joinCoord z w) E EB) (hB' : IsPull O x (joinCoord z w) E' E'B)
    (φ : FlagPair O (joinCoord x z) EF E'F)
    (hvert : ∀ i, IsVertDiv O (mcIdeal O (joinCoord x (joinCoord z w)))
      (assocDeg (K₂ := K₂) (φ.deg i - φ.deg' i)) (rename (assocVar ι₂) (φ.f i)) (rename (assocVar ι₂) (φ.g i))) :
    FlagPair O (joinCoord x (joinCoord z w)) EB E'B where
  Vs := φ.Vs
  mono := φ.mono
  dim := φ.dim
  top := φ.top
  deg i := assocDeg (K₂ := K₂) (φ.deg i)
  gen := φ.gen
  gen_mem := φ.gen_mem
  frame := isGradedFrame_assoc O x z w hF hB φ.frame
  deg' i := assocDeg (K₂ := K₂) (φ.deg' i)
  gen' := φ.gen'
  gen'_mem := φ.gen'_mem
  frame' := isGradedFrame_assoc O x z w hF' hB' φ.frame'
  f i := rename (assocVar ι₂) (φ.f i)
  g i := rename (assocVar ι₂) (φ.g i)
  rel i := by
    simp only [aeval_assoc]
    exact φ.rel i
  vert i := by
    have h := hvert i
    rwa [assocDeg_sub] at h
end Pairs
end FlagPairJoinLeft
end GroundTheory.Heights₂.Heights.NumbersDVR


