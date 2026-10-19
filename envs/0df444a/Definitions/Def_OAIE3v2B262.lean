-- Prove2me | Definitions.Def_OAIE3v2B262
-- name    : OAIE3v2B262
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:57:20.888324+00:00
-- url     : https://prove2.me/theorems/fccfec22-5cbc-4a78-87b2-196bbefaae5d
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 269 of 311
-- statement:
--   Definitions bundle 269 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B248`, `OAIE3v2B251`, `OAIE3v2B253` of this split.
--
--   Modules: `Dynamics/PreparedFiniteNestedCanonicalEarlyPrimitiveBudget.lean`, `Geometry/AllocatedExternalCandidateBufferedCoordinates.lean`, `Sampling/PreparedActualForecastSetup.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B248
import Definitions.Def_OAIE3v2B251
import Definitions.Def_OAIE3v2B253

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

section Generic

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem preparedActualForecastShortSelection_small
    (a : PreparedActualForecastShortIndex B U b S) :
    basisAxisScale (b (preparedActualForecastShortSelection B U b S a).1)
      (preparedActualForecastShortSelection B U b S a).2 ≤
      S.value ^ ((preparedActualForecastShortSelection B U b S a).1.val + 1) :=
  a.property

theorem preparedActualForecastShortSelection_exhaustive
    (a : LayerSamplerAxis I n) (ha : allocatedShortAxis U b S.value a) :
    ∃ i : PreparedActualForecastShortIndex B U b S,
      (⟨(preparedActualForecastShortSelection B U b S i).1,
        Sum.inr (preparedActualForecastShortSelection B U b S i).2⟩ :
          LayerSamplerAxis I n) = a := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl a => exact False.elim ha
  | inr a => exact ⟨⟨⟨j, a⟩, ha⟩, rfl⟩

end Generic

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical BigOperators

section Grid

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def preparedActualForecastGridVolume : ℝ :=
  ∏ a : PreparedActualForecastShortIndex B U b S,
    (basisAxisScale (b (preparedActualForecastShortSelection B U b S a).1)
      (preparedActualForecastShortSelection B U b S a).2 : ℝ)

theorem preparedActualForecastGridVolume_one_le :
    1 ≤ preparedActualForecastGridVolume B U b S := by
  unfold preparedActualForecastGridVolume
  apply Finset.one_le_prod
  intro a _
  exact_mod_cast basisAxisScale_pos
    (b (preparedActualForecastShortSelection B U b S a).1)
    (preparedActualForecastShortSelection B U b S a).2

theorem preparedActualForecastGridVolume_pos :
    0 < preparedActualForecastGridVolume B U b S :=
  lt_of_lt_of_le zero_lt_one (preparedActualForecastGridVolume_one_le B U b S)

end Grid

section EnlargedPrepared

variable {m : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ
  (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock prep Jalloc) U b R σ)

noncomputable abbrev preparedForecastGridVolume : ℝ :=
  preparedActualForecastGridVolume (EnlargedPreparedCommonSamplerBlock prep Jalloc) U b S

end EnlargedPrepared

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem preparedActualForecastGridVolume_mul_active_heights :
    preparedActualForecastGridVolume B U b S *
      (∏ a : AllocatedActiveIntegerAxis U b S.value,
        (basisAxisScale (b a.val.1) a.val.2 : ℝ)) =
      ∏ j : Fin m, ∏ i : Fin (n j), (basisAxisScale (b j) i : ℝ) := by
  let p : (Σ j : Fin m, Fin (n j)) → Prop :=
    fun a => basisAxisScale (b a.1) a.2 ≤ S.value ^ (a.1.val + 1)
  let activeEquiv : {a // ¬p a} ≃ AllocatedActiveIntegerAxis U b S.value :=
    { toFun := fun a => ⟨a.val, Nat.lt_of_not_ge a.property⟩
      invFun := fun a => ⟨a.val, Nat.not_le.mpr a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hactive : (∏ a : {a // ¬p a}, (basisAxisScale (b a.val.1) a.val.2 : ℝ)) =
      ∏ a : AllocatedActiveIntegerAxis U b S.value,
        (basisAxisScale (b a.val.1) a.val.2 : ℝ) :=
    Fintype.prod_equiv activeEquiv _ _ (fun _ => rfl)
  have h := Fintype.prod_subtype_mul_prod_subtype p
    (fun a : Σ j : Fin m, Fin (n j) => (basisAxisScale (b a.1) a.2 : ℝ))
  rw [hactive, Fintype.prod_sigma] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped Classical BigOperators

section Generic
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type*} [Fintype X]

theorem preparedActualForecastJacobian_eq_ratio (τ : ℝ) :
    forecastGeometricJacobian (X := X) (I := I) U b R S.value
      (preparedActualForecastGridVolume B U b S) τ =
    (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)) *
      ((τ / 8) ^ Fintype.card X)⁻¹ *
      (∏ a : Σ j, I j, R a.1)⁻¹ *
      (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1)⁻¹ := by
  have hcombined : coveredJetArrayScale (O := fun _ : Fin m => Unit) U *
      preparedActualForecastGridVolume B U b S *
        (∏ a : AllocatedActiveIntegerAxis U b S.value,
          (basisAxisScale (b a.val.1) a.val.2 : ℝ)) =
      (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j))⁻¹ := by
    rw [mul_assoc, preparedActualForecastGridVolume_mul_active_heights]
    simp only [coveredJetArrayScale, Fintype.card_unit, pow_one,
      mixedDensityCovolumeRatio, div_eq_mul_inv, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, mul_inv_rev, inv_inv]
    ring
  have hactive : (∏ a, allocatedActiveIntegerGridScale U b R S.value a) =
      (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1) *
        (∏ a : AllocatedActiveIntegerAxis U b S.value,
          (basisAxisScale (b a.val.1) a.val.2 : ℝ)) := by
    simp only [allocatedActiveIntegerGridScale, Finset.prod_mul_distrib]
  have hden : coveredJetArrayScale (O := fun _ : Fin m => Unit) U *
      preparedActualForecastGridVolume B U b S * (τ / 8) ^ Fintype.card X *
        (∏ a : Σ j, I j, R a.1) * (∏ a, allocatedActiveIntegerGridScale U b R S.value a) =
      (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j))⁻¹ *
        (τ / 8) ^ Fintype.card X * (∏ a : Σ j, I j, R a.1) *
        (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1) := by
    rw [hactive]
    calc
      _ = (coveredJetArrayScale (O := fun _ : Fin m => Unit) U *
          preparedActualForecastGridVolume B U b S *
            (∏ a : AllocatedActiveIntegerAxis U b S.value,
              (basisAxisScale (b a.val.1) a.val.2 : ℝ))) *
          (τ / 8) ^ Fintype.card X * (∏ a : Σ j, I j, R a.1) *
          (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1) := by ring
      _ = _ := by rw [hcombined]
  rw [forecastGeometricJacobian, hden]
  simp only [mul_inv_rev, inv_inv]
  ring

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem preparedActualForecastJacobian_ratio_le_exp
    (hR : ∀ j, 0 < R j) {τ P : ℝ} (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ Real.exp P) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P) :
    forecastGeometricJacobian (X := X) (I := I) U b R S.value
      (preparedActualForecastGridVolume B U b S) τ ≤
    Real.exp ((m : ℝ) * P + (Fintype.card X : ℝ) * (P + 3) +
      (Fintype.card (Σ j, I j) : ℝ) * P +
      (Fintype.card (AllocatedActiveIntegerAxis U b S.value) : ℝ) * P) := by
  have hchart : (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)) ≤
      Real.exp ((m : ℝ) * P) := by
    simpa only [Fintype.card_fin] using ratioJacobian_product_le_exp
      (fun j => mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j))
      (fun j => (mixedDensityCovolumeRatio_pos (euclideanSubspace (U j)) (b j)).le) hratio
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      convert Real.add_one_le_exp (1 : ℝ) using 1
      norm_num
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hsp : ((τ / 8) ^ Fintype.card X)⁻¹ ≤
      Real.exp ((Fintype.card X : ℝ) * (P + 3)) := by
    rw [← inv_pow]
    have hi : (τ / 8)⁻¹ ≤ Real.exp (P + 3) := by
      calc
        _ = 8 * τ⁻¹ := by rw [inv_div, div_eq_mul_inv]
        _ ≤ Real.exp 3 * Real.exp P :=
          mul_le_mul h8 hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    exact (pow_le_pow_left₀ (inv_nonneg.mpr (div_pos hτ (by norm_num)).le) hi _).trans_eq
      (Real.exp_nat_mul _ _).symm
  have hcontinuous : (∏ a : Σ j, I j, R a.1)⁻¹ ≤
      Real.exp ((Fintype.card (Σ j, I j) : ℝ) * P) := by
    simpa only [← Finset.prod_inv_distrib] using ratioJacobian_product_le_exp
      (fun a : Σ j, I j => (R a.1)⁻¹)
      (fun a => inv_nonneg.mpr (hR a.1).le) (fun a => hRinv a.1)
  have hactive : (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1)⁻¹ ≤
      Real.exp ((Fintype.card (AllocatedActiveIntegerAxis U b S.value) : ℝ) * P) := by
    simpa only [← Finset.prod_inv_distrib] using ratioJacobian_product_le_exp
      (fun a : AllocatedActiveIntegerAxis U b S.value => (R a.val.1)⁻¹)
      (fun a => inv_nonneg.mpr (hR a.val.1).le) (fun a => hRinv a.val.1)
  have hcs := mul_le_mul hchart hsp
    (inv_nonneg.mpr (pow_nonneg (div_pos hτ (by norm_num)).le _)) (Real.exp_nonneg _)
  have hcsc := mul_le_mul hcs hcontinuous
    (inv_nonneg.mpr (Finset.prod_nonneg (fun a _ => (hR a.1).le))) (by positivity)
  have hfull := mul_le_mul hcsc hactive
    (inv_nonneg.mpr (Finset.prod_nonneg (fun a _ => (hR a.val.1).le))) (by positivity)
  rw [preparedActualForecastJacobian_eq_ratio]
  simpa only [← Real.exp_add] using hfull

theorem preparedActualForecastJacobian_ratio_uniform_le_exp
    (hR : ∀ j, 0 < R j) {τ P : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ Real.exp P) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P) :
    forecastGeometricJacobian (X := X) (I := I) U b R S.value
      (preparedActualForecastGridVolume B U b S) τ ≤
    Real.exp (((m : ℝ) + Fintype.card X + Fintype.card (Σ j, I j) +
      Fintype.card (Σ j : Fin m, Fin (n j))) * (P + 3)) := by
  apply (preparedActualForecastJacobian_ratio_le_exp B U b S hR hτ hτinv hRinv hratio).trans
  apply Real.exp_le_exp.mpr
  have hcard : (Fintype.card (AllocatedActiveIntegerAxis U b S.value) : ℝ) ≤
      Fintype.card (Σ j : Fin m, Fin (n j)) := by
    exact_mod_cast (Fintype.card_subtype_le
      (fun a : Σ j : Fin m, Fin (n j) =>
        S.value ^ (a.1.val + 1) < basisAxisScale (b a.1) a.2))
  have hmul := mul_le_mul_of_nonneg_right hcard hP
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hi0 : (0 : ℝ) ≤ Fintype.card (Σ j, I j) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ Fintype.card (Σ j : Fin m, Fin (n j)) := Nat.cast_nonneg _
  nlinarith

end Generic

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical BigOperators

theorem preparedActualForecastJacobian_ratio_budget
    {m M nX : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    {G : Type*} [Fintype G]
    (B : LayerSamplerAxis (PreparedSamplerContinuous prep)
      (preparedSamplerTransverse prep) → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    {pRadius gainLog Pchart : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog) (hChart : 0 ≤ Pchart)
    (hR : ∀ j, 0 < R j) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hratio : ∀ j, mixedDensityCovolumeRatio
      (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart) :
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let Pκ := ((nX + m + m * M : ℕ) : ℝ) *
      (pRadius + gainLog + nX + Pchart + 11)
    0 < forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous prep)
      U b R S.value (preparedActualForecastGridVolume B U b S) τ ∧
    0 ≤ Pκ ∧
    forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous prep)
      U b R S.value (preparedActualForecastGridVolume B U b S) τ ≤ Real.exp Pκ := by
  intro τ Pκ
  let P := pRadius + gainLog + nX + Pchart + 8
  have hn : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp only [P]; linarith
  have hrP : pRadius ≤ P := by dsimp only [P]; linarith
  have hcP : Pchart ≤ P := by dsimp only [P]; linarith
  have htP : gainLog + nX + 8 ≤ P := by dsimp only [P]; linarith
  have hτ : 0 < τ := Real.exp_pos _
  have hτinv : τ⁻¹ ≤ Real.exp P := by
    change (Real.exp (-(gainLog + (nX : ℝ) + 8)))⁻¹ ≤ Real.exp P
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr htP
  have hdim : Fintype.card (Σ j, PreparedSamplerContinuous prep j) +
      Fintype.card (Σ j : Fin m, Fin (preparedSamplerTransverse prep j)) ≤ m * M := by
    simp only [Fintype.card_sigma, Fintype.card_fin, ← Finset.sum_add_distrib]
    calc
      _ = ∑ j : Fin m, Fintype.card (prep j).Coord := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [PreparedSamplerContinuous, Fintype.card_fin] using preparedSampler_axis_card prep j
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ => hCoord j)
      _ = m * M := by simp
  have hdimR := Nat.cast_le (α := ℝ).mpr hdim
  simp only [Nat.cast_add, Nat.cast_mul] at hdimR
  have hκ := preparedActualForecastJacobian_ratio_uniform_le_exp
    (X := Fin nX) B U b S hR hP hτ hτinv
    (fun j => (hRinv j).trans (Real.exp_le_exp.mpr hrP))
    (fun j => (hratio j).trans (Real.exp_le_exp.mpr hcP))
  refine ⟨forecastGeometricJacobian_pos U b hR S.value
    (preparedActualForecastGridVolume_pos B U b S) hτ, ?_, ?_⟩
  · dsimp only [Pκ]
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  · apply hκ.trans (Real.exp_le_exp.mpr ?_)
    have hmult := mul_le_mul_of_nonneg_right
      (show (m : ℝ) + Fintype.card (Fin nX) +
        Fintype.card (Σ j, PreparedSamplerContinuous prep j) +
        Fintype.card (Σ j : Fin m, Fin (preparedSamplerTransverse prep j)) ≤
        ((nX + m + m * M : ℕ) : ℝ) by
          simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul]
          linarith) (show 0 ≤ P + 3 by linarith)
    apply hmult.trans_eq
    dsimp only [Pκ, P]
    ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateBufferedCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m d : ℕ} {X : Type*} {J : Fin m → Type*}

noncomputable def fullTaggedBufferedCoordinates (e : Fin d ≃ Σ j, J j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : ∀ j, J j → ℝ) (x : X → ℤ) : Fin d → ℝ :=
  fun i => eval (fun a => (x a : ℝ)) (poly (e i).1) (e i).2 - c (e i).1 (e i).2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedCanonicalEarlyPrimitiveBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardPairedSourcePrecision_le_direct
    (A Cdirect : ℕ) (constants : ℕ → ℕ) (stage : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    preparedFiniteForwardPairedSourcePrecision A Cdirect constants stage isDirect x gainLog stageLog ≤
      preparedFiniteForwardPairedSourcePrecision A Cdirect constants stage true x gainLog stageLog := by
  cases isDirect with
  | true => exact le_rfl
  | false =>
    rw [preparedFiniteForwardPairedSourcePrecision_model,
      preparedFiniteForwardPairedSourcePrecision_direct]
    apply le_add_of_nonneg_right
    exact pow_nonneg (add_nonneg
      (add_nonneg (preparedFiniteForward_model_precision_bounds A constants stage hx hg hs).2.1
        (preparedFiniteForwardWork_nonneg A constants stage hx)) (Nat.cast_nonneg Cdirect)) _

theorem preparedFiniteForwardAllSlotResource_budget
    (A Cdirect Cresource : ℕ) (constants : ℕ → ℕ) (stage : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    (preparedFiniteForwardPairedSourcePrecision A Cdirect constants stage isDirect x gainLog stageLog +
      preparedFiniteForwardWork A constants stage x + Cresource) ^ Cresource ≤
    (preparedFiniteForwardSourcePrecision A constants stage x gainLog stageLog +
      preparedFiniteForwardWork A constants stage x +
      preparedFiniteForwardInnerSourceExponent Cdirect Cresource) ^
        preparedFiniteForwardInnerSourceExponent Cdirect Cresource := by
  apply le_trans _ ((Classical.choose_spec
    (exists_preparedFiniteForwardPairedResource_budget Cdirect Cresource)).2
      A constants stage hx hg hs)
  apply pow_le_pow_left₀
    (add_nonneg
      (add_nonneg (preparedFiniteForwardPairedSourcePrecision_nonneg
        A Cdirect constants stage isDirect hx hg hs)
        (preparedFiniteForwardWork_nonneg A constants stage hx)) (Nat.cast_nonneg Cresource))
  exact add_le_add
    (add_le_add (preparedFiniteForwardPairedSourcePrecision_le_direct
      A Cdirect constants stage isDirect hx hg hs) le_rfl) le_rfl

end Erdos3.VectorPolynomial

end

end OAI
end


