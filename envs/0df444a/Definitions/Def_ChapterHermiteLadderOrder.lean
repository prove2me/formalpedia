-- Prove2me | Definitions.Def_ChapterHermiteLadderOrder
-- name    : ChapterHermiteLadderOrder
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-04T14:41:05.769081+00:00
-- url     : https://prove2.me/theorems/c597a290-98b4-4f82-b067-ab882100e787
-- title:
--   Chapter HermiteLadderOrder
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterHermiteLadderOrder.lean`): generated def bundle for ChapterHermiteLadderOrder. See BookProof/ChapterHermiteLadderOrder.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteLadderOrder.lean

import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Mathlib
import Theorems.Thm_BookProof_HermiteProductBasis_annPoly_apply
import Theorems.Thm_BookProof_HermiteProductBasis_annPoly_hermiteMvLp
import Theorems.Thm_BookProof_HermiteProductBasis_crePoly_apply
import Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvBasis_apply
import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_C
import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_X
import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_mul
import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_sub
import Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_coreD
import Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_neg
import Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_pgLp_pgLp
import Theorems.Thm_BookProof_HermiteProductBasis_crePoly_hermiteMvLp


/-!
# Hermite–Sobolev weights and the ladder order of polynomial differential operators

Let `ψ_α` be the product Hermite basis of `L²(ℝᵈ)` (`BookProof.HermiteProductBasis`) and
write `c_α(v) = ⟪ψ_α, v⟫` for the Hermite coefficients of `v`.  For `m : ℕ` put

`‖v‖²_m = ∑_α (|α| + 1)^m |c_α(v)|²  ∈ [0, ∞]`

(`hn m v`, an extended non-negative real, so no summability bookkeeping is needed).  A linear
map `T` of the polynomial ring has **ladder order** `n` (`LadderOrd T n`) if, on the
Gauss–polynomial core, `‖T v‖²_m ≤ C_m ‖v‖²_{m+n}` for every `m`.

* the ladder operators `aᵢ = annPoly i` and `aᵢ† = crePoly i` have ladder order `1`
  (`ladderOrd_annPoly`, `ladderOrd_crePoly`) — this is where the Hermite structure enters,
  through the adjoint relations `⟪q, aᵢ p⟫ = ⟪aᵢ† q, p⟫` (`inner_pgLp_annPoly`) and the
  action of `aᵢ†`, `aᵢ` on the basis;
* ladder order is stable under sums, scalar multiples and compositions (orders add);
* consequently every operator `−Δ_S + W` with a polynomial potential `W` has *some* finite
  ladder order (`exists_ladderOrd_hamPolyL`), and hence, by Parseval
  (`hn_zero_eq`), `‖(−Δ_S + W) v‖² ≤ C ‖v‖²_n` on the core (`norm_sq_le_hn`).
-/

namespace BookProof.HermiteLadder

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.DegSchrodinger
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Hermite coefficients and the weighted norms -/

/-- The Hermite coefficient `c_α(v) = ⟪ψ_α, v⟫`. -/
def coef (a : Fin d →₀ ℕ) (v : L2d d) : ℂ := inner ℂ (hermiteMvLp a) v

theorem coef_add (a : Fin d →₀ ℕ) (v w : L2d d) : coef a (v + w) = coef a v + coef a w :=
  inner_add_right _ _ _

theorem coef_smul (a : Fin d →₀ ℕ) (c : ℂ) (v : L2d d) : coef a (c • v) = c * coef a v :=
  inner_smul_right _ _ _

theorem coef_sub (a : Fin d →₀ ℕ) (v w : L2d d) : coef a (v - w) = coef a v - coef a w :=
  inner_sub_right _ _ _

theorem coef_zero (a : Fin d →₀ ℕ) : coef a (0 : L2d d) = 0 := inner_zero_right _

/-- The weight `(|α| + 1)^m`. -/
def wt (m : ℕ) (a : Fin d →₀ ℕ) : ℝ≥0∞ := ((a.degree + 1 : ℕ) : ℝ≥0∞) ^ m

theorem wt_mono {m m' : ℕ} (h : m ≤ m') (a : Fin d →₀ ℕ) : wt m a ≤ wt m' a :=
  pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos _) h

theorem wt_zero (a : Fin d →₀ ℕ) : wt 0 a = 1 := pow_zero _

/-- The Hermite–Sobolev norm `‖v‖²_m = ∑_α (|α| + 1)^m |c_α(v)|²`. -/
def hn (m : ℕ) (v : L2d d) : ℝ≥0∞ := ∑' a, wt m a * ‖coef a v‖ₑ ^ 2

theorem hn_mono {m m' : ℕ} (h : m ≤ m') (v : L2d d) : hn m v ≤ hn m' v :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul_left (wt_mono h a) _

theorem hn_zero_vec (m : ℕ) : hn m (0 : L2d d) = 0 := by
  simp [hn, coef_zero]

theorem enorm_add_sq_le (x y : ℂ) : ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have h1 : ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ := enorm_add_le _ _
  have h2 : (‖x‖ₑ + ‖y‖ₑ) ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    have h3 : ((‖x‖₊ + ‖y‖₊) ^ 2 : NNReal) ≤ 2 * ‖x‖₊ ^ 2 + 2 * ‖y‖₊ ^ 2 := by
      rw [← NNReal.coe_le_coe]
      push_cast
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
    exact_mod_cast h3
  exact (pow_le_pow_left₀ (M₀ := ℝ≥0∞) (by simp) h1 2).trans h2

theorem hn_add_le (m : ℕ) (v w : L2d d) : hn m (v + w) ≤ 2 * hn m v + 2 * hn m w := by
  unfold hn
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [coef_add]
  calc wt m a * ‖coef a v + coef a w‖ₑ ^ 2
      ≤ wt m a * (2 * ‖coef a v‖ₑ ^ 2 + 2 * ‖coef a w‖ₑ ^ 2) :=
        by gcongr; exact enorm_add_sq_le _ _
    _ = 2 * (wt m a * ‖coef a v‖ₑ ^ 2) + 2 * (wt m a * ‖coef a w‖ₑ ^ 2) := by ring

theorem hn_smul (m : ℕ) (c : ℂ) (v : L2d d) : hn m (c • v) = ‖c‖ₑ ^ 2 * hn m v := by
  unfold hn
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun a => ?_
  rw [coef_smul, enorm_mul, mul_pow]
  ring

/-! ## 2. Ladder order -/

/-- `T` has **ladder order** `n`: `‖T v‖²_m ≤ C_m ‖v‖²_{m+n}` on the core, for every `m`. -/
def LadderOrd (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) (n : ℕ) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ p, hn m (pgLp (T p)) ≤ C * hn (m + n) (pgLp p)

theorem pgLp_add' (p q : MvPolynomial (Fin d) ℂ) : pgLp (p + q) = pgLp p + pgLp q := by
  rw [← HermiteProductCore.pgMap_apply, map_add]
  rfl

theorem pgLp_smul' (c : ℂ) (p : MvPolynomial (Fin d) ℂ) : pgLp (c • p) = c • pgLp p := by
  rw [← HermiteProductCore.pgMap_apply, map_smul]
  rfl

theorem pgLp_zero' : pgLp (0 : MvPolynomial (Fin d) ℂ) = 0 := by
  rw [← HermiteProductCore.pgMap_apply, map_zero]

theorem LadderOrd.mono {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {n n' : ℕ}
    (h : LadderOrd T n) (hn' : n ≤ n') : LadderOrd T n' := by
  intro m
  obtain ⟨C, hC, hT⟩ := h m
  exact ⟨C, hC, fun p => (hT p).trans (by gcongr; exact hn_mono (by omega) _)⟩

theorem ladderOrd_id : LadderOrd (LinearMap.id : MvPolynomial (Fin d) ℂ →ₗ[ℂ] _) 0 :=
  fun _ => ⟨1, ENNReal.one_ne_top, fun p => by simp⟩

theorem ladderOrd_zero (n : ℕ) : LadderOrd (0 : MvPolynomial (Fin d) ℂ →ₗ[ℂ] _) n :=
  fun _ => ⟨0, ENNReal.zero_ne_top, fun p => by simp [pgLp_zero', hn_zero_vec]⟩

theorem LadderOrd.add {S T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {n : ℕ}
    (hS : LadderOrd S n) (hT : LadderOrd T n) : LadderOrd (S + T) n := by
  intro m
  obtain ⟨C₁, hC₁, h₁⟩ := hS m
  obtain ⟨C₂, hC₂, h₂⟩ := hT m
  refine ⟨2 * C₁ + 2 * C₂, by finiteness, fun p => ?_⟩
  rw [LinearMap.add_apply, pgLp_add']
  calc hn m (pgLp (S p) + pgLp (T p)) ≤ 2 * hn m (pgLp (S p)) + 2 * hn m (pgLp (T p)) :=
        hn_add_le _ _ _
    _ ≤ 2 * (C₁ * hn (m + n) (pgLp p)) + 2 * (C₂ * hn (m + n) (pgLp p)) := by
        gcongr
        · exact h₁ p
        · exact h₂ p
    _ = (2 * C₁ + 2 * C₂) * hn (m + n) (pgLp p) := by ring

theorem LadderOrd.smul {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {n : ℕ}
    (hT : LadderOrd T n) (c : ℂ) : LadderOrd (c • T) n := by
  intro m
  obtain ⟨C, hC, h⟩ := hT m
  refine ⟨‖c‖ₑ ^ 2 * C, by finiteness, fun p => ?_⟩
  rw [LinearMap.smul_apply, pgLp_smul', hn_smul, mul_assoc]
  gcongr
  exact h p

theorem LadderOrd.neg {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {n : ℕ}
    (hT : LadderOrd T n) : LadderOrd (-T) n := by
  have heq : -T = (-1 : ℂ) • T := by
    refine LinearMap.ext fun p => ?_
    simp
  rw [heq]
  exact hT.smul (-1)

theorem LadderOrd.sub {S T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {n : ℕ}
    (hS : LadderOrd S n) (hT : LadderOrd T n) : LadderOrd (S - T) n := by
  rw [sub_eq_add_neg]
  exact hS.add hT.neg

theorem LadderOrd.comp {S T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {a b : ℕ}
    (hS : LadderOrd S a) (hT : LadderOrd T b) : LadderOrd (S ∘ₗ T) (a + b) := by
  intro m
  obtain ⟨C₁, hC₁, h₁⟩ := hS m
  obtain ⟨C₂, hC₂, h₂⟩ := hT (m + a)
  refine ⟨C₁ * C₂, by finiteness, fun p => ?_⟩
  rw [LinearMap.comp_apply]
  calc hn m (pgLp (S (T p))) ≤ C₁ * hn (m + a) (pgLp (T p)) := h₁ _
    _ ≤ C₁ * (C₂ * hn (m + a + b) (pgLp p)) := by gcongr; exact h₂ p
    _ = C₁ * C₂ * hn (m + (a + b)) (pgLp p) := by rw [← add_assoc, mul_assoc]

theorem LadderOrd.sum {ι : Type*} (s : Finset ι)
    {T : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {n : ℕ}
    (h : ∀ i ∈ s, LadderOrd (T i) n) : LadderOrd (∑ i ∈ s, T i) n := by
  classical
  induction s using Finset.induction with
  | empty => simpa using ladderOrd_zero n
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ## 3. The ladder operators -/

theorem C_half_add_C_half :
    (C (1 / 2 : ℂ) : MvPolynomial (Fin d) ℂ) + C (1 / 2 : ℂ) = 1 := by
  rw [← C_add]
  norm_num

theorem annPoly_eq_coreD (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    annPoly i p = coreD i p + C (1 / 2 : ℂ) * (X i * p) := by
  rw [annPoly_apply, coreD]
  ring

theorem crePoly_eq_coreD (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    crePoly i p = C (1 / 2 : ℂ) * (X i * p) - coreD i p := by
  rw [crePoly_apply, coreD]
  linear_combination (-(X i * p)) * (C_half_add_C_half (d := d))

theorem gaussInt_sub' (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by
  rw [sub_eq_add_neg, gaussInt_add, gaussInt_neg, ← sub_eq_add_neg]

/-- **`aᵢ† = aᵢ*`** on the core: `⟪q, aᵢ p⟫ = ⟪aᵢ† q, p⟫`. -/
theorem inner_pgLp_annPoly (i : Fin d) (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp q) (pgLp (annPoly i p)) : ℂ) = inner ℂ (pgLp (crePoly i q)) (pgLp p) := by
  rw [inner_pgLp_pgLp, inner_pgLp_pgLp, annPoly_eq_coreD, crePoly_eq_coreD, mul_add,
    gaussInt_add, cpoly_sub, sub_mul, gaussInt_sub']
  have h1 : gaussInt (cpoly q * coreD i p) = -gaussInt (cpoly (coreD i q) * p) := by
    rw [gaussInt_coreD, neg_neg]
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by norm_num [Complex.ext_iff]
  have h2 : cpoly q * (C (1 / 2 : ℂ) * (X i * p)) = cpoly (C (1 / 2 : ℂ) * (X i * q)) * p := by
    simp only [cpoly_mul, cpoly_C, cpoly_X, hhalf]
    ring
  rw [h1, h2]
  ring

/-- **`aᵢ = (aᵢ†)*`** on the core. -/
theorem inner_pgLp_crePoly (i : Fin d) (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp q) (pgLp (crePoly i p)) : ℂ) = inner ℂ (pgLp (annPoly i q)) (pgLp p) := by
  rw [← inner_conj_symm, ← inner_pgLp_annPoly, inner_conj_symm]

theorem coef_eq_inner_pgLp (a : Fin d →₀ ℕ) (v : L2d d) :
    coef a v = ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ * inner ℂ (pgLp (hermiteMv a)) v := by
  rw [coef, hermiteMvLp, inner_smul_left]
  simp

/-- The Hermite coefficients of `aᵢ v`: `c_β(aᵢ v) = √(βᵢ + 1) c_{β+eᵢ}(v)`. -/
theorem coef_annPoly (i : Fin d) (b : Fin d →₀ ℕ) (p : MvPolynomial (Fin d) ℂ) :
    coef b (pgLp (annPoly i p))
      = ((Real.sqrt ((b i : ℝ) + 1) : ℝ) : ℂ) * coef (b + Finsupp.single i 1) (pgLp p) := by
  have hN : ∀ x : L2d d, ((hermiteMvNorm b : ℝ) : ℂ)⁻¹ * inner ℂ (pgLp (crePoly i (hermiteMv b))) x
      = inner ℂ (((hermiteMvNorm b : ℝ) : ℂ)⁻¹ • pgLp (crePoly i (hermiteMv b))) x := by
    intro x
    rw [inner_smul_left]
    simp
  rw [coef_eq_inner_pgLp, inner_pgLp_annPoly, hN, crePoly_hermiteMvLp, inner_smul_left, coef]
  simp

/-- The Hermite coefficients of `aᵢ† v`: `c_β(aᵢ† v) = √βᵢ c_{β−eᵢ}(v)`. -/
theorem coef_crePoly (i : Fin d) (b : Fin d →₀ ℕ) (p : MvPolynomial (Fin d) ℂ) :
    coef b (pgLp (crePoly i p))
      = ((Real.sqrt ((b i : ℝ)) : ℝ) : ℂ) * coef (b - Finsupp.single i 1) (pgLp p) := by
  have hN : ∀ x : L2d d, ((hermiteMvNorm b : ℝ) : ℂ)⁻¹ * inner ℂ (pgLp (annPoly i (hermiteMv b))) x
      = inner ℂ (((hermiteMvNorm b : ℝ) : ℂ)⁻¹ • pgLp (annPoly i (hermiteMv b))) x := by
    intro x
    rw [inner_smul_left]
    simp
  rw [coef_eq_inner_pgLp, inner_pgLp_crePoly, hN, annPoly_hermiteMvLp, inner_smul_left, coef]
  simp

theorem enorm_sqrt_mul_sq {x : ℝ} (hx : 0 ≤ x) (c : ℂ) :
    ‖((Real.sqrt x : ℝ) : ℂ) * c‖ₑ ^ 2 = ENNReal.ofReal x * ‖c‖ₑ ^ 2 := by
  rw [enorm_mul, mul_pow]
  congr 1
  rw [show ‖((Real.sqrt x : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (Real.sqrt x) by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]]
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hx]

/-- **The annihilation operators have ladder order one.** -/
theorem ladderOrd_annPoly (i : Fin d) : LadderOrd (annPoly i) 1 := by
  intro m
  refine ⟨1, ENNReal.one_ne_top, fun p => ?_⟩
  rw [one_mul]
  unfold hn
  calc ∑' b, wt m b * ‖coef b (pgLp (annPoly i p))‖ₑ ^ 2
      ≤ ∑' b, wt (m + 1) (b + Finsupp.single i 1)
          * ‖coef (b + Finsupp.single i 1) (pgLp p)‖ₑ ^ 2 := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        rw [coef_annPoly, enorm_sqrt_mul_sq (by positivity), ← mul_assoc]
        gcongr
        have hdeg : (b + Finsupp.single i 1).degree = b.degree + 1 := by
          rw [map_add, Finsupp.degree_single]
        have hbi : b i ≤ b.degree := Finsupp.le_degree i b
        rw [wt, wt, hdeg, show ENNReal.ofReal ((b i : ℝ) + 1) = ((b i + 1 : ℕ) : ℝ≥0∞) by
          rw [show ((b i : ℝ) + 1) = ((b i + 1 : ℕ) : ℝ) by push_cast; ring,
            ENNReal.ofReal_natCast]]
        rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_mul, Nat.cast_le, pow_succ]
        exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) m) (by omega)
    _ ≤ ∑' a, wt (m + 1) a * ‖coef a (pgLp p)‖ₑ ^ 2 :=
        ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective _)
          (fun a => wt (m + 1) a * ‖coef a (pgLp p)‖ₑ ^ 2)

/-- **The creation operators have ladder order one.** -/
theorem ladderOrd_crePoly (i : Fin d) : LadderOrd (crePoly i) 1 := by
  intro m
  refine ⟨2 ^ m, by finiteness, fun p => ?_⟩
  unfold hn
  have hsupp : Function.support (fun b => wt m b * ‖coef b (pgLp (crePoly i p))‖ₑ ^ 2)
      ⊆ Set.range (fun a : Fin d →₀ ℕ => a + Finsupp.single i 1) := by
    intro b hb
    by_cases hbi : b i = 0
    · exfalso
      apply hb
      simp only
      rw [coef_crePoly, hbi]
      simp
    · refine ⟨b - Finsupp.single i 1, ?_⟩
      ext j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [hj]
  rw [← (add_left_injective (Finsupp.single i 1)).tsum_eq hsupp, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [coef_crePoly, enorm_sqrt_mul_sq (by positivity), add_tsub_cancel_right, ← mul_assoc,
    ← mul_assoc]
  refine mul_le_mul_left ?_ _
  have hdeg : (a + Finsupp.single i 1).degree = a.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hai : a i ≤ a.degree := Finsupp.le_degree i a
  have hcast : ENNReal.ofReal (((a + Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) : ℝ)
      = ((a i + 1 : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_natCast]
    simp
  rw [wt, wt, hdeg, hcast, show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) by norm_num]
  rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_mul,
    Nat.cast_le, pow_succ, ← mul_assoc, ← mul_pow]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) m) (by omega)

/-! ## 4. Polynomial differential operators have finite ladder order -/

/-- Multiplication by a polynomial, as a linear map. -/
def mulL (q : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  LinearMap.mulLeft ℂ q

@[simp] theorem mulL_apply (q p : MvPolynomial (Fin d) ℂ) : mulL q p = q * p := rfl

theorem mulL_X_eq (i : Fin d) : mulL (X i : MvPolynomial (Fin d) ℂ) = annPoly i + crePoly i := by
  refine LinearMap.ext fun p => ?_
  -- `annPoly_apply` / `crePoly_apply` arrive as theorem nodes, and a published
  -- node carries no `@[simp]` attribute -- name them instead of relying on it.
  simp [annPoly_apply, crePoly_apply]

theorem ladderOrd_mulL_X (i : Fin d) : LadderOrd (mulL (X i : MvPolynomial (Fin d) ℂ)) 1 := by
  rw [mulL_X_eq]
  exact (ladderOrd_annPoly i).add (ladderOrd_crePoly i)

/-- **Multiplication by any polynomial has finite ladder order.** -/
theorem exists_ladderOrd_mulL (q : MvPolynomial (Fin d) ℂ) : ∃ n, LadderOrd (mulL q) n := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      refine ⟨0, ?_⟩
      have h : mulL (C a : MvPolynomial (Fin d) ℂ) = a • LinearMap.id := by
        refine LinearMap.ext fun p => ?_
        simp [smul_eq_C_mul]
      rw [h]
      exact ladderOrd_id.smul a
  | add p q hp hq =>
      obtain ⟨n₁, h₁⟩ := hp
      obtain ⟨n₂, h₂⟩ := hq
      refine ⟨max n₁ n₂, ?_⟩
      have h : mulL (p + q) = mulL p + mulL q := by
        refine LinearMap.ext fun r => ?_
        simp [add_mul]
      rw [h]
      exact (h₁.mono (le_max_left _ _)).add (h₂.mono (le_max_right _ _))
  | mul_X p i hp =>
      obtain ⟨n, h⟩ := hp
      refine ⟨n + 1, ?_⟩
      have h' : mulL (p * X i) = mulL p ∘ₗ mulL (X i) := by
        refine LinearMap.ext fun r => ?_
        simp [mul_assoc]
      rw [h']
      exact h.comp (ladderOrd_mulL_X i)

/-- The twisted derivative `coreD j`, as a linear map. -/
def coreDL (j : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ where
  toFun := coreD j
  map_add' := coreD_add j
  map_smul' := coreD_smul j

theorem coreDL_apply (j : Fin d) (p : MvPolynomial (Fin d) ℂ) : coreDL j p = coreD j p := rfl

theorem coreDL_eq (j : Fin d) :
    coreDL j = (1 / 2 : ℂ) • annPoly j - (1 / 2 : ℂ) • crePoly j := by
  refine LinearMap.ext fun p => ?_
  simp only [coreDL_apply, LinearMap.sub_apply, LinearMap.smul_apply, annPoly_apply,
    crePoly_apply, coreD, smul_eq_C_mul]
  linear_combination (-(pderiv j p)) * (C_half_add_C_half (d := d))

theorem ladderOrd_coreDL (j : Fin d) : LadderOrd (coreDL j) 1 := by
  rw [coreDL_eq]
  exact ((ladderOrd_annPoly j).smul _).sub ((ladderOrd_crePoly j).smul _)

/-- The polynomial realization `p ↦ kinPolyS S p + q p` of `−Δ_S + W`, as a linear map. -/
def hamPolyL (S : Finset (Fin d)) (q : MvPolynomial (Fin d) ℂ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ where
  toFun p := kinPolyS S p + q * p
  map_add' p r := by
    rw [kinPolyS_add]
    ring
  map_smul' c p := by
    rw [kinPolyS_smul, RingHom.id_apply, smul_add, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
    ring







/-! ## 5. Parseval -/

theorem coef_eq_repr (a : Fin d →₀ ℕ) (v : L2d d) : coef a v = hermiteMvBasis.repr v a := by
  rw [HilbertBasis.repr_apply_apply, hermiteMvBasis_apply, coef]

/-- **Parseval**: `‖v‖²_0 = ‖v‖²`. -/
theorem hn_zero_eq (v : L2d d) : hn 0 v = ENNReal.ofReal (‖v‖ ^ 2) := by
  have hsum := lp.hasSum_norm (p := 2) (by norm_num) (hermiteMvBasis.repr v)
  simp only [LinearIsometryEquiv.norm_map] at hsum
  have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  simp only [h2, Real.rpow_natCast] at hsum
  unfold hn
  simp only [wt_zero, one_mul]
  have hpt : ∀ a, ‖coef a v‖ₑ ^ 2 = ENNReal.ofReal (‖(hermiteMvBasis.repr v : _) a‖ ^ 2) := by
    intro a
    rw [coef_eq_repr, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  simp only [hpt]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => by positivity) hsum.summable, hsum.tsum_eq]

/-- **The norm bound on the core.**  An operator of ladder order `n` satisfies
`‖T v‖² ≤ C ‖v‖²_n` on the core.

Inlined from `BookProof/Toolbox/ChapterHermiteLadderOrder.lean` (line 435): the chapter's
`exists_hamCoreS_bound` in `Def_ChapterHermiteGraphApprox` destructures it, so the ladder
bundle has to carry it. -/
theorem LadderOrd.norm_sq_le {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {n : ℕ}
    (hT : LadderOrd T n) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ p, ENNReal.ofReal (‖pgLp (T p)‖ ^ 2) ≤ C * hn n (pgLp p) := by
  obtain ⟨C, hC, h⟩ := hT 0
  refine ⟨C, hC, fun p => ?_⟩
  rw [← hn_zero_eq]
  simpa using h p

end

end BookProof.HermiteLadder


