-- Prove2me | Definitions.Def_GirvingAKS_MGG_YoungAssembly
-- name    : GirvingAKS_MGG_YoungAssembly
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:39:31.853087+00:00
-- url     : https://prove2.me/theorems/08e20ee4-7bc1-40cd-adf6-f150bc0d11d6
-- title:
--   AKS sorting networks (Seiferas port) — Young's Assembly and Final Bound
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/MGG/YoungAssembly.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Combines the pointwise condition into the final Young's inequality assembly: `∑ G·[...] ≤ (5√2/4)·∑ G²`. Depends on `Young.lean` for `pointwiseCondition_forall`.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/YoungAssembly.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_MGG_Young

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/MGG/YoungAssembly.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Young's Assembly and Final Bound

  Combines the pointwise condition into the final Young's inequality assembly:
  `∑ G·[...] ≤ (5√2/4)·∑ G²`.
  Depends on `Young.lean` for `pointwiseCondition_forall`.
-/


section

open Matrix BigOperators Finset Real
open scoped Real

/-! **Step 7: Young's Assembly and Final Bound** -/

/-- `shearS2Fin` as a permutation on `Fin n × Fin n`. -/
def shearS2Equiv (n : ℕ) (hn : 0 < n) : (Fin n × Fin n) ≃ (Fin n × Fin n) where
  toFun := shearS2Fin n hn
  invFun := shearS2InvFin n hn
  left_inv := shearS2Fin_inv_right n hn
  right_inv := shearS2Fin_inv_left n hn

/-- `shearS1Fin` as a permutation on `Fin n × Fin n`. -/
def shearS1Equiv (n : ℕ) (hn : 0 < n) : (Fin n × Fin n) ≃ (Fin n × Fin n) where
  toFun := shearS1Fin n hn
  invFun := shearS1InvFin n hn
  left_inv := shearS1Fin_inv_right n hn
  right_inv := shearS1Fin_inv_left n hn

/-- `1/ψ(α,β) = ψ(β,α)` (division form of the reciprocal property). -/
theorem psiWeight_div_eq (n α₁ α₂ β₁ β₂ : ℕ) :
    1 / psiWeight n α₁ α₂ β₁ β₂ = psiWeight n β₁ β₂ α₁ α₂ := by
  have hpos := psiWeight_pos n α₁ α₂ β₁ β₂
  have := psiWeight_mul_comm n α₁ α₂ β₁ β₂
  field_simp at this ⊢; linarith

/-- `shearS2InvFin` preserves the first coordinate. -/
theorem shearS2InvFin_fst (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    (shearS2InvFin n hn p).1 = p.1 := rfl

/-- `shearS1InvFin` preserves the second coordinate. -/
theorem shearS1InvFin_snd (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    (shearS1InvFin n hn p).2 = p.2 := rfl

/-- `shearS2Fin` at `Fin` level matches `shearS2` at `ℕ` level. -/
theorem shearS2Fin_val (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    ((shearS2Fin n hn p).1.val, (shearS2Fin n hn p).2.val) =
    shearS2 n p.1.val p.2.val := by rfl

/-- `shearS1Fin` at `Fin` level matches `shearS1` at `ℕ` level. -/
theorem shearS1Fin_val (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    ((shearS1Fin n hn p).1.val, (shearS1Fin n hn p).2.val) =
    shearS1 n p.1.val p.2.val := by rfl

/-- `shearS2InvFin` at `Fin` level matches `shearS2Inv` at `ℕ` level. -/
theorem shearS2InvFin_val (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    ((shearS2InvFin n hn p).1.val, (shearS2InvFin n hn p).2.val) =
    shearS2Inv n p.1.val p.2.val := by rfl

/-- `shearS1InvFin` at `Fin` level matches `shearS1Inv` at `ℕ` level. -/
theorem shearS1InvFin_val (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    ((shearS1InvFin n hn p).1.val, (shearS1InvFin n hn p).2.val) =
    shearS1Inv n p.1.val p.2.val := by rfl

/-- Young + reindex for S₂ alone: `2·∑ G·G(S₂α)·cos₁ ≤ ∑ G²·cos₁·(ψ₂+ψ₂⁻¹)`.

    Proof: Young's pointwise gives `2GG' ≤ ψG² + (1/ψ)G'²`.
    Multiply by `cos₁ ≥ 0`, sum, split.
    Reindex `G²(S₂α)` term via `shearS2Equiv.sum_comp`:
    `cos₁(S₂⁻¹β) = cos₁(β)` since S₂⁻¹ preserves first coord,
    and `ψ(S₂α,α) = 1/ψ(α,S₂α) = ψ(β,S₂⁻¹β)` after substitution. -/
theorem young_S2_bound (n : ℕ) (hn : 0 < n)
    (G : Fin n → Fin n → ℝ) :
    2 * ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * G (shearS2Fin n hn (α₁, α₂)).1 (shearS2Fin n hn (α₁, α₂)).2 *
        |cos (↑π * ↑α₁.val / ↑n)| ≤
    ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ ^ 2 * |cos (↑π * ↑α₁.val / ↑n)| *
      (psiWeight n α₁.val α₂.val (shearS2 n α₁.val α₂.val).1
        (shearS2 n α₁.val α₂.val).2 +
       psiWeight n α₁.val α₂.val (shearS2Inv n α₁.val α₂.val).1
        (shearS2Inv n α₁.val α₂.val).2) := by
  -- Step 1: Pointwise Young's inequality, multiplied by cos₁ ≥ 0, summed
  -- For each (α₁,α₂): 2*G*G'*|cos| ≤ (ψ*G² + ψ'*G'²)*|cos|
  have h_pw : ∀ α₁ α₂ : Fin n,
      2 * (G α₁ α₂ * G (shearS2Fin n hn (α₁, α₂)).1 (shearS2Fin n hn (α₁, α₂)).2 *
        |cos (↑π * ↑α₁.val / ↑n)|) ≤
      (psiWeight n α₁.val α₂.val (shearS2 n α₁.val α₂.val).1
        (shearS2 n α₁.val α₂.val).2 * G α₁ α₂ ^ 2 +
       psiWeight n (shearS2 n α₁.val α₂.val).1 (shearS2 n α₁.val α₂.val).2
        α₁.val α₂.val *
        G (shearS2Fin n hn (α₁, α₂)).1 (shearS2Fin n hn (α₁, α₂)).2 ^ 2) *
      |cos (↑π * ↑α₁.val / ↑n)| := by
    intro α₁ α₂
    have hψ := psiWeight_pos n α₁.val α₂.val (shearS2 n α₁.val α₂.val).1
      (shearS2 n α₁.val α₂.val).2
    have hy := young_reciprocal_weight (G α₁ α₂)
      (G (shearS2Fin n hn (α₁, α₂)).1 (shearS2Fin n hn (α₁, α₂)).2)
      (psiWeight n α₁.val α₂.val (shearS2 n α₁.val α₂.val).1
        (shearS2 n α₁.val α₂.val).2) hψ
    rw [psiWeight_div_eq] at hy
    nlinarith [abs_nonneg (cos (↑π * ↑α₁.val / ↑n))]
  -- Sum the pointwise bound
  have h_le : 2 * ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * G (shearS2Fin n hn (α₁, α₂)).1 (shearS2Fin n hn (α₁, α₂)).2 *
        |cos (↑π * ↑α₁.val / ↑n)| ≤
    ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      (psiWeight n α₁.val α₂.val (shearS2 n α₁.val α₂.val).1
        (shearS2 n α₁.val α₂.val).2 * G α₁ α₂ ^ 2 +
       psiWeight n (shearS2 n α₁.val α₂.val).1 (shearS2 n α₁.val α₂.val).2
        α₁.val α₂.val *
        G (shearS2Fin n hn (α₁, α₂)).1 (shearS2Fin n hn (α₁, α₂)).2 ^ 2) *
      |cos (↑π * ↑α₁.val / ↑n)| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro α₁ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro α₂ _
    exact h_pw α₁ α₂
  -- Step 2: Split the middle sum and reindex
  -- Split: ∑(A+B)*cos = ∑A*cos + ∑B*cos
  have h_split : ∀ (f g : Fin n → Fin n → ℝ) (w : Fin n → Fin n → ℝ),
      ∑ a₁ : Fin n, ∑ a₂ : Fin n, (f a₁ a₂ + g a₁ a₂) * w a₁ a₂ =
      ∑ a₁ : Fin n, ∑ a₂ : Fin n, f a₁ a₂ * w a₁ a₂ +
      ∑ a₁ : Fin n, ∑ a₂ : Fin n, g a₁ a₂ * w a₁ a₂ := by
    intro f g w
    simp_rw [add_mul, ← Finset.sum_add_distrib]
  -- Reindex second sum via shearS2Equiv: ∑_α h(S₂α) = ∑_β h(β)
  have h_reindex : ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      psiWeight n (shearS2 n α₁.val α₂.val).1 (shearS2 n α₁.val α₂.val).2
        α₁.val α₂.val *
      G (shearS2Fin n hn (α₁, α₂)).1 (shearS2Fin n hn (α₁, α₂)).2 ^ 2 *
      |cos (↑π * ↑α₁.val / ↑n)| =
    ∑ β₁ : Fin n, ∑ β₂ : Fin n,
      psiWeight n β₁.val β₂.val (shearS2Inv n β₁.val β₂.val).1
        (shearS2Inv n β₁.val β₂.val).2 *
      G β₁ β₂ ^ 2 * |cos (↑π * ↑β₁.val / ↑n)| := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    -- Each LHS summand equals F(S₂p) where F(β) = ψ(β,S₂⁻¹β)·G(β)²·cos₁(β)
    -- using S₂⁻¹∘S₂ = id and S₂ preserves first coord
    have key : ∀ p : Fin n × Fin n,
        psiWeight n (shearS2 n p.1.val p.2.val).1 (shearS2 n p.1.val p.2.val).2
          p.1.val p.2.val *
        G (shearS2Fin n hn p).1 (shearS2Fin n hn p).2 ^ 2 *
        |cos (↑π * ↑p.1.val / ↑n)| =
        (fun β : Fin n × Fin n =>
          psiWeight n β.1.val β.2.val (shearS2Inv n β.1.val β.2.val).1
            (shearS2Inv n β.1.val β.2.val).2 *
          G β.1 β.2 ^ 2 * |cos (↑π * ↑β.1.val / ↑n)|) (shearS2Fin n hn p) := by
      intro p
      -- Extract Nat-level round-trip from Fin-level shearS2Fin_inv_right
      have h_rt := shearS2Fin_inv_right n hn p
      have h2 : (shearS2Inv n p.1.val (shearS2Fin n hn p).2.val).2 = p.2.val := by
        show (shearS2InvFin n hn (shearS2Fin n hn p)).2.val = p.2.val
        exact congrArg (·.2.val) h_rt
      -- S₂ preserves first coord; h2 rewrites the round-trip; rest is definitional
      simp only [shearS2Fin_fst, h2]; rfl
    exact Fintype.sum_equiv (shearS2Equiv n hn) _ _ key
  -- Combine everything
  calc 2 * _ ≤ _ := h_le
    _ = ∑ α₁, ∑ α₂,
        psiWeight n α₁.val α₂.val (shearS2 n α₁.val α₂.val).1
          (shearS2 n α₁.val α₂.val).2 * G α₁ α₂ ^ 2 *
        |cos (↑π * ↑α₁.val / ↑n)| +
      ∑ α₁, ∑ α₂,
        psiWeight n (shearS2 n α₁.val α₂.val).1 (shearS2 n α₁.val α₂.val).2
          α₁.val α₂.val *
        G (shearS2Fin n hn (α₁, α₂)).1 (shearS2Fin n hn (α₁, α₂)).2 ^ 2 *
        |cos (↑π * ↑α₁.val / ↑n)| := by rw [h_split]
    _ = ∑ α₁, ∑ α₂,
        psiWeight n α₁.val α₂.val (shearS2 n α₁.val α₂.val).1
          (shearS2 n α₁.val α₂.val).2 * G α₁ α₂ ^ 2 *
        |cos (↑π * ↑α₁.val / ↑n)| +
      ∑ β₁, ∑ β₂,
        psiWeight n β₁.val β₂.val (shearS2Inv n β₁.val β₂.val).1
          (shearS2Inv n β₁.val β₂.val).2 *
        G β₁ β₂ ^ 2 * |cos (↑π * ↑β₁.val / ↑n)| := by
        rw [h_reindex]
    _ = _ := by
        rw [← Finset.sum_add_distrib]; congr 1; ext α₁
        rw [← Finset.sum_add_distrib]; congr 1; ext α₂; ring

/-- Young + reindex for S₁ alone: `2·∑ G·G(S₁α)·cos₂ ≤ ∑ G²·cos₂·(ψ₁+ψ₁⁻¹)`.
    Same structure as `young_S2_bound`, with S₁ (preserves second coord). -/
theorem young_S1_bound (n : ℕ) (hn : 0 < n)
    (G : Fin n → Fin n → ℝ) :
    2 * ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * G (shearS1Fin n hn (α₁, α₂)).1 (shearS1Fin n hn (α₁, α₂)).2 *
        |cos (↑π * ↑α₂.val / ↑n)| ≤
    ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ ^ 2 * |cos (↑π * ↑α₂.val / ↑n)| *
      (psiWeight n α₁.val α₂.val (shearS1 n α₁.val α₂.val).1
        (shearS1 n α₁.val α₂.val).2 +
       psiWeight n α₁.val α₂.val (shearS1Inv n α₁.val α₂.val).1
        (shearS1Inv n α₁.val α₂.val).2) := by
  -- Step 1: Pointwise Young's inequality, multiplied by cos₂ ≥ 0, summed
  have h_pw : ∀ α₁ α₂ : Fin n,
      2 * (G α₁ α₂ * G (shearS1Fin n hn (α₁, α₂)).1 (shearS1Fin n hn (α₁, α₂)).2 *
        |cos (↑π * ↑α₂.val / ↑n)|) ≤
      (psiWeight n α₁.val α₂.val (shearS1 n α₁.val α₂.val).1
        (shearS1 n α₁.val α₂.val).2 * G α₁ α₂ ^ 2 +
       psiWeight n (shearS1 n α₁.val α₂.val).1 (shearS1 n α₁.val α₂.val).2
        α₁.val α₂.val *
        G (shearS1Fin n hn (α₁, α₂)).1 (shearS1Fin n hn (α₁, α₂)).2 ^ 2) *
      |cos (↑π * ↑α₂.val / ↑n)| := by
    intro α₁ α₂
    have hψ := psiWeight_pos n α₁.val α₂.val (shearS1 n α₁.val α₂.val).1
      (shearS1 n α₁.val α₂.val).2
    have hy := young_reciprocal_weight (G α₁ α₂)
      (G (shearS1Fin n hn (α₁, α₂)).1 (shearS1Fin n hn (α₁, α₂)).2)
      (psiWeight n α₁.val α₂.val (shearS1 n α₁.val α₂.val).1
        (shearS1 n α₁.val α₂.val).2) hψ
    rw [psiWeight_div_eq] at hy
    nlinarith [abs_nonneg (cos (↑π * ↑α₂.val / ↑n))]
  have h_le : 2 * ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * G (shearS1Fin n hn (α₁, α₂)).1 (shearS1Fin n hn (α₁, α₂)).2 *
        |cos (↑π * ↑α₂.val / ↑n)| ≤
    ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      (psiWeight n α₁.val α₂.val (shearS1 n α₁.val α₂.val).1
        (shearS1 n α₁.val α₂.val).2 * G α₁ α₂ ^ 2 +
       psiWeight n (shearS1 n α₁.val α₂.val).1 (shearS1 n α₁.val α₂.val).2
        α₁.val α₂.val *
        G (shearS1Fin n hn (α₁, α₂)).1 (shearS1Fin n hn (α₁, α₂)).2 ^ 2) *
      |cos (↑π * ↑α₂.val / ↑n)| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro α₁ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro α₂ _
    exact h_pw α₁ α₂
  -- Step 2: Split and reindex
  have h_split : ∀ (f g : Fin n → Fin n → ℝ) (w : Fin n → Fin n → ℝ),
      ∑ a₁ : Fin n, ∑ a₂ : Fin n, (f a₁ a₂ + g a₁ a₂) * w a₁ a₂ =
      ∑ a₁ : Fin n, ∑ a₂ : Fin n, f a₁ a₂ * w a₁ a₂ +
      ∑ a₁ : Fin n, ∑ a₂ : Fin n, g a₁ a₂ * w a₁ a₂ := by
    intro f g w
    simp_rw [add_mul, ← Finset.sum_add_distrib]
  have h_reindex : ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      psiWeight n (shearS1 n α₁.val α₂.val).1 (shearS1 n α₁.val α₂.val).2
        α₁.val α₂.val *
      G (shearS1Fin n hn (α₁, α₂)).1 (shearS1Fin n hn (α₁, α₂)).2 ^ 2 *
      |cos (↑π * ↑α₂.val / ↑n)| =
    ∑ β₁ : Fin n, ∑ β₂ : Fin n,
      psiWeight n β₁.val β₂.val (shearS1Inv n β₁.val β₂.val).1
        (shearS1Inv n β₁.val β₂.val).2 *
      G β₁ β₂ ^ 2 * |cos (↑π * ↑β₂.val / ↑n)| := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    have key : ∀ p : Fin n × Fin n,
        psiWeight n (shearS1 n p.1.val p.2.val).1 (shearS1 n p.1.val p.2.val).2
          p.1.val p.2.val *
        G (shearS1Fin n hn p).1 (shearS1Fin n hn p).2 ^ 2 *
        |cos (↑π * ↑p.2.val / ↑n)| =
        (fun β : Fin n × Fin n =>
          psiWeight n β.1.val β.2.val (shearS1Inv n β.1.val β.2.val).1
            (shearS1Inv n β.1.val β.2.val).2 *
          G β.1 β.2 ^ 2 * |cos (↑π * ↑β.2.val / ↑n)|) (shearS1Fin n hn p) := by
      intro p
      -- Extract Nat-level round-trip from Fin-level shearS1Fin_inv_right
      have h_rt := shearS1Fin_inv_right n hn p
      have h1 : (shearS1Inv n (shearS1Fin n hn p).1.val p.2.val).1 = p.1.val := by
        show (shearS1InvFin n hn (shearS1Fin n hn p)).1.val = p.1.val
        exact congrArg (·.1.val) h_rt
      -- S₁ preserves second coord; h1 rewrites the round-trip; rest is definitional
      simp only [shearS1Fin_snd, h1]; rfl
    exact Fintype.sum_equiv (shearS1Equiv n hn) _ _ key
  calc 2 * _ ≤ _ := h_le
    _ = ∑ α₁, ∑ α₂,
        psiWeight n α₁.val α₂.val (shearS1 n α₁.val α₂.val).1
          (shearS1 n α₁.val α₂.val).2 * G α₁ α₂ ^ 2 *
        |cos (↑π * ↑α₂.val / ↑n)| +
      ∑ α₁, ∑ α₂,
        psiWeight n (shearS1 n α₁.val α₂.val).1 (shearS1 n α₁.val α₂.val).2
          α₁.val α₂.val *
        G (shearS1Fin n hn (α₁, α₂)).1 (shearS1Fin n hn (α₁, α₂)).2 ^ 2 *
        |cos (↑π * ↑α₂.val / ↑n)| := by rw [h_split]
    _ = ∑ α₁, ∑ α₂,
        psiWeight n α₁.val α₂.val (shearS1 n α₁.val α₂.val).1
          (shearS1 n α₁.val α₂.val).2 * G α₁ α₂ ^ 2 *
        |cos (↑π * ↑α₂.val / ↑n)| +
      ∑ β₁, ∑ β₂,
        psiWeight n β₁.val β₂.val (shearS1Inv n β₁.val β₂.val).1
          (shearS1Inv n β₁.val β₂.val).2 *
        G β₁ β₂ ^ 2 * |cos (↑π * ↑β₂.val / ↑n)| := by
        rw [h_reindex]
    _ = _ := by
        rw [← Finset.sum_add_distrib]; congr 1; ext α₁
        rw [← Finset.sum_add_distrib]; congr 1; ext α₂; ring

/-- Young's inequality + sum reindexing: `2·LHS ≤ ∑ G²·PC(α)`.

    Combines `young_S2_bound` + `young_S1_bound` via sum splitting. -/
theorem young_bilinear_le_pc (n : ℕ) (hn : 0 < n)
    (G : Fin n → Fin n → ℝ) :
    2 * ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * (G (shearS2Fin n hn (α₁, α₂)).1
                    (shearS2Fin n hn (α₁, α₂)).2 *
                  |cos (↑π * ↑α₁.val / ↑n)| +
                  G (shearS1Fin n hn (α₁, α₂)).1
                    (shearS1Fin n hn (α₁, α₂)).2 *
                  |cos (↑π * ↑α₂.val / ↑n)|) ≤
    ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ ^ 2 *
      (|cos (↑π * ↑α₁.val / ↑n)| *
        (psiWeight n α₁.val α₂.val (shearS2 n α₁.val α₂.val).1
          (shearS2 n α₁.val α₂.val).2 +
         psiWeight n α₁.val α₂.val (shearS2Inv n α₁.val α₂.val).1
          (shearS2Inv n α₁.val α₂.val).2) +
       |cos (↑π * ↑α₂.val / ↑n)| *
        (psiWeight n α₁.val α₂.val (shearS1 n α₁.val α₂.val).1
          (shearS1 n α₁.val α₂.val).2 +
         psiWeight n α₁.val α₂.val (shearS1Inv n α₁.val α₂.val).1
          (shearS1Inv n α₁.val α₂.val).2)) := by
  -- Split LHS: distribute G*(...+...) and separate sums
  have hS2 := young_S2_bound n hn G
  have hS1 := young_S1_bound n hn G
  -- LHS = 2*∑(G*G_S₂*cos₁) + 2*∑(G*G_S₁*cos₂)
  have h_lhs : 2 * ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * (G (shearS2Fin n hn (α₁, α₂)).1 (shearS2Fin n hn (α₁, α₂)).2 *
          |cos (↑π * ↑α₁.val / ↑n)| +
        G (shearS1Fin n hn (α₁, α₂)).1 (shearS1Fin n hn (α₁, α₂)).2 *
          |cos (↑π * ↑α₂.val / ↑n)|) =
      2 * ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        G α₁ α₂ * G (shearS2Fin n hn (α₁, α₂)).1 (shearS2Fin n hn (α₁, α₂)).2 *
          |cos (↑π * ↑α₁.val / ↑n)| +
      2 * ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        G α₁ α₂ * G (shearS1Fin n hn (α₁, α₂)).1 (shearS1Fin n hn (α₁, α₂)).2 *
          |cos (↑π * ↑α₂.val / ↑n)| := by
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1; ext α₁; congr 1; ext α₂; ring
  -- RHS = ∑(G²*cos₁*(ψ₂+ψ₂ᵢ)) + ∑(G²*cos₂*(ψ₁+ψ₁ᵢ))
  have h_rhs : ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ ^ 2 *
      (|cos (↑π * ↑α₁.val / ↑n)| *
        (psiWeight n α₁.val α₂.val (shearS2 n α₁.val α₂.val).1
          (shearS2 n α₁.val α₂.val).2 +
         psiWeight n α₁.val α₂.val (shearS2Inv n α₁.val α₂.val).1
          (shearS2Inv n α₁.val α₂.val).2) +
       |cos (↑π * ↑α₂.val / ↑n)| *
        (psiWeight n α₁.val α₂.val (shearS1 n α₁.val α₂.val).1
          (shearS1 n α₁.val α₂.val).2 +
         psiWeight n α₁.val α₂.val (shearS1Inv n α₁.val α₂.val).1
          (shearS1Inv n α₁.val α₂.val).2)) =
      ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        G α₁ α₂ ^ 2 * |cos (↑π * ↑α₁.val / ↑n)| *
        (psiWeight n α₁.val α₂.val (shearS2 n α₁.val α₂.val).1
          (shearS2 n α₁.val α₂.val).2 +
         psiWeight n α₁.val α₂.val (shearS2Inv n α₁.val α₂.val).1
          (shearS2Inv n α₁.val α₂.val).2) +
      ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        G α₁ α₂ ^ 2 * |cos (↑π * ↑α₂.val / ↑n)| *
        (psiWeight n α₁.val α₂.val (shearS1 n α₁.val α₂.val).1
          (shearS1 n α₁.val α₂.val).2 +
         psiWeight n α₁.val α₂.val (shearS1Inv n α₁.val α₂.val).1
          (shearS1Inv n α₁.val α₂.val).2) := by
    rw [← Finset.sum_add_distrib]; congr 1; ext α₁
    rw [← Finset.sum_add_distrib]; congr 1; ext α₂; ring
  rw [h_lhs, h_rhs]
  exact add_le_add hS2 hS1

/-- Pointwise condition bound: `∑ G²·PC(α) ≤ (5√2/2)·∑ G²`.

    For nonzero α: `PC(α) ≤ 5√2/2` by `pointwiseCondition_forall`.
    For α = (0,0): `G(0,0) = 0` so the term vanishes. -/
theorem pc_sum_le (n : ℕ) (hn : 3 ≤ n)
    (G : Fin n → Fin n → ℝ)
    (hG0 : G ⟨0, by omega⟩ ⟨0, by omega⟩ = 0) :
    ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ ^ 2 *
      (|cos (↑π * ↑α₁.val / ↑n)| *
        (psiWeight n α₁.val α₂.val (shearS2 n α₁.val α₂.val).1
          (shearS2 n α₁.val α₂.val).2 +
         psiWeight n α₁.val α₂.val (shearS2Inv n α₁.val α₂.val).1
          (shearS2Inv n α₁.val α₂.val).2) +
       |cos (↑π * ↑α₂.val / ↑n)| *
        (psiWeight n α₁.val α₂.val (shearS1 n α₁.val α₂.val).1
          (shearS1 n α₁.val α₂.val).2 +
         psiWeight n α₁.val α₂.val (shearS1Inv n α₁.val α₂.val).1
          (shearS1Inv n α₁.val α₂.val).2)) ≤
    5 * √2 / 2 * ∑ α₁ : Fin n, ∑ α₂ : Fin n, G α₁ α₂ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro α₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro α₂ _
  by_cases hα : α₁.val = 0 ∧ α₂.val = 0
  · obtain ⟨h1, h2⟩ := hα
    rw [show α₁ = ⟨0, by omega⟩ from Fin.ext h1,
        show α₂ = ⟨0, by omega⟩ from Fin.ext h2, hG0]
    simp
  · have hpc := pointwiseCondition_forall n α₁.val α₂.val hn α₁.isLt α₂.isLt hα
    unfold pointwiseCondition at hpc
    nlinarith [sq_nonneg (G α₁ α₂)]

theorem young_assembly (n : ℕ) (hn : 3 ≤ n)
    (G : Fin n → Fin n → ℝ)
    (hG0 : G ⟨0, by omega⟩ ⟨0, by omega⟩ = 0) :
    ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * (G (shearS2Fin n (by omega) (α₁, α₂)).1
                    (shearS2Fin n (by omega) (α₁, α₂)).2 *
                  |cos (↑π * ↑α₁.val / ↑n)| +
                  G (shearS1Fin n (by omega) (α₁, α₂)).1
                    (shearS1Fin n (by omega) (α₁, α₂)).2 *
                  |cos (↑π * ↑α₂.val / ↑n)|)
    ≤ 5 * √2 / 4 * ∑ α₁ : Fin n, ∑ α₂ : Fin n, G α₁ α₂ ^ 2 := by
  have hn0 : 0 < n := by omega
  have h1 := young_bilinear_le_pc n hn0 G
  have h2 := pc_sum_le n hn G hG0
  have h3 : 5 * √2 / 2 = 2 * (5 * √2 / 4) := by ring
  rw [h3] at h2
  linarith

end


