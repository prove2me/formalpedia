-- Prove2me | Definitions.Def_GirvingAKS_MGG_YoungDefs
-- name    : GirvingAKS_MGG_YoungDefs
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:33:28.326811+00:00
-- url     : https://prove2.me/theorems/75b1dc3d-2705-4283-b9fc-17f5157a3dde
-- title:
--   AKS sorting networks (Seiferas port) — Young's Inequality and Pointwise Condition for MGG
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/MGG/YoungDefs.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Proves the sufficient pointwise condition for the MGG spectral bound: for all α ∈ (Z/nZ)² \ {0}: |cos(πα₁/n)| · [ψ(α,S₂α) + ψ(α,S₂⁻¹α)] + |cos(πα₂/n)| · [ψ(α,S₁α) + ψ(α,S₁⁻¹α)] ≤ 5√2/2
--
--   Uses the distance-based weight function ψ and case analysis on diamond/outside-diamond regions. Definitions, helper lemmas, and cross-constraints.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/YoungDefs.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_MGG_DFT

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/MGG/YoungDefs.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Young's Inequality and Pointwise Condition for MGG

  Proves the sufficient pointwise condition for the MGG spectral bound:
  for all α ∈ (Z/nZ)² \ {0}:
    |cos(πα₁/n)| · [ψ(α,S₂α) + ψ(α,S₂⁻¹α)]
    + |cos(πα₂/n)| · [ψ(α,S₁α) + ψ(α,S₁⁻¹α)] ≤ 5√2/2

  Uses the distance-based weight function ψ and case analysis on
  diamond/outside-diamond regions. Definitions, helper lemmas, and cross-constraints.
-/


section

open Matrix BigOperators Finset Real
open scoped Real

/-- Young's inequality with reciprocal weights: `2ab ≤ ψ · a² + (1/ψ) · b²`.
    Risk: LOW — standard AM-GM variant. -/
theorem young_reciprocal_weight (a b ψ : ℝ) (hψ : 0 < ψ) :
    2 * a * b ≤ ψ * a ^ 2 + (1 / ψ) * b ^ 2 := by
  have hψne : ψ ≠ 0 := ne_of_gt hψ
  suffices h : 0 ≤ ψ * (ψ * a ^ 2 + (1 / ψ) * b ^ 2 - 2 * a * b) by nlinarith
  have : ψ * (ψ * a ^ 2 + (1 / ψ) * b ^ 2 - 2 * a * b) = (ψ * a - b) ^ 2 := by
    field_simp; ring
  rw [this]; exact sq_nonneg _


/-! **Step 5: Distance Function and Partial Order**

    Distance to origin in `Z/nZ`: `a(x) = min(x, n-x)` (satisfies `0 ≤ a(x) ≤ n/2`).

    Partial order on `(Z/nZ)² \ {0}`: `α ≥ β` iff `a(α₁) ≥ a(β₁)` and `a(α₂) ≥ a(β₂)`.
    Strict: `α > β` iff `α ≥ β` with at least one strict inequality.

    Diamond: `D = {α ∈ (Z/nZ)² \ {0} : a(α₁) + a(α₂) ≤ n/2}`.

    Weight function with `ε = √2/2`:
    - `ψ(α,β) = ε`   if `α > β`
    - `ψ(α,β) = 1/ε`  if `α < β`
    - `ψ(α,β) = 1`    if incomparable

    Satisfies `ψ(α,β) · ψ(β,α) = 1`.
-/

/-- Distance to 0 in `Z/nZ`: `zmodDist n x = min(x, n - x)`. -/
def zmodDist (n x : ℕ) : ℕ := min x (n - x)

/-- `zmodDist n x ≤ n / 2` for `x < n`. -/
theorem zmodDist_le_half (n x : ℕ) (hx : x < n) : zmodDist n x ≤ n / 2 := by
  unfold zmodDist; omega


/-! **Step 5b: Fourier-Domain Shear Maps**

    The shear maps `M₁, M₂` act on Fourier coefficients via their inverse transposes:
    - `S₁ = M₁⁻ᵀ = [[1,0],[-2,1]]`: maps `(α₁, α₂) → (α₁ - 2α₂, α₂)` mod n
    - `S₂ = M₂⁻ᵀ = [[1,-2],[0,1]]`: maps `(α₁, α₂) → (α₁, α₂ - 2α₁)` mod n

    Each forward map pair (M₁ and M₁+e₁, or M₂ and M₂+e₂) contributes a phase
    factor `(1 + ω^{-α_j})` in Fourier space. Since `(T₁⁻¹)ᵀ = T₂⁻¹` (the maps
    are transposes of each other), the Fourier-domain neighbors and cosine factors
    cross over: `|cos(πα₁/n)|` pairs with S₂ neighbors, `|cos(πα₂/n)|` with S₁.
-/

/-- Fourier-domain shear S₁: `(α₁, α₂) ↦ (α₁ - 2α₂ mod n, α₂)`.
    This is `M₁⁻ᵀ` acting on frequency space. Preserves `α₂`. -/
def shearS1 (n α₁ α₂ : ℕ) : ℕ × ℕ := ((α₁ + n - (2 * α₂) % n) % n, α₂)

/-- Fourier-domain shear S₂: `(α₁, α₂) ↦ (α₁, α₂ - 2α₁ mod n)`.
    This is `M₂⁻ᵀ` acting on frequency space. Preserves `α₁`. -/
def shearS2 (n α₁ α₂ : ℕ) : ℕ × ℕ := (α₁, (α₂ + n - (2 * α₁) % n) % n)

/-- Inverse Fourier-domain shear S₁⁻¹: `(α₁, α₂) ↦ (α₁ + 2α₂ mod n, α₂)`.
    Preserves `α₂`. Satisfies `S₁(S₁⁻¹(α)) = α` and `S₁⁻¹(S₁(α)) = α`. -/
def shearS1Inv (n α₁ α₂ : ℕ) : ℕ × ℕ := ((α₁ + (2 * α₂) % n) % n, α₂)

/-- Inverse Fourier-domain shear S₂⁻¹: `(α₁, α₂) ↦ (α₁, α₂ + 2α₁ mod n)`.
    Preserves `α₁`. Satisfies `S₂(S₂⁻¹(α)) = α` and `S₂⁻¹(S₂(α)) = α`. -/
def shearS2Inv (n α₁ α₂ : ℕ) : ℕ × ℕ := (α₁, (α₂ + (2 * α₁) % n) % n)

/-- Partial order on `(Z/nZ)²` by distance to axes: `α ≻ β` iff
    `zmodDist n α₁ ≥ zmodDist n β₁` and `zmodDist n α₂ ≥ zmodDist n β₂`
    with at least one strict inequality (α is "farther from axes"). -/
def zmodDistGt (n α₁ α₂ β₁ β₂ : ℕ) : Bool :=
  zmodDist n β₁ ≤ zmodDist n α₁ && zmodDist n β₂ ≤ zmodDist n α₂ &&
  (zmodDist n β₁ < zmodDist n α₁ || zmodDist n β₂ < zmodDist n α₂)

/-- Weight function ψ with parameter `α = √2` (matching notes' convention):
    - `√2` if α > β (α farther from axes → BIG weight)
    - `√2/2` if α < β (α closer → SMALL weight)
    - `1` if incomparable
    Product property: `ψ(α,β) · ψ(β,α) = 1`. -/
noncomputable def psiWeight (n α₁ α₂ β₁ β₂ : ℕ) : ℝ :=
  if zmodDistGt n α₁ α₂ β₁ β₂ = true then √2
  else if zmodDistGt n β₁ β₂ α₁ α₂ = true then √2 / 2
  else 1

/-- `zmodDistGt` is antisymmetric. -/
lemma zmodDistGt_antisymm (n α₁ α₂ β₁ β₂ : ℕ) :
    zmodDistGt n α₁ α₂ β₁ β₂ = true → zmodDistGt n β₁ β₂ α₁ α₂ = false := by
  unfold zmodDistGt
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.and_eq_false_iff, Bool.or_eq_false_iff, not_le, not_lt]
  omega

/-- The weight function satisfies `ψ(α,β) · ψ(β,α) = 1`. -/
theorem psiWeight_mul_comm (n α₁ α₂ β₁ β₂ : ℕ) :
    psiWeight n α₁ α₂ β₁ β₂ * psiWeight n β₁ β₂ α₁ α₂ = 1 := by
  have hsq : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  unfold psiWeight
  by_cases h1 : zmodDistGt n α₁ α₂ β₁ β₂ = true
  · rw [if_pos h1, if_neg (by simp [zmodDistGt_antisymm n α₁ α₂ β₁ β₂ h1]),
      if_pos h1]; nlinarith [sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)]
  · rw [if_neg h1]
    by_cases h2 : zmodDistGt n β₁ β₂ α₁ α₂ = true
    · rw [if_pos h2, if_pos h2]
      nlinarith [sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)]
    · rw [if_neg h2, if_neg h1, if_neg h2]; ring

/-- Each ψ value is positive. -/
theorem psiWeight_pos (n α₁ α₂ β₁ β₂ : ℕ) : 0 < psiWeight n α₁ α₂ β₁ β₂ := by
  unfold psiWeight; split <;> [positivity; split <;> positivity]

/-- The pointwise condition (*) for a single frequency α ≠ 0.
    After DFT + Young's inequality, the sufficient condition pairs each cosine
    with the shear that **preserves** that coordinate:
    - `|cos(πα₁/n)|` pairs with `S₂, S₂⁻¹` (which preserve `α₁`)
    - `|cos(πα₂/n)|` pairs with `S₁, S₁⁻¹` (which preserve `α₂`)

    This is because the substitution `α' = S_i α` in Young's inequality
    requires the cosine factor to be invariant under `S_i`. -/
def pointwiseCondition (n α₁ α₂ : ℕ) : Prop :=
  let s1 := shearS1 n α₁ α₂        -- S₁α (preserves α₂)
  let s1i := shearS1Inv n α₁ α₂    -- S₁⁻¹α (preserves α₂)
  let s2 := shearS2 n α₁ α₂        -- S₂α (preserves α₁)
  let s2i := shearS2Inv n α₁ α₂    -- S₂⁻¹α (preserves α₁)
  -- cos₁ with S₂ (preserves α₁), cos₂ with S₁ (preserves α₂)
  |cos (π * α₁ / n)| * (psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2) +
  |cos (π * α₂ / n)| * (psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2)
    ≤ 5 * √2 / 2


/-! **Step 6: Case Analysis**

    **Case A: Outside the diamond** (`a(α₁) + a(α₂) > n/2`).

    Key bound: `|cos(πα₁/n)| + |cos(πα₂/n)| ≤ √2` when `a(α₁) + a(α₂) > n/2`.
    Each ψ pair sum is at most `α + 1/α = √2 + √2/2 = 3√2/2`.
    Combined: `(3√2/2) · √2 = 3 < 5√2/2 ≈ 3.535`. ✓

    **Case B: Inside the diamond** (`a(α₁) + a(α₂) ≤ n/2`).

    Bound `|cos| ≤ 1`. The key combinatorial fact: for α inside the diamond,
    of the 4 neighbors `{S₁α, S₁⁻¹α, S₂α, S₂⁻¹α}`:
    - Typically 3 are "farther" (> α) and 1 is "closer" (< α):
      ψ sum = `3·(√2/2) + √2 = 5√2/2` (tight!)
      (With our convention: 3 farther neighbors get ψ = √2/2 since α < neighbor,
       1 closer neighbor gets ψ = √2 since α > neighbor.)
    - Or 2 are farther, 2 are incomparable:
      ψ sum = `2·(√2/2) + 2·1 = √2 + 2 < 5√2/2`
-/

/-- `|cos(πa/n)| = cos(π · zmodDist(n,a) / n)` for `a < n`. -/
lemma abs_cos_eq_cos_zmodDist (n a : ℕ) (ha : a < n) (hn : 0 < n) :
    |cos (π * ↑a / ↑n)| = cos (π * ↑(zmodDist n a) / ↑n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpi := pi_pos
  unfold zmodDist
  by_cases h : a ≤ n - a
  · rw [min_eq_left h, abs_of_nonneg]
    apply cos_nonneg_of_mem_Icc
    constructor
    · linarith [div_nonneg (mul_nonneg hpi.le (Nat.cast_nonneg (α := ℝ) a)) hn'.le]
    · have : 2 * (a : ℝ) ≤ n := by
        have := Nat.cast_le (α := ℝ).mpr h; rw [Nat.cast_sub ha.le] at this; linarith
      rw [div_le_div_iff₀ hn' two_pos]; nlinarith
  · push_neg at h
    rw [min_eq_right h.le, show π * (↑(n - a) : ℝ) / ↑n = π - π * ↑a / ↑n from by
      rw [Nat.cast_sub ha.le]; field_simp]
    rw [cos_pi_sub, abs_of_nonpos]
    apply cos_nonpos_of_pi_div_two_le_of_le
    · have : (n : ℝ) < 2 * a := by
        have := Nat.cast_lt (α := ℝ).mpr h; rw [Nat.cast_sub ha.le] at this; linarith
      rw [le_div_iff₀ hn']; nlinarith
    · rw [div_le_iff₀ hn']; nlinarith [Nat.cast_lt (α := ℝ).mpr ha]

/-- `cos y ≤ sin x` when `x + y > π/2` and `x, y ∈ [0, π/2]`.
    Follows from strict antitonicity of `cos` on `[0, π]`. -/
lemma cos_le_sin_of_sum_gt (x y : ℝ)
    (hx' : x ≤ π / 2) (hy' : y ≤ π / 2)
    (hsum : π / 2 < x + y) :
    cos y ≤ sin x := by
  have hpi := pi_pos
  calc cos y
      ≤ cos (π / 2 - x) :=
        cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    _ = sin x := cos_pi_div_two_sub x

/-- Cauchy-Schwarz inequality for two components:
    `a₁b₁ + a₂b₂ ≤ √(a₁²+a₂²) · √(b₁²+b₂²)` when all terms are non-negative. -/
lemma cauchy_schwarz_two (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    a₁ * b₁ + a₂ * b₂ ≤ √(a₁ ^ 2 + a₂ ^ 2) * √(b₁ ^ 2 + b₂ ^ 2) := by
  have h : 0 ≤ a₁ * b₁ + a₂ * b₂ := by positivity
  rw [← Real.sqrt_mul (by positivity : 0 ≤ a₁ ^ 2 + a₂ ^ 2)]
  rw [Real.le_sqrt h (by positivity)]
  nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁)]

/-- Outside the diamond, `cos²(πα₁/n) + cos²(πα₂/n) ≤ 1`.
    Follows from `cos(πd₂/n) ≤ sin(πd₁/n)` when `d₁ + d₂ > n/2`. -/
lemma cos_sq_sum_le_one (n α₁ α₂ : ℕ) (hn : 0 < n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hout : n / 2 < zmodDist n α₁ + zmodDist n α₂) :
    |cos (π * α₁ / n)| ^ 2 + |cos (π * α₂ / n)| ^ 2 ≤ 1 := by
  -- Rewrite |cos| to cos of zmodDist
  rw [abs_cos_eq_cos_zmodDist n α₁ hα₁ hn, abs_cos_eq_cos_zmodDist n α₂ hα₂ hn]
  set d₁ := zmodDist n α₁; set d₂ := zmodDist n α₂
  -- Use cos_sum_le_sqrt2 gives cos d₁ + cos d₂ ≤ √2
  -- More specifically: cos d₂ ≤ sin d₁ (from d₁ + d₂ > n/2 → θ₁ + θ₂ > π/2)
  -- Then cos²d₁ + cos²d₂ ≤ cos²d₁ + sin²d₁ = 1
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpi := pi_pos
  have hd₁_le : d₁ ≤ n / 2 := zmodDist_le_half n α₁ hα₁
  have hd₂_le : d₂ ≤ n / 2 := zmodDist_le_half n α₂ hα₂
  have hd_gt : n < 2 * (d₁ + d₂) := by omega
  have hd₁_2 : 2 * d₁ ≤ n := by omega
  have hd₂_2 : 2 * d₂ ≤ n := by omega
  have hd₁_r : 2 * (d₁ : ℝ) ≤ n := by exact_mod_cast hd₁_2
  have hd₂_r : 2 * (d₂ : ℝ) ≤ n := by exact_mod_cast hd₂_2
  have hd_gt_r : (n : ℝ) < 2 * ((d₁ : ℝ) + d₂) := by exact_mod_cast hd_gt
  -- θ₁ = πd₁/n, θ₂ = πd₂/n
  set θ₁ := π * (d₁ : ℝ) / n; set θ₂ := π * (d₂ : ℝ) / n
  have hθ₁_nn : 0 ≤ θ₁ := by positivity
  have hθ₂_nn : 0 ≤ θ₂ := by positivity
  have hθ₁_le : θ₁ ≤ π / 2 := by
    show π * ↑d₁ / ↑n ≤ π / 2
    rw [div_le_div_iff₀ hn' (by norm_num : (0:ℝ) < 2)]; nlinarith
  have hθ₂_le : θ₂ ≤ π / 2 := by
    show π * ↑d₂ / ↑n ≤ π / 2
    rw [div_le_div_iff₀ hn' (by norm_num : (0:ℝ) < 2)]; nlinarith
  have hθ_sum : π / 2 < θ₁ + θ₂ := by
    show π / 2 < π * ↑d₁ / ↑n + π * ↑d₂ / ↑n
    rw [show π * ↑d₁ / ↑n + π * ↑d₂ / ↑n = π * (↑d₁ + ↑d₂) / ↑n from by ring]
    rw [lt_div_iff₀ hn']; nlinarith
  have hcos₂_le : cos θ₂ ≤ sin θ₁ := cos_le_sin_of_sum_gt θ₁ θ₂ hθ₁_le hθ₂_le hθ_sum
  have hcos₂_nn : 0 ≤ cos θ₂ := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  nlinarith [sq_le_sq' (by linarith : -sin θ₁ ≤ cos θ₂) hcos₂_le, sin_sq_add_cos_sq θ₁]

/-! **Helper lemmas for pair squared sum bound** -/

/-- `psiWeight` is at most `√2`. -/
lemma psiWeight_le_sqrt2 (n α₁ α₂ β₁ β₂ : ℕ) : psiWeight n α₁ α₂ β₁ β₂ ≤ √2 := by
  have hsq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  unfold psiWeight; split <;> [linarith; split]
  · linarith
  · nlinarith [sq_nonneg (√2 - 1)]

/-- `psiWeight` is at most `1` when `α` is NOT farther from axes than `β`. -/
lemma psiWeight_le_one_of_not_gt (n α₁ α₂ β₁ β₂ : ℕ)
    (h : zmodDistGt n α₁ α₂ β₁ β₂ = false) : psiWeight n α₁ α₂ β₁ β₂ ≤ 1 := by
  have hsq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  unfold psiWeight
  rw [if_neg (Bool.eq_false_iff.mp h)]
  split
  · nlinarith [sq_nonneg (√2 - 2)]
  · linarith

/-- `psiWeight` equals `√2` when `α` IS farther from axes than `β`. -/
lemma psiWeight_eq_sqrt2_of_gt (n α₁ α₂ β₁ β₂ : ℕ)
    (h : zmodDistGt n α₁ α₂ β₁ β₂ = true) : psiWeight n α₁ α₂ β₁ β₂ = √2 := by
  unfold psiWeight; rw [if_pos h]

/-- `psiWeight` equals `√2/2` when `β` IS farther from axes than `α`. -/
lemma psiWeight_eq_sqrt2_div2_of_rev_gt (n α₁ α₂ β₁ β₂ : ℕ)
    (h1 : zmodDistGt n α₁ α₂ β₁ β₂ = false)
    (h2 : zmodDistGt n β₁ β₂ α₁ α₂ = true) : psiWeight n α₁ α₂ β₁ β₂ = √2 / 2 := by
  unfold psiWeight; rw [if_neg (Bool.eq_false_iff.mp h1), if_pos h2]

/-- When S₂ preserves the first coordinate (`s2.1 = α₁`), `zmodDistGt` reduces to
    comparing the second coordinate distances. -/
lemma zmodDistGt_of_fst_eq (n α₁ α₂ β₂ : ℕ) :
    zmodDistGt n α₁ α₂ α₁ β₂ = decide (zmodDist n β₂ < zmodDist n α₂) := by
  unfold zmodDistGt
  simp only [le_refl, lt_irrefl, decide_true, decide_false, Bool.true_and, Bool.false_or]
  cases Nat.decLt (zmodDist n β₂) (zmodDist n α₂) with
  | isTrue h => simp [h, h.le]
  | isFalse h => simp [h]

/-- When S₁ preserves the second coordinate (`s1.2 = α₂`), `zmodDistGt` reduces to
    comparing the first coordinate distances. -/
lemma zmodDistGt_of_snd_eq (n α₁ α₂ β₁ : ℕ) :
    zmodDistGt n α₁ α₂ β₁ α₂ = decide (zmodDist n β₁ < zmodDist n α₁) := by
  unfold zmodDistGt
  simp only [le_refl, lt_irrefl, decide_true, decide_false, Bool.and_true, Bool.or_false]
  cases Nat.decLt (zmodDist n β₁) (zmodDist n α₁) with
  | isTrue h => simp [h, h.le]
  | isFalse h => simp [h]

/-- Shear S₂ preserves the first coordinate. -/
lemma shearS2_fst (n α₁ α₂ : ℕ) : (shearS2 n α₁ α₂).1 = α₁ := rfl

/-- Shear S₂⁻¹ preserves the first coordinate. -/
lemma shearS2Inv_fst (n α₁ α₂ : ℕ) : (shearS2Inv n α₁ α₂).1 = α₁ := rfl

/-- Shear S₁ preserves the second coordinate. -/
lemma shearS1_snd (n α₁ α₂ : ℕ) : (shearS1 n α₁ α₂).2 = α₂ := rfl

/-- Shear S₁⁻¹ preserves the second coordinate. -/
lemma shearS1Inv_snd (n α₁ α₂ : ℕ) : (shearS1Inv n α₁ α₂).2 = α₂ := rfl

/-! **Cross-constraint: both S₂ closer prevents both S₁ closer**

    The key number-theoretic lemma: if both S₂ shear neighbors are strictly closer
    to the axes (in `zmodDist`), then S₁ closer implies S₁⁻¹ farther, and vice versa.
    Proved by case analysis on whether `2α₁, 2α₂ ≥ n` (determines `(2α)%n`),
    then 16-fold case splits on outer `%n` terms, each closed by `omega`. -/

/-! **Clean modular-arithmetic helpers for zmodDist of shear outputs.**

These eliminate all `%` from `zmodDist(shear(...))` in one rewrite step,
converting to `if/min` expressions that `split_ifs <;> omega` can close.
Shared across all 11 expensive case-analysis theorems below. -/

/-- Eliminates outer `%` from `min ((a + n - δ) % n) (n - (a + n - δ) % n)`. -/
theorem zd_sub (n a δ : ℕ) (ha : a < n) (hδ : δ < n) :
    min ((a + n - δ) % n) (n - (a + n - δ) % n) =
    if a < δ then min (a + n - δ) (δ - a) else min (a - δ) (n - a + δ) := by
  by_cases h : a < δ
  · rw [if_pos h, Nat.mod_eq_of_lt (by omega)]; simp only [Nat.min_def]; split_ifs <;> omega
  · rw [if_neg h, show a + n - δ = (a - δ) + n from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [Nat.min_def]; split_ifs <;> omega

/-- Eliminates outer `%` from `min ((a + δ) % n) (n - (a + δ) % n)`. -/
theorem zd_add (n a δ : ℕ) (ha : a < n) (hδ : δ < n) :
    min ((a + δ) % n) (n - (a + δ) % n) =
    if a + δ < n then min (a + δ) (n - a - δ) else min (a + δ - n) (2 * n - a - δ) := by
  by_cases h : a + δ < n
  · rw [if_pos h, Nat.mod_eq_of_lt h]; simp only [Nat.min_def]; split_ifs <;> omega
  · rw [if_neg h, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [Nat.min_def]; split_ifs <;> omega

/-- `zmodDist n (shearS2 n α₁ α₂).2` without outer `%`. -/
theorem zd_S2 (n α₁ α₂ : ℕ) (_ : α₁ < n) (h : α₂ < n) (hn : 0 < n) :
    zmodDist n (shearS2 n α₁ α₂).2 =
    if α₂ < (2*α₁)%n then min (α₂+n-(2*α₁)%n) ((2*α₁)%n-α₂)
    else min (α₂-(2*α₁)%n) (n-α₂+(2*α₁)%n) := by
  unfold zmodDist shearS2; simp only; exact zd_sub n α₂ _ h (Nat.mod_lt _ hn)

/-- `zmodDist n (shearS2Inv n α₁ α₂).2` without outer `%`. -/
theorem zd_S2I (n α₁ α₂ : ℕ) (_ : α₁ < n) (h : α₂ < n) (hn : 0 < n) :
    zmodDist n (shearS2Inv n α₁ α₂).2 =
    if α₂+(2*α₁)%n < n then min (α₂+(2*α₁)%n) (n-α₂-(2*α₁)%n)
    else min (α₂+(2*α₁)%n-n) (2*n-α₂-(2*α₁)%n) := by
  unfold zmodDist shearS2Inv; simp only; exact zd_add n α₂ _ h (Nat.mod_lt _ hn)

/-- `zmodDist n (shearS1 n α₁ α₂).1` without outer `%`. -/
theorem zd_S1 (n α₁ α₂ : ℕ) (h : α₁ < n) (_ : α₂ < n) (hn : 0 < n) :
    zmodDist n (shearS1 n α₁ α₂).1 =
    if α₁ < (2*α₂)%n then min (α₁+n-(2*α₂)%n) ((2*α₂)%n-α₁)
    else min (α₁-(2*α₂)%n) (n-α₁+(2*α₂)%n) := by
  unfold zmodDist shearS1; simp only; exact zd_sub n α₁ _ h (Nat.mod_lt _ hn)

/-- `zmodDist n (shearS1Inv n α₁ α₂).1` without outer `%`. -/
theorem zd_S1I (n α₁ α₂ : ℕ) (h : α₁ < n) (_ : α₂ < n) (hn : 0 < n) :
    zmodDist n (shearS1Inv n α₁ α₂).1 =
    if α₁+(2*α₂)%n < n then min (α₁+(2*α₂)%n) (n-α₁-(2*α₂)%n)
    else min (α₁+(2*α₂)%n-n) (2*n-α₁-(2*α₂)%n) := by
  unfold zmodDist shearS1Inv; simp only; exact zd_add n α₁ _ h (Nat.mod_lt _ hn)

/-- `(2 * α) % n = 2 * α` when `2α < n`. -/
theorem double_mod_lo (n α : ℕ) (h : 2 * α < n) : (2 * α) % n = 2 * α :=
  Nat.mod_eq_of_lt h

/-- `(2 * α) % n = 2 * α - n` when `2α ≥ n`. -/
theorem double_mod_hi (n α : ℕ) (hα : α < n) (h : ¬(2 * α < n)) :
    (2 * α) % n = 2 * α - n := by
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Cross-constraint forward: both S₂ closer ∧ S₁ closer ⟹ S₁⁻¹ strictly farther.
    Verified numerically for `n ≤ 300`. -/
theorem cross_constraint_fwd (n α₁ α₂ : ℕ) (hn : 3 ≤ n) (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hs2 : zmodDist n (shearS2 n α₁ α₂).2 < zmodDist n α₂)
    (hs2i : zmodDist n (shearS2Inv n α₁ α₂).2 < zmodDist n α₂)
    (hs1 : zmodDist n (shearS1 n α₁ α₂).1 < zmodDist n α₁) :
    zmodDist n α₁ < zmodDist n (shearS1Inv n α₁ α₂).1 := by
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega)] at hs2
  rw [zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)] at hs2i
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega)] at hs1
  rw [zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hs2 hs2i hs1 ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hs2 hs2i hs1 ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1 ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1 <;> omega
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hs2 hs2i hs1 ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1 ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1 <;> (try omega) <;> split_ifs <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hs2 hs2i hs1 ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1 ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1 <;> (try omega) <;> split_ifs <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hs2 hs2i hs1 ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1 ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1 <;> omega

/-- Cross-constraint reverse: both S₂ closer ∧ S₁⁻¹ closer ⟹ S₁ strictly farther. -/
theorem cross_constraint_rev (n α₁ α₂ : ℕ) (hn : 3 ≤ n) (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (hs2 : zmodDist n (shearS2 n α₁ α₂).2 < zmodDist n α₂)
    (hs2i : zmodDist n (shearS2Inv n α₁ α₂).2 < zmodDist n α₂)
    (hs1i : zmodDist n (shearS1Inv n α₁ α₂).1 < zmodDist n α₁) :
    zmodDist n α₁ < zmodDist n (shearS1 n α₁ α₂).1 := by
  rw [zd_S2 n α₁ α₂ hα₁ hα₂ (by omega)] at hs2
  rw [zd_S2I n α₁ α₂ hα₁ hα₂ (by omega)] at hs2i
  rw [zd_S1I n α₁ α₂ hα₁ hα₂ (by omega)] at hs1i
  rw [zd_S1 n α₁ α₂ hα₁ hα₂ (by omega)]
  unfold zmodDist at hs2 hs2i hs1i ⊢
  by_cases h1 : 2 * α₁ < n <;> by_cases h2 : 2 * α₂ < n
  · simp only [double_mod_lo n α₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hs2 hs2i hs1i ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1i ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1i <;> (try omega) <;> split_ifs <;> omega
  · simp only [double_mod_lo n α₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_left (by omega : α₁ ≤ n - α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hs2 hs2i hs1i ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1i ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1i <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_lo n α₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_left (by omega : α₂ ≤ n - α₂)] at hs2 hs2i hs1i ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1i ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1i <;> omega
  · simp only [double_mod_hi n α₁ hα₁ h1, double_mod_hi n α₂ hα₂ h2,
      Nat.min_eq_right (by omega : n - α₁ ≤ α₁),
      Nat.min_eq_right (by omega : n - α₂ ≤ α₂)] at hs2 hs2i hs1i ⊢
    simp only [Nat.min_def] at hs2 hs2i hs1i ⊢
    split_ifs at hs2 <;> (try omega) <;> split_ifs at hs2i <;> (try omega) <;>
      split_ifs at hs1i <;> (try omega) <;> split_ifs <;> omega

/-- When both S₂ neighbors are strictly closer, the S₁ pair sum is at most `3√2/2`.

    Proof: S₁ preserves `α₂`, so ψ for S₁ neighbors depends only on the first coordinate.
    By `cross_constraint_fwd`/`_rev`, at most one of `{S₁, S₁⁻¹}` can be closer:
    - If S₁ closer: S₁⁻¹ farther → pair₂ = `√2 + √2/2 = 3√2/2`.
    - If S₁⁻¹ closer: S₁ farther → pair₂ = `√2/2 + √2 = 3√2/2`.
    - If neither closer: each ψ ≤ 1 → pair₂ ≤ 2 ≤ 3√2/2. -/
theorem pair_bound_when_both_S2_closer (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (h_s2 : zmodDist n (shearS2 n α₁ α₂).2 < zmodDist n α₂)
    (h_s2i : zmodDist n (shearS2Inv n α₁ α₂).2 < zmodDist n α₂) :
    psiWeight n α₁ α₂ (shearS1 n α₁ α₂).1 (shearS1 n α₁ α₂).2 +
    psiWeight n α₁ α₂ (shearS1Inv n α₁ α₂).1 (shearS1Inv n α₁ α₂).2
      ≤ 3 * √2 / 2 := by
  set s1 := shearS1 n α₁ α₂
  set s1i := shearS1Inv n α₁ α₂
  have hs1_snd : s1.2 = α₂ := shearS1_snd n α₁ α₂
  have hs1i_snd : s1i.2 = α₂ := shearS1Inv_snd n α₁ α₂
  have hgt_s1 : zmodDistGt n α₁ α₂ s1.1 s1.2 = decide (zmodDist n s1.1 < zmodDist n α₁) := by
    rw [hs1_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1.1
  have hgt_s1i : zmodDistGt n α₁ α₂ s1i.1 s1i.2 = decide (zmodDist n s1i.1 < zmodDist n α₁) := by
    rw [hs1i_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1i.1
  -- Also get the reverse direction zmodDistGt
  have hgt_s1_rev : zmodDistGt n s1.1 s1.2 α₁ α₂ = decide (zmodDist n α₁ < zmodDist n s1.1) := by
    rw [hs1_snd]; exact zmodDistGt_of_snd_eq n s1.1 α₂ α₁
  have hgt_s1i_rev : zmodDistGt n s1i.1 s1i.2 α₁ α₂ = decide (zmodDist n α₁ < zmodDist n s1i.1) := by
    rw [hs1i_snd]; exact zmodDistGt_of_snd_eq n s1i.1 α₂ α₁
  have hsq2 : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  -- Case split on S₁ closer
  by_cases h_s1_closer : zmodDist n s1.1 < zmodDist n α₁
  · -- S₁ closer: ψ(α, S₁α) = √2
    have hψ1 := psiWeight_eq_sqrt2_of_gt n α₁ α₂ s1.1 s1.2
      (by rw [hgt_s1]; simp [h_s1_closer])
    -- By cross_constraint_fwd: S₁⁻¹ farther
    have h_s1i_farther : zmodDist n α₁ < zmodDist n s1i.1 :=
      cross_constraint_fwd n α₁ α₂ hn hα₁ hα₂ h_s2 h_s2i h_s1_closer
    -- ψ(α, S₁⁻¹α) = √2/2 (α < S₁⁻¹α in the partial order)
    have hψ2 := psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1i.1 s1i.2
      (by rw [hgt_s1i]; simp [not_lt.mpr h_s1i_farther.le])
      (by rw [hgt_s1i_rev]; simp [h_s1i_farther])
    rw [hψ1, hψ2]; nlinarith [sq_nonneg (√2 - 1)]
  · by_cases h_s1i_closer : zmodDist n s1i.1 < zmodDist n α₁
    · -- S₁⁻¹ closer: ψ(α, S₁⁻¹α) = √2
      have hψ2 := psiWeight_eq_sqrt2_of_gt n α₁ α₂ s1i.1 s1i.2
        (by rw [hgt_s1i]; simp [h_s1i_closer])
      -- By cross_constraint_rev: S₁ farther
      have h_s1_farther : zmodDist n α₁ < zmodDist n s1.1 :=
        cross_constraint_rev n α₁ α₂ hn hα₁ hα₂ h_s2 h_s2i h_s1i_closer
      -- ψ(α, S₁α) = √2/2
      have hψ1 := psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s1.1 s1.2
        (by rw [hgt_s1]; simp [not_lt.mpr h_s1_farther.le])
        (by rw [hgt_s1_rev]; simp [h_s1_farther])
      rw [hψ1, hψ2]; nlinarith [sq_nonneg (√2 - 1)]
    · -- Neither closer: each ψ ≤ 1
      have hψ1 := psiWeight_le_one_of_not_gt n α₁ α₂ s1.1 s1.2
        (by rw [hgt_s1]; exact decide_eq_false h_s1_closer)
      have hψ2 := psiWeight_le_one_of_not_gt n α₁ α₂ s1i.1 s1i.2
        (by rw [hgt_s1i]; exact decide_eq_false h_s1i_closer)
      -- 2 ≤ 3√2/2 since √2 ≥ 4/3
      nlinarith [sq_nonneg (3 * √2 - 4)]

/-- Symmetric version: when both S₁ neighbors are strictly closer, the S₂ pair sum
    is at most `3√2/2`. Proved by the same cross-constraint argument with
    coordinates swapped. -/
theorem pair_bound_when_both_S1_closer (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n)
    (h_s1 : zmodDist n (shearS1 n α₁ α₂).1 < zmodDist n α₁)
    (h_s1i : zmodDist n (shearS1Inv n α₁ α₂).1 < zmodDist n α₁) :
    psiWeight n α₁ α₂ (shearS2 n α₁ α₂).1 (shearS2 n α₁ α₂).2 +
    psiWeight n α₁ α₂ (shearS2Inv n α₁ α₂).1 (shearS2Inv n α₁ α₂).2
      ≤ 3 * √2 / 2 := by
  set s2 := shearS2 n α₁ α₂
  set s2i := shearS2Inv n α₁ α₂
  have hs2_fst : s2.1 = α₁ := shearS2_fst n α₁ α₂
  have hs2i_fst : s2i.1 = α₁ := shearS2Inv_fst n α₁ α₂
  have hgt_s2 : zmodDistGt n α₁ α₂ s2.1 s2.2 = decide (zmodDist n s2.2 < zmodDist n α₂) := by
    rw [hs2_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2.2
  have hgt_s2i : zmodDistGt n α₁ α₂ s2i.1 s2i.2 = decide (zmodDist n s2i.2 < zmodDist n α₂) := by
    rw [hs2i_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2i.2
  have hgt_s2_rev : zmodDistGt n s2.1 s2.2 α₁ α₂ = decide (zmodDist n α₂ < zmodDist n s2.2) := by
    rw [hs2_fst]; exact zmodDistGt_of_fst_eq n α₁ s2.2 α₂
  have hgt_s2i_rev : zmodDistGt n s2i.1 s2i.2 α₁ α₂ = decide (zmodDist n α₂ < zmodDist n s2i.2) := by
    rw [hs2i_fst]; exact zmodDistGt_of_fst_eq n α₁ s2i.2 α₂
  have hsq2 : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  -- Case split on S₂ closer
  by_cases h_s2_closer : zmodDist n s2.2 < zmodDist n α₂
  · -- S₂ closer: ψ(α, S₂α) = √2
    have hψ1 := psiWeight_eq_sqrt2_of_gt n α₁ α₂ s2.1 s2.2
      (by rw [hgt_s2]; simp [h_s2_closer])
    -- By cross_constraint_fwd(α₂, α₁): S₂⁻¹ farther
    have h_s2i_farther : zmodDist n α₂ < zmodDist n s2i.2 :=
      cross_constraint_fwd n α₂ α₁ hn hα₂ hα₁ h_s1 h_s1i h_s2_closer
    have hψ2 := psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2i.1 s2i.2
      (by rw [hgt_s2i]; simp [not_lt.mpr h_s2i_farther.le])
      (by rw [hgt_s2i_rev]; simp [h_s2i_farther])
    rw [hψ1, hψ2]; nlinarith [sq_nonneg (√2 - 1)]
  · by_cases h_s2i_closer : zmodDist n s2i.2 < zmodDist n α₂
    · -- S₂⁻¹ closer: ψ(α, S₂⁻¹α) = √2
      have hψ2 := psiWeight_eq_sqrt2_of_gt n α₁ α₂ s2i.1 s2i.2
        (by rw [hgt_s2i]; simp [h_s2i_closer])
      -- By cross_constraint_rev(α₂, α₁): S₂ farther
      have h_s2_farther : zmodDist n α₂ < zmodDist n s2.2 :=
        cross_constraint_rev n α₂ α₁ hn hα₂ hα₁ h_s1 h_s1i h_s2i_closer
      have hψ1 := psiWeight_eq_sqrt2_div2_of_rev_gt n α₁ α₂ s2.1 s2.2
        (by rw [hgt_s2]; simp [not_lt.mpr h_s2_farther.le])
        (by rw [hgt_s2_rev]; simp [h_s2_farther])
      rw [hψ1, hψ2]; nlinarith [sq_nonneg (√2 - 1)]
    · -- Neither closer: each ψ ≤ 1
      have hψ1 := psiWeight_le_one_of_not_gt n α₁ α₂ s2.1 s2.2
        (by rw [hgt_s2]; exact decide_eq_false h_s2_closer)
      have hψ2 := psiWeight_le_one_of_not_gt n α₁ α₂ s2i.1 s2i.2
        (by rw [hgt_s2i]; exact decide_eq_false h_s2i_closer)
      nlinarith [sq_nonneg (3 * √2 - 4)]

/-- The pair squared sum bound for outside-diamond frequencies.
    For `α ≠ 0` with `zmodDist n α₁ + zmodDist n α₂ > n/2`:
    `pair₁² + pair₂² ≤ 25/2`, where `pairᵢ` are the ψ-weighted pair sums.

    Proof: case split on whether pair₁ or pair₂ equals `2√2`.
    - If pair₁ = 2√2: by `pair_bound_when_both_S2_closer`, pair₂ ≤ 3√2/2.
      Then (2√2)² + (3√2/2)² = 8 + 9/2 = 25/2. ✓
    - If pair₂ = 2√2: symmetric. ✓
    - If neither: each pair ≤ 1+√2 (gap in discrete values).
      Then 2(1+√2)² = 6+4√2 < 25/2. ✓ -/
theorem pair_sq_sum_le_outside (n α₁ α₂ : ℕ) (hn : 3 ≤ n)
    (hα₁ : α₁ < n) (hα₂ : α₂ < n) :
    let s1 := shearS1 n α₁ α₂
    let s1i := shearS1Inv n α₁ α₂
    let s2 := shearS2 n α₁ α₂
    let s2i := shearS2Inv n α₁ α₂
    (psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2) ^ 2 +
    (psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2) ^ 2
      ≤ 25 / 2 := by
  simp only
  -- Abbreviations
  set s2 := shearS2 n α₁ α₂
  set s2i := shearS2Inv n α₁ α₂
  set s1 := shearS1 n α₁ α₂
  set s1i := shearS1Inv n α₁ α₂
  set pair₁ := psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2
  set pair₂ := psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2
  -- Common facts about √2
  have hsq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < √2 := sqrt_pos.mpr (by norm_num)
  -- Each ψ is positive and ≤ √2
  have hψ_s2 := psiWeight_le_sqrt2 n α₁ α₂ s2.1 s2.2
  have hψ_s2i := psiWeight_le_sqrt2 n α₁ α₂ s2i.1 s2i.2
  have hψ_s1 := psiWeight_le_sqrt2 n α₁ α₂ s1.1 s1.2
  have hψ_s1i := psiWeight_le_sqrt2 n α₁ α₂ s1i.1 s1i.2
  have hψ_s2_pos := (psiWeight_pos n α₁ α₂ s2.1 s2.2).le
  have hψ_s2i_pos := (psiWeight_pos n α₁ α₂ s2i.1 s2i.2).le
  have hψ_s1_pos := (psiWeight_pos n α₁ α₂ s1.1 s1.2).le
  have hψ_s1i_pos := (psiWeight_pos n α₁ α₂ s1i.1 s1i.2).le
  -- S₂ preserves first coordinate, S₁ preserves second
  have hs2_fst : s2.1 = α₁ := shearS2_fst n α₁ α₂
  have hs2i_fst : s2i.1 = α₁ := shearS2Inv_fst n α₁ α₂
  have hs1_snd : s1.2 = α₂ := shearS1_snd n α₁ α₂
  have hs1i_snd : s1i.2 = α₂ := shearS1Inv_snd n α₁ α₂
  -- Rewrite zmodDistGt using coordinate preservation
  have hgt_s2 : zmodDistGt n α₁ α₂ s2.1 s2.2 = decide (zmodDist n s2.2 < zmodDist n α₂) := by
    rw [hs2_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2.2
  have hgt_s2i : zmodDistGt n α₁ α₂ s2i.1 s2i.2 = decide (zmodDist n s2i.2 < zmodDist n α₂) := by
    rw [hs2i_fst]; exact zmodDistGt_of_fst_eq n α₁ α₂ s2i.2
  have hgt_s1 : zmodDistGt n α₁ α₂ s1.1 s1.2 = decide (zmodDist n s1.1 < zmodDist n α₁) := by
    rw [hs1_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1.1
  have hgt_s1i : zmodDistGt n α₁ α₂ s1i.1 s1i.2 = decide (zmodDist n s1i.1 < zmodDist n α₁) := by
    rw [hs1i_snd]; exact zmodDistGt_of_snd_eq n α₁ α₂ s1i.1
  -- Case split: are BOTH S₂ neighbors strictly closer?
  by_cases h_both_s2 : zmodDist n s2.2 < zmodDist n α₂ ∧ zmodDist n s2i.2 < zmodDist n α₂
  · -- Case 1: pair₁ = 2√2. Key lemma gives pair₂ ≤ 3√2/2.
    obtain ⟨h_s2_lt, h_s2i_lt⟩ := h_both_s2
    have hpair₂_le := pair_bound_when_both_S2_closer n α₁ α₂ hn hα₁ hα₂ h_s2_lt h_s2i_lt
    -- pair₁ = √2 + √2 = 2√2
    have hpair₁_eq : pair₁ = 2 * √2 := by
      show psiWeight n α₁ α₂ s2.1 s2.2 + psiWeight n α₁ α₂ s2i.1 s2i.2 = 2 * √2
      rw [psiWeight_eq_sqrt2_of_gt n α₁ α₂ s2.1 s2.2 (by rw [hgt_s2]; simp [h_s2_lt]),
          psiWeight_eq_sqrt2_of_gt n α₁ α₂ s2i.1 s2i.2 (by rw [hgt_s2i]; simp [h_s2i_lt])]
      ring
    -- (2√2)² + pair₂² ≤ 8 + (3√2/2)² = 8 + 9/2 = 25/2
    rw [hpair₁_eq]
    nlinarith [sq_nonneg (pair₂ - 3 * √2 / 2)]
  · -- pair₁ < 2√2, so at least one S₂ ψ ≤ 1, giving pair₁ ≤ 1 + √2
    by_cases h_both_s1 : zmodDist n s1.1 < zmodDist n α₁ ∧ zmodDist n s1i.1 < zmodDist n α₁
    · -- Case 2: pair₂ = 2√2. Symmetric key lemma gives pair₁ ≤ 3√2/2.
      obtain ⟨h_s1_lt, h_s1i_lt⟩ := h_both_s1
      have hpair₁_le := pair_bound_when_both_S1_closer n α₁ α₂ hn hα₁ hα₂ h_s1_lt h_s1i_lt
      have hpair₂_eq : pair₂ = 2 * √2 := by
        show psiWeight n α₁ α₂ s1.1 s1.2 + psiWeight n α₁ α₂ s1i.1 s1i.2 = 2 * √2
        rw [psiWeight_eq_sqrt2_of_gt n α₁ α₂ s1.1 s1.2 (by rw [hgt_s1]; simp [h_s1_lt]),
            psiWeight_eq_sqrt2_of_gt n α₁ α₂ s1i.1 s1i.2 (by rw [hgt_s1i]; simp [h_s1i_lt])]
        ring
      rw [hpair₂_eq]
      nlinarith [sq_nonneg (pair₁ - 3 * √2 / 2)]
    · -- Case 3: neither pair is 2√2. Each pair ≤ 1 + √2.
      -- At least one S₂ ψ ≤ 1
      have hpair₁_le : pair₁ ≤ 1 + √2 := by
        rcases not_and_or.mp h_both_s2 with h | h
        · -- First S₂ ψ ≤ 1 (not closer)
          have := psiWeight_le_one_of_not_gt n α₁ α₂ s2.1 s2.2
            (by rw [hgt_s2]; exact decide_eq_false h)
          linarith
        · -- Second S₂ ψ ≤ 1 (not closer)
          have := psiWeight_le_one_of_not_gt n α₁ α₂ s2i.1 s2i.2
            (by rw [hgt_s2i]; exact decide_eq_false h)
          linarith
      -- At least one S₁ ψ ≤ 1
      have hpair₂_le : pair₂ ≤ 1 + √2 := by
        rcases not_and_or.mp h_both_s1 with h | h
        · have := psiWeight_le_one_of_not_gt n α₁ α₂ s1.1 s1.2
            (by rw [hgt_s1]; exact decide_eq_false h)
          linarith
        · have := psiWeight_le_one_of_not_gt n α₁ α₂ s1i.1 s1i.2
            (by rw [hgt_s1i]; exact decide_eq_false h)
          linarith
      -- 2(1+√2)² = 6+4√2 < 25/2
      nlinarith [sq_nonneg (pair₁ - (1 + √2)), sq_nonneg (pair₂ - (1 + √2)),
                 sq_nonneg (√2 * 8 - 13)]


end


