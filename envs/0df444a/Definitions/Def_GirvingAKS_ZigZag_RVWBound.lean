-- Prove2me | Definitions.Def_GirvingAKS_ZigZag_RVWBound
-- name    : GirvingAKS_ZigZag_RVWBound
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:33:58.119943+00:00
-- url     : https://prove2.me/theorems/83c64b3d-00a5-4b3f-bad7-0a5012f7db34
-- title:
--   AKS sorting networks (Seiferas port) — Abstract RVW Operator Norm Bound
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/ZigZag/RVWBound.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** The pure operator-theory core of the Reingold–Vadhan–Wigderson spectral composition theorem. Given operators `W = B · Σ · B` on a Hilbert space with projections `Q ≥ P`, the bound `‖W - P‖ ≤ rvwBound(λ₁, λ₂)` follows from the contraction `∀ x ∈ ker Q, ‖Bx‖ ≤ λ₂·‖x‖` (B contracts the tilde subspace) and the spectral gap `‖QΣQ - P‖ ≤ λ₁`.
--
--   **Important:** The tilde contraction must be stated as a bound on `ker Q` (not as `‖B(I-Q)‖ ≤ λ₂`). The operator norm `‖B(I-Q)‖ ≤ λ₂` only gives `‖B(I-Q)x‖ ≤ λ₂·‖x‖` (full vector norm), not `‖B(I-Q)x‖ ≤ λ₂·‖(I-Q)x‖` (projected vector norm). The RVW proof requires the latter (Claim 4.1).
--
--   This file has NO graph imports — it works in abstract inner product spaces.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/ZigZag/RVWBound.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_ZigZag_RVWInequality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/ZigZag/RVWBound.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Abstract RVW Operator Norm Bound

  The pure operator-theory core of the Reingold–Vadhan–Wigderson spectral
  composition theorem. Given operators `W = B · Σ · B` on a Hilbert space
  with projections `Q ≥ P`, the bound `‖W - P‖ ≤ rvwBound(λ₁, λ₂)` follows
  from the contraction `∀ x ∈ ker Q, ‖Bx‖ ≤ λ₂·‖x‖` (B contracts the tilde
  subspace) and the spectral gap `‖QΣQ - P‖ ≤ λ₁`.

  **Important:** The tilde contraction must be stated as a bound on `ker Q`
  (not as `‖B(I-Q)‖ ≤ λ₂`). The operator norm `‖B(I-Q)‖ ≤ λ₂` only gives
  `‖B(I-Q)x‖ ≤ λ₂·‖x‖` (full vector norm), not `‖B(I-Q)x‖ ≤ λ₂·‖(I-Q)x‖`
  (projected vector norm). The RVW proof requires the latter (Claim 4.1).

  This file has NO graph imports — it works in abstract inner product spaces.
-/


section


open BigOperators


/-! **The RVW Bound Function** -/

/-- The precise RVW bound on the spectral gap of a zig-zag product.

    f(λ₁, λ₂) = (1 − λ₂²) · λ₁ / 2 + √((1 − λ₂²)² · λ₁² / 4 + λ₂²)

    This equals the largest eigenvalue of the 2×2 matrix
    `[[(1 - λ₂²)·λ₁, λ₂], [λ₂, 0]]`.

    It is tight (achieved by tensor products of complete graphs).
    The weaker additive bound `λ₁ + λ₂ + λ₂²` does NOT suffice for
    the iteration to converge with any finite base degree D. -/
noncomputable def rvwBound (lam₁ lam₂ : ℝ) : ℝ :=
  (1 - lam₂ ^ 2) * lam₁ / 2 + Real.sqrt ((1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2)


/-! **Monotonicity** -/

/-- The core inequality: when a ≤ 1, this term is nonnegative.
    This is the final reduction after polynomial expansion. -/
private lemma rvwBound_core_ineq {a b₁ b₂ : ℝ}
    (ha_pos : 0 < a) (ha1 : a ≤ 1) :
    let c₁ := 1 - b₁ ^ 2
    let c₂ := 1 - b₂ ^ 2
    let Δ := b₂ ^ 2 - b₁ ^ 2
    1 - (c₂ + c₁) * a ^ 2 / 4 - a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) - Δ * a ^ 2 / 4 ≥ 0 := by
  intro c₁ c₂ Δ
  -- Rearrange: the expression simplifies (using c₂+c₁+Δ = 2-2b₁²) to
  -- 1 - a²/2 + b₁²·a²/2 - a·S where S = √(c₁²·a²/4 + b₁²)
  set S := Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2)
  -- Algebraic simplification: combine all non-sqrt terms
  suffices h : 1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2 - a * S ≥ 0 by
    show 1 - (c₂ + c₁) * a ^ 2 / 4 - a * S - Δ * a ^ 2 / 4 ≥ 0; linarith
  -- Show LHS ≥ 0 by proving: 1 - a²/2 + b₁²·a²/2 ≥ a·S
  have hS_nonneg : 0 ≤ S := Real.sqrt_nonneg _
  have hLHS : 0 ≤ 1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2 := by nlinarith [sq_nonneg a, sq_nonneg b₁]

  suffices h : 1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2 ≥ a * S by linarith

  -- Square both sides (both nonneg)
  suffices h_sq : (1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2) ^ 2 ≥ (a * S) ^ 2 by
    have sqrt_ineq : Real.sqrt ((1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2) ^ 2) ≥
                     Real.sqrt ((a * S) ^ 2) := Real.sqrt_le_sqrt h_sq
    simp only [Real.sqrt_sq hLHS, Real.sqrt_sq (by nlinarith [hS_nonneg] : 0 ≤ a * S)] at sqrt_ineq
    exact sqrt_ineq

  -- Expand (a * S)² = a² * S² = a² * (c₁²·a²/4 + b₁²)
  have hS_sq : S ^ 2 = c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 := by
    have harg : 0 ≤ c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 := by
      nlinarith [sq_nonneg c₁, sq_nonneg a, sq_nonneg b₁]
    rw [Real.sq_sqrt harg]

  calc (1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2) ^ 2
      ≥ a ^ 2 * (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) := by
        -- After expansion using c₁ = 1 - b₁², this reduces to: 1 ≥ a²
        show (1 - a ^ 2 / 2 + b₁ ^ 2 * a ^ 2 / 2) ^ 2 ≥
          a ^ 2 * ((1 - b₁ ^ 2) ^ 2 * a ^ 2 / 4 + b₁ ^ 2)
        nlinarith [sq_nonneg a, sq_nonneg b₁]
    _ = a ^ 2 * S ^ 2 := by rw [hS_sq]
    _ = (a * S) ^ 2 := by ring

/-- The key polynomial identity after expanding the squared inequality.
    This is the core algebraic fact: when a ≤ 1, the polynomial inequality holds. -/
private lemma rvwBound_poly_ineq {a b₁ b₂ : ℝ}
    (ha_pos : 0 < a) (ha1 : a ≤ 1) (hb₁ : 0 ≤ b₁) (hbb : b₁ < b₂) :
    let c₁ := 1 - b₁ ^ 2
    let c₂ := 1 - b₂ ^ 2
    let Δ := b₂ ^ 2 - b₁ ^ 2
    c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2 ≥
    c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 + Δ * a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) +
    Δ ^ 2 * a ^ 2 / 4 := by
  intro c₁ c₂ Δ

  -- Factor LHS - RHS = Δ · (bracket from rvwBound_core_ineq) ≥ 0
  -- using Δ = c₁ - c₂ (i.e., b₂²-b₁² = (1-b₁²)-(1-b₂²))
  suffices h : c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2 -
              (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 + Δ * a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) +
               Δ ^ 2 * a ^ 2 / 4) ≥ 0 by linarith
  -- After algebraic manipulation: difference = Δ · (1 - (c₂+c₁)a²/4 - a·S - Δ·a²/4)
  have hfactor : c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2 -
      (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 + Δ * a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) +
       Δ ^ 2 * a ^ 2 / 4) =
      Δ * (1 - (c₂ + c₁) * a ^ 2 / 4 - a * Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2) -
       Δ * a ^ 2 / 4) := by
    have : Δ = c₁ - c₂ := by ring
    nlinarith [this]
  rw [hfactor]
  have hΔ_pos : 0 < Δ := by nlinarith [sq_nonneg b₁, sq_nonneg b₂]
  have h_bracket := rvwBound_core_ineq (b₁ := b₁) (b₂ := b₂) ha_pos ha1
  nlinarith [hΔ_pos, h_bracket]

/-- Core polynomial inequality for RVW bound monotonicity.
    When a ≤ 1 and b₁ ≤ b₂ ≤ 1, the square root increase dominates
    the linear coefficient decrease. -/
private lemma rvwBound_sqrt_ineq {a b₁ b₂ : ℝ}
    (ha_pos : 0 < a) (ha1 : a ≤ 1) (hb₁ : 0 ≤ b₁) (hb₂ : b₂ ≤ 1) (hbb : b₁ < b₂) :
    Real.sqrt ((1 - b₂ ^ 2) ^ 2 * a ^ 2 / 4 + b₂ ^ 2) -
    Real.sqrt ((1 - b₁ ^ 2) ^ 2 * a ^ 2 / 4 + b₁ ^ 2) ≥
    (b₂ ^ 2 - b₁ ^ 2) * a / 2 := by
  set c₁ := 1 - b₁ ^ 2
  set c₂ := 1 - b₂ ^ 2
  set S₁ := Real.sqrt (c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2)
  set S₂ := Real.sqrt (c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2)
  set Δ := b₂ ^ 2 - b₁ ^ 2

  have hc₁ : 0 ≤ c₁ := by nlinarith [sq_nonneg b₁]
  have hc₂ : 0 ≤ c₂ := by nlinarith [sq_nonneg b₂]
  have hS₁_sq_arg : 0 ≤ c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 := by nlinarith [sq_nonneg c₁, sq_nonneg a, sq_nonneg b₁]
  have hS₂_sq_arg : 0 ≤ c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2 := by nlinarith [sq_nonneg c₂, sq_nonneg a, sq_nonneg b₂]
  have hS₁_pos : 0 ≤ S₁ := Real.sqrt_nonneg _
  have hS₂_pos : 0 ≤ S₂ := Real.sqrt_nonneg _

  -- Prove: S₂ ≥ S₁ + Δ·a/2 by squaring both sides
  have hΔ_pos : 0 < Δ := by nlinarith [sq_nonneg b₁, sq_nonneg b₂]
  have hlhs : 0 ≤ S₁ + Δ * a / 2 := by nlinarith [hS₁_pos, hΔ_pos, ha_pos.le]

  suffices h : S₂ ^ 2 ≥ (S₁ + Δ * a / 2) ^ 2 by
    -- Use sqrt monotonicity
    have sq_ineq : Real.sqrt (S₂ ^ 2) ≥ Real.sqrt ((S₁ + Δ * a / 2) ^ 2) := Real.sqrt_le_sqrt h
    simp only [Real.sqrt_sq hS₂_pos, Real.sqrt_sq hlhs] at sq_ineq
    linarith

  -- Expand and apply polynomial inequality
  calc S₂ ^ 2
      = c₂ ^ 2 * a ^ 2 / 4 + b₂ ^ 2 := by rw [Real.sq_sqrt hS₂_sq_arg]
    _ ≥ c₁ ^ 2 * a ^ 2 / 4 + b₁ ^ 2 + Δ * a * S₁ + Δ ^ 2 * a ^ 2 / 4 :=
        rvwBound_poly_ineq ha_pos ha1 hb₁ hbb
    _ = S₁ ^ 2 + Δ * a * S₁ + Δ ^ 2 * a ^ 2 / 4 := by
        rw [Real.sq_sqrt hS₁_sq_arg]
    _ = (S₁ + Δ * a / 2) ^ 2 := by ring

/-- `rvwBound` is monotone in its first argument (for nonneg arguments with b ≤ 1).
    The constraint b ≤ 1 is natural since b represents a spectral gap bound. -/
theorem rvwBound_mono_left {a₁ a₂ b : ℝ}
    (ha₁ : 0 ≤ a₁) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hab : a₁ ≤ a₂) :
    rvwBound a₁ b ≤ rvwBound a₂ b := by
  unfold rvwBound
  have ha₂ : 0 ≤ a₂ := le_trans ha₁ hab
  have hsqrt : Real.sqrt ((1 - b ^ 2) ^ 2 * a₁ ^ 2 / 4 + b ^ 2) ≤
               Real.sqrt ((1 - b ^ 2) ^ 2 * a₂ ^ 2 / 4 + b ^ 2) := by
    gcongr
  have hc : 0 ≤ 1 - b ^ 2 := by nlinarith [sq_nonneg b]
  linarith [mul_le_mul_of_nonneg_left hab hc]

/-- `rvwBound` is monotone in its second argument (for nonneg arguments
    with both a, b ≤ 1). The constraints are natural since both represent
    spectral gap bounds. -/
theorem rvwBound_mono_right {a b₁ b₂ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb₁ : 0 ≤ b₁) (hb₂ : b₂ ≤ 1) (hbb : b₁ ≤ b₂) :
    rvwBound a b₁ ≤ rvwBound a b₂ := by
  unfold rvwBound
  by_cases ha_zero : a = 0
  · -- When a = 0, rvwBound 0 b = √(b²) = b
    subst ha_zero
    norm_num
    gcongr
  · -- Main case: 0 < a ≤ 1, 0 ≤ b₁ ≤ b₂ ≤ 1
    have ha_pos : 0 < a := ha.lt_of_ne (Ne.symm ha_zero)
    by_cases hbb_eq : b₁ = b₂
    · simp [hbb_eq]
    · have hbb_strict : b₁ < b₂ := lt_of_le_of_ne hbb hbb_eq
      have key := rvwBound_sqrt_ineq ha_pos ha1 hb₁ hb₂ hbb_strict
      linarith


/-! **Abstract Operator Norm Bound** -/

/-- Hat/tilde decomposition: x = Qx + (I-Q)x with orthogonality. -/
private lemma hat_tilde_orthogonal {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ_proj : Q * Q = Q) (hQ_sa : IsSelfAdjoint Q) (x : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ (Q x) ((1 - Q) x) = 0 := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right]
  -- ⟨Qx, x⟩ = ⟨Q²x, x⟩ = ⟨Qx, Qx⟩ by Q²=Q and self-adjointness
  have : @inner ℝ _ _ (Q x) x = @inner ℝ _ _ (Q x) (Q x) := by
    conv_lhs => rw [show Q x = (Q * Q) x from by rw [hQ_proj]]
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hQ_sa) (Q x) x
  linarith

/-- The squared norm decomposes: ‖x‖² = ‖Q x‖² + ‖(I-Q) x‖². -/
private lemma hat_tilde_norm_sq {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ_proj : Q * Q = Q) (hQ_sa : IsSelfAdjoint Q) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖(1 - Q) x‖ ^ 2 := by
  have decomp : x = Q x + (1 - Q) x := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]; abel
  conv_lhs => rw [decomp]
  rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (hat_tilde_orthogonal Q hQ_proj hQ_sa x), ← sq, ← sq]

/-- Helper: P annihilates (I-Q)x since PQ = P implies P(I-Q) = 0. -/
private lemma meanProj_annihilates_tilde {n : ℕ}
    (P Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hPQ : P * Q = P) (x : EuclideanSpace ℝ (Fin n)) :
    P ((1 - Q) x) = 0 := by
  show (P * (1 - Q)) x = 0; rw [mul_sub, mul_one, hPQ, sub_self, ContinuousLinearMap.zero_apply]

/-- Helper: Bound the hat block term |⟨(QΣQ - P)x̂, x̂⟩| ≤ λ₁·‖x̂‖². -/
private lemma hat_block_bound {n : ℕ}
    (Sig Q P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (lam₁ : ℝ) (h_hat : ‖Q * Sig * Q - P‖ ≤ lam₁)
    (x_hat : EuclideanSpace ℝ (Fin n)) :
    |@inner ℝ _ _ ((Q * Sig * Q - P) x_hat) x_hat| ≤ lam₁ * ‖x_hat‖ ^ 2 := by
  calc |@inner ℝ _ _ ((Q * Sig * Q - P) x_hat) x_hat|
      ≤ ‖(Q * Sig * Q - P) x_hat‖ * ‖x_hat‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖Q * Sig * Q - P‖ * ‖x_hat‖ * ‖x_hat‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ lam₁ * ‖x_hat‖ * ‖x_hat‖ := by gcongr
    _ = lam₁ * ‖x_hat‖ ^ 2 := by ring

/-- Helper: Self-adjoint involution has norm ≤ 1. -/
private lemma involution_norm_le_one {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig) :
    ‖Sig‖ ≤ 1 := by
  -- For self-adjoint Σ: ‖Σ‖² = ‖Σ²‖ = ‖1‖ = 1 by C*-identity
  have h_sq : ‖Sig‖ ^ 2 = ‖Sig * Sig‖ :=
    (@IsSelfAdjoint.norm_mul_self _ _ ContinuousLinearMap.instStarRingId _ _ hSig_sa).symm
  rw [hSig_inv] at h_sq
  -- ‖(1 : CLM)‖ = 1 when Nontrivial, = 0 when trivial
  by_cases hn : Nontrivial (EuclideanSpace ℝ (Fin n))
  · have h1 : ‖Sig‖ ^ 2 = 1 := by rw [h_sq]; exact norm_one
    have h2 : ‖Sig‖ * ‖Sig‖ = 1 := by simpa [sq] using h1
    have : (‖Sig‖ - 1) * (‖Sig‖ + 1) = 0 := by nlinarith
    rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
    · linarith
    · linarith [norm_nonneg Sig]
  · -- Trivial space: all operators are zero, so ‖Sig‖ = 0 ≤ 1
    rw [not_nontrivial_iff_subsingleton] at hn
    have : Sig = 0 := Subsingleton.eq_zero Sig
    simp [this]

/-- Helper: Bound ‖Bx̃‖ ≤ λ₂·‖x̃‖ using ‖B(I-Q)‖ ≤ λ₂. -/
private lemma tilde_contraction_bound {n : ℕ}
    (B Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (lam₂ : ℝ) (h_tilde : ∀ x, Q x = 0 → ‖B x‖ ≤ lam₂ * ‖x‖)
    (hQ_proj : Q * Q = Q)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖B ((1 - Q) x)‖ ≤ lam₂ * ‖(1 - Q) x‖ := by
  -- (1 - Q) x is in ker(Q) since Q((1-Q)x) = (Q - Q²)x = 0
  have hker : Q ((1 - Q) x) = 0 := by
    change (Q * (1 - Q)) x = 0
    rw [mul_sub, mul_one, hQ_proj, sub_self, ContinuousLinearMap.zero_apply]
  exact h_tilde ((1 - Q) x) hker

/-- For a self-adjoint involution Σ, `|⟨Σv, v⟩| ≤ ‖v‖²`. -/
private lemma reflection_rayleigh_le_norm_sq {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (v : EuclideanSpace ℝ (Fin n)) :
    |@inner ℝ _ _ (Sig v) v| ≤ ‖v‖ ^ 2 := by
  calc |@inner ℝ _ _ (Sig v) v|
      ≤ ‖Sig v‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖Sig‖ * ‖v‖ * ‖v‖ := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖v‖ * ‖v‖ := by gcongr; exact involution_norm_le_one Sig hSig_inv hSig_sa
    _ = ‖v‖ ^ 2 := by ring

/-- Bilinear expansion of `⟨Σ(u+w), u+w⟩` using `Σ* = Σ`. -/
private lemma reflection_bilinear_expand {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSig_sa : IsSelfAdjoint Sig)
    (u w : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ (Sig (u + w)) (u + w) =
      @inner ℝ _ _ (Sig u) u + 2 * @inner ℝ _ _ (Sig u) w +
      @inner ℝ _ _ (Sig w) w := by
  rw [map_add, inner_add_left, inner_add_right, inner_add_right]
  -- ⟨Σw, u⟩ = ⟨w, Σu⟩ = ⟨Σu, w⟩ by self-adjointness (real space)
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hSig_sa
  have h_symm : @inner ℝ _ _ (Sig w) u = @inner ℝ _ _ (Sig u) w :=
    (hSig_sa w u).trans (real_inner_comm _ _)
  rw [h_symm]; ring

/-- Helper: `Σ²v = v` from `Σ * Σ = 1`. -/
private lemma involution_apply_twice {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSig_inv : Sig * Sig = 1)
    (v : EuclideanSpace ℝ (Fin n)) : Sig (Sig v) = v := by
  have := ContinuousLinearMap.ext_iff.mp hSig_inv v
  simpa using this

/-- Helper: `‖Σv‖ = ‖v‖` from `Σ² = I` and `Σ* = Σ`. -/
private lemma involution_norm_eq {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (v : EuclideanSpace ℝ (Fin n)) : ‖Sig v‖ = ‖v‖ := by
  have h := involution_norm_le_one Sig hSig_inv hSig_sa
  have h1 : ‖Sig v‖ ≤ ‖v‖ := by
    calc ‖Sig v‖ ≤ ‖Sig‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖v‖ := by gcongr
      _ = ‖v‖ := one_mul _
  have h2 : ‖v‖ ≤ ‖Sig v‖ := by
    calc ‖v‖ = ‖Sig (Sig v)‖ := by rw [involution_apply_twice Sig hSig_inv]
      _ ≤ ‖Sig‖ * ‖Sig v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖Sig v‖ := by gcongr
      _ = ‖Sig v‖ := one_mul _
  exact le_antisymm h1 h2

/-- Cauchy-Schwarz via `(I ± Σ)`: for orthogonal `u`, `w` and self-adjoint
    involution `Σ`, with `q = ⟨Σu, w⟩`, `p = ⟨Σu, u⟩`, `r = ⟨Σw, w⟩`:
    - `sign = 1`: `q² ≤ (‖u‖²+p)(‖w‖²+r)` via `(I+Σ)`
    - `sign = -1`: `q² ≤ (‖u‖²-p)(‖w‖²-r)` via `(I-Σ)` -/
private lemma reflection_cs {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (u w : EuclideanSpace ℝ (Fin n)) (h_orth : @inner ℝ _ _ u w = 0)
    (sign : ℝ) (hsign : sign ^ 2 = 1) :
    (@inner ℝ _ _ (Sig u) w) ^ 2 ≤
      (‖u‖ ^ 2 + sign * @inner ℝ _ _ (Sig u) u) *
      (‖w‖ ^ 2 + sign * @inner ℝ _ _ (Sig w) w) := by
  set q := @inner ℝ _ _ (Sig u) w
  set p := @inner ℝ _ _ (Sig u) u
  set r := @inner ℝ _ _ (Sig w) w
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hSig_sa
  have hSS := involution_apply_twice Sig hSig_inv
  have h_uSw : @inner ℝ _ _ u (Sig w) = q := (hSig_sa u w).symm
  have h_sig_orth : @inner ℝ _ _ (Sig u) (Sig w) = 0 := by
    calc @inner ℝ _ _ (Sig u) (Sig w)
        = @inner ℝ _ _ u (Sig (Sig w)) := hSig_sa u (Sig w)
      _ = @inner ℝ _ _ u w := by rw [hSS]
      _ = 0 := h_orth
  -- v ↦ u + sign • Σu, similarly for w
  set U := u + sign • Sig u; set W := w + sign • Sig w
  have h_inner : @inner ℝ _ _ U W = 2 * sign * q := by
    simp only [U, W, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      conj_trivial, h_orth, h_uSw, h_sig_orth]; ring
  have h_norm_u : ‖U‖ ^ 2 = 2 * (‖u‖ ^ 2 + sign * p) := by
    simp only [U, norm_add_sq_real, inner_smul_right]
    rw [norm_smul, Real.norm_eq_abs, show @inner ℝ _ _ u (Sig u) = p from real_inner_comm _ _,
        involution_norm_eq Sig hSig_inv
          (by rwa [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]) u]
    nlinarith [sq_abs sign]
  have h_norm_w : ‖W‖ ^ 2 = 2 * (‖w‖ ^ 2 + sign * r) := by
    simp only [W, norm_add_sq_real, inner_smul_right]
    rw [norm_smul, Real.norm_eq_abs, show @inner ℝ _ _ w (Sig w) = r from real_inner_comm _ _,
        involution_norm_eq Sig hSig_inv
          (by rwa [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]) w]
    nlinarith [sq_abs sign]
  -- Cauchy-Schwarz: |⟨U, W⟩|² ≤ ‖U‖² · ‖W‖²
  have hCS := abs_real_inner_le_norm U W
  rw [h_inner] at hCS
  set M := ‖U‖ * ‖W‖ with hM_def
  have hCS_le := abs_le.mp hCS
  have h_prod_nonneg : 0 ≤ M ^ 2 - (2 * sign * q) ^ 2 := by
    have : 0 ≤ (M - 2 * sign * q) * (M + 2 * sign * q) :=
      mul_nonneg (by linarith [hCS_le.2]) (by linarith [hCS_le.1])
    nlinarith
  have hM_sq : M ^ 2 = 2 * (‖u‖ ^ 2 + sign * p) * (2 * (‖w‖ ^ 2 + sign * r)) := by
    rw [hM_def, mul_pow, h_norm_u, h_norm_w]
  rw [hM_sq] at h_prod_nonneg
  nlinarith [hsign]

/-! **Quadratic Root Reduction** -/

/-- `rvwBound(λ₁, λ₂)` satisfies the quadratic equation
    `x² = (1 - λ₂²) · λ₁ · x + λ₂²`.
    This characterizes it as the positive root of `t² - ct - d² = 0`
    where `c = (1-λ₂²)λ₁` and `d = λ₂`. -/
lemma rvwBound_quadratic_eq (lam₁ lam₂ : ℝ) :
    (rvwBound lam₁ lam₂) ^ 2 = (1 - lam₂ ^ 2) * lam₁ * rvwBound lam₁ lam₂ + lam₂ ^ 2 := by
  unfold rvwBound
  set S := Real.sqrt ((1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2)
  have hD : 0 ≤ (1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2 := by positivity
  have hS_sq : S ^ 2 = (1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2 := Real.sq_sqrt hD
  -- LHS = ((1-λ₂²)λ₁/2 + S)² = (1-λ₂²)²λ₁²/4 + (1-λ₂²)λ₁·S + S²
  -- RHS = (1-λ₂²)λ₁·((1-λ₂²)λ₁/2 + S) + λ₂² = (1-λ₂²)²λ₁²/2 + (1-λ₂²)λ₁·S + λ₂²
  -- Difference: LHS - RHS = (1-λ₂²)²λ₁²/4 + S² - (1-λ₂²)²λ₁²/2 - λ₂²
  --           = S² - (1-λ₂²)²λ₁²/4 - λ₂² = 0 (from hS_sq)
  nlinarith [hS_sq]

/-- `rvwBound` is nonneg when `0 ≤ λ₁` and `0 ≤ λ₂ ≤ 1`. -/
lemma rvwBound_nonneg (lam₁ lam₂ : ℝ) (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂)
    (hlam₂_le : lam₂ ≤ 1) :
    0 ≤ rvwBound lam₁ lam₂ := by
  unfold rvwBound
  have h1 : 0 ≤ (1 - lam₂ ^ 2) * lam₁ / 2 := by
    apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 2)
    exact mul_nonneg (by nlinarith [sq_nonneg lam₂]) hlam₁
  exact add_nonneg h1 (Real.sqrt_nonneg _)

/-- Quadratic root bound: if `x ≥ 0` and `x² ≤ cx + d²` with `c, d ≥ 0`,
    then `x ≤ (c + √(c² + 4d²))/2`.
    This is because `(c + √(c²+4d²))/2` is the positive root of `t² - ct - d² = 0`,
    and the polynomial is ≤ 0 on `[0, positive root]`. -/
lemma quadratic_root_upper_bound {x c d : ℝ}
    (hx : 0 ≤ x)
    (h : x ^ 2 ≤ c * x + d ^ 2) :
    x ≤ (c + Real.sqrt (c ^ 2 + 4 * d ^ 2)) / 2 := by
  set S := Real.sqrt (c ^ 2 + 4 * d ^ 2)
  set r := (c + S) / 2
  set r' := (c - S) / 2
  have hD : 0 ≤ c ^ 2 + 4 * d ^ 2 := by positivity
  have hS_sq : S ^ 2 = c ^ 2 + 4 * d ^ 2 := Real.sq_sqrt hD
  have hS_nonneg : 0 ≤ S := Real.sqrt_nonneg _
  have hS_ge_abs_c : |c| ≤ S := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith [sq_nonneg d])
  have hS_ge_c : c ≤ S := le_trans (le_abs_self c) hS_ge_abs_c
  have hr'_nonpos : r' ≤ 0 := by simp only [r']; linarith
  -- Factor: (x - r)(x - r') = x² - cx - d²
  have h_factor : (x - r) * (x - r') = x ^ 2 - c * x - d ^ 2 := by
    simp only [r, r']; nlinarith [hS_sq]
  have h_neg : (x - r) * (x - r') ≤ 0 := by rw [h_factor]; linarith
  -- Since x - r' > 0, we need x - r ≤ 0
  by_cases hxr' : x = r'
  · -- x = r' ≤ 0, but x ≥ 0, so x = 0 ≤ r
    have hx0 : x = 0 := le_antisymm (by rw [hxr']; exact hr'_nonpos) hx
    have hr_nonneg : 0 ≤ r := div_nonneg (by linarith [hS_ge_abs_c, neg_abs_le c]) (by norm_num)
    linarith
  · have h_pos : 0 < x - r' := by
      rcases (lt_or_gt_of_ne hxr') with h | h
      · -- x < r' ≤ 0, contradicts x ≥ 0
        linarith
      · linarith
    -- (x - r) * (x - r') ≤ 0 and (x - r') > 0, so (x - r) ≤ 0
    have : x - r ≤ 0 := by
      by_contra h_contra
      push_neg at h_contra
      have : 0 < (x - r) * (x - r') := mul_pos h_contra h_pos
      linarith
    linarith

private lemma rvw_exact_bound
    (a b c p q r : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hcb : c ≤ b)
    (h_unit : a ^ 2 + b ^ 2 = 1)
    (h_refl_u : |p| ≤ a ^ 2)
    (h_refl_w : |r| ≤ c ^ 2)
    (h_cs_plus : q ^ 2 ≤ (a ^ 2 + p) * (c ^ 2 + r))
    (h_cs_minus : q ^ 2 ≤ (a ^ 2 - p) * (c ^ 2 - r)) :
    |p + 2 * q + r| ≤ rvwBound (|p| / a ^ 2) (c / b) := by
  -- Use quadratic_root_upper_bound: from X² ≤ C·|X| + D², deduce |X| ≤ (C+√(C²+4D²))/2
  set μ₁ := |p| / a ^ 2
  set μ₂ := c / b
  have hμ₁ : 0 ≤ μ₁ := div_nonneg (abs_nonneg _) (by positivity)
  have hμ₂ : 0 ≤ μ₂ := div_nonneg hc hb.le
  have hμ₂_le : μ₂ ≤ 1 := by rw [div_le_one hb]; exact hcb
  have h_quad := rvw_quadratic_ineq a b c p q r ha hb hc hcb
    h_unit h_refl_u h_refl_w h_cs_plus h_cs_minus
  -- quadratic_root_upper_bound gives |X| ≤ (C + √(C² + 4D²))/2
  set C := (1 - μ₂ ^ 2) * μ₁
  have h_quad' : |p + 2 * q + r| ^ 2 ≤ C * |p + 2 * q + r| + μ₂ ^ 2 := by
    rwa [sq_abs]
  have h_bound := quadratic_root_upper_bound (abs_nonneg (p + 2 * q + r)) h_quad'
  -- Show rvwBound μ₁ μ₂ = (C + √(C² + 4·μ₂²))/2
  suffices h_eq : rvwBound μ₁ μ₂ = (C + Real.sqrt (C ^ 2 + 4 * μ₂ ^ 2)) / 2 by
    rw [h_eq]; exact h_bound
  unfold rvwBound
  -- Need: C/2 + √(C²/4 + μ₂²) = (C + √(C²+4μ₂²))/2
  -- Equiv: √(C²/4 + μ₂²) = √(C²+4μ₂²)/2
  have h_arith : C ^ 2 / 4 + μ₂ ^ 2 = (C ^ 2 + 4 * μ₂ ^ 2) / 4 := by ring
  have hC_def : (1 - μ₂ ^ 2) ^ 2 * μ₁ ^ 2 / 4 + μ₂ ^ 2 = C ^ 2 / 4 + μ₂ ^ 2 := by
    simp only [C]; ring
  rw [hC_def]
  rw [h_arith, Real.sqrt_div (by positivity : (0:ℝ) ≤ C ^ 2 + 4 * μ₂ ^ 2)]
  rw [show (4:ℝ) = 2 ^ 2 from by norm_num,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  ring

private lemma rvw_optimization_bound
    (a b c p q r lam₁ lam₂ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂)
    (hlam₁_le : lam₁ ≤ 1) (hlam₂_le : lam₂ ≤ 1)
    (h_unit : a ^ 2 + b ^ 2 = 1)
    (h_tilde : c ≤ lam₂ * b)
    (h_hat : |p| ≤ lam₁ * a ^ 2)
    (h_refl_u : |p| ≤ a ^ 2)
    (h_refl_w : |r| ≤ c ^ 2)
    (h_cs_plus : q ^ 2 ≤ (a ^ 2 + p) * (c ^ 2 + r))
    (h_cs_minus : q ^ 2 ≤ (a ^ 2 - p) * (c ^ 2 - r)) :
    |p + 2 * q + r| ≤ rvwBound lam₁ lam₂ := by
  -- Handle edge cases where a = 0 or b = 0
  by_cases ha0 : a = 0
  · -- a = 0: p = 0 (from |p| ≤ a² = 0), q = 0 (from CS), X = r
    have hp : p = 0 := by
      have : |p| ≤ 0 := by rw [ha0] at h_refl_u; simpa using h_refl_u
      exact abs_nonpos_iff.mp this
    have hq : q = 0 := by
      have h1 : q ^ 2 ≤ 0 := by rw [ha0, hp] at h_cs_plus; simpa using h_cs_plus
      exact sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg q))
    simp only [hp, hq, mul_zero, add_zero, zero_add]
    -- |r| ≤ c² ≤ (λ₂b)² = λ₂²b² = λ₂²(1-0) = λ₂²
    have hb1 : b = 1 := by nlinarith [sq_nonneg b, ha0]
    have hc_le : c ≤ lam₂ := by rw [hb1] at h_tilde; linarith [mul_one lam₂]
    -- |r| ≤ c² ≤ λ₂² ≤ λ₂ (since λ₂ ≤ 1)
    calc |r| ≤ c ^ 2 := h_refl_w
      _ ≤ lam₂ ^ 2 := by nlinarith
      _ ≤ lam₂ := by nlinarith [sq_nonneg lam₂]
      _ ≤ rvwBound lam₁ lam₂ := by
            unfold rvwBound
            have : lam₂ ^ 2 ≤ (1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2 := by
              linarith [sq_nonneg ((1 - lam₂ ^ 2) * lam₁)]
            have h4 : Real.sqrt (lam₂ ^ 2) ≤
                Real.sqrt ((1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2) :=
              Real.sqrt_le_sqrt this
            rw [Real.sqrt_sq hlam₂] at h4
            have : 0 ≤ (1 - lam₂ ^ 2) * lam₁ / 2 := by
              apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 2)
              exact mul_nonneg (by nlinarith [sq_nonneg lam₂]) hlam₁
            linarith
  · by_cases hb0 : b = 0
    · -- b = 0: c = 0 (from c ≤ λ₂b = 0), r = 0, q = 0, X = p
      have hc0 : c = 0 := by nlinarith [mul_nonneg hlam₂ hb]
      have hr : r = 0 := by
        have : |r| ≤ 0 := by rw [hc0] at h_refl_w; simpa using h_refl_w
        exact abs_nonpos_iff.mp this
      have hq : q = 0 := by
        have h1 : q ^ 2 ≤ 0 := by rw [hc0, hr] at h_cs_plus; simpa using h_cs_plus
        exact sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg q))
      simp only [hq, hr, mul_zero, add_zero]
      -- |p| ≤ λ₁a² ≤ λ₁ (since a²+0=1)
      have ha1 : a ^ 2 = 1 := by nlinarith [sq_nonneg a, hb0]
      calc |p| ≤ lam₁ * a ^ 2 := h_hat
        _ = lam₁ := by rw [ha1, mul_one]
        _ ≤ rvwBound lam₁ lam₂ := by
              -- Need: λ₁ ≤ (1-λ₂²)λ₁/2 + √((1-λ₂²)²λ₁²/4 + λ₂²)
              -- Key: √D ≥ (1+λ₂²)λ₁/2  (since D - ((1+λ₂²)λ₁/2)² = λ₂²(1-λ₁²) ≥ 0)
              unfold rvwBound
              set D := (1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2
              have hD_ge : ((1 + lam₂ ^ 2) * lam₁ / 2) ^ 2 ≤ D := by
                show ((1 + lam₂ ^ 2) * lam₁ / 2) ^ 2 ≤
                  (1 - lam₂ ^ 2) ^ 2 * lam₁ ^ 2 / 4 + lam₂ ^ 2
                have : lam₁ ^ 2 ≤ 1 := by nlinarith
                nlinarith [sq_nonneg lam₂, sq_nonneg (lam₁ * lam₂)]
              have hnn : 0 ≤ (1 + lam₂ ^ 2) * lam₁ / 2 := by positivity
              have hsqrt_le := Real.sqrt_le_sqrt hD_ge
              rw [Real.sqrt_sq hnn] at hsqrt_le
              linarith
    · -- Main case: a > 0, b > 0
      have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      -- Step 1: Bound with exact μ values
      have hcb : c ≤ b := le_trans h_tilde (by nlinarith)
      have h1 := rvw_exact_bound a b c p q r ha_pos hb_pos hc hcb
        h_unit h_refl_u h_refl_w h_cs_plus h_cs_minus
      -- Step 2: Show μ₁ = |p|/a² ≤ λ₁ and μ₂ = c/b ≤ λ₂
      have hmu1 : |p| / a ^ 2 ≤ lam₁ := by
        rwa [div_le_iff₀ (by positivity : (0:ℝ) < a ^ 2)]
      have hmu2 : c / b ≤ lam₂ := by
        rw [div_le_iff₀ hb_pos]; linarith [h_tilde]
      have hmu1_nonneg : 0 ≤ |p| / a ^ 2 := div_nonneg (abs_nonneg _) (by positivity)
      have hmu2_nonneg : 0 ≤ c / b := div_nonneg hc hb_pos.le
      have hmu1_le : |p| / a ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity : (0:ℝ) < a ^ 2)]; exact h_refl_u
      have hmu2_le : c / b ≤ 1 := le_trans hmu2 hlam₂_le
      -- Step 3: Apply monotonicity
      calc |p + 2 * q + r|
          ≤ rvwBound (|p| / a ^ 2) (c / b) := h1
        _ ≤ rvwBound lam₁ (c / b) :=
            rvwBound_mono_left hmu1_nonneg hmu2_nonneg hmu2_le hmu1
        _ ≤ rvwBound lam₁ lam₂ :=
            rvwBound_mono_right hlam₁ hlam₁_le hmu2_nonneg hlam₂_le hmu2

/-- The reflection–Rayleigh quotient bound (RVW section 4.2).

For a self-adjoint involution `Σ` (a reflection: `Σ² = I`, `Σ* = Σ`) and orthogonal
vectors `u`, `w` with:
- `|⟨Σu, u⟩| ≤ λ₁ · ‖u‖²` (hat block spectral gap)
- `‖w‖ ≤ λ₂ · b` where `b² + ‖u‖² = 1` (tilde contraction)

We have: `|⟨Σ(u + w), u + w⟩| ≤ rvwBound(λ₁, λ₂)`.

**Why the triangle inequality approach fails:** Naively bounding
`|⟨Σv, v⟩| ≤ |⟨Σu, u⟩| + 2|⟨Σu, w⟩| + |⟨Σw, w⟩| ≤ λ₁a² + 2ac + c²`
gives the weaker bound `λ₁ + λ₂`, not `rvwBound`. The three terms
cannot simultaneously achieve their maxima because `Σ` is a reflection:
`⟨Σv, v⟩ = cos(2θ) · ‖v‖²` for some angle `θ`. The cross terms are
constrained by the hat term through the reflection geometry.

**Proof strategy (algebraic, avoiding trigonometry):**
1. Bilinear expansion: `⟨Σ(u+w), u+w⟩ = p + 2q + r` where `p = ⟨Σu,u⟩`,
   `q = ⟨Σu,w⟩`, `r = ⟨Σw,w⟩` (using `Σ* = Σ`).
2. Reflection bounds: `|p| ≤ ‖u‖²`, `|r| ≤ ‖w‖²` (from `‖Σ‖ ≤ 1`).
3. Key Cauchy-Schwarz constraints from the reflection structure:
   - `q² ≤ (‖u‖²+p)(‖w‖²+r)` via `(I+Σ)`: expand `⟨(I+Σ)u, (I+Σ)w⟩ = 2q`
   - `q² ≤ (‖u‖²-p)(‖w‖²-r)` via `(I-Σ)`: expand `⟨(I-Σ)u, (I-Σ)w⟩ = -2q`
   These two constraints together prevent `q` from being large simultaneously
   with `p`, which is the key geometric insight.
4. Reduce to `rvw_optimization_bound`: a pure real-analysis optimization.
-/
private lemma reflection_quadratic_bound {n : ℕ}
    (Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (u w : EuclideanSpace ℝ (Fin n)) (h_orth : @inner ℝ _ _ u w = 0)
    (b : ℝ) (hb : 0 ≤ b)
    (h_unit : ‖u‖ ^ 2 + b ^ 2 = 1)
    (lam₁ lam₂ : ℝ) (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂)
    (hlam₁_le : lam₁ ≤ 1) (hlam₂_le : lam₂ ≤ 1)
    (h_hat : |@inner ℝ _ _ (Sig u) u| ≤ lam₁ * ‖u‖ ^ 2)
    (h_tilde_norm : ‖w‖ ≤ lam₂ * b) :
    |@inner ℝ _ _ (Sig (u + w)) (u + w)| ≤ rvwBound lam₁ lam₂ := by
  -- Set up the real variables for the optimization bound
  set a := ‖u‖
  set c := ‖w‖
  set p := @inner ℝ _ _ (Sig u) u
  set q := @inner ℝ _ _ (Sig u) w
  set r := @inner ℝ _ _ (Sig w) w
  -- Step 1: Bilinear expansion ⟨Σ(u+w), u+w⟩ = p + 2q + r
  have h_expand := reflection_bilinear_expand Sig hSig_sa u w
  rw [h_expand]
  -- Step 2: Gather all constraints
  have ha : 0 ≤ a := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have h_refl_u := reflection_rayleigh_le_norm_sq Sig hSig_inv hSig_sa u
  have h_refl_w := reflection_rayleigh_le_norm_sq Sig hSig_inv hSig_sa w
  have h_cs_plus := reflection_cs Sig hSig_inv hSig_sa u w h_orth 1 (by norm_num)
  have h_cs_minus := reflection_cs Sig hSig_inv hSig_sa u w h_orth (-1) (by norm_num)
  simp only [one_mul, neg_one_mul] at h_cs_plus h_cs_minus
  -- Step 3: Apply the pure real optimization bound
  exact rvw_optimization_bound a b c p q r lam₁ lam₂
    ha hb hc hlam₁ hlam₂ hlam₁_le hlam₂_le h_unit h_tilde_norm h_hat h_refl_u h_refl_w
    h_cs_plus h_cs_minus

/-- For self-adjoint operators, an inner product bound implies an operator norm bound.
    If `∀ x, |⟨Ax, x⟩| ≤ c · ‖x‖²`, then `‖A‖ ≤ c`.
    Proof via polarization identity + parallelogram law. -/
lemma sa_opNorm_le_of_inner_le {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT_sa : IsSelfAdjoint T) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x, |@inner ℝ _ _ (T x) x| ≤ c * ‖x‖ ^ 2) :
    ‖T‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  by_cases hx : x = 0
  · simp [hx]
  by_cases hTx : T x = 0
  · simp [hTx]; positivity
  -- Self-adjointness: ⟨Ty, x⟩ = ⟨Tx, y⟩
  have hT_sym : ∀ u v : EuclideanSpace ℝ (Fin n),
      @inner ℝ _ _ (T u) v = @inner ℝ _ _ u (T v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT_sa
  have hTx_pos : (0 : ℝ) < ‖T x‖ := norm_pos_iff.mpr hTx
  -- Choose y = (‖x‖/‖Tx‖) • Tx so that ‖y‖ = ‖x‖
  set y := (‖x‖ / ‖T x‖) • T x
  have hy_norm : ‖y‖ = ‖x‖ := by
    simp only [y, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) hTx_pos.le)]
    exact div_mul_cancel₀ _ (ne_of_gt hTx_pos)
  -- ⟨Tx, y⟩ = ‖x‖ · ‖Tx‖
  have hTxy : @inner ℝ _ _ (T x) y = ‖x‖ * ‖T x‖ := by
    simp only [y, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  -- Polarization: ⟨T(x+y), x+y⟩ - ⟨T(x-y), x-y⟩ = 4⟨Tx, y⟩
  have h_polar : @inner ℝ _ _ (T (x + y)) (x + y) - @inner ℝ _ _ (T (x - y)) (x - y) =
      4 * @inner ℝ _ _ (T x) y := by
    have hsym : @inner ℝ _ _ (T y) x = @inner ℝ _ _ (T x) y := by
      rw [hT_sym y x, real_inner_comm]
    simp only [map_add, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right]
    linarith
  -- Bound: 4⟨Tx,y⟩ ≤ |⟨T(x+y),x+y⟩| + |⟨T(x-y),x-y⟩| ≤ c(‖x+y‖² + ‖x-y‖²)
  have h_bound : 4 * (‖x‖ * ‖T x‖) ≤ c * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) := by
    calc 4 * (‖x‖ * ‖T x‖)
        = 4 * @inner ℝ _ _ (T x) y := by rw [hTxy]
      _ = @inner ℝ _ _ (T (x + y)) (x + y) -
            @inner ℝ _ _ (T (x - y)) (x - y) := by linarith [h_polar]
      _ ≤ |@inner ℝ _ _ (T (x + y)) (x + y)| +
            |@inner ℝ _ _ (T (x - y)) (x - y)| := by
          linarith [le_abs_self (@inner ℝ _ _ (T (x + y)) (x + y)),
                    neg_abs_le (@inner ℝ _ _ (T (x - y)) (x - y))]
      _ ≤ c * ‖x + y‖ ^ 2 + c * ‖x - y‖ ^ 2 := by linarith [h (x + y), h (x - y)]
      _ = c * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) := by ring
  -- Parallelogram: ‖x+y‖² + ‖x-y‖² = 2(‖x‖² + ‖y‖²)
  have h_para : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have := parallelogram_law_with_norm (𝕜 := ℝ) x y
    nlinarith [sq (‖x + y‖), sq (‖x - y‖), sq ‖x‖, sq ‖y‖]
  rw [h_para, hy_norm] at h_bound
  -- h_bound : 4 * (‖x‖ * ‖T x‖) ≤ c * (2 * (‖x‖ ^ 2 + ‖x‖ ^ 2)) = 4c‖x‖²
  have hx_pos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have h_ineq : ‖x‖ * ‖T x‖ ≤ ‖x‖ * (c * ‖x‖) := by nlinarith
  exact le_of_mul_le_mul_left h_ineq hx_pos

/-- `WP = P` from the factorization `W = BΣB` and operator identities. -/
private lemma walk_proj_fixed {n : ℕ}
    (W B Sig P Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hfact : W = B * Sig * B)
    (hBQ : B * Q = Q) (hQP : Q * P = P) (hSigP : Sig * P = P) :
    W * P = P := by
  have hBP : B * P = P := by rw [← hQP, ← mul_assoc, hBQ]
  rw [hfact]; simp only [mul_assoc]; rw [hBP, hSigP, hBP]

/-- For `y` with `Py = 0`: `⟨Wy, y⟩ = ⟨Σ(By), By⟩` by B self-adjointness. -/
private lemma walk_inner_eq_sig {n : ℕ}
    (W B Sig : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hfact : W = B * Sig * B) (hB_sa : IsSelfAdjoint B)
    (y : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ (W y) y = @inner ℝ _ _ (Sig (B y)) (B y) := by
  have hB_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB_sa
  rw [hfact, show (B * Sig * B) y = B (Sig (B y)) from rfl]
  exact hB_sym (Sig (B y)) y

/-- `By = Qy + B((1-Q)y)` with orthogonality `⟨Qy, B((1-Q)y)⟩ = 0`. -/
private lemma B_decomp_orthog {n : ℕ}
    (B Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hBQ : B * Q = Q) (hQB : Q * B = Q)
    (hQ_proj : Q * Q = Q) (hQ_sa : IsSelfAdjoint Q)
    (y : EuclideanSpace ℝ (Fin n)) :
    B y = Q y + B ((1 - Q) y) ∧ @inner ℝ _ _ (Q y) (B ((1 - Q) y)) = 0 := by
  have hQ_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hQ_sa
  have hQ_tilde : Q ((1 - Q) y) = 0 := by
    change (Q * (1 - Q)) y = 0
    rw [mul_sub, mul_one, hQ_proj, sub_self, ContinuousLinearMap.zero_apply]
  constructor
  · have : y = Q y + (1 - Q) y := by
      simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    conv_lhs => rw [this]
    rw [map_add, show B (Q y) = (B * Q) y from rfl, hBQ]
  · calc @inner ℝ _ _ (Q y) (B ((1 - Q) y))
        = @inner ℝ _ _ y ((Q * B) ((1 - Q) y)) := hQ_sym y (B ((1 - Q) y))
      _ = @inner ℝ _ _ y (Q ((1 - Q) y)) := by rw [hQB]
      _ = 0 := by rw [hQ_tilde, inner_zero_right]

/-- `|⟨Σ(Qy), Qy⟩| ≤ λ₁ · ‖Qy‖²` when `Py = 0` and `‖QΣQ - P‖ ≤ λ₁`. -/
private lemma hat_sig_inner_bound {n : ℕ}
    (Sig Q P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ_proj : Q * Q = Q) (hQ_sa : IsSelfAdjoint Q)
    (hPQ : P * Q = P) (lam₁ : ℝ) (h_hat_norm : ‖Q * Sig * Q - P‖ ≤ lam₁)
    (y : EuclideanSpace ℝ (Fin n)) (hPy : P y = 0) :
    |@inner ℝ _ _ (Sig (Q y)) (Q y)| ≤ lam₁ * ‖Q y‖ ^ 2 := by
  have hQ_Qy : Q (Q y) = Q y := by show (Q * Q) y = Q y; rw [hQ_proj]
  have hP_Qy : P (Q y) = 0 := by show (P * Q) y = 0; rw [hPQ]; exact hPy
  -- ⟨Σ(Qy), Qy⟩ = ⟨(QΣQ - P)(Qy), Qy⟩ since P(Qy) = 0 and Q(Qy) = Qy
  have hQ_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hQ_sa
  have key : @inner ℝ _ _ (Sig (Q y)) (Q y) =
      @inner ℝ _ _ ((Q * Sig * Q - P) (Q y)) (Q y) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      hQ_Qy, hP_Qy, sub_zero]
    -- Goal: inner (Sig (Q y)) (Q y) = inner (Q (Sig (Q y))) (Q y)
    -- By Q-symmetry: inner (Q u) v = inner u (Q v), applied with u = Sig(Qy), v = Qy
    have h := hQ_sym (Sig (Q y)) (Q y)
    -- h : inner (Q (Sig (Q y))) (Q y) = inner (Sig (Q y)) (Q (Q y))
    -- Since Q(Qy) = Qy, the RHS is inner (Sig (Q y)) (Q y)
    conv_rhs at h => rw [show (↑Q : _ →ₗ[ℝ] _) (Q y) = (Q * Q) y from rfl, hQ_proj]
    exact h.symm
  rw [key]; exact hat_block_bound Sig Q P lam₁ h_hat_norm (Q y)

/-- For `y` with `Py = 0`: `|⟨Σ(By), By⟩| ≤ rvwBound(λ₁, λ₂) · ‖y‖²`. -/
private lemma sig_inner_perp_bound {n : ℕ}
    (B Sig Q P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ_proj : Q * Q = Q) (hQ_sa : IsSelfAdjoint Q)
    (hBQ : B * Q = Q) (hQB : Q * B = Q)
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (hPQ : P * Q = P)
    (lam₁ lam₂ : ℝ) (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂)
    (hlam₁_le : lam₁ ≤ 1) (hlam₂_le : lam₂ ≤ 1)
    (h_tilde : ∀ x, Q x = 0 → ‖B x‖ ≤ lam₂ * ‖x‖)
    (h_hat : ‖Q * Sig * Q - P‖ ≤ lam₁)
    (y : EuclideanSpace ℝ (Fin n)) (hPy : P y = 0) :
    |@inner ℝ _ _ (Sig (B y)) (B y)| ≤ rvwBound lam₁ lam₂ * ‖y‖ ^ 2 := by
  -- Decompose By = Qy + B((1-Q)y)
  obtain ⟨hBdecomp, h_orth⟩ := B_decomp_orthog B Q hBQ hQB hQ_proj hQ_sa y
  set u₀ := Q y; set w₀ := B ((1 - Q) y)
  rw [hBdecomp]
  -- Handle y = 0
  by_cases hy : y = 0
  · have hu : u₀ = 0 := by simp [u₀, hy]
    have hw : w₀ = 0 := by simp [w₀, hy]
    simp [hu, hw, hy]
  have hy_pos : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  -- Normalize: set s = ‖y‖⁻¹
  set s := ‖y‖⁻¹ with s_def
  have hs_pos : 0 < s := inv_pos.mpr hy_pos
  set u := s • u₀; set w := s • w₀
  -- Scale inner product: ⟨Σ(u₀+w₀), u₀+w₀⟩ = ‖y‖² · ⟨Σ(u+w), u+w⟩
  have huw : u₀ + w₀ = ‖y‖ • (u + w) := by
    simp only [u, w, s_def, smul_add, ← mul_smul,
      mul_inv_cancel₀ (ne_of_gt hy_pos), one_smul]
  have hscale : @inner ℝ _ _ (Sig (u₀ + w₀)) (u₀ + w₀) =
      ‖y‖ ^ 2 * @inner ℝ _ _ (Sig (u + w)) (u + w) := by
    rw [huw, map_smul, inner_smul_left, inner_smul_right, conj_trivial]; ring
  rw [hscale, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖y‖ ^ 2), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  -- Prepare arguments for reflection_quadratic_bound
  have h_orth_scaled : @inner ℝ _ _ u w = 0 := by
    simp only [u, w, inner_smul_left, inner_smul_right, conj_trivial, h_orth, mul_zero]
  have h_unit : ‖u‖ ^ 2 + (s * ‖(1 - Q) y‖) ^ 2 = 1 := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs_pos.le, mul_pow]
    rw [← mul_add, ← hat_tilde_norm_sq Q hQ_proj hQ_sa y, s_def, inv_pow,
        inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hy_pos))]
  have h_hat_scaled : |@inner ℝ _ _ (Sig u) u| ≤ lam₁ * ‖u‖ ^ 2 := by
    simp only [u, map_smul, inner_smul_left, inner_smul_right, conj_trivial,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hs_pos.le, mul_pow]
    rw [show |s * (s * @inner ℝ _ _ (Sig u₀) u₀)| =
          s ^ 2 * |@inner ℝ _ _ (Sig u₀) u₀| from by
      rw [show s * (s * @inner ℝ _ _ (Sig u₀) u₀) = s ^ 2 * @inner ℝ _ _ (Sig u₀) u₀ from
        by ring, abs_mul, abs_of_nonneg (by positivity : 0 ≤ s ^ 2)]]
    rw [show lam₁ * (s ^ 2 * ‖u₀‖ ^ 2) = s ^ 2 * (lam₁ * ‖u₀‖ ^ 2) from by ring]
    exact mul_le_mul_of_nonneg_left
      (hat_sig_inner_bound Sig Q P hQ_proj hQ_sa hPQ lam₁ h_hat y hPy) (by positivity)
  have h_tilde_scaled : ‖w‖ ≤ lam₂ * (s * ‖(1 - Q) y‖) := by
    simp only [w, w₀, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs_pos.le]
    have h_tc := tilde_contraction_bound B Q lam₂ h_tilde hQ_proj y
    nlinarith
  exact reflection_quadratic_bound Sig hSig_inv hSig_sa u w
    h_orth_scaled (s * ‖(1 - Q) y‖) (by positivity) h_unit
    lam₁ lam₂ hlam₁ hlam₂ hlam₁_le hlam₂_le h_hat_scaled h_tilde_scaled

/-- **The core RVW operator norm bound (abstract).**

    Given operators on a real inner product space satisfying:
    - `W = B · Σ · B` (walk factorization)
    - `Q` orthogonal projection (`Q² = Q`, `Q* = Q`)
    - `B` self-adjoint contraction preserving `Q` (`BQ = QB = Q`, `‖B‖ ≤ 1`)
    - `Σ` self-adjoint involution (`Σ² = 1`, `Σ* = Σ`, `ΣP = P`)
    - `P ≤ Q` projections (`PQ = QP = P`)
    - `∀ x ∈ ker Q, ‖Bx‖ ≤ λ₂·‖x‖` (within-cluster contraction on tilde subspace)
    - `‖QΣQ - P‖ ≤ λ₁` (hat-block spectral gap)

    Then `‖W - P‖ ≤ rvwBound(λ₁, λ₂)`. -/
theorem rvw_operator_norm_bound
    {n : ℕ}
    (W B Sig Q P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hfact : W = B * Sig * B)
    (hQ_proj : Q * Q = Q) (hQ_sa : IsSelfAdjoint Q)
    (hBQ : B * Q = Q) (hQB : Q * B = Q)
    (hB_sa : IsSelfAdjoint B)
    (hSig_inv : Sig * Sig = 1) (hSig_sa : IsSelfAdjoint Sig)
    (hSigP : Sig * P = P)
    (hP_proj : P * P = P) (hP_sa : IsSelfAdjoint P)
    (hPQ : P * Q = P) (hQP : Q * P = P)
    (lam₁ lam₂ : ℝ) (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂)
    (hlam₁_le : lam₁ ≤ 1) (hlam₂_le : lam₂ ≤ 1)
    (h_tilde : ∀ x, Q x = 0 → ‖B x‖ ≤ lam₂ * ‖x‖)
    (h_hat : ‖Q * Sig * Q - P‖ ≤ lam₁) :
    ‖W - P‖ ≤ rvwBound lam₁ lam₂ := by
  -- W is self-adjoint (via B*·Σ*·B* = B·Σ·B since all are self-adjoint)
  have hB_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB_sa
  have hSig_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hSig_sa
  have hP_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP_sa
  have hW_sym : (W : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _).IsSymmetric := by
    intro u v; rw [hfact]
    calc @inner ℝ _ _ ((B * Sig * B) u) v
        = @inner ℝ _ _ (Sig (B u)) (B v) := hB_sym (Sig (B u)) v
      _ = @inner ℝ _ _ (B u) (Sig (B v)) := hSig_sym (B u) (B v)
      _ = @inner ℝ _ _ u ((B * Sig * B) v) := hB_sym u (Sig (B v))
  have hW_sa : IsSelfAdjoint W :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hW_sym
  -- W - P is self-adjoint (Star diamond workaround)
  have hWP_sa : IsSelfAdjoint (W - P) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, ContinuousLinearMap.coe_sub]
    exact hW_sym.sub hP_sym
  have hWP_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hWP_sa
  -- WP = P, so (W-P)P = 0
  have hWP := walk_proj_fixed W B Sig P Q hfact hBQ hQP hSigP
  -- Apply polarization: suffices to bound |⟨(W-P)x, x⟩| ≤ rvwBound · ‖x‖²
  apply sa_opNorm_le_of_inner_le _ hWP_sa _ (rvwBound_nonneg _ _ hlam₁ hlam₂ hlam₂_le)
  intro x
  -- Reduce to y = x - Px (since (W-P) annihilates range(P))
  set y := x - P x
  have hPy : P y = 0 := by
    simp [y, map_sub, show P (P x) = (P * P) x from rfl, hP_proj]
  have hWP_annihil : (W - P) (P x) = 0 := by
    simp [ContinuousLinearMap.sub_apply, show W (P x) = (W * P) x from rfl, hWP,
          show P (P x) = (P * P) x from rfl, hP_proj]
  -- ⟨(W-P)y, Px⟩ = 0 by self-adjointness + annihilation
  have h_cross_zero : @inner ℝ _ _ ((W - P) y) (P x) = 0 := by
    calc @inner ℝ _ _ ((W - P) y) (P x)
        = @inner ℝ _ _ y ((W - P) (P x)) := hWP_sym y (P x)
      _ = 0 := by rw [hWP_annihil, inner_zero_right]
  -- ⟨(W-P)x, x⟩ = ⟨(W-P)y, y⟩
  have hreduce : @inner ℝ _ _ ((W - P) x) x = @inner ℝ _ _ ((W - P) y) y := by
    have hx_eq : x = P x + y := by simp [y]
    conv_lhs => rw [hx_eq]; rw [map_add, hWP_annihil, zero_add]
    rw [inner_add_right, h_cross_zero, zero_add]
  -- ⟨(W-P)y, y⟩ = ⟨Wy, y⟩ since Py = 0
  have hWP_to_W : @inner ℝ _ _ ((W - P) y) y = @inner ℝ _ _ (W y) y := by
    simp [ContinuousLinearMap.sub_apply, hPy]
  -- ⟨Wy, y⟩ = ⟨Σ(By), By⟩
  have hW_to_sig := walk_inner_eq_sig W B Sig hfact hB_sa y
  rw [hreduce, hWP_to_W, hW_to_sig]
  -- |⟨Σ(By), By⟩| ≤ rvwBound · ‖y‖² ≤ rvwBound · ‖x‖²
  have h_bound := sig_inner_perp_bound B Sig Q P hQ_proj hQ_sa hBQ hQB
    hSig_inv hSig_sa hPQ lam₁ lam₂ hlam₁ hlam₂ hlam₁_le hlam₂_le h_tilde h_hat y hPy
  -- ‖y‖² ≤ ‖x‖² (orthogonal decomposition)
  have h_norm_le : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have : ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖y‖ ^ 2 := hat_tilde_norm_sq P hP_proj hP_sa x
    linarith [sq_nonneg ‖P x‖]
  calc |@inner ℝ _ _ (Sig (B y)) (B y)|
      ≤ rvwBound lam₁ lam₂ * ‖y‖ ^ 2 := h_bound
    _ ≤ rvwBound lam₁ lam₂ * ‖x‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left h_norm_le
          (rvwBound_nonneg _ _ hlam₁ hlam₂ hlam₂_le)

/-- `rvwBound(λ₁, λ₂) ≤ c` follows from the polynomial condition
    `(1 − λ₂²) · λ₁ · c + λ₂² ≤ c²`, which is decidable for rationals
    via `norm_num`. This avoids `Real.sqrt` in downstream proofs.

    Proof: by contradiction. If `x = rvwBound > c`, the quadratic identity
    `x² = (1−λ₂²)λ₁x + λ₂²` and hypothesis `(1−λ₂²)λ₁c + λ₂² ≤ c²` give
    `(x−c)(x+c) ≤ (1−λ₂²)λ₁(x−c)`, so `x+c ≤ (1−λ₂²)λ₁ ≤ c`,
    contradicting `x ≥ λ₂ > 0`. -/
lemma rvwBound_le_of_poly {lam₁ lam₂ c : ℝ}
    (hlam₂_pos : 0 < lam₂) (hlam₂_le : lam₂ ≤ 1)
    (hlam₁_nn : 0 ≤ lam₁) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1)
    (h : (1 - lam₂ ^ 2) * lam₁ * c + lam₂ ^ 2 ≤ c ^ 2) :
    rvwBound lam₁ lam₂ ≤ c := by
  set x := rvwBound lam₁ lam₂
  have hx_nn := rvwBound_nonneg lam₁ lam₂ hlam₁_nn (le_of_lt hlam₂_pos) hlam₂_le
  have hx_quad := rvwBound_quadratic_eq lam₁ lam₂
  by_contra hlt
  push_neg at hlt
  have hxc : 0 < x - c := by linarith
  have hsum : x + c ≤ (1 - lam₂ ^ 2) * lam₁ := by
    have h1 : (x - c) * (x + c) ≤ (1 - lam₂ ^ 2) * lam₁ * (x - c) := by nlinarith
    exact le_of_mul_le_mul_left (by linarith) hxc
  have hx_ge : lam₂ ≤ x := by
    have : lam₂ ^ 2 ≤ x ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (by nlinarith [sq_nonneg lam₂] : lam₂ ^ 2 ≤ 1))
        (mul_nonneg hlam₁_nn hx_nn)]
    nlinarith [sq_nonneg (x - lam₂)]
  have hc_pos : 0 < c := by
    by_contra hc0; push_neg at hc0
    have : c = 0 := le_antisymm (by linarith) hc_nn
    subst this; nlinarith [sq_nonneg lam₂]
  have hcoeff_le : (1 - lam₂ ^ 2) * lam₁ ≤ c := by
    have : (1 - lam₂ ^ 2) * lam₁ * c ≤ c ^ 2 := by nlinarith [sq_nonneg lam₂]
    exact le_of_mul_le_mul_right (by nlinarith [sq_nonneg c]) hc_pos
  linarith

end


