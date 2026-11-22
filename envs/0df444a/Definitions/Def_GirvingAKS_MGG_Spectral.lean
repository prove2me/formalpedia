-- Prove2me | Definitions.Def_GirvingAKS_MGG_Spectral
-- name    : GirvingAKS_MGG_Spectral
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:42:11.946726+00:00
-- url     : https://prove2.me/theorems/00541902-2c36-4a27-ad56-7a3ac034c247
-- title:
--   AKS sorting networks (Seiferas port) — MGG Spectral Gap Bound
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/MGG/Spectral.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** The spectral gap bound for the Margulis-Gabber-Galil expander: `spectralGap (mgg n) ≤ 5 * √2 / 8` for `n ≥ 3`.
--
--   - Gabber & Galil (1981), "Explicit constructions of linear-sized superconcentrators."
--
--   Original spectral analysis via continuous torus.
--
--   - Jimbo & Maruoka (1987), "Expanders obtained from affine transformations,"
--
--   *Combinatorica* 7, 343–355. Discrete Fourier proof giving adjacency eigenvalue `≤ 5√2`. Simplified by Boppana; see Linial–Wigderson lecture notes Chapter 7 (`docs/hlw-expander-notes.pdf`).
--
--   See `docs/jimbo-maruoka.md` for the full proof plan.
--
--   The proof works entirely in Fourier space on `(Z/nZ)²` via the **full 2D DFT**. No L₁/L₂ decomposition, no fiber projections.
--
--   **Step 0.** Reduce `spectralGap ≤ 5√2/8` to bounding the Rayleigh quotient: for all `f ⊥ 1` with `‖f‖ = 1`, show `|⟨f, Af⟩| ≤ 5√2` where `A` is the adjacency operator (since walk = A/8).
--
--   **Step 1.** By self-adjointness and substitution (inverse maps give same sum), reduce to bounding 4 "forward" sums involving `M₁v`, `M₁v+e₁`, `M₂v`, `M₂v+e₂`.
--
--   **Step 2.** Apply the 2D DFT. The DFT shift property converts `f(Mv+b)` into phase-shifted Fourier coefficients. The key identity `|1 + ω^a| = 2|cos(πa/n)|` converts phase factors into cosines.
--
--   **Step 3.** Take absolute values to reduce to a real non-negative function `G = |f̂|`. The bilinear form becomes: `∑_{α≠0} G(α) · [G(S₁α)|cos(πα₁/n)| + G(S₂α)|cos(πα₂/n)|]` where `S₁ = M₁⁻ᵀ` (preserves `α₂`), `S₂ = M₂⁻ᵀ` (preserves `α₁`).
--
--   **Step 4.** Apply Young's inequality (weighted AM-GM) with weight function `ψ` satisfying `ψ(α,β) · ψ(β,α) = 1`. This converts the bilinear form into a quadratic form, reducing to a pointwise condition on each `α ≠ 0`.
--
--   **Step 5.** Define `ψ` using a partial order on `(Z/nZ)² \ {0}` based on the "distance to axes" function `a(x) = min(x, n-x)`. Set `ε = √2/2`:
--
--   - `ψ(α,β) = ε` if `α > β` (α farther from axes)
--   - `ψ(α,β) = 1/ε` if `α < β`
--   - `ψ(α,β) = 1` if incomparable
--
--   **Step 6.** Verify the pointwise condition by cases:
--
--   - **Outside diamond** (`a(α₁) + a(α₂) > n/2`): `|cos(πα₁/n)| + |cos(πα₂/n)| ≤ √2`
--
--   by convexity. Combined with ψ bounds: LHS ≤ 3 < 5√2/2.
--
--   - **Inside diamond** (`a(α₁) + a(α₂) ≤ n/2`): combinatorial case analysis shows
--
--   3 of the 4 neighbors `{S₁α, S₁⁻¹α, S₂α, S₂⁻¹α}` satisfy `> α` and 1 satisfies `< α`, giving ψ sum = `3ε + 1/ε = 5√2/2` (tight!).
--
--   **Step 7.** Assemble: pointwise condition → quadratic form bound → Rayleigh quotient → spectral gap.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/Spectral.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_MGG_Defs
import Definitions.Def_GirvingAKS_MGG_DFT
import Definitions.Def_GirvingAKS_MGG_WalkExpansion
import Definitions.Def_GirvingAKS_MGG_YoungAssembly
import Definitions.Def_GirvingAKS_Graph_Square
import Definitions.Def_GirvingAKS_ZigZag_RVWBound

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/MGG/Spectral.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # MGG Spectral Gap Bound

  The spectral gap bound for the Margulis-Gabber-Galil expander:
  `spectralGap (mgg n) ≤ 5 * √2 / 8` for `n ≥ 3`.

  ## References

  - Gabber & Galil (1981), "Explicit constructions of linear-sized superconcentrators."
    Original spectral analysis via continuous torus.
  - Jimbo & Maruoka (1987), "Expanders obtained from affine transformations,"
    *Combinatorica* 7, 343–355. Discrete Fourier proof giving adjacency eigenvalue `≤ 5√2`.
    Simplified by Boppana; see Linial–Wigderson lecture notes Chapter 7
    (`docs/hlw-expander-notes.pdf`).

  See `docs/jimbo-maruoka.md` for the full proof plan.

  ## Proof Architecture (Boppana-simplified Jimbo-Maruoka)

  The proof works entirely in Fourier space on `(Z/nZ)²` via the **full 2D DFT**.
  No L₁/L₂ decomposition, no fiber projections.

  **Step 0.** Reduce `spectralGap ≤ 5√2/8` to bounding the Rayleigh quotient:
  for all `f ⊥ 1` with `‖f‖ = 1`, show `|⟨f, Af⟩| ≤ 5√2` where `A` is the
  adjacency operator (since walk = A/8).

  **Step 1.** By self-adjointness and substitution (inverse maps give same sum),
  reduce to bounding 4 "forward" sums involving `M₁v`, `M₁v+e₁`, `M₂v`, `M₂v+e₂`.

  **Step 2.** Apply the 2D DFT. The DFT shift property converts `f(Mv+b)` into
  phase-shifted Fourier coefficients. The key identity `|1 + ω^a| = 2|cos(πa/n)|`
  converts phase factors into cosines.

  **Step 3.** Take absolute values to reduce to a real non-negative function `G = |f̂|`.
  The bilinear form becomes:
  `∑_{α≠0} G(α) · [G(S₁α)|cos(πα₁/n)| + G(S₂α)|cos(πα₂/n)|]`
  where `S₁ = M₁⁻ᵀ` (preserves `α₂`), `S₂ = M₂⁻ᵀ` (preserves `α₁`).

  **Step 4.** Apply Young's inequality (weighted AM-GM) with weight function `ψ`
  satisfying `ψ(α,β) · ψ(β,α) = 1`. This converts the bilinear form into a
  quadratic form, reducing to a pointwise condition on each `α ≠ 0`.

  **Step 5.** Define `ψ` using a partial order on `(Z/nZ)² \ {0}` based on the
  "distance to axes" function `a(x) = min(x, n-x)`. Set `ε = √2/2`:
  - `ψ(α,β) = ε` if `α > β` (α farther from axes)
  - `ψ(α,β) = 1/ε` if `α < β`
  - `ψ(α,β) = 1` if incomparable

  **Step 6.** Verify the pointwise condition by cases:
  - **Outside diamond** (`a(α₁) + a(α₂) > n/2`): `|cos(πα₁/n)| + |cos(πα₂/n)| ≤ √2`
    by convexity. Combined with ψ bounds: LHS ≤ 3 < 5√2/2.
  - **Inside diamond** (`a(α₁) + a(α₂) ≤ n/2`): combinatorial case analysis shows
    3 of the 4 neighbors `{S₁α, S₁⁻¹α, S₂α, S₂⁻¹α}` satisfy `> α` and 1 satisfies
    `< α`, giving ψ sum = `3ε + 1/ε = 5√2/2` (tight!).

  **Step 7.** Assemble: pointwise condition → quadratic form bound → Rayleigh quotient
  → spectral gap.
-/


section


open Matrix BigOperators Finset Real
open scoped Real


/-! **Step 0: Rayleigh Quotient Reduction**

    By `sa_opNorm_le_of_inner_le` (in `RVWBound.lean`), `spectralGap ≤ c` reduces to:
    for all `f ⊥ 1` with `‖f‖ = 1`, `|⟨f, (W - mean) f⟩| ≤ c`.
    Since `A = 8 · W` and `spectralGap = ‖W - mean‖`, this becomes
    `|⟨f, Af⟩| ≤ 8c = 5√2` for the adjacency operator `A`.
-/

/-- Generic Rayleigh quotient reduction: for any `RegularGraph N d` with `d > 0`,
    if `|⟨f, Wf⟩| ≤ c` for all mean-zero unit `f`, then `spectralGap G ≤ c`.
    Used by `mgg` (8-regular). -/
theorem spectralGap_of_rayleigh_bound {N d : ℕ} (G : RegularGraph N d)
    (c : ℝ) (hc : 0 ≤ c) (hd : 0 < d)
    (h : ∀ f : EuclideanSpace ℝ (Fin N),
      @inner ℝ _ _ f (meanCLM N f) = 0 → ‖f‖ = 1 →
      |@inner ℝ _ _ f (G.walkCLM f)| ≤ c) :
    spectralGap G ≤ c := by
  let W := G.walkCLM
  let P := meanCLM N
  have hW_sym : ∀ u v, @inner ℝ _ _ (W u) v = @inner ℝ _ _ u (W v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (walkCLM_isSelfAdjoint G)
  have hP_sym : ∀ u v, @inner ℝ _ _ (P u) v = @inner ℝ _ _ u (P v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (meanCLM_isSelfAdjoint N)
  have hWP_sa : IsSelfAdjoint (W - P) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, ContinuousLinearMap.coe_sub]
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (walkCLM_isSelfAdjoint G)).sub
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (meanCLM_isSelfAdjoint N))
  have hWP_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hWP_sa
  have hWP_comp : ∀ f, W (P f) = P f := walkCLM_comp_meanCLM G hd
  have hPP : ∀ f, P (P f) = P f := by
    intro f; change (P * P) f = P f; rw [meanCLM_idempotent]
  have hWP_annihil : ∀ x, (W - P) (P x) = 0 := by
    intro x; show W (P x) - P (P x) = 0; rw [hWP_comp, hPP, sub_self]
  unfold spectralGap
  apply sa_opNorm_le_of_inner_le _ hWP_sa _ hc
  intro x
  set y := x - P x with hy_def
  have hPy : P y = 0 := by
    show P (x - P x) = 0; rw [map_sub, hPP, sub_self]
  have h_cross : @inner ℝ _ _ ((W - P) y) (P x) = 0 := by
    calc @inner ℝ _ _ ((W - P) y) (P x)
        = @inner ℝ _ _ y ((W - P) (P x)) := hWP_sym y (P x)
      _ = 0 := by rw [hWP_annihil, inner_zero_right]
  have hreduce : @inner ℝ _ _ ((W - P) x) x = @inner ℝ _ _ ((W - P) y) y := by
    have hx_eq : x = P x + y := by simp [hy_def]
    conv_lhs => rw [hx_eq, map_add, hWP_annihil, zero_add, inner_add_right, h_cross, zero_add]
  have hWP_to_W : @inner ℝ _ _ ((W - P) y) y = @inner ℝ _ _ (W y) y := by
    show @inner ℝ _ _ (W y - P y) y = _; rw [hPy, sub_zero]
  have h_norm_le : ‖y‖ ≤ ‖x‖ := norm_sub_meanCLM_le N x
  rw [hreduce, hWP_to_W]
  by_cases hy0 : y = 0
  · simp [hy0]; positivity
  · set g := (1 / ‖y‖) • y with hg_def
    have hy_pos : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy0
    have hg_norm : ‖g‖ = 1 := by
      rw [hg_def, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg zero_le_one hy_pos.le), div_mul_cancel₀ 1 (ne_of_gt hy_pos)]
    have hg_orth : @inner ℝ _ _ g (P g) = 0 := by
      rw [hg_def, map_smul, inner_smul_left, inner_smul_right, hPy,
        inner_zero_right, mul_zero, mul_zero]
    have hy_eq : y = ‖y‖ • g := by
      rw [hg_def, smul_smul, mul_one_div, div_self (ne_of_gt hy_pos), one_smul]
    have hscale : @inner ℝ _ _ (W y) y = ‖y‖ ^ 2 * @inner ℝ _ _ (W g) g := by
      conv_lhs => rw [hy_eq]
      rw [map_smul, inner_smul_left, inner_smul_right]
      simp only [conj_trivial, sq]; ring
    have hswap : @inner ℝ _ _ (W g) g = @inner ℝ _ _ g (W g) := hW_sym g g
    rw [hscale, abs_mul, abs_of_nonneg (sq_nonneg _), hswap]
    calc ‖y‖ ^ 2 * |@inner ℝ _ _ g (W g)|
        ≤ ‖y‖ ^ 2 * c := by nlinarith [h g hg_orth hg_norm]
      _ ≤ ‖x‖ ^ 2 * c := by
          apply mul_le_mul_of_nonneg_right _ hc
          exact sq_le_sq' (by linarith) h_norm_le
      _ = c * ‖x‖ ^ 2 := by ring

/-- MGG-specific Rayleigh reduction: one-liner calling the generic version. -/
theorem mgg_spectralGap_of_rayleigh_bound (n : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ f : EuclideanSpace ℝ (Fin (n * n)),
      @inner ℝ _ _ f (meanCLM (n * n) f) = 0 → ‖f‖ = 1 →
      |@inner ℝ _ _ f ((mgg n).walkCLM f)| ≤ c) :
    spectralGap (mgg n) ≤ c :=
  spectralGap_of_rayleigh_bound (mgg n) c hc (by omega) h


/-! **Step 1: Reduce to Forward Maps**

    The adjacency sum `⟨f, Af⟩ = ∑_v f(v) · ∑_{w ~ v} f(w)` splits into 8 terms.
    By substitution (replacing `v` by `M⁻¹v` in the inverse-map terms), each
    `M⁻¹` term equals the corresponding `M` term. So:
    `⟨f, Af⟩ = 2 · Re[∑_v f(v) · (f(M₁v) + f(M₁v+e₁) + f(M₂v) + f(M₂v+e₂))]`

    It suffices to bound:
    `|∑_v f(v) · [f(M₁v) + f(M₁v+e₁) + f(M₂v) + f(M₂v+e₂)]| ≤ (5√2/2) · ‖f‖²`
-/

/-! **Step 2: DFT and Shift Property**

    Characters of `(Z/nZ)²`: `χ_α(v) = ω^{⟨α,v⟩}` for `α ∈ (Z/nZ)²`.
    DFT: `f̂(α) = (1/n) ∑_v f(v) · ω^{-⟨α,v⟩}`.

    DFT shift property: if `g(v) = f(Mv + b)`, then
    `ĝ(α) = ω^{⟨(M⁻¹)ᵀ α, b⟩} · f̂((M⁻¹)ᵀ α)`.

    Key identity: `|1 + ω^a| = 2|cos(πa/n)|`.

    After DFT + shift property + Parseval, the bilinear form in Fourier space is:
    `∑_{α≠0} f̂(α)* · [f̂(S₁α)(1+ω^{α₁}) + f̂(S₂α)(1+ω^{α₂})]`
    where `S₁ = M₁⁻ᵀ = [[1,0],[-2,1]]`, `S₂ = M₂⁻ᵀ = [[1,-2],[0,1]]`.
-/

/-- `|1 + ω^a| = 2|cos(πa/n)|` where `ω = exp(2πi/n)`.
    Risk: LOW — direct computation using `exp(iθ) + 1 = 2cos(θ/2)exp(iθ/2)`. -/
theorem abs_one_add_rootOfUnity (n a : ℕ) :
    2 * |cos (π * a / n)| = 2 * |cos (π * a / n)| := by
  rfl  -- placeholder for the actual complex norm identity


/-! **Step 3: Reduce to Non-Negative Function**

    Setting `G(α) = |f̂(α)| ≥ 0` and using triangle inequality + the cosine identity:
    `∑_{α≠0} G(α) · [G(T₂⁻¹α) · |cos(πα₁/n)| + G(T₁⁻¹α) · |cos(πα₂/n)|] ≤ (5√2/4) · ∑ G²(α)`

    where `T₂⁻¹ = (T₂⁻¹)ᵀ⁻¹` preserves `α₁` and `T₁⁻¹ = (T₁⁻¹)ᵀ⁻¹` preserves `α₂`.
    (Since `T₁ᵀ = T₂`, we have `(T₁⁻¹)ᵀ = T₂⁻¹`, giving the cross-pairing.)
-/


/-! **Step 4: Young's Inequality with Weight Function ψ**

    For any `ψ : (Z/nZ)² × (Z/nZ)² → ℝ₊` with `ψ(α,β) · ψ(β,α) = 1`:
    `2 · G(α) · G(β) ≤ ψ(α,β) · G(α)² + ψ(β,α) · G(β)²`

    Applying to each `G(α)G(Sᵢα)` term and substituting `α' = Sᵢα`:

    `2 · LHS ≤ ∑_α G²(α) · [|cos(πα₁/n)| · (ψ(α,S₂α) + ψ(α,S₂⁻¹α))
                             + |cos(πα₂/n)| · (ψ(α,S₁α) + ψ(α,S₁⁻¹α))]`

    (Note: `cos₁` pairs with `S₂` because `S₂` preserves `α₁`, and vice versa.)

    So the **sufficient pointwise condition** is: for all `α ∈ (Z/nZ)² \ {0}`:
    `|cos(πα₁/n)| · [ψ(α,S₂α) + ψ(α,S₂⁻¹α)]
     + |cos(πα₂/n)| · [ψ(α,S₁α) + ψ(α,S₁⁻¹α)] ≤ 5√2/2`
-/


/-- DFT bridge: the walkCLM inner product is bounded by the Fourier bilinear form.

    For mean-zero `f` and `g(x,y) = f(x·n + y)`, `G(α) = ‖dft2d n g α‖`:

    `|⟨f, Wf⟩| · 2n² ≤ ∑_α G(α)·[G(S₂α)·|cos(πα₁/n)| + G(S₁α)·|cos(πα₂/n)|]`

    Proof: chain `mgg_walkCLM_inner_eq_corr` → `corr_pair1/2` → triangle inequality
    → `norm_one_add_ω_inv`. -/
theorem mgg_dft_bridge (n : ℕ) (hn : 3 ≤ n)
    (f : EuclideanSpace ℝ (Fin (n * n)))
    :
    let g : Fin n → Fin n → ℝ := fun x y =>
      f ⟨x.val * n + y.val, by nlinarith [x.isLt, y.isLt]⟩
    let G : Fin n → Fin n → ℝ := fun α₁ α₂ => ‖dft2d n g α₁ α₂‖
    |@inner ℝ _ _ f ((mgg n).walkCLM f)| * (2 * (↑n : ℝ) ^ 2) ≤
      ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        G α₁ α₂ * (G (shearS2Fin n (by omega) (α₁, α₂)).1
                      (shearS2Fin n (by omega) (α₁, α₂)).2 *
                    |cos (↑π * ↑α₁.val / ↑n)| +
                    G (shearS1Fin n (by omega) (α₁, α₂)).1
                      (shearS1Fin n (by omega) (α₁, α₂)).2 *
                    |cos (↑π * ↑α₂.val / ↑n)|) := by
  intro g G
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn0 : 0 < n := by omega
  -- Abbreviate the correlation sums
  set C₁ := ∑ x : Fin n, ∑ y : Fin n,
    g x y * (g ⟨(x.val + 2 * y.val) % n, Nat.mod_lt _ hn0⟩ y +
             g ⟨(x.val + 2 * y.val + 1) % n, Nat.mod_lt _ hn0⟩ y)
  set C₂ := ∑ x : Fin n, ∑ y : Fin n,
    g x y * (g x ⟨(2 * x.val + y.val) % n, Nat.mod_lt _ hn0⟩ +
             g x ⟨(2 * x.val + y.val + 1) % n, Nat.mod_lt _ hn0⟩)
  -- Step 1: Walk operator expansion: 4*inner = C₁ + C₂
  have hcorr := mgg_walkCLM_inner_eq_corr n hn f
  -- Step 2: DFT of correlation sums (from corr_pair1/2, complex-valued)
  have hF₁ := corr_pair1 n (by omega) g hn
  have hF₂ := corr_pair2 n (by omega) g hn
  -- Abbreviate the Fourier sums
  set F₁ := ∑ α₁ : Fin n, ∑ α₂ : Fin n,
    dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g α₁
      ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn0⟩) *
    (1 + ω n ^ (-(α₁.val : ℤ)))
  set F₂ := ∑ α₁ : Fin n, ∑ α₂ : Fin n,
    dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g
      ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn0⟩ α₂) *
    (1 + ω n ^ (-(α₂.val : ℤ)))
  -- hF₁ : (↑n)² * ↑C₁ = F₁, hF₂ : (↑n)² * ↑C₂ = F₂
  -- Step 3: |inner| * 2n² = |C₁+C₂|/4 * 2n² = |C₁+C₂| * n²/2
  -- From hcorr: 4*inner = C₁+C₂ → inner = (C₁+C₂)/4
  have h_inner : @inner ℝ _ _ f ((mgg n).walkCLM f) = (C₁ + C₂) / 4 := by
    linarith
  rw [h_inner, abs_div, show |(4:ℝ)| = 4 from by norm_num]
  -- Goal: |C₁+C₂|/4 * (2*n²) ≤ RHS
  -- Simplify: |C₁+C₂|/4 * 2*n² = |C₁+C₂| * n²/2
  rw [div_mul_eq_mul_div]
  -- Goal: |C₁+C₂| * (2*n²) / 4 ≤ RHS
  -- |C₁+C₂| * n² ≤ |n²*C₁| + |n²*C₂|
  -- Since n²*(C₁+C₂) = Re(F₁) + Re(F₂) = Re(F₁+F₂)
  -- We need: |C₁+C₂| * (2*n²) / 4 = |C₁+C₂| * n² / 2
  have h4 : |C₁ + C₂| * (2 * (↑n : ℝ) ^ 2) / 4 = |C₁ + C₂| * (↑n : ℝ) ^ 2 / 2 := by ring
  rw [h4]
  -- Now bound |C₁+C₂| * n²/2
  -- n²*C₁ = Re(F₁) in ℝ: extract from the complex equality
  have h_re_cast : ((↑n : ℂ) ^ 2).re = (↑n : ℝ) ^ 2 := by norm_cast
  have h_C₁_re : (↑n : ℝ) ^ 2 * C₁ = (F₁).re := by
    have := congr_arg Complex.re hF₁
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at this
    rw [h_re_cast] at this; exact this
  have h_C₂_re : (↑n : ℝ) ^ 2 * C₂ = (F₂).re := by
    have := congr_arg Complex.re hF₂
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at this
    rw [h_re_cast] at this; exact this
  -- |C₁+C₂|*n²/2 = |n²*C₁ + n²*C₂|/2 = |Re(F₁) + Re(F₂)|/2
  have h_sum : |C₁ + C₂| * (↑n : ℝ) ^ 2 = |F₁.re + F₂.re| := by
    have h_nn : (0 : ℝ) ≤ (↑n : ℝ) ^ 2 := by positivity
    rw [mul_comm, ← abs_of_nonneg h_nn, ← abs_mul, mul_add, h_C₁_re, h_C₂_re]
  rw [h_sum]
  -- |Re(F₁) + Re(F₂)|/2 ≤ (‖F₁‖ + ‖F₂‖)/2  [|Re z| ≤ ‖z‖]
  -- ≤ (∑|term₁| + ∑|term₂|)/2  [triangle inequality on sums]
  -- Each |term| = G*G∘S*‖1+ω‖ = G*G∘S*2|cos|  [norm_one_add_ω_inv]
  -- So ≤ (2*∑G*G∘S₂*|cos₁| + 2*∑G*G∘S₁*|cos₂|)/2
  -- = ∑G*(G∘S₂*|cos₁| + G∘S₁*|cos₂|)
  -- Bound |Re(F₁)+Re(F₂)| ≤ |Re(F₁)| + |Re(F₂)| ≤ ‖F₁‖ + ‖F₂‖
  have hre_le : |F₁.re + F₂.re| / 2 ≤ (‖F₁‖ + ‖F₂‖) / 2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) < 2).le
    calc |F₁.re + F₂.re| ≤ |F₁.re| + |F₂.re| := abs_add_le _ _
      _ ≤ ‖F₁‖ + ‖F₂‖ := add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
  -- Bound ‖F_j‖ ≤ ∑‖term_j‖ (triangle inequality on sums)
  have hF₁_tri : ‖F₁‖ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * G α₁ ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn0⟩ *
      ‖(1 : ℂ) + ω n ^ (-(α₁.val : ℤ))‖ := by
    calc ‖F₁‖ ≤ ∑ α₁ : Fin n, ‖∑ α₂ : Fin n,
        dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g α₁
          ⟨(α₂.val + n - (2 * α₁.val) % n) % n, _⟩) *
        (1 + ω n ^ (-(α₁.val : ℤ)))‖ := norm_sum_le _ _
      _ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        ‖dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g α₁
          ⟨(α₂.val + n - (2 * α₁.val) % n) % n, _⟩) *
        (1 + ω n ^ (-(α₁.val : ℤ)))‖ := by
        gcongr with α₁; exact norm_sum_le _ _
      _ = _ := by
        congr 1; ext α₁; congr 1; ext α₂
        rw [norm_mul, norm_mul, Complex.norm_conj]
  have hF₂_tri : ‖F₂‖ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * G ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn0⟩ α₂ *
      ‖(1 : ℂ) + ω n ^ (-(α₂.val : ℤ))‖ := by
    calc ‖F₂‖ ≤ ∑ α₁ : Fin n, ‖∑ α₂ : Fin n,
        dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g
          ⟨(α₁.val + n - (2 * α₂.val) % n) % n, _⟩ α₂) *
        (1 + ω n ^ (-(α₂.val : ℤ)))‖ := norm_sum_le _ _
      _ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        ‖dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g
          ⟨(α₁.val + n - (2 * α₂.val) % n) % n, _⟩ α₂) *
        (1 + ω n ^ (-(α₂.val : ℤ)))‖ := by
        gcongr with α₁; exact norm_sum_le _ _
      _ = _ := by
        congr 1; ext α₁; congr 1; ext α₂
        rw [norm_mul, norm_mul, Complex.norm_conj]
  -- Apply norm_one_add_ω_inv: ‖1+ω^{-a}‖ = 2*|cos(πa/n)|
  simp_rw [norm_one_add_ω_inv n (by omega)] at hF₁_tri hF₂_tri
  -- Chain everything
  calc |F₁.re + F₂.re| / 2
      ≤ (‖F₁‖ + ‖F₂‖) / 2 := hre_le
    _ ≤ ((∑ α₁, ∑ α₂, G α₁ α₂ * G α₁ ⟨(α₂.val + n - (2 * α₁.val) % n) % n, _⟩ *
            (2 * |cos (↑π * ↑α₁.val / ↑n)|)) +
         (∑ α₁, ∑ α₂, G α₁ α₂ * G ⟨(α₁.val + n - (2 * α₂.val) % n) % n, _⟩ α₂ *
            (2 * |cos (↑π * ↑α₂.val / ↑n)|))) / 2 := by
        gcongr
    _ = ∑ α₁, ∑ α₂, G α₁ α₂ *
          (G (shearS2Fin n hn0 (α₁, α₂)).1 (shearS2Fin n hn0 (α₁, α₂)).2 *
            |cos (↑π * ↑α₁.val / ↑n)| +
           G (shearS1Fin n hn0 (α₁, α₂)).1 (shearS1Fin n hn0 (α₁, α₂)).2 *
            |cos (↑π * ↑α₂.val / ↑n)|) := by
      -- Factor out 2/2 = 1 and combine sums
      rw [div_eq_iff (show (2:ℝ) ≠ 0 by norm_num)]
      rw [← Finset.sum_add_distrib]
      simp_rw [← Finset.sum_add_distrib]
      conv_rhs => rw [Finset.sum_mul]; arg 2; ext; rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro α₁ _
      apply Finset.sum_congr rfl; intro α₂ _
      simp only [shearS2Fin, shearS1Fin]
      ring

/-- The adjacency eigenvalue bound: for mean-zero `f` with `‖f‖ = 1`,
    `|⟨f, Wf⟩| ≤ 5√2/8` where `W = A/8` is the normalized walk operator.

    Combines:
    - `mgg_dft_bridge`: `|⟨f,Wf⟩| · 2n² ≤ ∑ G·[G∘S₂·cos₁ + G∘S₁·cos₂]`
    - `young_assembly`: `∑ G·[...] ≤ (5√2/4)·∑ G²`
    - `parseval_2d`: `∑ ‖ĝ‖² = n²·∑ g²` and `∑ g² = ‖f‖² = 1`
    - Constants: `(5√2/4)·n² / (2n²) = 5√2/8` -/
theorem mgg_rayleigh_bound (n : ℕ) (hn : 3 ≤ n)
    (f : EuclideanSpace ℝ (Fin (n * n)))
    (horth : @inner ℝ _ _ f (meanCLM (n * n) f) = 0)
    (hnorm : ‖f‖ = 1) :
    |@inner ℝ _ _ f ((mgg n).walkCLM f)| ≤ 5 * √2 / 8 := by
  -- Setup: define g (reindexed f) and G (DFT magnitudes)
  set g : Fin n → Fin n → ℝ := fun x y =>
    f ⟨x.val * n + y.val, by nlinarith [x.isLt, y.isLt]⟩ with hg_def
  set G : Fin n → Fin n → ℝ := fun α₁ α₂ => ‖dft2d n g α₁ α₂‖ with hG_def
  -- G is nonneg (norms are nonneg)
  have hG : ∀ i j, 0 ≤ G i j := fun i j => norm_nonneg _
  -- Extract ∑ f = 0 from the orthogonality condition
  have hsum_f : ∑ v : Fin (n * n), f v = 0 := by
    have h0 : @inner ℝ _ _ f (meanCLM (n * n) f) =
        ∑ v : Fin (n * n), f v * ((∑ w : Fin (n * n), f w) / ↑(n * n)) := by
      rw [PiLp.inner_apply]
      simp_rw [show ∀ (a b : ℝ), @inner ℝ ℝ _ a b = b * a from fun a b => by
        show RCLike.re (b * starRingEnd ℝ a) = b * a
        simp only [RCLike.conj_to_real, RCLike.re_to_real]]
      simp [meanCLM_apply, mul_comm]
    rw [h0] at horth
    set S := ∑ v : Fin (n * n), f v
    have h1 : S * (S / ↑(n * n)) = 0 := by
      convert horth using 1; rw [← Finset.sum_mul]
    have hnn : (0 : ℝ) < ↑(n * n) := Nat.cast_pos.mpr (by positivity)
    have h2 : S ^ 2 / ↑(n * n) = 0 := by
      linarith [show S * (S / ↑(n * n)) = S ^ 2 / ↑(n * n) from by ring]
    rcases div_eq_zero_iff.mp h2 with h3 | h3
    · exact sq_eq_zero_iff.mp h3
    · linarith
  -- Reindexing: ∑ g = ∑ f (bijection (x,y) ↦ x*n+y)
  have hsum_g : ∑ x : Fin n, ∑ y : Fin n, g x y = ∑ v : Fin (n * n), f v := by
    rw [← Fintype.sum_prod_type']
    rw [← finProdFinEquiv.sum_comp (fun v => f v)]
    congr 1; ext ⟨x, y⟩
    show g x y = f.ofLp (finProdFinEquiv (x, y))
    have : finProdFinEquiv (x, y) = ⟨x.val * n + y.val, by nlinarith [x.isLt, y.isLt]⟩ :=
      Fin.ext (by show _ = x.val * n + y.val; unfold finProdFinEquiv; simp; ring)
    rw [this]
  -- G(0,0) = 0 (from mean-zero condition)
  have hG0 : G ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
    show ‖dft2d n g ⟨0, _⟩ ⟨0, _⟩‖ = 0
    rw [norm_eq_zero, dft2d_zero n g (by omega)]
    exact_mod_cast (hsum_g ▸ hsum_f)
  -- Step 1: DFT bridge
  have h_bridge := mgg_dft_bridge n hn f
  -- Step 2: Young's assembly
  have h_young := young_assembly n hn G hG0
  -- Step 3: Chain the inequalities
  have h_chain : |@inner ℝ _ _ f ((mgg n).walkCLM f)| * (2 * (↑n : ℝ) ^ 2) ≤
      5 * √2 / 4 * ∑ α₁ : Fin n, ∑ α₂ : Fin n, G α₁ α₂ ^ 2 :=
    h_bridge.trans h_young
  -- Step 4: G² = Complex.normSq (Parseval compatibility)
  have hG2 : ∑ α₁ : Fin n, ∑ α₂ : Fin n, G α₁ α₂ ^ 2 =
      ∑ α₁ : Fin n, ∑ α₂ : Fin n, Complex.normSq (dft2d n g α₁ α₂) := by
    congr 1; ext α₁; congr 1; ext α₂
    exact Complex.sq_norm (dft2d n g α₁ α₂)
  -- Step 5: Parseval's identity
  rw [hG2, parseval_2d n (by omega) g] at h_chain
  -- Step 6: ∑ g² = ‖f‖² = 1
  have hg_sq : ∑ v₁ : Fin n, ∑ v₂ : Fin n, (g v₁ v₂ : ℝ) ^ 2 = 1 := by
    have h_reindex : ∑ x : Fin n, ∑ y : Fin n, (g x y) ^ 2 =
        ∑ v : Fin (n * n), (f v) ^ 2 := by
      rw [← Fintype.sum_prod_type']
      rw [← finProdFinEquiv.sum_comp (fun v => (f v) ^ 2)]
      congr 1; ext ⟨x, y⟩
      have heq : finProdFinEquiv (x, y) =
          (⟨x.val * n + y.val, by nlinarith [x.isLt, y.isLt]⟩ : Fin (n * n)) :=
        Fin.ext (by show _ = x.val * n + y.val; unfold finProdFinEquiv; simp; ring)
      rw [heq]
    rw [h_reindex]
    have h_norm : ‖f‖ ^ 2 = ∑ v : Fin (n * n), (f v) ^ 2 := by
      rw [sq, ← real_inner_self_eq_norm_mul_norm, PiLp.inner_apply]; simp [sq]
    linarith [show ‖f‖ ^ 2 = 1 from by rw [hnorm]; norm_num]
  -- Step 7: Arithmetic: |inner| * 2n² ≤ (5√2/4) * (n² * 1) = (5√2/8) * (2n²)
  rw [hg_sq, mul_one] at h_chain
  -- h_chain : |inner| * (2 * n²) ≤ (5√2/4) * n²
  have h2n2 : (0 : ℝ) < 2 * (↑n : ℝ) ^ 2 := by positivity
  -- Rewrite RHS: (5√2/4) * n² = (5√2/8) * (2 * n²)
  have h_arith : 5 * √2 / 4 * (↑n : ℝ) ^ 2 = 5 * √2 / 8 * (2 * (↑n : ℝ) ^ 2) := by ring
  rw [h_arith] at h_chain
  exact le_of_mul_le_mul_right h_chain h2n2

/-- The MGG graph on `(Z/nZ)²` has spectral gap at most `5√2/8`.
    This is the Gabber-Galil (1981) / Jimbo-Maruoka (1987) bound,
    simplified by Boppana. See `docs/jimbo-maruoka.md` for proof plan. -/
theorem spectralGap_mgg (n : ℕ) (hn : 3 ≤ n) :
    spectralGap (mgg n) ≤ 5 * √2 / 8 := by
  apply mgg_spectralGap_of_rayleigh_bound n _ (by positivity)
  exact fun f horth hnorm => mgg_rayleigh_bound n hn f horth hnorm

end


