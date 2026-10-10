-- Prove2me | solution 1 for ArtinPrimitiveRoots.minor_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:45:49.904763+00:00
-- url     : https://prove2.me/submissions/3e59aabe-9ba2-49a7-a72a-1b74df4f509d

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare
import Theorems.Thm_ArtinPrimitiveRoots_re_dyadMoment_le
import Theorems.Thm_ArtinPrimitiveRoots_norm_dyadPairingSTS_sub_dyadPairingA_le
import Theorems.Thm_ArtinPrimitiveRoots_norm_minorSquare_sub_sum_dyadPairingSTS_le

section
/-! # L102D_OpDefs — alias of the bundle `Def_ArtinMinorOperator` (round 5)

The operator model now lives in `Definitions/Def_ArtinMinorOperator.lean` (same declarations, same
names). This module re-exports it and keeps `listProd`, which only the proofs use. -/

namespace ArtinPrimitiveRoots

/-- The product of all labels of a list. -/
def listProd {K J : ℕ} (ℓ : Fin K → Fin (J + 1) → ℕ) : ℕ := ∏ i, ∏ j, ℓ i j

end ArtinPrimitiveRoots
end

section
/-! # L102D: the cuts of D1c (`minor_square_bound`) and the reduction

Four statements about the operator model of `L102D_OpDefs` (draft bundle
`Def_ArtinMinorOperator`):

* `MomentBoundStmt` (D7, [21] (3.19)/(4.1)): the moment of `(AA*)^R` is `≤ UV L^{-E₀ N}`;
* `PairingFromMomentStmt` (D5, [21] (3.20)): the pairing `⟨f, A f⟩_σ` is controlled by the moment;
* `GoodnessRemovalStmt` (D8a, [21] (4.56)–(4.57)): removing `G` from the pairing costs `UV L^{-A}`;
* `PadLiftStmt` (D8bc, [21] (4.58)–(4.63)): `Q^min = ∑_{dyads} d₀⁻¹ ⟨f, S T S f⟩_σ + O(XY L^{-A})`.

`minor_square_bound_of_cuts` proves the D1c statement from the four. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-- **D7** ([21] Prop. 4.1, (4.1)): for every `E₀` one can choose `A₀`, then `K₀`, so that at every
dyad `d₀ = 2^k` the moment is `≤ U V L^{-E₀ N}`, `U = d₀ Y H_m`, `V = H_n`, `N = 2R`. -/
def MomentBoundStmt (δ c₁ c₂ : ℝ) : Prop :=
  ∀ E₀ : ℝ, 0 < E₀ → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
        (dyadMoment x a A₀ Y Hm Hn k).re ≤
          2 ^ k * Y * Hm * Hn * log x ^ (-(E₀ * (2 * momentPower x)))

/-- **D5** ([21] §3.3, (3.20)): the pairing with `A` is bounded through the moment. -/
def PairingFromMomentStmt (δ C c₁ c₂ : ℝ) : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
      ∀ α β : ℕ → ℂ,
        (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
          ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
        (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
        (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
        ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ, ∀ E₀ : ℝ, 0 ≤ E₀ →
          (dyadMoment x a A₀ Y Hm Hn k).re ≤
            2 ^ k * Y * Hm * Hn * log x ^ (-(E₀ * (2 * momentPower x))) →
          ‖dyadPairingA x a A₀ Y Hm Hn α β k‖ ≤
            c * (2 ^ k * Y * Hm * Hn * log x ^ (4 * C + 1 - E₀))

/-- **D8a** ([21] §4.9, (4.56)–(4.57)): removing the goodness projections from the pairing. -/
def GoodnessRemovalStmt (δ C c₁ c₂ : ℝ) : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∀ A : ℝ, 0 < A →
    ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
      ∀ α β : ℕ → ℂ,
        (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
          ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
        (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
        (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
        ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          ‖dyadPairingSTS x a A₀ Y Hm Hn α β k - dyadPairingA x a A₀ Y Hm Hn α β k‖ ≤
            c * (2 ^ k * Y * Hm * Hn * log x ^ (-A))

/-- **D8bc** ([21] §4.9, (4.58)–(4.63)): the pads are independent harmonic draws, so the dyadic
sum of the unprojected pairings reproduces `Q^min` up to pad collisions. -/
def PadLiftStmt (δ C c₁ c₂ : ℝ) : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∀ A : ℝ, 0 < A →
    ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
      ∀ α β : ℕ → ℂ,
        (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
          ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
        (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
        (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
        ∀ Y : ℝ, 1 ≤ Y →
          ‖minorSquare x a A₀ Y Hm Hn α β - ∑ k ∈ range (⌊log x⌋₊ + 1),
              ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k‖ ≤
            c * (Hm * Hn * Y * log x ^ (-A))

/-- **D1c from the four cuts.** -/
theorem minor_square_bound_of_cuts (δ C c₁ c₂ : ℝ) (hC : 0 < C)
    (hM : MomentBoundStmt δ c₁ c₂) (hP : PairingFromMomentStmt δ C c₁ c₂)
    (hG : GoodnessRemovalStmt δ C c₁ c₂) (hL : PadLiftStmt δ C c₁ c₂) :
    ∀ A : ℝ, 0 < A → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y →
            ‖minorSquare x a A₀ Y Hm Hn α β‖ ≤ c * (Hm * Hn * Y * log x ^ (-A)) := by
  intro A hA
  set E₀ := A + 4 * C + 3 with hE₀
  have hE₀pos : 0 < E₀ := by positivity
  obtain ⟨A₀, hA₀, K₀, hmom⟩ := hM E₀ hE₀pos
  refine ⟨A₀, hA₀, K₀, fun K hK hKK a ha hab => ?_⟩
  obtain ⟨x₁, hx₁⟩ := hmom K hK hKK a ha hab
  obtain ⟨c₂', x₂, hx₂⟩ := hL A₀ hA₀ K hK a ha hab A hA
  obtain ⟨c₃, x₃, hx₃⟩ := hG A₀ hA₀ K hK a ha hab (A + 2) (by linarith)
  obtain ⟨c₄, x₄, hx₄⟩ := hP A₀ hA₀ K hK a ha hab
  refine ⟨|c₂'| + |c₃| + |c₄|, max (max (max x₁ x₂) (max x₃ x₄)) (exp 2),
    fun x Hm Hn hx hm hn h1 h2 α β hαs hβs hαb hβb Y hY => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_of_max_le_left hx)
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_of_max_le_left hx)
  have hx3 : x₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_of_max_le_left hx)
  have hx4 : x₄ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_of_max_le_left hx)
  have hx5 : exp 2 ≤ x := le_of_max_le_right hx
  have hxpos : 0 < x := lt_of_lt_of_le (exp_pos _) hx5
  have hL2 : 2 ≤ log x := (Real.le_log_iff_exp_le hxpos).2 hx5
  have hL0 : 0 < log x := by linarith
  have hHm : 0 < Hm := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hm
  have hHn : 0 < Hn := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hn
  have hY0 : 0 < Y := by linarith
  set X := Hm * Hn * Y * log x ^ (-A) with hX
  have hX0 : 0 ≤ X := by positivity
  -- the per-dyad bound
  have hdyad : ∀ k : ℕ, ‖((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k‖ ≤
      (|c₃| + |c₄|) * (Hm * Hn * Y * log x ^ (-A - 2)) := by
    intro k
    have hG' := hx₃ x Hm Hn hx3 hm hn h1 h2 α β hαs hβs hαb hβb Y hY k
    have hmk := hx₁ x Hm Hn hx1 hm hn h1 h2 Y hY k
    have hP' := hx₄ x Hm Hn hx4 hm hn h1 h2 α β hαs hβs hαb hβb Y hY k E₀ hE₀pos.le hmk
    have he : 4 * C + 1 - E₀ = -A - 2 := by rw [hE₀]; ring
    rw [he] at hP'
    have hk : (0 : ℝ) < 2 ^ k := by positivity
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
    have htri : ‖dyadPairingSTS x a A₀ Y Hm Hn α β k‖ ≤
        ‖dyadPairingSTS x a A₀ Y Hm Hn α β k - dyadPairingA x a A₀ Y Hm Hn α β k‖ +
          ‖dyadPairingA x a A₀ Y Hm Hn α β k‖ := norm_le_norm_sub_add _ _
    have hpos : 0 ≤ 2 ^ k * Y * Hm * Hn * log x ^ (-A - 2) := by positivity
    have hG'' : ‖dyadPairingSTS x a A₀ Y Hm Hn α β k - dyadPairingA x a A₀ Y Hm Hn α β k‖ ≤
        |c₃| * (2 ^ k * Y * Hm * Hn * log x ^ (-A - 2)) := by
      rw [show -(A + 2) = -A - 2 by ring] at hG'
      exact hG'.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpos)
    have hP'' : ‖dyadPairingA x a A₀ Y Hm Hn α β k‖ ≤
        |c₄| * (2 ^ k * Y * Hm * Hn * log x ^ (-A - 2)) :=
      hP'.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpos)
    calc ((2 : ℝ) ^ k)⁻¹ * ‖dyadPairingSTS x a A₀ Y Hm Hn α β k‖
        ≤ ((2 : ℝ) ^ k)⁻¹ * ((|c₃| + |c₄|) * (2 ^ k * Y * Hm * Hn * log x ^ (-A - 2))) := by
          gcongr; linarith
      _ = (|c₃| + |c₄|) * (Hm * Hn * Y * log x ^ (-A - 2)) := by field_simp
  have hsum : ‖∑ k ∈ range (⌊log x⌋₊ + 1), ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k‖
      ≤ (|c₃| + |c₄|) * X := by
    refine (norm_sum_le _ _).trans ((sum_le_sum fun k _ => hdyad k).trans ?_)
    rw [sum_const, card_range, nsmul_eq_mul]
    have hcount : ((⌊log x⌋₊ + 1 : ℕ) : ℝ) ≤ log x ^ (2 : ℝ) := by
      push_cast
      have := Nat.floor_le hL0.le
      rw [Real.rpow_two]; nlinarith
    have hpow : log x ^ (2 : ℝ) * log x ^ (-A - 2) = log x ^ (-A) := by
      rw [← Real.rpow_add hL0]; ring_nf
    have hc0 : 0 ≤ |c₃| + |c₄| := by positivity
    calc ((⌊log x⌋₊ + 1 : ℕ) : ℝ) * ((|c₃| + |c₄|) * (Hm * Hn * Y * log x ^ (-A - 2)))
        ≤ log x ^ (2 : ℝ) * ((|c₃| + |c₄|) * (Hm * Hn * Y * log x ^ (-A - 2))) := by
          gcongr
      _ = (|c₃| + |c₄|) * X := by rw [hX, ← hpow]; ring
  have hlift := hx₂ x Hm Hn hx2 hm hn h1 h2 α β hαs hβs hαb hβb Y hY
  have hlift' : ‖minorSquare x a A₀ Y Hm Hn α β - ∑ k ∈ range (⌊log x⌋₊ + 1),
      ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k‖ ≤ |c₂'| * X :=
    hlift.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
  calc ‖minorSquare x a A₀ Y Hm Hn α β‖
      ≤ ‖minorSquare x a A₀ Y Hm Hn α β - ∑ k ∈ range (⌊log x⌋₊ + 1),
          ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k‖ +
        ‖∑ k ∈ range (⌊log x⌋₊ + 1), ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k‖ :=
        norm_le_norm_sub_add _ _
    _ ≤ |c₂'| * X + (|c₃| + |c₄|) * X := add_le_add hlift' hsum
    _ = (|c₂'| + |c₃| + |c₄|) * X := by ring

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the spectral Hölder step of [21] §3.3, (3.20), in abstract form

For a finite-dimensional complex inner product space `E`, an operator `A` and `B = A A†`:

* `re_inner_pow_eq_sum`: `re ⟪v, Tᵏ v⟫ = ∑ λᵢᵏ ‖cᵢ‖²` in an eigenbasis of a symmetric `T`;
* `re_inner_le_pow` (spectral Hölder): `re ⟪f, B f⟫ ≤ ‖f‖^{2(1-1/R)} (re ⟪f, Bᴿ f⟫)^{1/R}`
  for a positive symmetric `B`;
* `norm_inner_apply_le_moment`: `‖⟪f, A g⟫‖ ≤ ‖g‖ ‖f‖^{1-1/R} (re ⟪f, (A A†)ᴿ f⟫)^{1/(2R)}`;
* `re_inner_sum_le_trace` (largest eigenvalue ≤ trace): for `f = ∑ cₚ uₚ` and a positive `C`,
  `re ⟪f, C f⟫ ≤ (∑ |cₚ|²) (∑ re ⟪uₚ, C uₚ⟫)`;
* `norm_sum_inner_le_moment` (the localized Hölder step): for blocks `j`,
  `‖∑ⱼ ⟪fⱼ, A gⱼ⟫‖ ≤ (∑ ‖gⱼ‖²)^{1/2} (∑ ‖fⱼ‖²)^{(1-1/R)/2} (∑ⱼ re ⟪fⱼ, (A A†)ᴿ fⱼ⟫)^{1/(2R)}`.

These are exactly the inequalities used between (3.19) and (3.20) of [21]; the concrete inputs
(the slope-interval partition with `O(H)` primitive positions per interval, and the norm bounds
(3.18)) are separate. -/

namespace ArtinPrimitiveRoots.L102D

open RCLike Finset
open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Coordinates of `Tᵏ v` in an eigenbasis of a symmetric `T`. -/
lemma repr_pow_apply {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℂ E = n) (k : ℕ) (v : E) (i : Fin n) :
    (hT.eigenvectorBasis hn).repr ((T ^ k) v) i =
      ((hT.eigenvalues hn i : ℂ)) ^ k * (hT.eigenvectorBasis hn).repr v i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, hT.eigenvectorBasis_apply_self_apply hn, ih, pow_succ',
      mul_assoc]
    rfl

/-- The quadratic form of `Tᵏ` in an eigenbasis of a symmetric `T`. -/
lemma re_inner_pow_eq_sum {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℂ E = n) (k : ℕ) (v : E) :
    re ⟪v, (T ^ k) v⟫_ℂ =
      ∑ i, (hT.eigenvalues hn i) ^ k * ‖(hT.eigenvectorBasis hn).repr v i‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn
  rw [← b.repr.inner_map_map, PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_pow_apply hT hn k v i]
  simp only [RCLike.inner_apply, RCLike.re_to_complex, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im, b]
  ring

/-- Eigenvalues of a positive symmetric operator are nonnegative. -/
lemma eigenvalues_nonneg {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, 0 ≤ re ⟪x, T x⟫_ℂ) {n : ℕ} (hn : Module.finrank ℂ E = n) (i : Fin n) :
    0 ≤ hT.eigenvalues hn i :=
  eigenvalue_nonneg_of_nonneg (hT.hasEigenvalue_eigenvalues hn i) hpos

omit [FiniteDimensional ℂ E] in
lemma norm_sq_eq_sum_repr {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ E) (v : E) :
    ‖v‖ ^ 2 = ∑ i, ‖b.repr v i‖ ^ 2 := by
  rw [← b.repr.norm_map, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-- **Spectral Hölder.** For a positive symmetric `B` and `R ≥ 1`,
`re ⟪f, B f⟫ ≤ ‖f‖^{2(1-1/R)} (re ⟪f, Bᴿ f⟫)^{1/R}`. -/
theorem re_inner_le_pow {B : E →ₗ[ℂ] E} (hB : B.IsSymmetric) (hpos : ∀ x, 0 ≤ re ⟪x, B x⟫_ℂ)
    (R : ℕ) (hR : 1 ≤ R) (f : E) :
    re ⟪f, B f⟫_ℂ ≤ (‖f‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) * (re ⟪f, (B ^ R) f⟫_ℂ) ^ (R : ℝ)⁻¹ := by
  set n := Module.finrank ℂ E
  have hn : Module.finrank ℂ E = n := rfl
  set b := hB.eigenvectorBasis hn
  set w : Fin n → ℝ := fun i => ‖b.repr f i‖ ^ 2
  set lam : Fin n → ℝ := fun i => hB.eigenvalues hn i
  have h1 : re ⟪f, B f⟫_ℂ = ∑ i, w i * lam i := by
    have := re_inner_pow_eq_sum hB hn 1 f
    simp only [pow_one] at this
    rw [this]; exact Finset.sum_congr rfl fun i _ => by simp [w, lam, b, mul_comm]
  have hR' : re ⟪f, (B ^ R) f⟫_ℂ = ∑ i, w i * lam i ^ (R : ℝ) := by
    rw [re_inner_pow_eq_sum hB hn R f]
    exact Finset.sum_congr rfl fun i _ => by simp [w, lam, b, mul_comm, Real.rpow_natCast]
  have hf : ‖f‖ ^ 2 = ∑ i, w i := norm_sq_eq_sum_repr b f
  rw [h1, hR', hf]
  exact Real.inner_le_weight_mul_Lp_of_nonneg _ (by exact_mod_cast hR) w lam
    (fun i => by positivity) (fun i => eigenvalues_nonneg hB hpos hn i)

/-- `A A†` is symmetric. -/
lemma isSymmetric_mul_adjoint (A : E →ₗ[ℂ] E) : (A * LinearMap.adjoint A).IsSymmetric := by
  intro x y
  simp only [Module.End.mul_apply]
  rw [← LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_left]

/-- `A A†` is positive. -/
lemma re_inner_mul_adjoint_nonneg (A : E →ₗ[ℂ] E) (x : E) :
    0 ≤ re ⟪x, (A * LinearMap.adjoint A) x⟫_ℂ := by
  rw [Module.End.mul_apply, ← LinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
  positivity

lemma re_inner_pow_nonneg {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, 0 ≤ re ⟪x, T x⟫_ℂ) (k : ℕ) (x : E) : 0 ≤ re ⟪x, (T ^ k) x⟫_ℂ := by
  rw [re_inner_pow_eq_sum hT rfl k x]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (pow_nonneg (eigenvalues_nonneg hT hpos rfl i) _) (by positivity)

/-- **The pairing bound from the moment.** With `B = A A†` and `R ≥ 1`,
`‖⟪f, A g⟫‖ ≤ ‖g‖ ‖f‖^{1-1/R} (re ⟪f, Bᴿ f⟫)^{1/(2R)}`. -/
theorem norm_inner_apply_le_moment (A : E →ₗ[ℂ] E) (R : ℕ) (hR : 1 ≤ R) (f g : E) :
    ‖⟪f, A g⟫_ℂ‖ ≤ ‖g‖ * (‖f‖ ^ 2) ^ ((1 - (R : ℝ)⁻¹) / 2) *
      (re ⟪f, ((A * LinearMap.adjoint A) ^ R) f⟫_ℂ) ^ ((R : ℝ)⁻¹ / 2) := by
  set B := A * LinearMap.adjoint A
  have hB := isSymmetric_mul_adjoint A
  have hpos := re_inner_mul_adjoint_nonneg A
  have key : ‖LinearMap.adjoint A f‖ ^ 2 = re ⟪f, B f⟫_ℂ := by
    rw [Module.End.mul_apply, ← LinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
  have hsp := re_inner_le_pow hB hpos R hR f
  have hR0 := re_inner_pow_nonneg hB hpos R f
  have hnorm : ‖LinearMap.adjoint A f‖ ≤
      (‖f‖ ^ 2) ^ ((1 - (R : ℝ)⁻¹) / 2) * (re ⟪f, (B ^ R) f⟫_ℂ) ^ ((R : ℝ)⁻¹ / 2) := by
    have h0 : 0 ≤ (‖f‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) * (re ⟪f, (B ^ R) f⟫_ℂ) ^ (R : ℝ)⁻¹ := by
      positivity
    have := Real.sqrt_le_sqrt (key ▸ hsp)
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_eq_rpow, Real.mul_rpow (by positivity)
      (by positivity), ← Real.rpow_mul (by positivity), ← Real.rpow_mul hR0] at this
    convert this using 3 <;> ring
  calc ‖⟪f, A g⟫_ℂ‖ = ‖⟪LinearMap.adjoint A f, g⟫_ℂ‖ := by
        rw [LinearMap.adjoint_inner_left]
    _ ≤ ‖LinearMap.adjoint A f‖ * ‖g‖ := norm_inner_le_norm _ _
    _ ≤ _ := by
        rw [mul_comm ‖g‖, mul_assoc]
        exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _) |>.trans_eq (by ring)

/-- **Largest eigenvalue ≤ trace.** For a positive symmetric `B`, a power `k`, and
`f = ∑ₚ cₚ uₚ`, `re ⟪f, Bᵏ f⟫ ≤ (∑ ‖cₚ‖²) · ∑ₚ re ⟪uₚ, Bᵏ uₚ⟫`. This is (3.21) of [21]: the
matrix `⟪uₚ, Bᵏ u_q⟫` is positive semidefinite, so its quadratic form is at most its trace. -/
theorem re_inner_pow_sum_le_trace {B : E →ₗ[ℂ] E} (hB : B.IsSymmetric)
    (hpos : ∀ x, 0 ≤ re ⟪x, B x⟫_ℂ) (k : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (u : ι → E) :
    re ⟪∑ p ∈ s, c p • u p, (B ^ k) (∑ p ∈ s, c p • u p)⟫_ℂ ≤
      (∑ p ∈ s, ‖c p‖ ^ 2) * ∑ p ∈ s, re ⟪u p, (B ^ k) (u p)⟫_ℂ := by
  set n := Module.finrank ℂ E
  have hn : Module.finrank ℂ E = n := rfl
  set b := hB.eigenvectorBasis hn
  have hl : ∀ i, 0 ≤ hB.eigenvalues hn i ^ k := fun i =>
    pow_nonneg (eigenvalues_nonneg hB hpos hn i) k
  rw [re_inner_pow_eq_sum hB hn k]
  simp_rw [re_inner_pow_eq_sum hB hn k, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (hl i)
  have hrepr : b.repr (∑ p ∈ s, c p • u p) i = ∑ p ∈ s, c p * b.repr (u p) i := by
    simp [map_sum, map_smul]
  rw [hrepr]
  calc ‖∑ p ∈ s, c p * b.repr (u p) i‖ ^ 2
      ≤ (∑ p ∈ s, ‖c p‖ * ‖b.repr (u p) i‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    _ ≤ (∑ p ∈ s, ‖c p‖ ^ 2) * ∑ p ∈ s, ‖b.repr (u p) i‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- **The localized spectral Hölder step of (3.20).** For blocks `j ∈ s` with vectors
`fⱼ, gⱼ`, `B = A A†` and `R ≥ 2`,
`‖∑ⱼ ⟪fⱼ, A gⱼ⟫‖ ≤ (∑ ‖gⱼ‖²)^{1/2} (∑ ‖fⱼ‖²)^{(1-1/R)/2} (∑ⱼ re ⟪fⱼ, Bᴿ fⱼ⟫)^{1/(2R)}`.
In [21] the blocks are the slope intervals, `gⱼ` is `g` restricted to the neighbours of interval
`j` (so `⟪f, A g⟫ = ∑ⱼ ⟪fⱼ, A gⱼ⟫` and `∑ ‖gⱼ‖² ≪ ‖g‖²`), and `re ⟪fⱼ, Bᴿ fⱼ⟫ ≤ O(H) sup|f|² dⱼ`
by `re_inner_pow_sum_le_trace`. -/
theorem norm_sum_inner_le_moment (A : E →ₗ[ℂ] E) (R : ℕ) (hR : 2 ≤ R) {ι : Type*}
    (s : Finset ι) (f g : ι → E) :
    ‖∑ j ∈ s, ⟪f j, A (g j)⟫_ℂ‖ ≤ (∑ j ∈ s, ‖g j‖ ^ 2) ^ (1 / 2 : ℝ) *
      (∑ j ∈ s, ‖f j‖ ^ 2) ^ ((1 - (R : ℝ)⁻¹) / 2) *
      (∑ j ∈ s, re ⟪f j, ((A * LinearMap.adjoint A) ^ R) (f j)⟫_ℂ) ^ ((R : ℝ)⁻¹ / 2) := by
  set B := A * LinearMap.adjoint A
  have hB := isSymmetric_mul_adjoint A
  have hpos := re_inner_mul_adjoint_nonneg A
  set m : ι → ℝ := fun j => re ⟪f j, (B ^ R) (f j)⟫_ℂ
  have hm : ∀ j, 0 ≤ m j := fun j => re_inner_pow_nonneg hB hpos R (f j)
  have hRr : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hR0 : (0 : ℝ) < R := by linarith
  set X : ι → ℝ := fun j => ‖f j‖ ^ 2
  have hX0 : ∀ j, 0 ≤ X j := fun j => by simp only [X]; positivity
  have hR1 : (R : ℝ) - 1 ≠ 0 := by linarith
  set bb : ι → ℝ := fun j => X j ^ ((1 - (R : ℝ)⁻¹) / 2) * m j ^ ((R : ℝ)⁻¹ / 2)
  have step1 : ‖∑ j ∈ s, ⟪f j, A (g j)⟫_ℂ‖ ≤ ∑ j ∈ s, ‖g j‖ * bb j := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have := norm_inner_apply_le_moment A R (by omega) (f j) (g j)
    simpa [bb, X, m, mul_assoc] using this
  have hbb : ∀ j, bb j ^ 2 = X j ^ (1 - (R : ℝ)⁻¹) * m j ^ (R : ℝ)⁻¹ := by
    intro j
    simp only [bb]
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (hX0 j),
      ← Real.rpow_mul (hm j)]
    norm_num
  have step2 : ∑ j ∈ s, ‖g j‖ * bb j ≤
      (∑ j ∈ s, ‖g j‖ ^ 2) ^ (1 / 2 : ℝ) * (∑ j ∈ s, bb j ^ 2) ^ (1 / 2 : ℝ) := by
    have := Real.inner_le_Lp_mul_Lq_of_nonneg s (p := 2) (q := 2) Real.HolderConjugate.two_two
      (f := fun j => ‖g j‖) (g := bb) (fun j _ => norm_nonneg _)
      (fun j _ => mul_nonneg (Real.rpow_nonneg (hX0 j) _) (Real.rpow_nonneg (hm j) _))
    simpa [Real.rpow_two] using this
  have hp : Real.HolderConjugate ((R : ℝ) / (R - 1)) R := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · field_simp; ring
  have step3 : ∑ j ∈ s, bb j ^ 2 ≤
      (∑ j ∈ s, X j) ^ (1 - (R : ℝ)⁻¹) * (∑ j ∈ s, m j) ^ (R : ℝ)⁻¹ := by
    simp_rw [hbb]
    have := Real.inner_le_Lp_mul_Lq_of_nonneg s hp
      (f := fun j => X j ^ (1 - (R : ℝ)⁻¹)) (g := fun j => m j ^ (R : ℝ)⁻¹)
      (fun j _ => Real.rpow_nonneg (hX0 j) _) (fun j _ => Real.rpow_nonneg (hm j) _)
    have e1 : ∀ j, (X j ^ (1 - (R : ℝ)⁻¹)) ^ ((R : ℝ) / (R - 1)) = X j := by
      intro j
      rw [← Real.rpow_mul (hX0 j)]
      have : (1 - (R : ℝ)⁻¹) * (R / (R - 1)) = 1 := by field_simp
      rw [this, Real.rpow_one]
    have e2 : ∀ j, (m j ^ (R : ℝ)⁻¹) ^ (R : ℝ) = m j := by
      intro j
      rw [← Real.rpow_mul (hm j), inv_mul_cancel₀ hR0.ne', Real.rpow_one]
    simp only [e1, e2] at this
    convert this using 2
    · congr 1; field_simp
    · congr 1; field_simp
  have hX : 0 ≤ ∑ j ∈ s, X j := Finset.sum_nonneg fun j _ => hX0 j
  have hM : 0 ≤ ∑ j ∈ s, m j := Finset.sum_nonneg fun j _ => hm j
  calc ‖∑ j ∈ s, ⟪f j, A (g j)⟫_ℂ‖ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ (∑ j ∈ s, ‖g j‖ ^ 2) ^ (1 / 2 : ℝ) *
          ((∑ j ∈ s, X j) ^ (1 - (R : ℝ)⁻¹) * (∑ j ∈ s, m j) ^ (R : ℝ)⁻¹) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hX,
          ← Real.rpow_mul hM, mul_assoc]
        congr 3 <;> ring

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the localized spectral Hölder step of (3.20) for matrices

For a matrix `A` on a finite index set of states with positions `pos : ι → P`, a vector `f`
constant on positions, and a block index `blk : P → ℤ` such that `A` only connects blocks at
distance `≤ W` and each block has `≤ κ` positions,
`|⟨f, A f⟩| ≤ ((2W+1)‖f‖²)^{1/2} (‖f‖²)^{(1-1/R)/2} (κ F² M)^{1/(2R)}`,
`M = ∑_P ⟨u_P, (AA*)^R u_P⟩`, `F = sup |f|`. -/

namespace ArtinPrimitiveRoots.L102D

open Finset Matrix WithLp
open scoped InnerProductSpace ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sesquilinear form `∑_{s,s'} conj(v s) M(s,s') w(s')`. -/
noncomputable def qform (M : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ :=
  ∑ s, ∑ s', (starRingEnd ℂ) (v s) * M s s' * w s'

lemma inner_toLpLin (M : Matrix ι ι ℂ) (v w : ι → ℂ) :
    ⟪toLp 2 v, toLpLin 2 2 M (toLp 2 w)⟫_ℂ = qform M v w := by
  rw [toLpLin_toLp, PiLp.inner_apply]
  unfold qform
  refine sum_congr rfl fun s _ => ?_
  simp only [RCLike.inner_apply', Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_sum]
  refine sum_congr rfl fun s' _ => ?_
  ring

lemma toLpLin_mul_adjoint_pow (A : Matrix ι ι ℂ) (R : ℕ) :
    (toLpLin 2 2 A * LinearMap.adjoint (toLpLin 2 2 A)) ^ R =
      toLpLin 2 2 ((A * A.conjTranspose) ^ R) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, toLpLin_pow]
  congr 1
  rw [toLpLin_mul_same]
  rfl

/-- **The block form of (3.20).** -/
theorem norm_qform_le_blocks {P : Type*} [DecidableEq P] (A : Matrix ι ι ℂ) (R : ℕ)
    (hR : 2 ≤ R) (pos : ι → P) (blk : P → ℤ) (W : ℕ)
    (hA : ∀ s s', A s s' ≠ 0 → |blk (pos s) - blk (pos s')| ≤ W)
    (f : ι → ℂ) (hf : ∀ s s', pos s = pos s' → f s = f s') (F : ℝ) (hF0 : 0 ≤ F)
    (hF : ∀ s, ‖f s‖ ≤ F) (κ : ℕ) (hκ : ∀ j : ℤ, ((univ.image pos).filter fun p => blk p = j).card ≤ κ) :
    ‖qform A f f‖ ≤ (((2 * W + 1 : ℕ) : ℝ) * ∑ s, ‖f s‖ ^ 2) ^ (1 / 2 : ℝ) *
      (∑ s, ‖f s‖ ^ 2) ^ ((1 - (R : ℝ)⁻¹) / 2) *
      ((κ : ℝ) * F ^ 2 * (∑ s, ∑ s', if pos s = pos s' then
        ((A * A.conjTranspose) ^ R) s s' else 0).re) ^ ((R : ℝ)⁻¹ / 2) := by
  classical
  set T : Module.End ℂ (EuclideanSpace ℂ ι) := toLpLin 2 2 A
  set Js : Finset ℤ := univ.image fun s => blk (pos s)
  set fj : ℤ → EuclideanSpace ℂ ι := fun j => toLp 2 fun s => if blk (pos s) = j then f s else 0
  set gj : ℤ → EuclideanSpace ℂ ι := fun j =>
    toLp 2 fun s => if |blk (pos s) - j| ≤ W then f s else 0
  -- (1) the pairing is the sum of the block pairings
  have h1 : qform A f f = ∑ j ∈ Js, ⟪fj j, T (gj j)⟫_ℂ := by
    simp only [fj, gj, T, inner_toLpLin]
    unfold qform
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := Js) (g := fun s => blk (pos s))
      (fun s _ => mem_image_of_mem _ (mem_univ s))]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_filter]
    refine sum_congr rfl fun s _ => ?_
    by_cases hsj : blk (pos s) = j
    · rw [if_pos hsj]
      refine sum_congr rfl fun s' _ => ?_
      simp only [if_pos hsj]
      by_cases hA0 : A s s' = 0
      · simp [hA0]
      · have := hA s s' hA0
        rw [hsj] at this
        rw [if_pos (by rw [abs_sub_comm]; exact this)]
    · rw [if_neg hsj]
      simp [if_neg hsj]
  -- (2) norms of the pieces
  have hfj : ∑ j ∈ Js, ‖fj j‖ ^ 2 = ∑ s, ‖f s‖ ^ 2 := by
    simp only [fj, EuclideanSpace.norm_sq_eq]
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [sum_eq_single (blk (pos s))]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd (mem_image_of_mem _ (mem_univ s)) h
  have hgj : ∑ j ∈ Js, ‖gj j‖ ^ 2 ≤ ((2 * W + 1 : ℕ) : ℝ) * ∑ s, ‖f s‖ ^ 2 := by
    simp only [gj, EuclideanSpace.norm_sq_eq]
    rw [sum_comm, mul_sum]
    refine sum_le_sum fun s _ => ?_
    have hcount : (Js.filter fun j => |blk (pos s) - j| ≤ W).card ≤ 2 * W + 1 := by
      have hsub : (Js.filter fun j => |blk (pos s) - j| ≤ W) ⊆
          Icc (blk (pos s) - W) (blk (pos s) + W) := by
        intro j hj
        rw [mem_filter] at hj
        rw [mem_Icc]
        constructor <;> [linarith [(abs_le.1 hj.2).2]; linarith [(abs_le.1 hj.2).1]]
      refine (card_le_card hsub).trans (le_of_eq ?_)
      rw [Int.card_Icc]; try omega
    calc ∑ j ∈ Js, ‖(if |blk (pos s) - j| ≤ W then f s else 0)‖ ^ 2
        = ∑ j ∈ Js.filter (fun j => |blk (pos s) - j| ≤ W), ‖f s‖ ^ 2 := by
          rw [sum_filter]; refine sum_congr rfl fun j _ => by split_ifs <;> simp
      _ = ((Js.filter fun j => |blk (pos s) - j| ≤ W).card : ℝ) * ‖f s‖ ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ((2 * W + 1 : ℕ) : ℝ) * ‖f s‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (by positivity)
  -- (3) the moment of each block
  set B : Module.End ℂ (EuclideanSpace ℂ ι) := T * LinearMap.adjoint T
  have hB := isSymmetric_mul_adjoint T
  have hBpos := re_inner_mul_adjoint_nonneg T
  set u : P → EuclideanSpace ℂ ι := fun p => toLp 2 fun s => if pos s = p then 1 else 0
  set c : P → ℂ := fun p => if h : ∃ s, pos s = p then f h.choose else 0
  have hc : ∀ s, c (pos s) = f s := by
    intro s
    have h : ∃ s', pos s' = pos s := ⟨s, rfl⟩
    simp only [c, dif_pos h]
    exact hf _ _ h.choose_spec
  have hcF : ∀ p, ‖c p‖ ≤ F := by
    intro p; simp only [c]; split_ifs with h
    · exact hF _
    · simpa using hF0
  set Pj : ℤ → Finset P := fun j => (univ.image pos).filter fun p => blk p = j
  have hfj_eq : ∀ j, fj j = ∑ p ∈ Pj j, c p • u p := by
    intro j
    ext s
    simp only [fj, u, Pj, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq]
    by_cases hj : blk (pos s) = j
    · rw [if_pos hj, if_pos, hc]
      exact mem_filter.2 ⟨mem_image_of_mem _ (mem_univ s), hj⟩
    · rw [if_neg hj, if_neg]
      intro h; exact hj (mem_filter.1 h).2
  have hmom : ∀ p, (⟪u p, (B ^ R) (u p)⟫_ℂ) =
      ∑ s, ∑ s', if pos s = p ∧ pos s' = p then ((A * A.conjTranspose) ^ R) s s' else 0 := by
    intro p
    simp only [B, T, toLpLin_mul_adjoint_pow, u, inner_toLpLin]
    unfold qform
    refine sum_congr rfl fun s _ => sum_congr rfl fun s' _ => ?_
    by_cases h1 : pos s = p <;> by_cases h2 : pos s' = p <;> simp [h1, h2]
  have hblock : ∀ j ∈ Js, RCLike.re ⟪fj j, (B ^ R) (fj j)⟫_ℂ ≤
      (κ : ℝ) * F ^ 2 * ∑ p ∈ Pj j, RCLike.re ⟪u p, (B ^ R) (u p)⟫_ℂ := by
    intro j _
    rw [hfj_eq j]
    refine (re_inner_pow_sum_le_trace hB hBpos R (Pj j) c u).trans ?_
    have hsum0 : 0 ≤ ∑ p ∈ Pj j, RCLike.re ⟪u p, (B ^ R) (u p)⟫_ℂ :=
      sum_nonneg fun p _ => re_inner_pow_nonneg hB hBpos R _
    refine mul_le_mul_of_nonneg_right ?_ hsum0
    calc ∑ p ∈ Pj j, ‖c p‖ ^ 2 ≤ ∑ _p ∈ Pj j, F ^ 2 :=
          sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _) (hcF p) 2
      _ = ((Pj j).card : ℝ) * F ^ 2 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (κ : ℝ) * F ^ 2 := by gcongr; exact_mod_cast hκ j
  have htotal : ∑ j ∈ Js, ∑ p ∈ Pj j, RCLike.re ⟪u p, (B ^ R) (u p)⟫_ℂ =
      (∑ s, ∑ s', if pos s = pos s' then ((A * A.conjTranspose) ^ R) s s' else 0).re := by
    have hdisj : ∑ j ∈ Js, ∑ p ∈ Pj j, RCLike.re ⟪u p, (B ^ R) (u p)⟫_ℂ =
        ∑ p ∈ univ.image pos, RCLike.re ⟪u p, (B ^ R) (u p)⟫_ℂ := by
      simp only [Pj]
      rw [sum_fiberwise_of_maps_to (s := univ.image pos) (t := Js) (g := blk)]
      intro p hp
      obtain ⟨s, -, rfl⟩ := mem_image.1 hp
      exact mem_image_of_mem _ (mem_univ s)
    rw [hdisj]
    simp only [hmom, RCLike.re_to_complex, ← Complex.re_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun s' _ => ?_
    simp only [ite_and]
    rw [sum_ite_eq, if_pos (mem_image_of_mem _ (mem_univ s))]
    by_cases h : pos s' = pos s
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  -- (4) assemble
  have hmain := norm_sum_inner_le_moment T R hR Js fj gj
  rw [h1]
  refine hmain.trans ?_
  have hS0 : 0 ≤ ∑ s, ‖f s‖ ^ 2 := sum_nonneg fun s _ => by positivity
  have hblock' : ∑ j ∈ Js, RCLike.re ⟪fj j, ((T * LinearMap.adjoint T) ^ R) (fj j)⟫_ℂ ≤
      (κ : ℝ) * F ^ 2 *
        (∑ s, ∑ s', if pos s = pos s' then ((A * A.conjTranspose) ^ R) s s' else 0).re := by
    rw [← htotal, mul_sum]
    exact sum_le_sum hblock
  have hpos1 : 0 ≤ ∑ j ∈ Js, RCLike.re ⟪fj j, ((T * LinearMap.adjoint T) ^ R) (fj j)⟫_ℂ :=
    sum_nonneg fun j _ => re_inner_pow_nonneg hB hBpos R _
  have hR' : (0 : ℝ) ≤ (1 - (R : ℝ)⁻¹) / 2 := by
    have : (R : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ R))
    linarith
  have e1 := Real.rpow_le_rpow (sum_nonneg fun j _ => by positivity) hgj
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have e3 := Real.rpow_le_rpow hpos1 hblock' (by positivity : (0 : ℝ) ≤ (R : ℝ)⁻¹ / 2)
  rw [hfj]
  exact mul_le_mul (mul_le_mul_of_nonneg_right e1 (by positivity)) e3 (by positivity)
    (by positivity)

/-- The position moment is `∑_P ⟨u_P, (AA*)^R u_P⟩`, hence has nonnegative real part. -/
theorem moment_re_nonneg {P : Type*} [DecidableEq P] (A : Matrix ι ι ℂ) (R : ℕ) (pos : ι → P) :
    0 ≤ (∑ s, ∑ s', if pos s = pos s' then ((A * A.conjTranspose) ^ R) s s' else 0).re := by
  classical
  set T : Module.End ℂ (EuclideanSpace ℂ ι) := toLpLin 2 2 A
  have hB := isSymmetric_mul_adjoint T
  have hBpos := re_inner_mul_adjoint_nonneg T
  set u : P → EuclideanSpace ℂ ι := fun p => toLp 2 fun s => if pos s = p then 1 else 0
  have hmom : ∀ p, (⟪u p, ((T * LinearMap.adjoint T) ^ R) (u p)⟫_ℂ) =
      ∑ s, ∑ s', if pos s = p ∧ pos s' = p then ((A * A.conjTranspose) ^ R) s s' else 0 := by
    intro p
    simp only [T, toLpLin_mul_adjoint_pow, u, inner_toLpLin]
    unfold qform
    refine sum_congr rfl fun s _ => sum_congr rfl fun s' _ => ?_
    by_cases h1 : pos s = p <;> by_cases h2 : pos s' = p <;> simp [h1, h2]
  have htot : (∑ s, ∑ s', if pos s = pos s' then ((A * A.conjTranspose) ^ R) s s' else 0) =
      ∑ p ∈ univ.image pos, ⟪u p, ((T * LinearMap.adjoint T) ^ R) (u p)⟫_ℂ := by
    simp only [hmom]
    symm
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun s' _ => ?_
    simp only [ite_and]
    rw [sum_ite_eq, if_pos (mem_image_of_mem _ (mem_univ s))]
    by_cases h : pos s' = pos s
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [htot, Complex.re_sum]
  exact sum_nonneg fun p _ => re_inner_pow_nonneg hB hBpos R _

end ArtinPrimitiveRoots.L102D
end

section
/-!
# Elementary divisor-sum estimates
-/

namespace ArtinBV

open Finset

end ArtinBV
end

section
/-! # L102D: the exact outer reduction of (10.9) ([21] §3.1, (3.10)–(3.11))

`Q_Y − Q_Y^maj = Q^sh − Q^{maj,sh} + Q^min`, where `Q^sh`, `Q^{maj,sh}` are the parts of the two
squares over label pairs whose products `a, b` are not coprime, and `Q^min` is the coprime part
of the minor-arc square, with kernel `ψ(t/Y) ∫_{[0,1) ∖ 𝔐} e(θ(t − b + a)) dθ`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary inputs -/

lemma dyadicBump_ne_zero {u : ℝ} (h : dyadicBump u ≠ 0) : 1 < u ∧ u < 4 := by
  unfold dyadicBump at h
  constructor
  · by_contra hu
    push Not at hu
    apply h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · by_contra hu
    push Not at hu
    apply h
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith)]
    simp

/-! ## The identity -/

/-! ## The reduction of (10.9) to the shared-label bound (D1b) and the minor-arc bound (D1c) -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: good positions and their measure ([21] §3.2, Lemma 3.2)

For lists `ℓ` of `M` primes in each group, the omission products `D` (omit one label per group),
the two good-state tests on a ratio `r ∈ ℝ/ℤ` (realized on `(0, 1]`), and Lemma 3.2: the set of
`r` failing goodness has measure at most `exp(-c L^{0.1})`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Distance to the nearest integer and its level sets -/

/-! ## Test (i): the union bound -/

/-! ## Markov's inequality for a finite weighted family of bad sets -/

/-! ## Test (ii): one fresh draw, then Markov over the fresh draws -/

lemma pos_of_mem_primeGroup {x b : ℝ} {p : ℕ} (h : p ∈ primeGroup x b) : 0 < p := by
  unfold primeGroup at h
  exact (Finset.mem_filter.1 h).2.1.pos

/-! ## Counting and asymptotics -/

/-- `L^b ≤ ε L^c` eventually, for `b < c` and `ε > 0`. -/
lemma eventually_rpow_le_rpow {b c : ℝ} (hbc : b < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, L ^ b ≤ ε * L ^ c := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.2 hbc)).eventually (ge_mem_nhds hε)
  filter_upwards [h, Filter.eventually_gt_atTop 0] with L hL hL0
  have : L ^ b = L ^ (-(c - b)) * L ^ c := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hL (by positivity)

/-! ## Lemma 3.2 -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the divisor input (3.9) of [21] §3.1

`∑_{h ≤ Z} τ(1 + l h)² ≤ 4 (Z + T)(1 + log T)³` whenever every `m` with `m⁴ ≤ (1 + lZ)³` is
`≤ T`. The proof replaces `τ(n)² = #{(d₁, d₂) : d₁, d₂ ∣ n}` by four times the number of divisor
pairs with `lcm⁴ ≤ n³` (one of `(d₁,d₂)`, `(n/d₁,n/d₂)`, `(d₁,n/d₂)`, `(n/d₁,d₂)` qualifies), and
then counts `h` in one residue class modulo the `lcm`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the shared-label parts are negligible ([21] §3.1 (3.9), §4.9 (4.61), (4.63))

Bounds for the inner sums `rawInner`, `majInner` at one pair of label products, for the measure of
the major arcs, and for the normalized mass of label pairs with a common prime. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary facts about the cutoffs and coefficients -/

lemma abs_arcCutoff_le (u : ℝ) : |arcCutoff u| ≤ if |u| < 5 then 1 else 0 := by
  unfold arcCutoff
  have h1 := Real.smoothTransition.nonneg (5 - u)
  have h2 := Real.smoothTransition.nonneg (5 + u)
  have h3 := Real.smoothTransition.le_one (5 - u)
  have h4 := Real.smoothTransition.le_one (5 + u)
  rw [abs_of_nonneg (mul_nonneg h1 h2)]
  split_ifs with hu
  · nlinarith
  · rw [abs_lt] at hu
    push Not at hu
    by_cases hu' : u ≤ -5
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 + u ≤ 0), mul_zero]
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith [hu (not_le.1 hu')] : 5 - u ≤ 0),
        zero_mul]

/-! ## The measure of the major arcs -/

/-! ## The raw inner sum at one pair of label products -/

/-! ## The major inner sum at one pair of label products -/

/-! ## The mass of label pairs with a common prime -/

/-! ## Inputs about the groups for large `x` -/

lemma le_of_mem_primeGroup {x b : ℝ} {q : ℕ} (h : q ∈ primeGroup x b) :
    exp (log x ^ b) ≤ q ∧ (q : ℝ) ≤ exp (2 * log x ^ b) := by
  unfold primeGroup at h
  simp only [mem_filter, mem_range] at h
  refine ⟨h.2.2, ?_⟩
  have := Nat.lt_succ_iff.1 h.1
  exact (Nat.cast_le.2 this).trans (Nat.floor_le (exp_pos _).le)

lemma dyadicBump_eq_zero_of_le_one {u : ℝ} (hu : u ≤ 1) : dyadicBump u = 0 := by
  by_contra h
  linarith [(dyadicBump_ne_zero h).1]

/-! ## Numerics -/


/-! ## D1b: the shared-label bound -/

/-- Common setting: the hypotheses used by both halves of D1b, at one `x`. -/
structure SharedSetting (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (C : ℝ) :
    Prop where
  hL1 : 1 ≤ log x
  hx : 0 < x
  hHm : 0 < Hm
  hHn : 0 < Hn
  hY : 1 ≤ Y
  hX1 : 1 ≤ Hm * Hn
  hα0 : α 0 = 0
  hβ0 : β 0 = 0
  hαb : ∀ m, ‖α m‖ ≤ log x ^ C
  hβb : ∀ n, ‖β n‖ ≤ log x ^ C
  hV : ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j)
  hab : ∀ i, (0.1 : ℝ) < a i
  hlog : 1 + log (17 * (Hm * Hn)) ≤ 2 * log x


end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D5, the pairing from the moment ([21] §3.3, (3.20)), for the operator model

The concrete inputs to `norm_qform_le_blocks`: `A` only connects slope blocks at distance `≤ 12`,
a slope block of length `H/U²` holds `≤ 17(512H + 1)` primitive positions, `f` depends only on the
position, `|f| ≤ L^{2C}`, and `σ ∑ |f|² ≤ 32 U V L^{4C}` ((3.18)). -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

section Geometry

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {U V : ℝ}

lemma mem_posBox_of_state (s : PhysState x a J U V) : s.1.1 ∈ posBox U V :=
  (mem_product.1 (mem_filter.1 s.2).1).1

lemma state_pos_bounds (hU : 0 < U) (hV : 0 < V) (s : PhysState x a J U V) :
    U ≤ s.1.1.1 ∧ (s.1.1.1 : ℝ) ≤ 16 * U ∧ Nat.Coprime s.1.1.1 s.1.1.2 ∧
      V ≤ s.1.1.2 ∧ (s.1.1.2 : ℝ) ≤ 2 * V := by
  have h := mem_posBox_of_state s
  simp only [posBox, mem_filter, mem_product, mem_Icc] at h
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := h
  exact ⟨(Nat.le_ceil U).trans (by exact_mod_cast h1),
    (Nat.cast_le.2 h2).trans (Nat.floor_le (by linarith)), h5,
    (Nat.le_ceil V).trans (by exact_mod_cast h3), (Nat.cast_le.2 h4).trans (Nat.floor_le (by linarith))⟩

/-- A nonzero entry of the row operation has `|det(P, Q)| < (5Y + 1) · 2d₀`. -/
lemma rowOp_ne_zero {A₀ Y : ℝ} {d₀ : ℕ} {s s' : PhysState x a J U V}
    (h : rowOp x a A₀ Y J d₀ U V s s' ≠ 0) :
    |((s.1.1.1 : ℤ) * s'.1.1.2 - (s.1.1.2 : ℤ) * s'.1.1.1 : ℤ)| < (5 * Y + 1) * (2 * d₀) ∧
      d₀ ≤ padProd s.1.2 ∧ dyadicBump ((lastProd s.1.2 : ℝ) / Y) ≠ 0 := by
  unfold rowOp at h
  split_ifs at h with hc
  · obtain ⟨-, -, hd1, hd2⟩ := hc
    set det : ℤ := (s.1.1.1 : ℤ) * s'.1.1.2 - (s.1.1.2 : ℤ) * s'.1.1.1
    set D := padProd s.1.2
    have hk := (mul_ne_zero_iff.1 h).2
    have hr := Complex.ofReal_ne_zero.1 (mul_ne_zero_iff.1 h).1
    have hψ : arcCutoff (((det / (D : ℤ) : ℤ) : ℝ) / Y) ≠ 0 := by
      intro h0; apply hk; unfold minorKernel; rw [h0]; simp
    have ht : |(((det / (D : ℤ) : ℤ) : ℝ) / Y)| < 5 := by
      by_contra hge
      have := abs_arcCutoff_le (((det / (D : ℤ) : ℤ) : ℝ) / Y)
      rw [if_neg hge] at this
      exact hψ (abs_nonpos_iff.1 this)
    have hD0 : (0 : ℤ) < D := by
      have : 0 < d₀ ∨ d₀ = 0 := (Nat.eq_zero_or_pos d₀).symm
      rcases this with h0 | h0
      · exact_mod_cast lt_of_lt_of_le h0 hd1
      · omega
    have hη2 : dyadicBump ((lastProd s.1.2 : ℝ) / Y) ≠ 0 :=
      (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 hr).1).1).2
    have hY : 0 < Y := by
      by_contra hY; push Not at hY
      apply hη2
      apply dyadicBump_eq_zero_of_le_one
      exact (div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hY).trans zero_le_one
    refine ⟨?_, hd1, hη2⟩
    have hq := Int.mul_ediv_add_emod det D
    have hr0 := Int.emod_nonneg det hD0.ne'
    have hr1 := Int.emod_lt_of_pos det hD0
    rw [abs_div, abs_of_pos hY, div_lt_iff₀ hY] at ht
    have hDr : (D : ℝ) < 2 * d₀ := by exact_mod_cast hd2
    have hdet : (det : ℝ) = D * ((det / (D : ℤ) : ℤ) : ℝ) + ((det % D : ℤ) : ℝ) := by
      exact_mod_cast hq.symm
    have hr0' : (0 : ℝ) ≤ ((det % D : ℤ) : ℝ) := by exact_mod_cast hr0
    have hr1' : ((det % D : ℤ) : ℝ) < D := by exact_mod_cast hr1
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hD0
    have habs : |(det : ℝ)| ≤ D * |((det / (D : ℤ) : ℤ) : ℝ)| + D := by
      rw [hdet]
      calc |(D : ℝ) * ((det / (D : ℤ) : ℤ) : ℝ) + ((det % D : ℤ) : ℝ)|
          ≤ |(D : ℝ) * ((det / (D : ℤ) : ℤ) : ℝ)| + |((det % D : ℤ) : ℝ)| := abs_add_le _ _
        _ ≤ D * |((det / (D : ℤ) : ℤ) : ℝ)| + D := by
            rw [abs_mul, abs_of_pos hDpos, abs_of_nonneg hr0']; linarith
    rw [Int.cast_abs]
    calc |(det : ℝ)| ≤ D * |((det / (D : ℤ) : ℤ) : ℝ)| + D := habs
      _ ≤ D * (5 * Y) + D := by gcongr
      _ = D * (5 * Y + 1) := by ring
      _ < 2 * d₀ * (5 * Y + 1) := by gcongr
      _ = (5 * Y + 1) * (2 * d₀) := by ring
  · exact absurd rfl h

lemma matrix_mul_ne_zero {ι : Type*} [Fintype ι] {M N : Matrix ι ι ℂ} {s s' : ι}
    (h : (M * N) s s' ≠ 0) : ∃ t, M s t ≠ 0 ∧ N t s' ≠ 0 := by
  rw [Matrix.mul_apply] at h
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨t, left_ne_zero_of_mul ht, right_ne_zero_of_mul ht⟩

lemma slotSym_ne_zero {s s' : PhysState x a J U V} (h : slotSym x a J U V s s' ≠ 0) :
    s.1.1 = s'.1.1 := by
  unfold slotSym at h
  split_ifs at h with hc
  · exact hc.1
  · exact absurd rfl h

/-- A nonzero entry of `A = GSTSG` comes from a nonzero entry of `T` between the same positions. -/
lemma opA_ne_zero {A₀ Y : ℝ} {d₀ : ℕ} {s s' : PhysState x a J U V}
    (h : opA x a A₀ Y J d₀ U V s s' ≠ 0) :
    ∃ s₁ s₂ : PhysState x a J U V, s₁.1.1 = s.1.1 ∧ s₂.1.1 = s'.1.1 ∧
      rowOp x a A₀ Y J d₀ U V s₁ s₂ ≠ 0 := by
  unfold opA goodProj at h
  rw [Matrix.mul_diagonal] at h
  obtain ⟨t3, h3, h3'⟩ := matrix_mul_ne_zero (left_ne_zero_of_mul h)
  obtain ⟨t2, h2, h2'⟩ := matrix_mul_ne_zero h3
  rw [Matrix.diagonal_mul] at h2
  exact ⟨t2, t3, (slotSym_ne_zero (right_ne_zero_of_mul h2)).symm, slotSym_ne_zero h3', h2'⟩

end Geometry

/-! ## Slope blocks -/

/-- The slope block of a position: `⌊P₂ U² / (P₁ Δ)⌋`. -/
noncomputable def slopeBlock (U Δ : ℝ) (P : ℕ × ℕ) : ℤ :=
  ⌊(P.2 : ℝ) * U ^ 2 / ((P.1 : ℝ) * Δ)⌋

lemma abs_floor_sub_le_one {u v : ℝ} (h : |u - v| < 1) : |⌊u⌋ - ⌊v⌋| ≤ 1 := by
  rw [abs_lt] at h
  have h1 := Int.floor_le u; have h2 := Int.lt_floor_add_one u
  have h3 := Int.floor_le v; have h4 := Int.lt_floor_add_one v
  have e1 : ((⌊u⌋ - ⌊v⌋ : ℤ) : ℝ) < 2 := by push_cast; linarith
  have e2 : ((⌊u⌋ - ⌊v⌋ : ℤ) : ℝ) > -2 := by push_cast; linarith
  have e1' : ⌊u⌋ - ⌊v⌋ < 2 := by exact_mod_cast e1
  have e2' : ⌊u⌋ - ⌊v⌋ > -2 := by exact_mod_cast e2
  rw [abs_le]; constructor <;> omega

/-- Positions joined by an edge lie in neighbouring slope blocks (block length `Δ/U²`). -/
lemma slopeBlock_near {P Q : ℕ × ℕ} {U Δ : ℝ} (hU : 0 < U) (hΔ : 0 < Δ) (hP : U ≤ P.1)
    (hQ : U ≤ Q.1) (hdet : |((P.1 : ℤ) * Q.2 - (P.2 : ℤ) * Q.1 : ℤ)| < Δ) :
    |slopeBlock U Δ P - slopeBlock U Δ Q| ≤ 1 := by
  apply abs_floor_sub_le_one
  have hP0 : (0 : ℝ) < P.1 := lt_of_lt_of_le hU hP
  have hQ0 : (0 : ℝ) < Q.1 := lt_of_lt_of_le hU hQ
  have e : (P.2 : ℝ) * U ^ 2 / ((P.1 : ℝ) * Δ) - (Q.2 : ℝ) * U ^ 2 / ((Q.1 : ℝ) * Δ) =
      -(((P.1 : ℝ) * Q.2 - (P.2 : ℝ) * Q.1) * U ^ 2 / ((P.1 : ℝ) * Q.1 * Δ)) := by
    field_simp; ring
  rw [e, abs_neg, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < P.1 * Q.1 * Δ),
    abs_of_pos (by positivity : (0 : ℝ) < U ^ 2), div_lt_one (by positivity)]
  have hdet' : |(P.1 : ℝ) * Q.2 - (P.2 : ℝ) * Q.1| < Δ := by
    have := hdet; push_cast at this; exact this
  have hPQ : U ^ 2 ≤ (P.1 : ℝ) * Q.1 := by nlinarith
  calc |(P.1 : ℝ) * Q.2 - (P.2 : ℝ) * Q.1| * U ^ 2 < Δ * U ^ 2 := by gcongr
    _ ≤ Δ * ((P.1 : ℝ) * Q.1) := by gcongr
    _ = (P.1 : ℝ) * Q.1 * Δ := by ring

/-- A slope block of length `Δ/U²` contains at most `17 (2⌊256Δ⌋ + 1)` primitive positions of
`[U, 16U] × ℝ`. -/
lemma card_slopeBlock_le (S : Finset (ℕ × ℕ)) {U Δ : ℝ} (hU : 0 < U) (hΔ : 0 < Δ)
    (hS : ∀ P ∈ S, U ≤ P.1 ∧ (P.1 : ℝ) ≤ 16 * U ∧ Nat.Coprime P.1 P.2) (j : ℤ) :
    (S.filter fun P => slopeBlock U Δ P = j).card ≤ 17 * (2 * ⌊256 * Δ⌋₊ + 1) := by
  set B := S.filter fun P => slopeBlock U Δ P = j
  rcases B.eq_empty_or_nonempty with hB | ⟨P₀, hP₀⟩
  · rw [hB]; simp
  have hP₀S := (mem_filter.1 hP₀).1
  obtain ⟨hP₀1, hP₀2, hP₀c⟩ := hS P₀ hP₀S
  have hP₀pos : (0 : ℝ) < P₀.1 := lt_of_lt_of_le hU hP₀1
  set det : ℕ × ℕ → ℤ := fun P => (P₀.1 : ℤ) * P.2 - (P₀.2 : ℤ) * P.1
  set φ : ℕ × ℕ → ℤ × ℕ := fun P => (det P, P.1 / P₀.1)
  set M := ⌊256 * Δ⌋₊
  have hmaps : Set.MapsTo φ B ↑((Icc (-(M : ℤ)) M) ×ˢ (range 17)) := by
    intro P hP
    have hPB := mem_filter.1 hP
    obtain ⟨hP1, hP2, -⟩ := hS P hPB.1
    have hPpos : (0 : ℝ) < P.1 := lt_of_lt_of_le hU hP1
    rw [mem_coe, mem_product, mem_Icc, mem_range]
    simp only [φ]
    constructor
    · -- `|det| < 256 Δ` from the common block
      have hblk : |(P₀.2 : ℝ) * U ^ 2 / ((P₀.1 : ℝ) * Δ) - (P.2 : ℝ) * U ^ 2 / ((P.1 : ℝ) * Δ)| < 1 := by
        have h1 := hPB.2; have h2 := (mem_filter.1 hP₀).2
        unfold slopeBlock at h1 h2
        rw [abs_lt]
        constructor
        · have := Int.floor_le ((P₀.2 : ℝ) * U ^ 2 / ((P₀.1 : ℝ) * Δ))
          have := Int.lt_floor_add_one ((P.2 : ℝ) * U ^ 2 / ((P.1 : ℝ) * Δ))
          rw [h1] at *; rw [h2] at *; linarith
        · have := Int.floor_le ((P.2 : ℝ) * U ^ 2 / ((P.1 : ℝ) * Δ))
          have := Int.lt_floor_add_one ((P₀.2 : ℝ) * U ^ 2 / ((P₀.1 : ℝ) * Δ))
          rw [h1] at *; rw [h2] at *; linarith
      have e : (P₀.2 : ℝ) * U ^ 2 / ((P₀.1 : ℝ) * Δ) - (P.2 : ℝ) * U ^ 2 / ((P.1 : ℝ) * Δ) =
          -(((P₀.1 : ℝ) * P.2 - (P₀.2 : ℝ) * P.1) * U ^ 2 / ((P₀.1 : ℝ) * P.1 * Δ)) := by
        field_simp; ring
      rw [e, abs_neg, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < P₀.1 * P.1 * Δ),
        abs_of_pos (by positivity : (0 : ℝ) < U ^ 2), div_lt_one (by positivity)] at hblk
      have hPP : (P₀.1 : ℝ) * P.1 ≤ 256 * U ^ 2 := by nlinarith
      have hdetR : |(det P : ℝ)| < 256 * Δ := by
        have hU2 : (0 : ℝ) < U ^ 2 := by positivity
        have : |(det P : ℝ)| * U ^ 2 < 256 * Δ * U ^ 2 := by
          calc |(det P : ℝ)| * U ^ 2 = |(P₀.1 : ℝ) * P.2 - (P₀.2 : ℝ) * P.1| * U ^ 2 := by
                simp only [det]; push_cast; rfl
            _ < (P₀.1 : ℝ) * P.1 * Δ := hblk
            _ ≤ 256 * U ^ 2 * Δ := by gcongr
            _ = 256 * Δ * U ^ 2 := by ring
        exact lt_of_mul_lt_mul_right this hU2.le
      have hM : |det P| ≤ (M : ℤ) := by
        have : (|det P| : ℝ) ≤ 256 * Δ := by push_cast; exact hdetR.le
        have h0 : (0 : ℝ) ≤ 256 * Δ := by positivity
        have := Nat.le_floor (show ((|det P|).toNat : ℝ) ≤ 256 * Δ by
          rw [show ((|det P|).toNat : ℝ) = ((|det P| : ℤ) : ℝ) by
            exact_mod_cast Int.toNat_of_nonneg (abs_nonneg _)]
          exact_mod_cast this)
        have h2 : (|det P|).toNat ≤ M := this
        omega
      exact abs_le.1 hM
    · -- `P₁ / P₀₁ ≤ 16`
      have : P.1 < 17 * P₀.1 := by
        have : (P.1 : ℝ) < 17 * P₀.1 := by nlinarith
        exact_mod_cast this
      exact Nat.div_lt_of_lt_mul (by linarith)
  have hinj : Set.InjOn φ B := by
    intro P hP P' hP' hφ
    simp only [φ, Prod.mk.injEq] at hφ
    obtain ⟨hd, hq⟩ := hφ
    have hcop : IsCoprime (P₀.1 : ℤ) (P₀.2 : ℤ) := Nat.isCoprime_iff_coprime.2 hP₀c
    have hlin : (P₀.1 : ℤ) * ((P.2 : ℤ) - P'.2) = (P₀.2 : ℤ) * ((P.1 : ℤ) - P'.1) := by
      simp only [det] at hd; linarith
    have hdvd : (P₀.1 : ℤ) ∣ ((P.1 : ℤ) - P'.1) :=
      hcop.dvd_of_dvd_mul_left ⟨(P.2 : ℤ) - P'.2, hlin.symm⟩
    have hP01 : 0 < P₀.1 := by exact_mod_cast hP₀pos
    have h1 : P.1 = P'.1 := by
      have hm1 := Nat.mod_add_div P.1 P₀.1
      have hm2 := Nat.mod_add_div P'.1 P₀.1
      have hl1 := Nat.mod_lt P.1 hP01
      have hl2 := Nat.mod_lt P'.1 hP01
      obtain ⟨c, hc⟩ := hdvd
      have hc' : ((P.1 % P₀.1 : ℕ) : ℤ) - (P'.1 % P₀.1 : ℕ) = P₀.1 * c := by
        have e1 : (P.1 : ℤ) = (P.1 % P₀.1 : ℕ) + P₀.1 * (P.1 / P₀.1 : ℕ) := by exact_mod_cast hm1.symm
        have e2 : (P'.1 : ℤ) = (P'.1 % P₀.1 : ℕ) + P₀.1 * (P'.1 / P₀.1 : ℕ) := by
          exact_mod_cast hm2.symm
        rw [hq] at e1
        linarith
      have hc0 : c = 0 := by
        by_contra hc0
        have : (P₀.1 : ℤ) ≤ |(P₀.1 : ℤ) * c| := by
          rw [abs_mul, abs_of_pos (by exact_mod_cast hP01)]
          exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hc0)
        rw [← hc'] at this
        have : |((P.1 % P₀.1 : ℕ) : ℤ) - (P'.1 % P₀.1 : ℕ)| < P₀.1 := by
          rw [abs_lt]; constructor <;> push_cast <;> omega
        omega
      rw [hc0, mul_zero] at hc
      omega
    have h2 : P.2 = P'.2 := by
      rw [h1, sub_self, mul_zero] at hlin
      have : ((P.2 : ℤ) - P'.2) = 0 := by
        rcases mul_eq_zero.1 hlin with h | h
        · exact absurd h (by exact_mod_cast hP01.ne')
        · exact h
      omega
    exact Prod.ext h1 h2
  calc B.card ≤ ((Icc (-(M : ℤ)) M) ×ˢ (range 17)).card := card_le_card_of_injOn φ hmaps hinj
    _ = 17 * (2 * M + 1) := by
        rw [card_product, Int.card_Icc, card_range]
        have : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
        rw [this]; ring

/-! ## The endpoint norm (3.18) -/

section Norm

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ}

/-- Disjoint groups: entries of a list of a state are pairwise distinct primes, so their product
divides `P₁`. -/
lemma listProd_dvd_of_disjoint {J : ℕ} {U V : ℝ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (s : PhysState x a J U V) : listProd s.1.2 ∣ s.1.1.1 := by
  have hs := mem_filter.1 s.2
  obtain ⟨hmem, hinj, hdvd⟩ := hs
  have hcand := (mem_product.1 hmem).2
  have hgrp : ∀ i j, s.1.2 i j ∈ primeGroup x (a i) := fun i j =>
    Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hcand i) j
  have hprime : ∀ i j, (s.1.2 i j).Prime := fun i j => by
    have := hgrp i j; unfold primeGroup at this; exact (mem_filter.1 this).2.1
  have hne : ∀ q q' : Fin K × Fin (J + 1), q ≠ q' → s.1.2 q.1 q.2 ≠ s.1.2 q'.1 q'.2 := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hq heq
    by_cases hi : i = i'
    · subst hi
      have : j = j' := hinj i heq
      exact hq (by rw [this])
    · exact Finset.disjoint_left.1 (hdisj i i' hi) (hgrp i j) (heq ▸ hgrp i' j')
  have hZ : (∏ q : Fin K × Fin (J + 1), ((s.1.2 q.1 q.2 : ℕ) : ℤ)) ∣ (s.1.1.1 : ℤ) := by
    refine Fintype.prod_dvd_of_coprime (fun q q' hqq => ?_) fun q => ?_
    · simp only [Function.onFun]
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.coprime_primes (hprime q.1 q.2) (hprime q'.1 q'.2)).2 (hne q q' hqq)
    · exact_mod_cast hdvd q.1 q.2
  have : ((listProd s.1.2 : ℕ) : ℤ) ∣ (s.1.1.1 : ℤ) := by
    unfold listProd; push_cast
    have e := Fintype.prod_prod_type' (fun (i : Fin K) (j : Fin (J + 1)) => ((s.1.2 i j : ℕ) : ℤ))
    rw [e] at hZ
    exact hZ
  exact_mod_cast this

/-- The number of positions of `posBox U V` with `G ∣ P₁` is at most `(16U/G)(2V)`. -/
lemma card_posBox_dvd_le {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (G : ℕ) (hG : 0 < G) :
    (((posBox U V).filter fun P => G ∣ P.1).card : ℝ) ≤ 16 * U / G * (2 * V) := by
  have hsub : (posBox U V).filter (fun P => G ∣ P.1) ⊆
      ((Ioc 0 ⌊16 * U⌋₊).filter (fun n => G ∣ n)) ×ˢ (Icc ⌈V⌉₊ ⌊2 * V⌋₊) := by
    intro P hP
    simp only [posBox, mem_filter, mem_product, mem_Icc, mem_Ioc] at hP ⊢
    obtain ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, -⟩, h5⟩ := hP
    have : 1 ≤ ⌈U⌉₊ := Nat.one_le_iff_ne_zero.2 (by
      intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
    exact ⟨⟨⟨by omega, h2⟩, h5⟩, h3, h4⟩
  have h1 := card_le_card hsub
  rw [card_product, Nat.Ioc_filter_dvd_card_eq_div, Nat.card_Icc] at h1
  have h1' : (((posBox U V).filter fun P => G ∣ P.1).card : ℝ) ≤
      ((⌊16 * U⌋₊ / G : ℕ) : ℝ) * ((⌊2 * V⌋₊ + 1 - ⌈V⌉₊ : ℕ) : ℝ) := by exact_mod_cast h1
  have hG' : (0 : ℝ) < G := by exact_mod_cast hG
  have ha : ((⌊16 * U⌋₊ / G : ℕ) : ℝ) ≤ 16 * U / G :=
    Nat.cast_div_le.trans (div_le_div_of_nonneg_right (Nat.floor_le (by positivity)) hG'.le)
  have hb : ((⌊2 * V⌋₊ + 1 - ⌈V⌉₊ : ℕ) : ℝ) ≤ 2 * V := by
    have hc : 1 ≤ ⌈V⌉₊ := Nat.one_le_iff_ne_zero.2 (by
      intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
    have : ⌊2 * V⌋₊ + 1 - ⌈V⌉₊ ≤ ⌊2 * V⌋₊ := by omega
    exact (Nat.cast_le.2 this).trans (Nat.floor_le (by positivity))
  exact h1'.trans (mul_le_mul ha hb (Nat.cast_nonneg _) (by positivity))

lemma sum_inv_listProd (J : ℕ) :
    ∑ ℓ ∈ listCands x a J, (1 : ℝ) / listProd ℓ =
      ∏ i, (groupReciprocalSum x (a i)) ^ (J + 1) := by
  unfold listCands listProd
  calc ∑ ℓ ∈ Fintype.piFinset (fun i => Fintype.piFinset fun _ : Fin (J + 1) => primeGroup x (a i)),
        (1 : ℝ) / ((∏ i, ∏ j, ℓ i j : ℕ) : ℝ)
      = ∑ ℓ ∈ Fintype.piFinset (fun i => Fintype.piFinset fun _ : Fin (J + 1) => primeGroup x (a i)),
          ∏ i, ∏ j, (1 : ℝ) / (ℓ i j : ℝ) := by
        refine sum_congr rfl fun ℓ _ => ?_
        push_cast
        simp only [one_div, prod_inv_distrib]
    _ = ∏ i, ∑ ℓi ∈ Fintype.piFinset (fun _ : Fin (J + 1) => primeGroup x (a i)),
          ∏ j, (1 : ℝ) / (ℓi j : ℝ) :=
        (Finset.prod_univ_sum (fun i => Fintype.piFinset fun _ : Fin (J + 1) => primeGroup x (a i))
          (fun _ ℓi => ∏ j, (1 : ℝ) / (ℓi j : ℝ))).symm
    _ = ∏ i, (groupReciprocalSum x (a i)) ^ (J + 1) := by
        refine prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_univ_sum (fun _ : Fin (J + 1) => primeGroup x (a i))
          (fun _ (q : ℕ) => (1 : ℝ) / q)]
        simp [groupReciprocalSum]

/-- **(3.18)** `σ ∑_s |f(s)|² ≤ 32 U V B²`, `B = sup` of the coefficient sizes, when the groups are
disjoint and all `Vᵢ > 0`. -/
lemma stateNorm_sum_sq_le {J : ℕ} {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (α β : ℕ → ℂ) (B : ℝ)
    (hαB : ∀ m, ‖α m‖ ≤ B) (hβB : ∀ n, ‖β n‖ ≤ B)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) :
    stateNorm x a J * ∑ s : PhysState x a J U V, ‖endpointVec x a J U V α β s‖ ^ 2 ≤
      32 * U * V * B ^ 4 := by
  classical
  have hB : 0 ≤ B := (norm_nonneg _).trans (hαB 0)
  have hpt : ∀ s : PhysState x a J U V, ‖endpointVec x a J U V α β s‖ ^ 2 ≤ B ^ 4 := by
    intro s
    unfold endpointVec
    split_ifs
    · rw [norm_mul, Complex.norm_conj]
      have := mul_le_mul (hαB (s.1.1.1 / groupPart x a s.1.1.1)) (hβB s.1.1.2) (norm_nonneg _) hB
      calc (‖α (s.1.1.1 / groupPart x a s.1.1.1)‖ * ‖β s.1.1.2‖) ^ 2 ≤ (B * B) ^ 2 :=
            pow_le_pow_left₀ (by positivity) this 2
        _ = B ^ 4 := by ring
    · simp; positivity
  have hcard : ((Fintype.card (PhysState x a J U V)) : ℝ) ≤
      ∑ ℓ ∈ listCands x a J, 16 * U / listProd ℓ * (2 * V) := by
    rw [Fintype.card_coe]
    have hsub : stateSet x a J U V ⊆ (posBox U V ×ˢ listCands x a J).filter
        fun s => listProd s.2 ∣ s.1.1 := by
      intro s hs
      refine mem_filter.2 ⟨(mem_filter.1 hs).1, ?_⟩
      exact listProd_dvd_of_disjoint hdisj ⟨s, hs⟩
    have h1 := card_le_card hsub
    have h2 : ((posBox U V ×ˢ listCands x a J).filter fun s => listProd s.2 ∣ s.1.1).card =
        ∑ ℓ ∈ listCands x a J, ((posBox U V).filter fun P => listProd ℓ ∣ P.1).card := by
      rw [card_filter, sum_product_right]
      refine sum_congr rfl fun ℓ _ => ?_
      rw [card_filter]
    rw [h2] at h1
    refine (Nat.cast_le.2 h1).trans ?_
    push_cast
    refine sum_le_sum fun ℓ hℓ => ?_
    have hpos : 0 < listProd ℓ := by
      unfold listProd
      refine prod_pos fun i _ => prod_pos fun j _ => ?_
      exact pos_of_mem_primeGroup (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hℓ i) j)
    exact card_posBox_dvd_le hU hV _ hpos
  have hσ : stateNorm x a J * ∏ i, (groupReciprocalSum x (a i)) ^ (J + 1) = 1 := by
    unfold stateNorm
    rw [← prod_mul_distrib]
    refine prod_eq_one fun i _ => ?_
    rw [← mul_pow, inv_mul_cancel₀ (hVpos i).ne', one_pow]
  have hσ0 : 0 ≤ stateNorm x a J := prod_nonneg fun i _ => by
    have := hVpos i; positivity
  calc stateNorm x a J * ∑ s : PhysState x a J U V, ‖endpointVec x a J U V α β s‖ ^ 2
      ≤ stateNorm x a J * (Fintype.card (PhysState x a J U V) * B ^ 4) := by
        gcongr
        calc ∑ s : PhysState x a J U V, ‖endpointVec x a J U V α β s‖ ^ 2
            ≤ ∑ _s : PhysState x a J U V, B ^ 4 := sum_le_sum fun s _ => hpt s
          _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ stateNorm x a J * ((∑ ℓ ∈ listCands x a J, 16 * U / listProd ℓ * (2 * V)) * B ^ 4) := by
        gcongr
    _ = 32 * U * V * B ^ 4 * (stateNorm x a J * ∑ ℓ ∈ listCands x a J, (1 : ℝ) / listProd ℓ) := by
        rw [mul_sum, mul_sum, sum_mul, mul_sum]
        refine sum_congr rfl fun ℓ _ => ?_
        ring
    _ = 32 * U * V * B ^ 4 := by rw [sum_inv_listProd, hσ, mul_one]

end Norm


/-! ## D5 at one `x` -/

/-- The real-variable step: `σ (3S)^{1/2} S^{(1-1/R)/2} (κF M)^{1/(2R)} ≤ √3 Z κ^{1/(2R)} θ` when
`σ S ≤ Z`, `σ M ≤ m`, `F m ≤ Z θ^{2R}`. -/
lemma real_pairing_step (σ S M Z m κ F θ : ℝ) (R : ℕ) (hR : 2 ≤ R) (hσ : 0 < σ) (hS : 0 ≤ S)
    (hM : 0 ≤ M) (hκ : 0 ≤ κ) (hF : 0 ≤ F) (hθ : 0 ≤ θ) (hSZ : σ * S ≤ Z) (hMm : σ * M ≤ m)
    (hFm : F * m ≤ Z * θ ^ (2 * R)) :
    σ * ((3 * S) ^ (1 / 2 : ℝ) * S ^ ((1 - (R : ℝ)⁻¹) / 2) * (κ * F * M) ^ ((R : ℝ)⁻¹ / 2)) ≤
      Real.sqrt 3 * Z * κ ^ ((R : ℝ)⁻¹ / 2) * θ := by
  have hRr : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hR0 : (0 : ℝ) < R := by linarith
  set e := (R : ℝ)⁻¹ / 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 / 4 := by
    have : (R : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hR0 (by norm_num)]; linarith
    rw [he]; linarith
  have hZ : 0 ≤ Z := le_trans (by positivity) hSZ
  have hsum : (1 / 2 : ℝ) + (1 - (R : ℝ)⁻¹) / 2 = 1 - e := by rw [he]; ring
  -- rewrite in terms of `σS` and `σM`
  have h1 : (3 * S) ^ (1 / 2 : ℝ) * S ^ ((1 - (R : ℝ)⁻¹) / 2) = Real.sqrt 3 * S ^ (1 - e) := by
    rw [Real.mul_rpow (by norm_num) hS, mul_assoc, ← Real.rpow_add' hS (by rw [hsum]; linarith),
      hsum, Real.sqrt_eq_rpow]
  rw [h1]
  have hS' : S ≤ Z / σ := by rw [le_div_iff₀ hσ]; linarith
  have hM' : M ≤ m / σ := by rw [le_div_iff₀ hσ]; linarith
  have hm0 : 0 ≤ m := le_trans (by positivity) hMm
  have hstep : σ * (Real.sqrt 3 * S ^ (1 - e) * (κ * F * M) ^ e) ≤
      σ * (Real.sqrt 3 * (Z / σ) ^ (1 - e) * (κ * F * (m / σ)) ^ e) := by
    gcongr
    · linarith
  refine hstep.trans ?_
  have hsplit : σ * (Real.sqrt 3 * (Z / σ) ^ (1 - e) * (κ * F * (m / σ)) ^ e) =
      Real.sqrt 3 * Z ^ (1 - e) * (κ * (F * m)) ^ e := by
    rw [Real.div_rpow hZ hσ.le, show κ * F * (m / σ) = κ * (F * m) / σ by ring,
      Real.div_rpow (by positivity) hσ.le]
    have hσe : σ ^ (1 - e) * σ ^ e = σ := by
      rw [← Real.rpow_add hσ]; simp
    calc σ * (Real.sqrt 3 * (Z ^ (1 - e) / σ ^ (1 - e)) * ((κ * (F * m)) ^ e / σ ^ e))
        = Real.sqrt 3 * Z ^ (1 - e) * (κ * (F * m)) ^ e * (σ / (σ ^ (1 - e) * σ ^ e)) := by ring
      _ = Real.sqrt 3 * Z ^ (1 - e) * (κ * (F * m)) ^ e := by
          rw [hσe, div_self hσ.ne', mul_one]
  rw [hsplit]
  have hFm' : κ * (F * m) ≤ κ * (Z * θ ^ (2 * R)) := mul_le_mul_of_nonneg_left hFm hκ
  have hpow : (κ * (Z * θ ^ (2 * R))) ^ e = κ ^ e * Z ^ e * θ := by
    rw [Real.mul_rpow hκ (by positivity), Real.mul_rpow hZ (by positivity)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hθ]
    have : ((2 * R : ℕ) : ℝ) * e = 1 := by rw [he]; push_cast; field_simp
    rw [this, Real.rpow_one]; ring
  calc Real.sqrt 3 * Z ^ (1 - e) * (κ * (F * m)) ^ e
      ≤ Real.sqrt 3 * Z ^ (1 - e) * (κ * (Z * θ ^ (2 * R))) ^ e := by
        gcongr
    _ = Real.sqrt 3 * (Z ^ (1 - e) * Z ^ e) * κ ^ e * θ := by rw [hpow]; ring
    _ = Real.sqrt 3 * Z * κ ^ e * θ := by
        rcases hZ.eq_or_lt with h0 | h0
        · simp [← h0, Real.zero_rpow (by linarith : (1 - e) ≠ 0)]
        · rw [← Real.rpow_add h0]; simp

/-- **D5 at one `x`.** With disjoint groups, `Vᵢ > 0`, `R ≥ 2`, `|α|, |β| ≤ B`, and
`re(moment) ≤ U V θ^{2R}`: `‖⟨f, A f⟩_σ‖ ≤ √3 · 32 U V B⁴ · κ^{1/(2R)} · θ`,
`κ = 17 (2⌊256 Δ⌋ + 1)`, `Δ = (5Y + 1) 2d₀`. -/
theorem pairing_le_of_moment {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {U V : ℝ} (A₀ Y : ℝ)
    (R d₀ : ℕ) (hU : 0 < U) (hV : 0 < V) (hY : 0 < Y) (hR : 2 ≤ R) (α β : ℕ → ℂ) (B θ : ℝ)
    (hαB : ∀ m, ‖α m‖ ≤ B) (hβB : ∀ n, ‖β n‖ ≤ B) (hθ : 0 ≤ θ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (hVpos : ∀ i, 0 < groupReciprocalSum x (a i))
    (hmom : (momentSum x a A₀ Y J R d₀ U V).re ≤ U * V * θ ^ (2 * R)) :
    ‖opPairing x a J U V α β (opA x a A₀ Y J d₀ U V)‖ ≤
      Real.sqrt 3 * (32 * U * V * B ^ 4) *
        ((17 * (2 * ⌊256 * ((5 * Y + 1) * (2 * d₀))⌋₊ + 1) : ℕ) : ℝ) ^ ((R : ℝ)⁻¹ / 2) * θ := by
  classical
  have hB : 0 ≤ B := (norm_nonneg _).trans (hαB 0)
  set Δ := (5 * Y + 1) * (2 * (d₀ : ℝ)) with hΔ
  set κ := 17 * (2 * ⌊256 * Δ⌋₊ + 1)
  set f := endpointVec x a J U V α β
  set A := opA x a A₀ Y J d₀ U V
  set σ := stateNorm x a J
  have hσ : 0 < σ := prod_pos fun i _ => by have := hVpos i; positivity
  set pos : PhysState x a J U V → ℕ × ℕ := fun s => s.1.1
  -- the case `A = 0`
  by_cases hA0 : ∀ s s', A s s' = 0
  · have : opPairing x a J U V α β A = 0 := by
      unfold opPairing; simp [hA0]
    rw [this, norm_zero]; positivity
  push Not at hA0
  obtain ⟨s₀, s₀', hs₀⟩ := hA0
  obtain ⟨t₁, t₂, -, -, ht⟩ := opA_ne_zero hs₀
  have hd₀ : 0 < d₀ := by
    obtain ⟨-, hD, -⟩ := rowOp_ne_zero ht
    by_contra h0; push Not at h0
    have : d₀ = 0 := by omega
    subst this
    unfold rowOp at ht
    split_ifs at ht with hc
    · obtain ⟨-, -, -, h2⟩ := hc; omega
    · exact ht rfl
  have hΔ0 : 0 < Δ := by positivity
  -- block structure
  have hblk := norm_qform_le_blocks A R hR pos (slopeBlock U Δ) 1
    (fun s s' h => by
      obtain ⟨s₁, s₂, e₁, e₂, h₁₂⟩ := opA_ne_zero h
      have hdet := (rowOp_ne_zero h₁₂).1
      have hp1 := (state_pos_bounds hU hV s₁).1
      have hp2 := (state_pos_bounds hU hV s₂).1
      have := slopeBlock_near hU hΔ0 hp1 hp2 (by simpa [hΔ] using hdet)
      simp only [pos]; rw [← e₁, ← e₂]; exact_mod_cast this)
    f (fun s s' h => by simp only [f, endpointVec, pos] at h ⊢; rw [h]) (B ^ 2) (by positivity)
    (fun s => by
      simp only [f, endpointVec]
      split_ifs
      · rw [norm_mul, Complex.norm_conj, sq]
        exact mul_le_mul (hαB _) (hβB _) (norm_nonneg _) hB
      · simp; positivity)
    κ (fun j => card_slopeBlock_le _ hU hΔ0 (fun P hP => by
      obtain ⟨s, -, rfl⟩ := mem_image.1 hP
      obtain ⟨h1, h2, h3, -⟩ := state_pos_bounds hU hV s
      exact ⟨h1, h2, h3⟩) j)
  -- norms and moment
  have hS := stateNorm_sum_sq_le hU hV α β B hαB hβB hdisj hVpos (J := J)
  set S := ∑ s, ‖f s‖ ^ 2
  set Mc := ∑ s, ∑ s', if pos s = pos s' then ((A * A.conjTranspose) ^ R) s s' else 0
  have hmom' : σ * Mc.re ≤ U * V * θ ^ (2 * R) := by
    have : (momentSum x a A₀ Y J R d₀ U V).re = σ * Mc.re := by
      unfold momentSum; rw [Complex.re_ofReal_mul]
    rw [← this]; exact hmom
  have hMc0 : 0 ≤ Mc.re := moment_re_nonneg A R pos
  have hS0 : 0 ≤ S := sum_nonneg fun s _ => by positivity
  have hpair : opPairing x a J U V α β A = (σ : ℂ) * qform A f f := rfl
  rw [hpair, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
  refine (mul_le_mul_of_nonneg_left hblk hσ.le).trans ?_
  have hκ0 : (0 : ℝ) ≤ (κ : ℝ) := Nat.cast_nonneg _
  have := real_pairing_step σ S Mc.re (32 * U * V * B ^ 4) (U * V * θ ^ (2 * R)) κ ((B ^ 2) ^ 2)
    θ R hR hσ hS0 hMc0 hκ0 (by positivity) hθ hS hmom' (by
      have hUV : 0 ≤ U * V := by positivity
      rw [show ((B ^ 2) ^ 2 : ℝ) = B ^ 4 by ring]
      have h32 : U * V * B ^ 4 ≤ 32 * U * V * B ^ 4 := by nlinarith [pow_nonneg hB 4]
      calc B ^ 4 * (U * V * θ ^ (2 * R)) = U * V * B ^ 4 * θ ^ (2 * R) := by ring
        _ ≤ 32 * U * V * B ^ 4 * θ ^ (2 * R) := by gcongr)
  have e3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have hW : (((2 * 1 + 1 : ℕ) : ℝ)) = 3 := by norm_num
  rw [hW]
  exact this


/-! ## Large-`x` inputs and D5 -/

/-- For large `x` the prime groups are pairwise disjoint. -/
lemma eventually_disjoint_groups {K : ℕ} (a : Fin K → ℝ) (ha : StrictMono a)
    (_hpos : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
  have hL : ∀ᶠ L : ℝ in Filter.atTop, ∀ i j : Fin K, a i < a j → 2 * L ^ a i < L ^ a j := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hij : a i < a j
    · filter_upwards [eventually_rpow_le_rpow hij (ε := 1 / 3) (by norm_num),
        Filter.eventually_gt_atTop 0] with L h1 h2 _
      have : 0 < L ^ a j := by positivity
      linarith
    · exact Filter.Eventually.of_forall fun L h => absurd h hij
  filter_upwards [Real.tendsto_log_atTop.eventually hL] with x hx
  intro i j hij
  have key : ∀ i j : Fin K, a i < a j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
    intro i j h
    refine Finset.disjoint_left.2 fun p hp hp' => ?_
    have h1 := (le_of_mem_primeGroup hp).2
    have h2 := (le_of_mem_primeGroup hp').1
    have := exp_lt_exp.2 (hx i j h)
    linarith
  rcases lt_or_gt_of_ne (ha.injective.ne hij) with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- For large `x` every group is nonempty (Bertrand), so every `Vᵢ > 0`. -/
lemma eventually_groupReciprocalSum_pos {K : ℕ} (a : Fin K → ℝ) (hpos : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i, 0 < groupReciprocalSum x (a i) := by
  refine Filter.eventually_all.2 fun i => ?_
  have hy : Filter.Tendsto (fun x : ℝ => log x ^ a i) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (hpos i)).comp tendsto_log_atTop
  filter_upwards [hy.eventually_ge_atTop 2] with x hx
  set y := exp (log x ^ a i)
  have hy3 : 3 ≤ y := by
    have : exp 2 ≤ y := exp_le_exp.2 hx
    linarith [Real.exp_one_gt_d9, Real.add_one_le_exp (1 : ℝ), show exp 2 = exp 1 * exp 1 by
      rw [← exp_add]; norm_num, show (2.7182818283 : ℝ) * 2.7182818283 ≥ 3 by norm_num,
      mul_le_mul (le_of_lt Real.exp_one_gt_d9) (le_of_lt Real.exp_one_gt_d9) (by norm_num)
        (exp_pos 1).le]
  set n := ⌈y⌉₊
  have hn0 : n ≠ 0 := by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith
  obtain ⟨p, hp, hnp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul n hn0
  have hmem : p ∈ primeGroup x (a i) := by
    unfold primeGroup
    refine mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor ?_)), hp, ?_⟩
    · have h1 : (n : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
      have h2 : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2
      have h3 : exp (2 * log x ^ a i) = y * y := by rw [← exp_add]; ring_nf
      rw [h3]; nlinarith
    · have : (n : ℝ) < p := by exact_mod_cast hnp
      linarith [Nat.le_ceil y]
  have : 0 < (1 : ℝ) / p := by have := hp.pos; positivity
  exact lt_of_lt_of_le this (single_le_sum (f := fun q : ℕ => (1 : ℝ) / q)
    (fun q _ => by positivity) hmem)

lemma entry_le_of_state {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {U V : ℝ}
    (hL1 : 1 ≤ log x) (hab : ∀ i, a i < 0.2) (s : PhysState x a J U V) (i : Fin K)
    (j : Fin (J + 1)) : (s.1.2 i j : ℝ) ≤ exp (2 * log x ^ (0.2 : ℝ)) := by
  have hcand := (mem_product.1 (mem_filter.1 s.2).1).2
  have hg := Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hcand i) j
  refine (le_of_mem_primeGroup hg).2.trans (exp_le_exp.2 ?_)
  have := Real.rpow_le_rpow_of_exponent_le hL1 (hab i).le
  linarith

/-- **D5 (PROVED).** -/
theorem pairing_from_moment (δ C c₁ c₂ : ℝ) : PairingFromMomentStmt δ C c₁ c₂ := by
  intro A₀ _hA₀ K hK a ha hab
  have hapos : ∀ i, 0 < a i := fun i => (by norm_num : (0 : ℝ) < 0.1).trans (hab i).1
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hLc : ∀ᶠ L : ℝ in Filter.atTop, 3 ≤ L ∧ 12 + 4 * K * L ^ (0.21 : ℝ) ≤ L ^ (0.5 : ℝ) := by
    have e1 := eventually_rpow_le_rpow (b := 0.21) (c := 0.5) (by norm_num) (ε := 1 / (8 * K))
      (by positivity)
    have e2 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.5)).eventually_ge_atTop 24
    filter_upwards [e1, e2, Filter.eventually_ge_atTop 3] with L h1 h2 h3
    refine ⟨h3, ?_⟩
    have : 4 * K * L ^ (0.21 : ℝ) ≤ L ^ (0.5 : ℝ) / 2 := by
      calc 4 * K * L ^ (0.21 : ℝ) ≤ 4 * K * (1 / (8 * K) * L ^ (0.5 : ℝ)) := by gcongr
        _ = L ^ (0.5 : ℝ) / 2 := by field_simp; ring
    linarith
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    ((eventually_disjoint_groups a ha hapos).and ((eventually_groupReciprocalSum_pos a hapos).and
      ((Real.tendsto_log_atTop.eventually hLc).and (Filter.eventually_gt_atTop 0))))
  refine ⟨56, x₀, fun x Hm Hn hx hm hn h1 h2 α β hαs hβs hαb hβb Y hY k E₀ hE₀ hmom => ?_⟩
  obtain ⟨hdisj, hVpos, ⟨hL3, hLR⟩, hxpos⟩ := hx₀ x hx
  set L := log x with hLdef
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hHm : 0 < Hm := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hm
  have hHn : 0 < Hn := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hn
  have hY0 : 0 < Y := by linarith
  set U := 2 ^ k * Y * Hm with hUdef
  have hU : 0 < U := by positivity
  set R := momentPower x
  set J := padCount x
  have h2R : L ^ (0.5 : ℝ) ≤ 2 * R := by
    have := Nat.le_ceil (L ^ (0.5 : ℝ) / 2); simp only [R, momentPower]; linarith
  have hR : 2 ≤ R := by
    have : (1 : ℝ) < R := by have := Real.rpow_nonneg hL0.le (0.21 : ℝ); nlinarith
    have : 1 < R := by exact_mod_cast this
    omega
  set θ := L ^ (-E₀)
  have hθ : 0 ≤ θ := by positivity
  have hmom' : (momentSum x a A₀ Y J R (2 ^ k) U Hn).re ≤ U * Hn * θ ^ (2 * R) := by
    have e : θ ^ (2 * R) = L ^ (-(E₀ * (2 * (R : ℝ)))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; push_cast; ring_nf
    rw [e]
    have := hmom
    simp only [dyadMoment] at this
    calc _ ≤ 2 ^ k * Y * Hm * Hn * L ^ (-(E₀ * (2 * (R : ℝ)))) := this
      _ = U * Hn * L ^ (-(E₀ * (2 * (R : ℝ)))) := by rw [hUdef]
  have hmain := pairing_le_of_moment (x := x) (a := a) (J := J) A₀ Y R (2 ^ k) hU hHn hY0 hR α β
    (L ^ C) θ hαb hβb hθ hdisj hVpos hmom'
  have hgoal_nonneg : 0 ≤ 56 * (2 ^ k * Y * Hm * Hn * L ^ (4 * C + 1 - E₀)) := by positivity
  show ‖opPairing x a J U Hn α β (opA x a A₀ Y J (2 ^ k) U Hn)‖ ≤ _
  by_cases hA0 : ∀ s s', opA x a A₀ Y J (2 ^ k) U Hn s s' = 0
  · have : opPairing x a J U Hn α β (opA x a A₀ Y J (2 ^ k) U Hn) = 0 := by
      unfold opPairing; simp [hA0]
    rw [this, norm_zero]; exact hgoal_nonneg
  push Not at hA0
  obtain ⟨s₀, s₀', hs₀⟩ := hA0
  obtain ⟨t₁, t₂, -, -, ht⟩ := opA_ne_zero hs₀
  obtain ⟨-, hdD, hη⟩ := rowOp_ne_zero ht
  have hYlast : Y < (lastProd t₁.1.2 : ℝ) := by
    have := (dyadicBump_ne_zero hη).1
    rwa [one_lt_div hY0] at this
  set E := exp (2 * L ^ (0.2 : ℝ))
  have hE1 : 1 ≤ E := one_le_exp (by positivity)
  have hent := fun i j => entry_le_of_state (U := U) (V := Hn) hL1 (fun i => (hab i).2) t₁ i j
  have hpad : (padProd t₁.1.2 : ℝ) ≤ (E ^ J) ^ K := by
    unfold padProd; push_cast
    calc ∏ i, ∏ j : Fin J, (t₁.1.2 i j.castSucc : ℝ) ≤ ∏ _i : Fin K, ∏ _j : Fin J, E :=
          prod_le_prod (fun i _ => prod_nonneg fun j _ => Nat.cast_nonneg _)
            fun i _ => prod_le_prod (fun j _ => Nat.cast_nonneg _) fun j _ => hent i _
      _ = (E ^ J) ^ K := by simp
  have hlast : (lastProd t₁.1.2 : ℝ) ≤ E ^ K := by
    unfold lastProd; push_cast
    calc ∏ i, (t₁.1.2 i (Fin.last J) : ℝ) ≤ ∏ _i : Fin K, E :=
          prod_le_prod (fun i _ => Nat.cast_nonneg _) fun i _ => hent i _
      _ = E ^ K := by simp
  have hEK : 1 ≤ E ^ K := one_le_pow₀ hE1
  have hEJK : 1 ≤ (E ^ J) ^ K := one_le_pow₀ (one_le_pow₀ hE1)
  set Δ := (5 * Y + 1) * (2 * ((2 ^ k : ℕ) : ℝ))
  have hd : ((2 ^ k : ℕ) : ℝ) ≤ (E ^ J) ^ K := (Nat.cast_le.2 hdD).trans hpad
  have hΔ : Δ ≤ 12 * (E ^ K * (E ^ J) ^ K) := by
    have hY' : Y ≤ E ^ K := hYlast.le.trans hlast
    show (5 * Y + 1) * (2 * ((2 ^ k : ℕ) : ℝ)) ≤ 12 * (E ^ K * (E ^ J) ^ K)
    calc (5 * Y + 1) * (2 * ((2 ^ k : ℕ) : ℝ)) ≤ (6 * E ^ K) * (2 * (E ^ J) ^ K) :=
          mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = 12 * (E ^ K * (E ^ J) ^ K) := by ring
  set κ := 17 * (2 * ⌊256 * Δ⌋₊ + 1)
  have hκ : (κ : ℝ) ≤ 104465 * (E ^ K * (E ^ J) ^ K) := by
    have hfl : (⌊256 * Δ⌋₊ : ℝ) ≤ 256 * Δ := Nat.floor_le (by positivity)
    have h1' : 1 ≤ E ^ K * (E ^ J) ^ K := one_le_mul_of_one_le_of_one_le hEK hEJK
    simp only [κ]; push_cast
    nlinarith
  have hJ : (J : ℝ) + 1 ≤ 2 * L ^ (0.01 : ℝ) := by
    have h1' : (J : ℝ) ≤ L ^ (0.01 : ℝ) := Nat.floor_le (by positivity)
    have h2' : 1 ≤ L ^ (0.01 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    linarith
  have hlogκ : (κ : ℝ) ≤ exp (2 * R) := by
    have hEE : E ^ K * (E ^ J) ^ K = exp (K * ((J : ℝ) + 1) * (2 * L ^ (0.2 : ℝ))) := by
      rw [← pow_mul, ← pow_add, ← exp_nat_mul]; congr 1; push_cast; ring
    have h104 : (104465 : ℝ) ≤ exp 12 := by
      have := Real.exp_one_gt_d9
      have h12 : exp 12 = exp 1 ^ 12 := by rw [← exp_nat_mul]; norm_num
      rw [h12]
      calc (104465 : ℝ) ≤ 2.7182818283 ^ 12 := by norm_num
        _ ≤ exp 1 ^ 12 := by gcongr
    have hexp : K * ((J : ℝ) + 1) * (2 * L ^ (0.2 : ℝ)) ≤ 4 * K * L ^ (0.21 : ℝ) := by
      have hp : L ^ (0.01 : ℝ) * L ^ (0.2 : ℝ) = L ^ (0.21 : ℝ) := by
        rw [← Real.rpow_add hL0]; norm_num
      have := Real.rpow_nonneg hL0.le (0.2 : ℝ)
      calc K * ((J : ℝ) + 1) * (2 * L ^ (0.2 : ℝ)) ≤ K * (2 * L ^ (0.01 : ℝ)) * (2 * L ^ (0.2 : ℝ)) := by
            gcongr
        _ = 4 * K * (L ^ (0.01 : ℝ) * L ^ (0.2 : ℝ)) := by ring
        _ = 4 * K * L ^ (0.21 : ℝ) := by rw [hp]
    calc (κ : ℝ) ≤ 104465 * (E ^ K * (E ^ J) ^ K) := hκ
      _ ≤ exp 12 * exp (4 * K * L ^ (0.21 : ℝ)) := by
          rw [hEE]; gcongr
      _ = exp (12 + 4 * K * L ^ (0.21 : ℝ)) := by rw [exp_add]
      _ ≤ exp (2 * R) := exp_le_exp.2 (by linarith)
  have hκe : (κ : ℝ) ^ ((R : ℝ)⁻¹ / 2) ≤ L := by
    have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
    have hLe : exp 1 ≤ L := by
      have := Real.exp_one_lt_d9; linarith
    calc (κ : ℝ) ^ ((R : ℝ)⁻¹ / 2) ≤ (exp (2 * R)) ^ ((R : ℝ)⁻¹ / 2) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hlogκ (by positivity)
      _ = exp 1 := by rw [← Real.exp_mul]; congr 1; field_simp
      _ ≤ L := hLe
  refine hmain.trans ?_
  have hsqrt : Real.sqrt 3 ≤ 7 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB4 : (L ^ C) ^ 4 = L ^ (4 * C) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
  have hfin : L ^ (4 * C) * L * θ = L ^ (4 * C + 1 - E₀) := by
    rw [show 4 * C + 1 - E₀ = 4 * C + 1 + -E₀ by ring, Real.rpow_add hL0, Real.rpow_add hL0,
      Real.rpow_one]
  have hκ0 : (0 : ℝ) ≤ (κ : ℝ) ^ ((R : ℝ)⁻¹ / 2) := by positivity
  calc Real.sqrt 3 * (32 * U * Hn * (L ^ C) ^ 4) * (κ : ℝ) ^ ((R : ℝ)⁻¹ / 2) * θ
      ≤ 7 / 4 * (32 * U * Hn * (L ^ C) ^ 4) * L * θ := by
        gcongr
    _ = 56 * (U * Hn * (L ^ (4 * C) * L * θ)) := by rw [hB4]; ring
    _ = 56 * (2 ^ k * Y * Hm * Hn * L ^ (4 * C + 1 - E₀)) := by rw [hfin, hUdef]

end ArtinPrimitiveRoots.L102D
end

section
/-! Check module: `chk_minor_square_bound`, the published statement `minor_square_bound` verbatim, proved from the
development and the cuts `re_dyadMoment_le`, `norm_dyadPairingSTS_sub_dyadPairingA_le`, `norm_minorSquare_sub_sum_dyadPairingSTS_le`. -/

namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ A : ℝ, 0 < A → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y →
            ‖minorSquare x a A₀ Y Hm Hn α β‖ ≤ c * (Hm * Hn * Y * log x ^ (-A)) :=
  L102D.minor_square_bound_of_cuts δ C c₁ c₂ hC (re_dyadMoment_le δ c₁ c₂ hδ)
    (L102D.pairing_from_moment δ C c₁ c₂) (norm_dyadPairingSTS_sub_dyadPairingA_le δ C c₁ c₂ hδ)
    (norm_minorSquare_sub_sum_dyadPairingSTS_le δ C c₁ c₂ hc₁)
end
