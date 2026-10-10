-- Prove2me | solution 1 for ArtinPrimitiveRoots.opBound_ghost_of_norm_le_ghostCoeff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:19:21.276724+00:00
-- url     : https://prove2.me/submissions/7fee89ac-a6d8-445f-9400-75ef71981420

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinMemoryModel
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare
section
/-! # L102D_OpDefs — alias of the bundle `Def_ArtinMinorOperator` (round 5)

The operator model now lives in `Definitions/Def_ArtinMinorOperator.lean` (same declarations, same
names). This module re-exports it and keeps `listProd`, which only the proofs use. -/

namespace ArtinPrimitiveRoots

end ArtinPrimitiveRoots
end

section
/-! # L102D_MemDefs — alias of the bundle `Def_ArtinMemoryModel` (round 5)

The memory model (root coordinates, `pathPhi`, `rootIL`, the memory space, `ghostOp`, `edgeOp`,
`memMomentD`, `dyadParams`, and `MemParams.RootIn`) now lives in
`Definitions/Def_ArtinMemoryModel.lean` (same declarations, same names). -/
end

section
/-! # L102D: basic facts about the memory parameters (no stubs)

`etav_mem`, `bprime_mem` (`0 < b'_p ≤ 1` once `N < p`), `bprime_ge_half`, `abs_baseline_le`, and
the asymptotic fact that the group primes eventually exceed any fixed multiple of `R + 1`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

lemma etav_mem (P : MemParams) (j : ℕ) : 0 ≤ P.etav j ∧ P.etav j ≤ 1 := by
  unfold MemParams.etav MemParams.qv
  split_ifs <;> norm_num

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the weighted Schur test for choice-indexed operators

An operator in the row convention, `(O f)(s) = ∑_{c ∈ Ch} coeff(s, c) f(out(s, c))` (outputs
outside the state set `St` dropped), on `ℓ²(St, μ)`. With a positive Schur weight `w`, a weighted
row bound `R` and a weighted column bound `C` give `‖O f‖² ≤ R C ‖f‖²` ([21] §4.4). -/

namespace ArtinPrimitiveRoots.L102D

open Finset

variable {α γ : Type*} [DecidableEq α]

/-- The choice-indexed operator. -/
def choiceOp (St : Finset α) (Ch : Finset γ) (coeff : α → γ → ℂ) (out : α → γ → α)
    (f : α → ℂ) (s : α) : ℂ :=
  ∑ c ∈ Ch, coeff s c * (if out s c ∈ St then f (out s c) else 0)

/-- **Weighted Schur test.** -/
theorem schur_choiceOp (St : Finset α) (Ch : Finset γ) (coeff : α → γ → ℂ) (out : α → γ → α)
    (μ w : α → ℝ) (R C : ℝ) (hμ : ∀ s ∈ St, 0 ≤ μ s) (hw : ∀ s ∈ St, 0 < w s)
    (hR : 0 ≤ R)
    (hrow : ∀ s ∈ St, ∑ c ∈ Ch, ‖coeff s c‖ * (if out s c ∈ St then w (out s c) else 0) ≤
      R * w s)
    (hcol : ∀ s' ∈ St, ∑ s ∈ St, ∑ c ∈ Ch,
      (if out s c = s' then μ s * w s * ‖coeff s c‖ else 0) ≤ C * (μ s' * w s'))
    (f : α → ℂ) :
    ∑ s ∈ St, μ s * ‖choiceOp St Ch coeff out f s‖ ^ 2 ≤ R * C * ∑ s ∈ St, μ s * ‖f s‖ ^ 2 := by
  -- the pointwise Cauchy–Schwarz step
  set a : α → γ → ℝ := fun s c => ‖coeff s c‖ * (if out s c ∈ St then 1 else 0) with ha
  have hpt : ∀ s ∈ St, ‖choiceOp St Ch coeff out f s‖ ^ 2 ≤
      R * w s * ∑ c ∈ Ch, a s c * (‖f (out s c)‖ ^ 2 / w (out s c)) := by
    intro s hs
    have h1 : ‖choiceOp St Ch coeff out f s‖ ≤ ∑ c ∈ Ch, a s c * ‖f (out s c)‖ := by
      unfold choiceOp
      refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
      rw [norm_mul, ha]
      by_cases hc : out s c ∈ St
      · simp only [if_pos hc, mul_one]; exact le_refl _
      · simp [hc]
    have hcs : (∑ c ∈ Ch, a s c * ‖f (out s c)‖) ^ 2 ≤
        (∑ c ∈ Ch, a s c * (if out s c ∈ St then w (out s c) else 0)) *
          ∑ c ∈ Ch, a s c * (‖f (out s c)‖ ^ 2 / w (out s c)) := by
      have := sum_mul_sq_le_sq_mul_sq Ch
        (fun c => √(a s c * (if out s c ∈ St then w (out s c) else 0)))
        (fun c => √(a s c * (‖f (out s c)‖ ^ 2 / w (out s c))))
      have e1 : ∀ c ∈ Ch, √(a s c * (if out s c ∈ St then w (out s c) else 0)) *
          √(a s c * (‖f (out s c)‖ ^ 2 / w (out s c))) = a s c * ‖f (out s c)‖ := by
        intro c _
        by_cases hc : out s c ∈ St
        · have hwp := hw _ hc
          have ha0 : 0 ≤ a s c := by rw [ha]; positivity
          rw [if_pos hc, ← Real.sqrt_mul (by positivity)]
          have : a s c * w (out s c) * (a s c * (‖f (out s c)‖ ^ 2 / w (out s c))) =
              (a s c * ‖f (out s c)‖) ^ 2 := by field_simp
          rw [this, Real.sqrt_sq (by positivity)]
        · have : a s c = 0 := by rw [ha]; simp [hc]
          simp [this]
      have e2 : ∀ c ∈ Ch, √(a s c * (if out s c ∈ St then w (out s c) else 0)) ^ 2 =
          a s c * (if out s c ∈ St then w (out s c) else 0) := by
        intro c _
        apply Real.sq_sqrt
        have ha0 : 0 ≤ a s c := by rw [ha]; positivity
        split_ifs with hc
        · exact mul_nonneg ha0 (hw _ hc).le
        · simp
      have e3 : ∀ c ∈ Ch, √(a s c * (‖f (out s c)‖ ^ 2 / w (out s c))) ^ 2 =
          a s c * (‖f (out s c)‖ ^ 2 / w (out s c)) := by
        intro c _
        apply Real.sq_sqrt
        by_cases hc : out s c ∈ St
        · have ha0 : 0 ≤ a s c := by rw [ha]; positivity
          have := hw _ hc
          positivity
        · have : a s c = 0 := by rw [ha]; simp [hc]
          simp [this]
      rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3] at this
      exact this
    have hrow' : ∑ c ∈ Ch, a s c * (if out s c ∈ St then w (out s c) else 0) ≤ R * w s := by
      refine le_trans (le_of_eq (sum_congr rfl fun c _ => ?_)) (hrow s hs)
      rw [ha]; by_cases hc : out s c ∈ St <;> simp [hc]
    have hnn : 0 ≤ ∑ c ∈ Ch, a s c * (‖f (out s c)‖ ^ 2 / w (out s c)) := by
      refine sum_nonneg fun c _ => ?_
      by_cases hc : out s c ∈ St
      · have ha0 : 0 ≤ a s c := by rw [ha]; positivity
        have := hw _ hc
        positivity
      · have : a s c = 0 := by rw [ha]; simp [hc]
        simp [this]
    calc ‖choiceOp St Ch coeff out f s‖ ^ 2 ≤ (∑ c ∈ Ch, a s c * ‖f (out s c)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := hcs
      _ ≤ R * w s * ∑ c ∈ Ch, a s c * (‖f (out s c)‖ ^ 2 / w (out s c)) :=
          mul_le_mul_of_nonneg_right hrow' hnn
  -- sum over states and regroup by the output
  have hsum : ∑ s ∈ St, μ s * ‖choiceOp St Ch coeff out f s‖ ^ 2 ≤
      R * ∑ s ∈ St, ∑ c ∈ Ch, μ s * w s * a s c * (‖f (out s c)‖ ^ 2 / w (out s c)) := by
    rw [mul_sum]
    refine sum_le_sum fun s hs => ?_
    calc μ s * ‖choiceOp St Ch coeff out f s‖ ^ 2 ≤
        μ s * (R * w s * ∑ c ∈ Ch, a s c * (‖f (out s c)‖ ^ 2 / w (out s c))) :=
          mul_le_mul_of_nonneg_left (hpt s hs) (hμ s hs)
      _ = R * ∑ c ∈ Ch, μ s * w s * a s c * (‖f (out s c)‖ ^ 2 / w (out s c)) := by
          rw [mul_sum, mul_sum, mul_sum]; refine sum_congr rfl fun c _ => by ring
  have hregroup : ∑ s ∈ St, ∑ c ∈ Ch, μ s * w s * a s c * (‖f (out s c)‖ ^ 2 / w (out s c)) =
      ∑ s' ∈ St, (‖f s'‖ ^ 2 / w s') * ∑ s ∈ St, ∑ c ∈ Ch,
        (if out s c = s' then μ s * w s * ‖coeff s c‖ else 0) := by
    have : ∀ s ∈ St, ∀ c ∈ Ch, μ s * w s * a s c * (‖f (out s c)‖ ^ 2 / w (out s c)) =
        ∑ s' ∈ St, (‖f s'‖ ^ 2 / w s') *
          (if out s c = s' then μ s * w s * ‖coeff s c‖ else 0) := by
      intro s _ c _
      rw [ha]
      by_cases hc : out s c ∈ St
      · rw [sum_eq_single (out s c)]
        · simp only [if_pos hc, if_true, mul_one]; ring
        · intro b _ hb; rw [if_neg (Ne.symm hb), mul_zero]
        · intro h; exact absurd hc h
      · simp only [if_neg hc, mul_zero, zero_mul]
        refine (sum_eq_zero fun s' hs' => ?_).symm
        have : out s c ≠ s' := fun h => hc (h ▸ hs')
        rw [if_neg this, mul_zero]
    calc ∑ s ∈ St, ∑ c ∈ Ch, μ s * w s * a s c * (‖f (out s c)‖ ^ 2 / w (out s c))
        = ∑ s ∈ St, ∑ c ∈ Ch, ∑ s' ∈ St, (‖f s'‖ ^ 2 / w s') *
            (if out s c = s' then μ s * w s * ‖coeff s c‖ else 0) :=
          sum_congr rfl fun s hs => sum_congr rfl fun c hc => this s hs c hc
      _ = ∑ s ∈ St, ∑ s' ∈ St, ∑ c ∈ Ch, (‖f s'‖ ^ 2 / w s') *
            (if out s c = s' then μ s * w s * ‖coeff s c‖ else 0) :=
          sum_congr rfl fun s _ => sum_comm
      _ = ∑ s' ∈ St, ∑ s ∈ St, ∑ c ∈ Ch, (‖f s'‖ ^ 2 / w s') *
            (if out s c = s' then μ s * w s * ‖coeff s c‖ else 0) := sum_comm
      _ = _ := by
          refine sum_congr rfl fun s' _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun s _ => (mul_sum _ _ _).symm
  have hfin : ∑ s' ∈ St, (‖f s'‖ ^ 2 / w s') * ∑ s ∈ St, ∑ c ∈ Ch,
      (if out s c = s' then μ s * w s * ‖coeff s c‖ else 0) ≤
      C * ∑ s ∈ St, μ s * ‖f s‖ ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun s' hs' => ?_
    have hwp := hw s' hs'
    calc (‖f s'‖ ^ 2 / w s') * ∑ s ∈ St, ∑ c ∈ Ch,
          (if out s c = s' then μ s * w s * ‖coeff s c‖ else 0) ≤
        (‖f s'‖ ^ 2 / w s') * (C * (μ s' * w s')) :=
          mul_le_mul_of_nonneg_left (hcol s' hs') (by positivity)
      _ = C * (μ s' * ‖f s'‖ ^ 2) := by field_simp
  calc ∑ s ∈ St, μ s * ‖choiceOp St Ch coeff out f s‖ ^ 2 ≤ _ := hsum
    _ = R * ∑ s' ∈ St, (‖f s'‖ ^ 2 / w s') * ∑ s ∈ St, ∑ c ∈ Ch,
        (if out s c = s' then μ s * w s * ‖coeff s c‖ else 0) := by rw [hregroup]
    _ ≤ R * (C * ∑ s ∈ St, μ s * ‖f s‖ ^ 2) := mul_le_mul_of_nonneg_left hfin hR
    _ = R * C * ∑ s ∈ St, μ s * ‖f s‖ ^ 2 := by ring

end ArtinPrimitiveRoots.L102D
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

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the cuts of D7 (the moment (4.1)) and the reduction

Seven statements about the draft model `L102D_OpDefs` + `L102D_MemDefs`, in the order of the
proof of [21] Proposition 4.1:

* `PathExpansionStmt` (D7p, exact): the physical moment is the sum over primitive roots `P₀` of
  the path functional in root coordinates, [21] §3.5 (3.30)–(3.32).
* `RootReplacementStmt` (D7r, [21] Lemma 3.4): the sum over roots is `UV/ζ(2)` times the integral
  of the independent-line moment over `[1,16] × [1,2] × [0,1]`, up to `UV L^{-AN}`.
* `MemoryIdentityStmt` (D7a, exact, [21] (4.5)–(4.15)): the independent-line moment is the
  baseline times the memory moment with global birth distinctness (no truncation).
* `TruncationStmt` (D7b, [21] (4.16)): truncating the memory at `B = ⌈L²⌉` costs `L^{-AN}`.
* `GhostBoundStmt` (D7c, [21] (4.19)–(4.22)): `‖G_j‖ ≤ C_K` on `H_B`.
* `EdgeBoundStmt` (D7d, [21] (4.23)–(4.42)): `‖E_j‖ ≤ L^{-G}` on `H_B`, `A₀` and then `K` large.
* `DistinctnessStmt` (D7e, [21] (4.43)–(4.55)): given D7c and D7d, the truncated memory moment
  with global birth distinctness is `≤ L^{-(G-1)N}`.

`moment_bound_of_cuts` proves `MomentBoundStmt` (D7) from them. -/

-- `MemParams.RootIn` now lives in the bundle `Def_ArtinMemoryModel` (round 5).

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D7c, the ghost bound ([21] (4.19)–(4.22))

Weighted Schur test with the weight `w = v₀^{memory size}`, `v₀ = 12`. The ghost coefficient is a
product over particle types (`gAbs`), so the weighted row and column sums factor:
* row, per hit type: `∑_{u ≤ n} C(n,u) (η'/ρ)^u (q/ρ²)^{n−u} v₀^{n−u} · ∑_v (v₀ η'Vλ/ρ)^v/v!
  ≤ v₀^n (η'/(ρv₀) + q/ρ²)^n exp(v₀η'Vλ/ρ)`;
* column, per hit type (input count `n' − v + u` for output count `n'`):
  `λ^{n'} v₀^{n'}/n'! · (q/ρ² + η'V/(ρ v₀))^{n'} · exp(v₀ η' λ/ρ)`.
With `ρ = 3/4`, `q_j ∈ {1/2, 1/4}`, `Vᵢ ≤ 3/2` (Mertens, through the stub) the parentheses are
`≤ 1`, and `∑_{hits} λ ≤ ∑ᵢ ∑_p νᵢ(p) ≤ 2K` once `b'_p ≥ 1/2`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

section GhostAlg

variable (P : MemParams)

/-- The absolute ghost factor of one particle type: input count `n`, deleted `u`, born `v`. -/
noncomputable def gAbs (j : ℕ) (z : ℤ × ℤ) (y : P.PT) (n u v : ℕ) : ℝ :=
  if P.IsHit z y then
    (if u ≤ n then (n.choose u : ℝ) * (P.etav j / memRho) ^ u * (P.qv j / memRho ^ 2) ^ (n - u) *
      (P.etav j * P.Vg y.1.1 / memRho * P.lam y) ^ v / (v.factorial : ℝ) else 0)
  else (if u = 0 ∧ v = 0 then 1 else 0)

lemma memRho_pos : (0 : ℝ) < memRho := by unfold memRho; norm_num

lemma qv_nonneg (j : ℕ) : 0 ≤ P.qv j := by unfold MemParams.qv; split_ifs <;> norm_num

lemma gAbs_nonneg (j : ℕ) (z : ℤ × ℤ) (y : P.PT) (n u v : ℕ) (hV : 0 ≤ P.Vg y.1.1)
    (hl : 0 ≤ P.lam y) : 0 ≤ gAbs P j z y n u v := by
  have := (etav_mem P j).1
  have := qv_nonneg P j
  have := memRho_pos
  unfold gAbs
  split_ifs <;> positivity

lemma norm_ghostCoeff_le (j : ℕ) (s : P.MState) (c : P.Mem × P.Mem)
    (hV : ∀ i, 0 ≤ P.Vg i) (hl : ∀ y, 0 ≤ P.lam y) :
    ‖P.ghostCoeff j s c‖ ≤ ∏ y, gAbs P j s.1 y (s.2.2 y) (c.1 y) (c.2 y) := by
  have hη := (etav_mem P j).1
  have hq := qv_nonneg P j
  have hρ := memRho_pos
  unfold MemParams.ghostCoeff
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_prod]
    refine prod_le_prod (fun y _ => abs_nonneg _) fun y _ => ?_
    unfold gAbs
    by_cases hy : P.IsHit s.1 y
    · rw [if_pos hy, if_pos hy, if_pos (h.1 y)]
      have e : ((s.2.2 y).choose (c.1 y) : ℝ) * (-P.etav j / memRho) ^ c.1 y *
          (P.qv j / memRho ^ 2) ^ (s.2.2 y - c.1 y) *
          (-P.etav j * P.Vg y.1.1 / memRho) ^ c.2 y * P.lam y ^ c.2 y /
            ((c.2 y).factorial : ℝ) =
          (-1) ^ (c.1 y + c.2 y) * (((s.2.2 y).choose (c.1 y) : ℝ) *
            (P.etav j / memRho) ^ c.1 y * (P.qv j / memRho ^ 2) ^ (s.2.2 y - c.1 y) *
            (P.etav j * P.Vg y.1.1 / memRho * P.lam y) ^ c.2 y / ((c.2 y).factorial : ℝ)) := by
        rw [pow_add, mul_pow (P.etav j * P.Vg y.1.1 / memRho), neg_div, neg_pow,
          neg_mul, neg_div, neg_pow]
        ring
      rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by have := hV y.1.1; have := hl y; positivity)]
    · rw [if_neg hy, if_neg hy, abs_one, if_pos ⟨(h.2 y hy).1, (h.2 y hy).2⟩]
  · rw [norm_zero]
    exact prod_nonneg fun y _ => gAbs_nonneg P j _ y _ _ _ (hV _) (hl y)

/-- The weighted row sum of one particle type. -/
lemma row_type (j : ℕ) (z : ℤ × ℤ) (y : P.PT) (n : ℕ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hV : 0 ≤ P.Vg y.1.1) (hl : 0 ≤ P.lam y)
    (hX : P.etav j / memRho / v₀ + P.qv j / memRho ^ 2 ≤ 1) :
    ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1), gAbs P j z y n u v * v₀ ^ (n - u + v) ≤
      v₀ ^ n * (if P.IsHit z y then
        exp (v₀ * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1) := by
  have hη := (etav_mem P j).1
  have hq := qv_nonneg P j
  have hρ := memRho_pos
  unfold gAbs
  by_cases hy : P.IsHit z y
  · simp only [if_pos hy]
    set X := P.etav j / memRho
    set Q := P.qv j / memRho ^ 2
    set W := P.etav j * P.Vg y.1.1 / memRho * P.lam y
    have hX0 : 0 ≤ X := by positivity
    have hQ0 : 0 ≤ Q := by positivity
    have hW0 : 0 ≤ W := by positivity
    have hsplit : ∀ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1),
        (if u ≤ n then (n.choose u : ℝ) * X ^ u * Q ^ (n - u) * W ^ v / (v.factorial : ℝ)
          else 0) * v₀ ^ (n - u + v) =
        (if u ≤ n then (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) else 0) *
          ∑ v ∈ range (P.B + 1), (v₀ * W) ^ v / (v.factorial : ℝ) := by
      intro u _
      rw [mul_sum]
      refine sum_congr rfl fun v _ => ?_
      split_ifs
      · rw [pow_add, mul_pow, mul_pow]; ring
      · simp
    rw [sum_congr rfl hsplit, ← sum_mul]
    have hexp : ∑ v ∈ range (P.B + 1), (v₀ * W) ^ v / (v.factorial : ℝ) ≤ exp (v₀ * W) :=
      Real.sum_le_exp_of_nonneg (by positivity) _
    have hbin : ∑ u ∈ range (P.B + 1),
        (if u ≤ n then (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) else 0) ≤ v₀ ^ n := by
      have h1 : ∑ u ∈ range (P.B + 1),
          (if u ≤ n then (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) else 0) ≤
          ∑ u ∈ range (n + 1), (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) := by
        rw [← sum_filter]
        refine sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) (fun u _ _ => by positivity)
        simp only [mem_filter, mem_range] at hu ⊢; omega
      have h2 : ∑ u ∈ range (n + 1), (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) =
          (X + Q * v₀) ^ n := by
        rw [add_pow]; refine sum_congr rfl fun u _ => by ring
      have h3 : X + Q * v₀ = v₀ * (X / v₀ + Q) := by field_simp
      have h4 : (X + Q * v₀) ^ n ≤ v₀ ^ n := by
        rw [h3, mul_pow]
        have : (X / v₀ + Q) ^ n ≤ 1 := pow_le_one₀ (by positivity) hX
        calc v₀ ^ n * (X / v₀ + Q) ^ n ≤ v₀ ^ n * 1 :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = v₀ ^ n := mul_one _
      linarith
    calc (∑ u ∈ range (P.B + 1),
          (if u ≤ n then (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) else 0)) *
          ∑ v ∈ range (P.B + 1), (v₀ * W) ^ v / (v.factorial : ℝ) ≤
        v₀ ^ n * exp (v₀ * W) :=
          mul_le_mul hbin hexp (sum_nonneg fun v _ => by positivity) (by positivity)
      _ = v₀ ^ n * exp (v₀ * W) := rfl
  · simp only [if_neg hy, mul_one]
    rw [sum_eq_single 0]
    · rw [sum_eq_single 0]
      · simp
      · intro v _ hv; simp [hv]
      · intro h; simp at h
    · intro u _ hu
      refine sum_eq_zero fun v _ => ?_
      simp [hu]
    · intro h; simp at h

/-- The per-term identity behind the column sum. -/
lemma col_identity (lam v₀ X Q Bv : ℝ) (hv₀ : v₀ ≠ 0) (k u v : ℕ) :
    lam ^ (k + u) / ((k + u).factorial : ℝ) * v₀ ^ (k + u) *
      (((k + u).choose u : ℝ) * X ^ u * Q ^ k * (Bv * lam) ^ v / (v.factorial : ℝ)) =
    lam ^ (v + k) / ((v + k).factorial : ℝ) * v₀ ^ (v + k) *
      ((((v + k).choose v : ℝ) * (Bv / v₀) ^ v * Q ^ k) * ((v₀ * X * lam) ^ u /
        (u.factorial : ℝ))) := by
  rw [Nat.cast_choose ℝ (Nat.le_add_left u k), Nat.cast_choose ℝ (Nat.le_add_right v k)]
  have e4 : k + u - u = k := by omega
  have e5 : v + k - v = k := by omega
  rw [e4, e5, div_pow]
  have hf1 : ((k + u).factorial : ℝ) ≠ 0 := by positivity
  have hf2 : ((v + k).factorial : ℝ) ≠ 0 := by positivity
  have hf3 : (u.factorial : ℝ) ≠ 0 := by positivity
  have hf4 : (v.factorial : ℝ) ≠ 0 := by positivity
  have hf5 : (k.factorial : ℝ) ≠ 0 := by positivity
  have hv0 : v₀ ^ v ≠ 0 := pow_ne_zero _ hv₀
  field_simp
  ring

/-- The weighted column sum of one particle type, output count `n'`. -/
lemma col_type (j : ℕ) (z : ℤ × ℤ) (y : P.PT) (n' : ℕ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hV : 0 ≤ P.Vg y.1.1) (hl : 0 ≤ P.lam y)
    (hY : P.qv j / memRho ^ 2 + P.etav j * P.Vg y.1.1 / memRho / v₀ ≤ 1) :
    ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1),
      (if v ≤ n' then P.lam y ^ (n' - v + u) / ((n' - v + u).factorial : ℝ) *
        v₀ ^ (n' - v + u) * gAbs P j z y (n' - v + u) u v else 0) ≤
      P.lam y ^ n' / (n'.factorial : ℝ) * v₀ ^ n' *
        (if P.IsHit z y then exp (v₀ * (P.etav j / memRho) * P.lam y) else 1) := by
  have hη := (etav_mem P j).1
  have hq := qv_nonneg P j
  have hρ := memRho_pos
  unfold gAbs
  by_cases hy : P.IsHit z y
  · simp only [if_pos hy]
    set X := P.etav j / memRho
    set Q := P.qv j / memRho ^ 2
    set Bv := P.etav j * P.Vg y.1.1 / memRho
    set lam := P.lam y
    have hX0 : 0 ≤ X := by positivity
    have hQ0 : 0 ≤ Q := by positivity
    have hB0 : 0 ≤ Bv := by positivity
    -- the per-term identity
    set A : ℕ → ℝ := fun v =>
      if v ≤ n' then (n'.choose v : ℝ) * (Bv / v₀) ^ v * Q ^ (n' - v) else 0 with hA
    set Bu : ℕ → ℝ := fun u => (v₀ * X * lam) ^ u / (u.factorial : ℝ) with hBu
    set c0 := lam ^ n' / (n'.factorial : ℝ) * v₀ ^ n' with hc0
    have hterm : ∀ u v : ℕ, (if v ≤ n' then lam ^ (n' - v + u) / ((n' - v + u).factorial : ℝ) *
        v₀ ^ (n' - v + u) * (if u ≤ n' - v + u then ((n' - v + u).choose u : ℝ) * X ^ u *
          Q ^ (n' - v + u - u) * (Bv * lam) ^ v / (v.factorial : ℝ) else 0) else 0) =
        c0 * (A v * Bu u) := by
      intro u v
      rw [hc0, hA, hBu]
      dsimp only
      by_cases hv : v ≤ n'
      · rw [if_pos hv, if_pos (Nat.le_add_left u (n' - v)), if_pos hv]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hv
        have e1 : v + k - v + u = k + u := by omega
        have e2 : k + u - u = k := by omega
        have e3 : v + k - v = k := by omega
        rw [e1, e2, e3]
        exact col_identity lam v₀ X Q Bv hv₀.ne' k u v
      · rw [if_neg hv, if_neg hv]; ring
    rw [sum_congr rfl fun u _ => sum_congr rfl fun v _ => hterm u v]
    have hsum : ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1), c0 * (A v * Bu u) =
        c0 * ((∑ v ∈ range (P.B + 1), A v) * ∑ u ∈ range (P.B + 1), Bu u) := by
      rw [sum_mul_sum, mul_sum]
      conv_lhs => rw [sum_comm]
      refine sum_congr rfl fun v _ => ?_
      rw [mul_sum]
    rw [hsum]
    have hexp : ∑ u ∈ range (P.B + 1), (v₀ * X * lam) ^ u / (u.factorial : ℝ) ≤
        exp (v₀ * X * lam) := Real.sum_le_exp_of_nonneg (by positivity) _
    have hbin : ∑ v ∈ range (P.B + 1), A v ≤ 1 := by
      have h1 : ∑ v ∈ range (P.B + 1), A v ≤
          ∑ v ∈ range (n' + 1), (n'.choose v : ℝ) * (Bv / v₀) ^ v * Q ^ (n' - v) := by
        rw [hA]; dsimp only
        rw [← sum_filter]
        refine sum_le_sum_of_subset_of_nonneg (fun v hv => ?_) (fun v _ _ => by positivity)
        simp only [mem_filter, mem_range] at hv ⊢; omega
      have h2 : ∑ v ∈ range (n' + 1), (n'.choose v : ℝ) * (Bv / v₀) ^ v * Q ^ (n' - v) =
          (Bv / v₀ + Q) ^ n' := by
        rw [add_pow]; refine sum_congr rfl fun v _ => by ring
      have h3 : (Bv / v₀ + Q) ^ n' ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
      linarith
    have hpre : 0 ≤ c0 := by rw [hc0]; positivity
    have hBu0 : 0 ≤ ∑ u ∈ range (P.B + 1), Bu u := sum_nonneg fun u _ => by rw [hBu]; positivity
    calc c0 * ((∑ v ∈ range (P.B + 1), A v) * ∑ u ∈ range (P.B + 1), Bu u) ≤
        c0 * (1 * exp (v₀ * X * lam)) := by
          apply mul_le_mul_of_nonneg_left _ hpre
          exact mul_le_mul hbin hexp hBu0 zero_le_one
      _ = c0 * exp (v₀ * X * lam) := by ring
  · simp only [if_neg hy, mul_one]
    rw [sum_eq_single 0]
    · rw [sum_eq_single 0]
      · simp
      · intro v _ hv; simp [hv]
      · intro h; simp at h
    · intro u _ hu
      refine sum_eq_zero fun v _ => ?_
      split_ifs <;> simp_all
    · intro h; simp at h

end GhostAlg

section GhostAssembly

lemma sum_le_single_of_zero {α : Type*} (S : Finset α) (G : α → ℝ) (a : α)
    (hG : 0 ≤ G a) (h : ∀ s ∈ S, s ≠ a → G s = 0) : ∑ s ∈ S, G s ≤ G a := by
  classical
  by_cases hmem : a ∈ S
  · exact (sum_eq_single_of_mem a hmem h).le
  · exact (sum_eq_zero fun s hs => h s hs fun e => hmem (e ▸ hs)).le.trans hG

variable (P : MemParams)

/-- The product formula for sums over pairs of memories. -/
lemma sum_ghostChoices_prod_le (F : P.PT → ℕ → ℕ → ℝ) (hF : ∀ y u v, 0 ≤ F y u v) :
    ∑ c ∈ P.ghostChoices, ∏ y, F y (c.1 y) (c.2 y) ≤
      ∏ y, ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1), F y u v := by
  set T := Fintype.piFinset fun _ : P.PT => range (P.B + 1) with hT
  have hsub : P.ghostChoices ⊆ T ×ˢ T := by
    intro c hc
    simp only [MemParams.ghostChoices, mem_product, MemParams.memSet, mem_filter] at hc
    exact mem_product.2 ⟨hc.1.1, hc.2.1⟩
  calc ∑ c ∈ P.ghostChoices, ∏ y, F y (c.1 y) (c.2 y) ≤
      ∑ c ∈ T ×ˢ T, ∏ y, F y (c.1 y) (c.2 y) :=
        sum_le_sum_of_subset_of_nonneg hsub fun c _ _ => prod_nonneg fun y _ => hF _ _ _
    _ = ∑ e ∈ T, ∑ b ∈ T, ∏ y, F y (e y) (b y) := sum_product _ _ _
    _ = ∑ e ∈ T, ∏ y, ∑ v ∈ range (P.B + 1), F y (e y) v := by
        refine sum_congr rfl fun e _ => ?_
        rw [hT, prod_univ_sum]
    _ = ∏ y, ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1), F y u v := by
        rw [hT, prod_univ_sum]

lemma memSize_pow (v₀ : ℝ) (m : P.Mem) : v₀ ^ P.memSize m = ∏ y, v₀ ^ m y := by
  unfold MemParams.memSize; rw [prod_pow_eq_pow_sum]

/-- **The weighted ghost row bound.** -/
theorem ghost_row (j : ℕ) (s : P.MState) {v₀ : ℝ} (hv₀ : 0 < v₀) (hV : ∀ i, 0 ≤ P.Vg i)
    (hl : ∀ y, 0 ≤ P.lam y) (hX : P.etav j / memRho / v₀ + P.qv j / memRho ^ 2 ≤ 1) :
    ∑ c ∈ P.ghostChoices, ‖P.ghostCoeff j s c‖ *
      (if P.ghostOut s c ∈ P.stSet then v₀ ^ P.memSize (P.ghostOut s c).2.2 else 0) ≤
    (∏ y, if P.IsHit s.1 y then exp (v₀ * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1) *
      v₀ ^ P.memSize s.2.2 := by
  calc ∑ c ∈ P.ghostChoices, ‖P.ghostCoeff j s c‖ *
        (if P.ghostOut s c ∈ P.stSet then v₀ ^ P.memSize (P.ghostOut s c).2.2 else 0) ≤
      ∑ c ∈ P.ghostChoices, ∏ y, (gAbs P j s.1 y (s.2.2 y) (c.1 y) (c.2 y) *
        v₀ ^ (s.2.2 y - c.1 y + c.2 y)) := by
        refine sum_le_sum fun c _ => ?_
        have h1 := norm_ghostCoeff_le P j s c hV hl
        have h2 : (if P.ghostOut s c ∈ P.stSet then v₀ ^ P.memSize (P.ghostOut s c).2.2 else 0) ≤
            ∏ y, v₀ ^ (s.2.2 y - c.1 y + c.2 y) := by
          rw [← memSize_pow]
          split_ifs
          · rfl
          · positivity
        rw [prod_mul_distrib]
        exact mul_le_mul h1 h2 (by split_ifs <;> positivity)
          (prod_nonneg fun y _ => gAbs_nonneg P j _ y _ _ _ (hV _) (hl y))
    _ ≤ ∏ y, ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1),
          gAbs P j s.1 y (s.2.2 y) u v * v₀ ^ (s.2.2 y - u + v) :=
        sum_ghostChoices_prod_le P (fun y u v => gAbs P j s.1 y (s.2.2 y) u v *
          v₀ ^ (s.2.2 y - u + v)) fun y u v =>
            mul_nonneg (gAbs_nonneg P j _ y _ _ _ (hV _) (hl y)) (by positivity)
    _ ≤ ∏ y, (v₀ ^ s.2.2 y * (if P.IsHit s.1 y then
          exp (v₀ * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1)) :=
        prod_le_prod (fun y _ => sum_nonneg fun u _ => sum_nonneg fun v _ =>
          mul_nonneg (gAbs_nonneg P j _ y _ _ _ (hV _) (hl y)) (by positivity))
          fun y _ => row_type P j s.1 y (s.2.2 y) hv₀ (hV _) (hl y) hX
    _ = _ := by rw [prod_mul_distrib, memSize_pow, mul_comm]

/-- **The weighted ghost column bound.** -/
theorem ghost_col (j : ℕ) (s' : P.MState) {v₀ : ℝ} (hv₀ : 0 < v₀) (hV : ∀ i, 0 ≤ P.Vg i)
    (hl : ∀ y, 0 ≤ P.lam y) (hLW : 0 ≤ P.listWeight s'.2.1)
    (hY : ∀ y : P.PT, P.qv j / memRho ^ 2 + P.etav j * P.Vg y.1.1 / memRho / v₀ ≤ 1) :
    ∑ s ∈ P.stSet, ∑ c ∈ P.ghostChoices, (if P.ghostOut s c = s' then
      P.stWeight s * v₀ ^ P.memSize s.2.2 * ‖P.ghostCoeff j s c‖ else 0) ≤
    (∏ y, if P.IsHit s'.1 y then exp (v₀ * (P.etav j / memRho) * P.lam y) else 1) *
      (P.stWeight s' * v₀ ^ P.memSize s'.2.2) := by
  set Tc : P.PT → ℕ → ℕ → ℝ := fun y u v => if v ≤ s'.2.2 y then
    P.lam y ^ (s'.2.2 y - v + u) / ((s'.2.2 y - v + u).factorial : ℝ) *
      v₀ ^ (s'.2.2 y - v + u) * gAbs P j s'.1 y (s'.2.2 y - v + u) u v else 0 with hTc
  have hTc0 : ∀ y u v, 0 ≤ Tc y u v := by
    intro y u v; rw [hTc]; dsimp only
    split_ifs
    · exact mul_nonneg (by have := hl y; positivity) (gAbs_nonneg P j _ y _ _ _ (hV _) (hl y))
    · exact le_refl _
  -- for each choice, only one input contributes
  have hone : ∀ c ∈ P.ghostChoices, ∑ s ∈ P.stSet, (if P.ghostOut s c = s' then
      P.stWeight s * v₀ ^ P.memSize s.2.2 * ‖P.ghostCoeff j s c‖ else 0) ≤
      P.listWeight s'.2.1 * ∏ y, Tc y (c.1 y) (c.2 y) := by
    intro c _
    set s₀ : P.MState := (s'.1, s'.2.1, fun y => s'.2.2 y - c.2 y + c.1 y) with hs₀
    set G : P.MState → ℝ := fun s => if P.ghostOut s c = s' then
      P.stWeight s * v₀ ^ P.memSize s.2.2 * ‖P.ghostCoeff j s c‖ else 0 with hG
    have hstw : 0 ≤ P.stWeight s₀ := by
      unfold MemParams.stWeight MemParams.memWeight
      exact mul_nonneg hLW (prod_nonneg fun y _ => by have := hl y; positivity)
    have hG0 : 0 ≤ G s₀ := by
      rw [hG]; dsimp only; split_ifs
      · exact mul_nonneg (mul_nonneg hstw (by positivity)) (norm_nonneg _)
      · exact le_refl _
    have hzero : ∀ s ∈ P.stSet, s ≠ s₀ → G s = 0 := by
      intro s _ hne
      rw [hG]; dsimp only
      by_cases hout : P.ghostOut s c = s'
      · rw [if_pos hout]
        by_cases hc : P.ghostCoeff j s c = 0
        · rw [hc, norm_zero, mul_zero]
        · exfalso
          have hle : ∀ y, c.1 y ≤ s.2.2 y := by
            by_contra hcon
            apply hc
            unfold MemParams.ghostCoeff
            rw [if_neg]
            exact fun h => hcon h.1
          apply hne
          rw [hs₀, ← hout]
          simp only [MemParams.ghostOut]
          refine Prod.ext rfl (Prod.ext rfl (funext fun y => ?_))
          have := hle y
          dsimp only
          omega
      · rw [if_neg hout]
    have hsum : ∑ s ∈ P.stSet, G s ≤ G s₀ := sum_le_single_of_zero P.stSet G s₀ hG0 hzero
    refine hsum.trans ?_
    rw [hG]; dsimp only
    split_ifs with hout
    · have hb : ∀ y, c.2 y ≤ s'.2.2 y := by
        intro y
        have := congrArg (fun t : P.MState => t.2.2 y) hout
        simp only [MemParams.ghostOut, hs₀] at this
        omega
      have hw : P.stWeight s₀ * v₀ ^ P.memSize s₀.2.2 =
          P.listWeight s'.2.1 * ∏ y, (P.lam y ^ (s'.2.2 y - c.2 y + c.1 y) /
            ((s'.2.2 y - c.2 y + c.1 y).factorial : ℝ) * v₀ ^ (s'.2.2 y - c.2 y + c.1 y)) := by
        rw [hs₀]
        unfold MemParams.stWeight MemParams.memWeight
        rw [memSize_pow, prod_mul_distrib]
        ring
      rw [hw, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hLW
      have hnc := norm_ghostCoeff_le P j s₀ c hV hl
      calc (∏ y, (P.lam y ^ (s'.2.2 y - c.2 y + c.1 y) /
            ((s'.2.2 y - c.2 y + c.1 y).factorial : ℝ) * v₀ ^ (s'.2.2 y - c.2 y + c.1 y))) *
            ‖P.ghostCoeff j s₀ c‖ ≤
          (∏ y, (P.lam y ^ (s'.2.2 y - c.2 y + c.1 y) /
            ((s'.2.2 y - c.2 y + c.1 y).factorial : ℝ) * v₀ ^ (s'.2.2 y - c.2 y + c.1 y))) *
            ∏ y, gAbs P j s₀.1 y (s₀.2.2 y) (c.1 y) (c.2 y) :=
            mul_le_mul_of_nonneg_left hnc
              (prod_nonneg fun y _ => by have := hl y; positivity)
        _ = ∏ y, Tc y (c.1 y) (c.2 y) := by
            rw [← prod_mul_distrib]
            refine prod_congr rfl fun y _ => ?_
            rw [hTc]; dsimp only
            rw [if_pos (hb y)]
    · exact mul_nonneg hLW (prod_nonneg fun y _ => hTc0 y _ _)
  rw [sum_comm]
  calc ∑ c ∈ P.ghostChoices, ∑ s ∈ P.stSet, (if P.ghostOut s c = s' then
        P.stWeight s * v₀ ^ P.memSize s.2.2 * ‖P.ghostCoeff j s c‖ else 0) ≤
      ∑ c ∈ P.ghostChoices, P.listWeight s'.2.1 * ∏ y, Tc y (c.1 y) (c.2 y) :=
        sum_le_sum hone
    _ = P.listWeight s'.2.1 * ∑ c ∈ P.ghostChoices, ∏ y, Tc y (c.1 y) (c.2 y) := by
        rw [mul_sum]
    _ ≤ P.listWeight s'.2.1 * ∏ y, ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1), Tc y u v :=
        mul_le_mul_of_nonneg_left (sum_ghostChoices_prod_le P Tc hTc0) hLW
    _ ≤ P.listWeight s'.2.1 * ∏ y, (P.lam y ^ s'.2.2 y / ((s'.2.2 y).factorial : ℝ) *
          v₀ ^ s'.2.2 y * (if P.IsHit s'.1 y then
            exp (v₀ * (P.etav j / memRho) * P.lam y) else 1)) := by
        refine mul_le_mul_of_nonneg_left (prod_le_prod (fun y _ => sum_nonneg fun u _ =>
          sum_nonneg fun v _ => hTc0 y u v) fun y _ => ?_) hLW
        exact col_type P j s'.1 y (s'.2.2 y) hv₀ (hV _) (hl y) (hY y)
    _ = _ := by
        unfold MemParams.stWeight MemParams.memWeight
        rw [memSize_pow, prod_mul_distrib, prod_mul_distrib]
        ring

end GhostAssembly

section GhostFinal

lemma mem_grp_of_part (P : MemParams) (y : P.PT) : y.1.2.1 ∈ P.grp y.1.1 := by
  have h := y.2
  simp only [MemParams.partSet, mem_biUnion, mem_univ, true_and, mem_image, mem_range] at h
  obtain ⟨i, p, hp, l, _, he⟩ := h
  rw [← he]; exact hp

lemma sum_hit_lam_le (P : MemParams) (z : ℤ × ℤ) (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) :
    ∑ y : P.PT, (if P.IsHit z y then P.lam y else 0) ≤ ∑ i, ∑ p ∈ P.grp i, P.nu i p := by
  rw [← sum_filter]
  set H := (univ : Finset P.PT).filter fun y => P.IsHit z y
  set g : P.PT → Fin P.K × ℕ := fun y => (y.1.1, y.1.2.1)
  set S := (univ ×ˢ P.gPrimes).filter fun q : Fin P.K × ℕ => q.2 ∈ P.grp q.1
  have hinj : Set.InjOn g H := by
    intro y hy y' hy' he
    simp only [H, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy hy'
    simp only [g, Prod.mk.injEq] at he
    apply Subtype.ext
    have h3 : y.1.2.2 = y'.1.2.2 := by
      unfold MemParams.IsHit at hy hy'; rw [hy, hy', he.2]
    exact Prod.ext he.1 (Prod.ext he.2 h3)
  have himg : H.image g ⊆ S := by
    intro q hq
    simp only [mem_image] at hq
    obtain ⟨y, _, rfl⟩ := hq
    simp only [S, g, mem_filter, mem_product, mem_univ, true_and]
    have := mem_grp_of_part P y
    refine ⟨?_, this⟩
    simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
    exact ⟨y.1.1, this⟩
  calc ∑ y ∈ H, P.lam y = ∑ y ∈ H, (fun q : Fin P.K × ℕ => P.nu q.1 q.2) (g y) := rfl
    _ = ∑ q ∈ H.image g, P.nu q.1 q.2 :=
        (sum_image (f := fun q : Fin P.K × ℕ => P.nu q.1 q.2) hinj).symm
    _ ≤ ∑ q ∈ S, P.nu q.1 q.2 := sum_le_sum_of_subset_of_nonneg himg fun q hq _ => by
        simp only [S, mem_filter] at hq; exact hnu _ _ hq.2
    _ = ∑ i, ∑ p ∈ P.grp i, P.nu i p := by
        rw [sum_filter, sum_product]
        refine sum_congr rfl fun i _ => ?_
        rw [← sum_filter]
        congr 1
        ext p
        simp only [mem_filter, and_iff_right_iff_imp]
        intro hp
        simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
        exact ⟨i, hp⟩

lemma ghost_params_ok (P : MemParams) (j : ℕ) (hV : ∀ i, P.Vg i ≤ 3 / 2) :
    P.etav j / memRho / 12 + P.qv j / memRho ^ 2 ≤ 1 ∧
      ∀ i, P.qv j / memRho ^ 2 + P.etav j * P.Vg i / memRho / 12 ≤ 1 := by
  unfold MemParams.etav MemParams.qv memRho
  constructor
  · split_ifs <;> norm_num
  · intro i
    have := hV i
    split_ifs
    · have h : (1 - 1 / 2 : ℝ) * P.Vg i / (3 / 4) / 12 ≤ 1 / 12 := by
        rw [div_le_iff₀ (by norm_num), div_le_iff₀ (by norm_num)]; nlinarith
      have h2 : (1 / 2 : ℝ) / (3 / 4) ^ 2 = 8 / 9 := by norm_num
      linarith
    · have h : (1 - 1 / 4 : ℝ) * P.Vg i / (3 / 4) / 12 ≤ 1 / 8 := by
        rw [div_le_iff₀ (by norm_num), div_le_iff₀ (by norm_num)]; nlinarith
      have h2 : (1 / 4 : ℝ) / (3 / 4) ^ 2 = 4 / 9 := by norm_num
      linarith

lemma ite_le_ite_of_le {p : Prop} [Decidable p] {a b : ℝ} (h : a ≤ b) :
    (if p then a else 0) ≤ (if p then b else 0) := by
  split_ifs
  · exact h
  · exact le_refl _

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **The ghost operator bound** for any parameters with `1/2 ≤ Vᵢ ≤ 3/2` and `b'_p ≥ 1/2`. -/
theorem ghost_opBound_gen (P : MemParams) (j : ℕ) (hVle' : ∀ i, P.Vg i ≤ 3 / 2)
    (hVge : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i) (hb : ∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p)
    (cf : P.MState → P.Mem × P.Mem → ℂ) (hcf : ∀ s c, ‖cf s c‖ ≤ ‖P.ghostCoeff j s c‖) :
    P.OpBound (choiceOp P.stSet P.ghostChoices cf P.ghostOut) (exp (30 * P.K)) := by
  intro f
  have hVpos : ∀ i, 0 < P.Vg i := fun i => by
    have : (1 : ℝ) / 2 ≤ P.Vg i := hVge i
    linarith
  have hV : ∀ i, 0 ≤ P.Vg i := fun i => (hVpos i).le
  have hgrp : ∀ i, ∀ p ∈ P.grp i, p ∈ P.gPrimes := by
    intro i p hp
    simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
    exact ⟨i, hp⟩
  have hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p := by
    intro i p hp
    have := hb p (hgrp i p hp)
    have := hVpos i
    unfold MemParams.nu; positivity
  have hl : ∀ y : P.PT, 0 ≤ P.lam y := fun y => hnu _ _ (mem_grp_of_part P y)
  have hsnu : ∀ i, ∑ p ∈ P.grp i, P.nu i p ≤ 2 := by
    intro i
    have hVi := hVpos i
    calc ∑ p ∈ P.grp i, P.nu i p ≤ ∑ p ∈ P.grp i, 2 / P.Vg i * (1 / (p : ℝ)) := by
          refine sum_le_sum fun p hp => ?_
          have hbp := hb p (hgrp i p hp)
          have hp0 : (0 : ℝ) < p := by
            have := hp; simp only [MemParams.grp, primeGroup, mem_filter] at this
            exact_mod_cast this.2.1.pos
          unfold MemParams.nu
          rw [div_le_iff₀ (by positivity)]
          rw [show 2 / P.Vg i * (1 / (p : ℝ)) * (P.Vg i * ((p : ℝ) + 1) * P.bprime p) =
            2 * P.bprime p * (((p : ℝ) + 1) / p) by field_simp]
          have : (1 : ℝ) ≤ ((p : ℝ) + 1) / p := by rw [le_div_iff₀ hp0]; linarith
          nlinarith
      _ = 2 / P.Vg i * P.Vg i := by
          rw [← mul_sum]; rfl
      _ = 2 := by field_simp
  have hhit : ∀ z, ∑ y : P.PT, (if P.IsHit z y then P.lam y else 0) ≤ 2 * P.K := by
    intro z
    refine (sum_hit_lam_le P z hnu).trans ?_
    calc ∑ i, ∑ p ∈ P.grp i, P.nu i p ≤ ∑ _i : Fin P.K, (2 : ℝ) := sum_le_sum fun i _ => hsnu i
      _ = 2 * P.K := by simp [mul_comm]
  -- weights
  have hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s := by
    intro s hs
    simp only [MemParams.stSet, mem_product] at hs
    unfold MemParams.stWeight MemParams.memWeight MemParams.listWeight
    refine mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun k _ => ?_)
      (prod_nonneg fun y _ => by have := hl y; positivity)
    apply hnu
    have := hs.2.1
    simp only [listCands, Fintype.mem_piFinset] at this
    exact this i k
  have hw : ∀ s ∈ P.stSet, (0 : ℝ) < 12 ^ P.memSize s.2.2 := fun s _ => by positivity
  obtain ⟨hX, hY⟩ := ghost_params_ok P j hVle'
  have hη := (etav_mem P j)
  have hrow : ∀ s ∈ P.stSet, ∑ c ∈ P.ghostChoices, ‖P.ghostCoeff j s c‖ *
      (if P.ghostOut s c ∈ P.stSet then (12 : ℝ) ^ P.memSize (P.ghostOut s c).2.2 else 0) ≤
      exp (36 * P.K) * 12 ^ P.memSize s.2.2 := by
    intro s _
    refine (ghost_row P j s (by norm_num) hV hl hX).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have e : ∏ y : P.PT, (if P.IsHit s.1 y then
        exp (12 * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1) =
        exp (∑ y : P.PT, if P.IsHit s.1 y then
          12 * (P.etav j * P.Vg y.1.1 / memRho * P.lam y) else 0) := by
      rw [Real.exp_sum]; refine prod_congr rfl fun y _ => ?_
      split_ifs <;> simp
    rw [e]
    refine exp_le_exp.2 ?_
    calc ∑ y : P.PT, (if P.IsHit s.1 y then 12 * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)
          else 0) ≤ ∑ y : P.PT, 18 * (if P.IsHit s.1 y then P.lam y else 0) := by
          refine sum_le_sum fun y _ => ?_
          split_ifs
          · have hly := hl y
            have h1 : P.etav j * P.Vg y.1.1 / memRho ≤ 3 / 2 := by
              unfold memRho
              rw [div_le_iff₀ (by norm_num)]
              have : P.etav j ≤ 3 / 4 := by
                unfold MemParams.etav MemParams.qv; split_ifs <;> norm_num
              nlinarith [hVle' y.1.1, hV y.1.1, hη.1]
            nlinarith
          · simp
      _ = 18 * ∑ y : P.PT, (if P.IsHit s.1 y then P.lam y else 0) := by rw [mul_sum]
      _ ≤ 18 * (2 * P.K) := by have := hhit s.1; linarith
      _ = 36 * P.K := by ring
  have hcol : ∀ s' ∈ P.stSet, ∑ s ∈ P.stSet, ∑ c ∈ P.ghostChoices,
      (if P.ghostOut s c = s' then P.stWeight s * (12 : ℝ) ^ P.memSize s.2.2 *
        ‖P.ghostCoeff j s c‖ else 0) ≤
      exp (24 * P.K) * (P.stWeight s' * 12 ^ P.memSize s'.2.2) := by
    intro s' hs'
    have hLW : 0 ≤ P.listWeight s'.2.1 := by
      simp only [MemParams.stSet, mem_product] at hs'
      refine prod_nonneg fun i _ => prod_nonneg fun k _ => ?_
      apply hnu
      have := hs'.2.1
      simp only [listCands, Fintype.mem_piFinset] at this
      exact this i k
    refine (ghost_col P j s' (by norm_num) hV hl hLW fun y => hY y.1.1).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (hμ s' hs') (pow_nonneg (by norm_num) _))
    have e : ∏ y : P.PT, (if P.IsHit s'.1 y then exp (12 * (P.etav j / memRho) * P.lam y)
        else 1) = exp (∑ y : P.PT, if P.IsHit s'.1 y then
          12 * (P.etav j / memRho) * P.lam y else 0) := by
      rw [Real.exp_sum]; refine prod_congr rfl fun y _ => ?_
      split_ifs <;> simp
    rw [e]
    refine exp_le_exp.2 ?_
    calc ∑ y : P.PT, (if P.IsHit s'.1 y then 12 * (P.etav j / memRho) * P.lam y else 0) ≤
        ∑ y : P.PT, 12 * (if P.IsHit s'.1 y then P.lam y else 0) := by
          refine sum_le_sum fun y _ => ?_
          split_ifs
          · have hly := hl y
            have h1 : P.etav j / memRho ≤ 1 := by
              unfold memRho
              rw [div_le_iff₀ (by norm_num)]
              unfold MemParams.etav MemParams.qv; split_ifs <;> norm_num
            nlinarith
          · simp
      _ = 12 * ∑ y : P.PT, (if P.IsHit s'.1 y then P.lam y else 0) := by rw [mul_sum]
      _ ≤ 12 * (2 * P.K) := by have := hhit s'.1; linarith
      _ = 24 * P.K := by ring
  have hrow' : ∀ s ∈ P.stSet, ∑ c ∈ P.ghostChoices, ‖cf s c‖ *
      (if P.ghostOut s c ∈ P.stSet then (12 : ℝ) ^ P.memSize (P.ghostOut s c).2.2 else 0) ≤
      exp (36 * P.K) * 12 ^ P.memSize s.2.2 := fun s hs =>
    le_trans (sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (hcf s c)
      (by split_ifs <;> positivity)) (hrow s hs)
  have hcol' : ∀ s' ∈ P.stSet, ∑ s ∈ P.stSet, ∑ c ∈ P.ghostChoices,
      (if P.ghostOut s c = s' then P.stWeight s * (12 : ℝ) ^ P.memSize s.2.2 *
        ‖cf s c‖ else 0) ≤
      exp (24 * P.K) * (P.stWeight s' * 12 ^ P.memSize s'.2.2) := fun s' hs' =>
    le_trans (sum_le_sum fun s hs => sum_le_sum fun c _ =>
      ite_le_ite_of_le (mul_le_mul_of_nonneg_left (hcf s c) (mul_nonneg (hμ s hs) (by positivity))))
      (hcol s' hs')
  have key := schur_choiceOp P.stSet P.ghostChoices cf P.ghostOut P.stWeight
    (fun s => (12 : ℝ) ^ P.memSize s.2.2) (exp (36 * P.K)) (exp (24 * P.K)) hμ hw
    (exp_pos _).le hrow' hcol' f
  unfold MemParams.wNorm
  have hfn : 0 ≤ ∑ s ∈ P.stSet, P.stWeight s * ‖f s‖ ^ 2 :=
    sum_nonneg fun s hs => mul_nonneg (hμ s hs) (sq_nonneg _)
  calc √(∑ s ∈ P.stSet, P.stWeight s *
        ‖choiceOp P.stSet P.ghostChoices cf P.ghostOut f s‖ ^ 2) ≤
      √(exp (36 * P.K) * exp (24 * P.K) * ∑ s ∈ P.stSet, P.stWeight s * ‖f s‖ ^ 2) :=
        Real.sqrt_le_sqrt key
    _ = √(exp (36 * P.K) * exp (24 * P.K)) * √(∑ s ∈ P.stSet, P.stWeight s * ‖f s‖ ^ 2) :=
        Real.sqrt_mul (by positivity) _
    _ = exp (30 * P.K) * √(∑ s ∈ P.stSet, P.stWeight s * ‖f s‖ ^ 2) := by
        congr 1
        rw [← Real.exp_add, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity),
          ← Real.exp_add]
        ring_nf


end GhostFinal

end ArtinPrimitiveRoots.L102D
end

section
/-! Check module: `chk_opBound_ghost_of_norm_le_ghostCoeff`, the published statement `opBound_ghost_of_norm_le_ghostCoeff` verbatim, proved from the
development. -/

namespace ArtinPrimitiveRoots

open Finset

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Finset
theorem solution (P : MemParams) (j : ℕ)
    (hVle : ∀ i, P.Vg i ≤ 3 / 2) (hVge : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i)
    (hb : ∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p)
    (cf : P.MState → P.Mem × P.Mem → ℂ) (hcf : ∀ s c, ‖cf s c‖ ≤ ‖P.ghostCoeff j s c‖) :
    P.OpBound (fun f s => ∑ c ∈ P.ghostChoices,
      cf s c * (if P.ghostOut s c ∈ P.stSet then f (P.ghostOut s c) else 0))
      (Real.exp (30 * P.K)) :=
  L102D.ghost_opBound_gen P j hVle hVge hb cf hcf
end
