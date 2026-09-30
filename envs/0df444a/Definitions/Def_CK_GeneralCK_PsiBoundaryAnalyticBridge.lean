-- Prove2me | Definitions.Def_CK_GeneralCK_PsiBoundaryAnalyticBridge
-- name    : CK_GeneralCK_PsiBoundaryAnalyticBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:56:31.388391+00:00
-- url     : https://prove2.me/theorems/6421fc09-6ace-4481-af80-f3282e7768d8
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiBoundaryAnalyticBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiBoundaryAnalyticBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiBoundaryAnalyticBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiBoundaryAnalyticBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiBoundaryAnalyticBridge.lean)

import Definitions.Def_CK_GeneralCK_PsiScalarOwnerCore

-- ===== source module GeneralCK.PsiBoundaryAnalyticBridge =====
section

/-!
# Analytic bridge for the opposite boundary strip

The archived discovery script `BOUNDARY_STRIP.py` covers the strip
`a ≤ 2^-28`, `1/2 ≤ b` by a one-dimensional interval certificate in the
coordinate `x = 1 - b`.  That script is a discovery source, not evidence.
It consumes exactly two external implications, and this file states both of
them as Lean theorems about `residualPsiScalarBound`.

* **Opposite-corner implication.**  The sub-strip `a + 1 - b ≤ 2^-13` is
  handed to the retained opposite-corner owner; the complementary sub-strip
  is exactly the interval domain `2^-13 - 2^-28 < x ≤ 1/2` reduced by the
  script.  See `residualPsiScalarBound_le_interiorCost_of_oppositeCorner`
  and `oppositeBoundary_corner_or_interval`.

* **Parent-dominance (factor eight) implication.**  With `q = 1 - a - b` and
  `C q = 1 - H ((a+b)/2)`, the retained criterion says that a parent with
  `0 < q ≤ 2/5` and `q / E ≥ 8` has `phi > psi`.  Since `ResidualPsiScalarOwner`
  already carries `phi ((a+b)/2) E < psi ((a+b)/2) E`, that whole branch is
  *vacuous*: it is discharged by contradiction, leaving `q/8 < E`.  Antitonicity
  of `eta` then sharpens the parent envelope from `eta (C q)` to
  `eta (q/8 + C q)`.  See `meanEntropy_gt_eighth_of_activePsi`,
  `residualPsiScalarBound_le_eta_parentEight` and
  `residualPsiScalarBound_le_eta_parentPlain`.

Neither retained input is proved here.  The opposite-corner owner enters as the
explicit hypothesis `ResidualPsiScalarOwner oppositeCornerResidualRegion`, and
the factor-eight parent criterion as the explicit hypothesis
`ParentEightDominance`.  Both are ordinary theorem parameters; no axiom is
introduced, and no leaf of the interval certificate is replayed here.

Nothing in this file claims the opposite-boundary owner.

## Status note (added after this file was first written)

The hypothesis `ResidualPsiScalarOwner oppositeCornerResidualRegion` carried by
`residualPsiScalarBound_le_interiorCost_of_oppositeCorner` is **false**.  It is
refuted, unconditionally and axiom-clean, by
`not_residualPsiScalarOwner_oppositeCorner` in
`GeneralCK/PsiCornerBoundaryRefutation.lean`; the same file also refutes
`ResidualPsiScalarOwner oppositeBoundaryResidualRegion`.  That corner theorem is
therefore **vacuously true** and must not be cited as evidence that the corner
sub-strip is owned.  Everything else in this file — the parent envelope, the
strip dichotomy, the factor-eight collapse and the two `eta` envelopes — is
independent of both owners and is unaffected.
-/

namespace GeneralCK
open Set

/-! ## 0. Exact rational thresholds

The archived script uses `A = 2 ^ (-28)` and `K = 2 ^ (-13)`.  The decimal and
power-of-two notation in the archived records is discovery data; the rational
literals appearing in `oppositeBoundaryResidualRegion`,
`oppositeCornerResidualRegion` and in the dichotomy below are checked here to be
exactly those numbers. -/

theorem cornerThreshold_eq : (1 : ℝ) / 8192 = (2 : ℝ) ^ (-13 : ℤ) := by norm_num

theorem boundaryThreshold_eq : (1 : ℝ) / 268435456 = (2 : ℝ) ^ (-28 : ℤ) := by norm_num

theorem twoBoundaryThreshold_eq :
    (1 : ℝ) / 134217728 = 2 * (2 : ℝ) ^ (-28 : ℤ) := by norm_num

/-- `K - 2 * A > 0`: the residual strip really does have a positive floor for
`q = 1 - a - b`. -/
theorem cornerThreshold_sub_two_boundaryThreshold_pos :
    0 < (1 : ℝ) / 8192 - 1 / 134217728 := by norm_num

/-! ## 1. The parent envelope

`residualPsiScalarBound` never exceeds the parent `psi` value, because the two
feasible-imbalance profile arguments stay inside the physical window `[0,1)`
where `Scalar.P` is nonnegative.  This is equation (1) of the archived
`PROOF.md`, written exactly in the formalized three-variable bound. -/

/-- `psi` at the parent is `eta` evaluated at `E + C q`, with `C q = 1 - H m`. -/
theorem psi_eq_eta_information (m E : ℝ) : psi m E = eta (E + (1 - H m)) := by
  unfold psi
  congr 1
  ring

/-- The two profile arguments of `residualPsiScalarBound` are physical. -/
theorem residualPsi_profile_args_mem {a b E : ℝ}
    (hHa0 : 0 ≤ H a) (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2) :
    ((H a + H b) / 2 - E - max 0 ((H a + H b) / 2 - E - H a)) ∈ Ico (0 : ℝ) 1 ∧
      ((H a + H b) / 2 - E + max 0 ((H a + H b) / 2 - E - H a)) ∈ Ico (0 : ℝ) 1 := by
  have hHa1 : H a ≤ 1 := H_le_one a
  have hHb1 : H b ≤ 1 := H_le_one b
  rcases le_total ((H a + H b) / 2 - E - H a) 0 with h | h
  · rw [max_eq_left h]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rw [max_eq_right h]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Parent envelope: the residual scalar bound is at most the parent `psi`. -/
theorem residualPsiScalarBound_le_psi {a b E : ℝ}
    (hHa0 : 0 ≤ H a) (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2) :
    residualPsiScalarBound a b E ≤ psi ((a + b) / 2) E := by
  obtain ⟨h1, h2⟩ := residualPsi_profile_args_mem hHa0 hE hEcap
  have hp1 := Scalar.P_nonneg_on_Ico h1
  have hp2 := Scalar.P_nonneg_on_Ico h2
  rw [psi_eq_P]
  show Scalar.P (H ((a + b) / 2) - E) -
      (Scalar.P ((H a + H b) / 2 - E - max 0 ((H a + H b) / 2 - E - H a)) +
        Scalar.P ((H a + H b) / 2 - E + max 0 ((H a + H b) / 2 - E - H a))) / 2 ≤
    Scalar.P (H ((a + b) / 2) - E)
  linarith

/-- Parent envelope in `eta` form. -/
theorem residualPsiScalarBound_le_eta {a b E : ℝ}
    (hHa0 : 0 ≤ H a) (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2) :
    residualPsiScalarBound a b E ≤ eta (E + (1 - H ((a + b) / 2))) := by
  rw [← psi_eq_eta_information]
  exact residualPsiScalarBound_le_psi hHa0 hE hEcap

/-! ## 2. The opposite-corner implication

`BOUNDARY_STRIP.py` hands the sub-strip `a + 1 - b ≤ 2^-13` to the retained
opposite corner.  The retained corner owner is *not* proved here: it is the
hypothesis `hcorner`. -/

/-- **Opposite-corner implication.**  Inside the boundary strip, a tuple with
`a + 1 - b ≤ 2^-13` is owned by the retained opposite-corner owner. -/
theorem residualPsiScalarBound_le_interiorCost_of_oppositeCorner
    (hcorner : ResidualPsiScalarOwner oppositeCornerResidualRegion)
    {a b E : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hsum : a + b ≤ 1)
    (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2)
    (hmean : 1 / 16 < a + b) (hinfo : 1 / 100 < H ((a + b) / 2) - E)
    (hstrip : oppositeBoundaryResidualRegion a b E)
    (hcornerStrip : a + 1 - b ≤ 1 / 8192)
    (hactive : phi ((a + b) / 2) E < psi ((a + b) / 2) E) :
    residualPsiScalarBound a b E ≤ interiorCost a b := by
  obtain ⟨hb2, _⟩ := hstrip
  exact hcorner a b E ha hab hb hsum hE hEcap hmean hinfo ⟨hb2, hcornerStrip⟩ hactive

/-- **Exact strip dichotomy.**  Every boundary-strip tuple either lies in the
retained opposite corner, or has its coordinate `x = 1 - b` strictly inside the
interval domain `(2^-13 - 2^-28, 1/2]` reduced by the archived script, with
`q = 1 - a - b > 2^-13 - 2^-27 > 0`.  The two rational thresholds are
`2^-13 - 2^-28 = 1/8192 - 1/268435456` and `2^-13 - 2^-27 = 1/8192 - 1/134217728`. -/
theorem oppositeBoundary_corner_or_interval {a b E : ℝ}
    (ha : 0 < a) (hstrip : oppositeBoundaryResidualRegion a b E) :
    oppositeCornerResidualRegion a b E ∨
      (1 / 8192 - 1 / 268435456 < 1 - b ∧ 1 - b ≤ 1 / 2 ∧
        1 / 8192 - 1 / 134217728 < 1 - a - b ∧ 1 - a - b < 1 - b) := by
  obtain ⟨hb2, hA⟩ := hstrip
  by_cases h : a + 1 - b ≤ 1 / 8192
  · exact Or.inl ⟨hb2, h⟩
  · have h' : 1 / 8192 < a + 1 - b := not_le.mp h
    exact Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## 3. The parent-dominance (factor-eight) implication

The retained criterion is stated at the parent mean `m`, where the archived
`q = |1 - a - b|` equals `1 - 2 * m`.  For the residual charts the mean
chamber gives `a + b ≤ 1`, so `1 - 2 * ((a + b) / 2) = 1 - a - b = q ≥ 0`. -/

/-- The retained factor-eight parent criterion (archived as `PARENT8`, used as
an input by `BOUNDARY_STRIP.py` and extended by `PARENT16`).  It is **not**
proved in this development; every theorem below that uses it takes it as an
explicit hypothesis.  In the archived notation `q = 1 - 2 * m`. -/
def ParentEightDominance : Prop :=
  ∀ m E : ℝ, 0 < E → 0 < 1 - 2 * m → 1 - 2 * m ≤ 2 / 5 → 8 * E ≤ 1 - 2 * m →
    psi m E < phi m E

/-- The criterion in the `(a,b,E)` coordinates of `residualPsiScalarBound`. -/
theorem psi_lt_phi_of_parentEight (hP : ParentEightDominance) {a b E : ℝ}
    (hE : 0 < E) (hq : 0 < 1 - a - b) (hq25 : 1 - a - b ≤ 2 / 5)
    (h8 : 8 * E ≤ 1 - a - b) :
    psi ((a + b) / 2) E < phi ((a + b) / 2) E := by
  have hmid : 1 - 2 * ((a + b) / 2) = 1 - a - b := by ring
  have h1 : 0 < 1 - 2 * ((a + b) / 2) := by rw [hmid]; exact hq
  have h2 : 1 - 2 * ((a + b) / 2) ≤ 2 / 5 := by rw [hmid]; exact hq25
  have h3 : 8 * E ≤ 1 - 2 * ((a + b) / 2) := by rw [hmid]; exact h8
  exact hP ((a + b) / 2) E hE h1 h2 h3

/-- **Parent-dominance collapse.**  `ResidualPsiScalarOwner` carries the
psi-active hypothesis, so the factor-eight branch `q / E ≥ 8` is vacuous: it
contradicts `hactive`.  What survives is the strict lower bound `q / 8 < E`
used to sharpen the parent envelope. -/
theorem meanEntropy_gt_eighth_of_activePsi (hP : ParentEightDominance) {a b E : ℝ}
    (hE : 0 < E) (hq : 0 < 1 - a - b) (hq25 : 1 - a - b ≤ 2 / 5)
    (hactive : phi ((a + b) / 2) E < psi ((a + b) / 2) E) :
    (1 - a - b) / 8 < E := by
  by_contra hcon
  have hcon' : E ≤ (1 - a - b) / 8 := not_lt.mp hcon
  exact absurd (psi_lt_phi_of_parentEight hP hE hq hq25 (by linarith))
    (not_lt.2 hactive.le)

/-- **Parent-dominance (factor-eight) implication.**  In the psi-active branch
with `0 < q ≤ 2/5` the residual scalar bound obeys the sharpened envelope
`eta (q/8 + C q)`, which is the quantity the archived script compares against
its cost lower bound on the first twelve initial intervals. -/
theorem residualPsiScalarBound_le_eta_parentEight (hP : ParentEightDominance)
    {a b E : ℝ} (hHa0 : 0 ≤ H a) (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2)
    (hcap : E < H ((a + b) / 2)) (hq : 0 < 1 - a - b) (hq25 : 1 - a - b ≤ 2 / 5)
    (hactive : phi ((a + b) / 2) E < psi ((a + b) / 2) E) :
    residualPsiScalarBound a b E ≤ eta ((1 - a - b) / 8 + (1 - H ((a + b) / 2))) := by
  have hlow := meanEntropy_gt_eighth_of_activePsi hP hE hq hq25 hactive
  have hHm1 : H ((a + b) / 2) ≤ 1 := H_le_one _
  have hu : (1 - a - b) / 8 + (1 - H ((a + b) / 2)) ∈ Ioc (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hv : E + (1 - H ((a + b) / 2)) ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  exact (residualPsiScalarBound_le_eta hHa0 hE hEcap).trans
    (eta_antitoneOn hu hv (by linarith))

/-- The unsharpened envelope `eta (C q)`, valid without the factor-eight input.
This is the quantity the archived script compares against on its last initial
interval `x ∈ [2/5, 1/2]`. -/
theorem residualPsiScalarBound_le_eta_parentPlain {a b E : ℝ}
    (hHa0 : 0 ≤ H a) (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2)
    (hab0 : 0 ≤ a + b) (hq : 0 < 1 - a - b) (hcap : E < H ((a + b) / 2)) :
    residualPsiScalarBound a b E ≤ eta (1 - H ((a + b) / 2)) := by
  have hHm : H ((a + b) / 2) < 1 := by
    calc H ((a + b) / 2) < H (1 / 2) :=
          H_strictMonoOn ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩ (by linarith)
      _ = 1 := H_half
  have hHm0 : 0 ≤ H ((a + b) / 2) := H_nonneg (by linarith) (by linarith)
  have hu : (1 - H ((a + b) / 2)) ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hv : E + (1 - H ((a + b) / 2)) ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  exact (residualPsiScalarBound_le_eta hHa0 hE hEcap).trans
    (eta_antitoneOn hu hv (by linarith))

/-! ## 3b. Leaf-uniform form of the envelopes

The archived script evaluates its envelope at the *leaf-uniform* value
`q₀ = l - A`, the exact rational lower bound of `q = 1 - a - b` on a leaf
`x ∈ [l,u]` with `a ≤ A`.  The step from the pointwise envelope to that
evaluation is monotonicity of `C q = 1 - H ((1-q)/2)` in `q`, proved here.
No leaf is replayed. -/

/-- `C q = 1 - H ((1 - q) / 2)` is monotone in `q` on `[0,1]`. -/
theorem parentDeficit_mono {q₀ q : ℝ} (hq₀ : 0 ≤ q₀) (hq : q₀ ≤ q) (hq1 : q ≤ 1) :
    1 - H ((1 - q₀) / 2) ≤ 1 - H ((1 - q) / 2) := by
  have h := H_strictMonoOn.monotoneOn (a := (1 - q) / 2) (b := (1 - q₀) / 2)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  linarith

/-- Leaf-uniform sharpened envelope: it is enough to evaluate at any exact
rational lower bound `q₀` for `q = 1 - a - b`. -/
theorem residualPsiScalarBound_le_eta_parentEight_uniform (hP : ParentEightDominance)
    {a b E q₀ : ℝ} (hHa0 : 0 ≤ H a) (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2)
    (hcap : E < H ((a + b) / 2)) (hq : 0 < 1 - a - b) (hq25 : 1 - a - b ≤ 2 / 5)
    (hq₀ : 0 < q₀) (hq₀le : q₀ ≤ 1 - a - b)
    (hactive : phi ((a + b) / 2) E < psi ((a + b) / 2) E) :
    residualPsiScalarBound a b E ≤ eta (q₀ / 8 + (1 - H ((1 - q₀) / 2))) := by
  have hlow := meanEntropy_gt_eighth_of_activePsi hP hE hq hq25 hactive
  have hHm1 : H ((a + b) / 2) ≤ 1 := H_le_one _
  have hH01 : H ((1 - q₀) / 2) ≤ 1 := H_le_one _
  have hC := parentDeficit_mono (q₀ := q₀) (q := 1 - a - b) hq₀.le hq₀le (by linarith)
  rw [show (1 - (1 - a - b)) / 2 = (a + b) / 2 from by ring] at hC
  have hv : (1 - a - b) / 8 + (1 - H ((a + b) / 2)) ∈ Ioc (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hu : q₀ / 8 + (1 - H ((1 - q₀) / 2)) ∈ Ioc (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  exact (residualPsiScalarBound_le_eta_parentEight hP hHa0 hE hEcap hcap hq hq25
    hactive).trans (eta_antitoneOn hu hv (by linarith))

/-- Leaf-uniform unsharpened envelope. -/
theorem residualPsiScalarBound_le_eta_parentPlain_uniform {a b E q₀ : ℝ}
    (hHa0 : 0 ≤ H a) (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2)
    (hab0 : 0 ≤ a + b) (hcap : E < H ((a + b) / 2))
    (hq₀ : 0 < q₀) (hq₀le : q₀ ≤ 1 - a - b) :
    residualPsiScalarBound a b E ≤ eta (1 - H ((1 - q₀) / 2)) := by
  have hq : 0 < 1 - a - b := lt_of_lt_of_le hq₀ hq₀le
  have hHm1 : H ((a + b) / 2) ≤ 1 := H_le_one _
  have hH01 : H ((1 - q₀) / 2) ≤ 1 := H_le_one _
  have hHm : H ((a + b) / 2) < 1 := by
    calc H ((a + b) / 2) < H (1 / 2) :=
          H_strictMonoOn ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩ (by linarith)
      _ = 1 := H_half
  have hH0 : H ((1 - q₀) / 2) < 1 := by
    calc H ((1 - q₀) / 2) < H (1 / 2) :=
          H_strictMonoOn ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩ (by linarith)
      _ = 1 := H_half
  have hC := parentDeficit_mono (q₀ := q₀) (q := 1 - a - b) hq₀.le hq₀le (by linarith)
  rw [show (1 - (1 - a - b)) / 2 = (a + b) / 2 from by ring] at hC
  have hv : (1 - H ((a + b) / 2)) ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hu : (1 - H ((1 - q₀) / 2)) ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  exact (residualPsiScalarBound_le_eta_parentPlain hHa0 hE hEcap hab0 hq hcap).trans
    (eta_antitoneOn hu hv (by linarith))

/-! ## 4. Leaf interfaces

These are the exact shapes an accepted interval leaf has to supply.  A leaf
certificate must still prove the cost comparison `eta (…) ≤ interiorCost a b`;
that comparison is *not* proved here. -/

/-- Sharpened leaf interface, in the hypothesis shape of
`ResidualPsiScalarOwner`. -/
theorem residualPsiScalarBound_le_interiorCost_of_parentEight_leaf
    (hP : ParentEightDominance) {a b E : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2)
    (hinfo : 1 / 100 < H ((a + b) / 2) - E)
    (hq : 0 < 1 - a - b) (hq25 : 1 - a - b ≤ 2 / 5)
    (hactive : phi ((a + b) / 2) E < psi ((a + b) / 2) E)
    (hleaf : eta ((1 - a - b) / 8 + (1 - H ((a + b) / 2))) ≤ interiorCost a b) :
    residualPsiScalarBound a b E ≤ interiorCost a b :=
  (residualPsiScalarBound_le_eta_parentEight hP
    (H_nonneg ha.le (hab.trans hb).le) hE hEcap (by linarith [hinfo]) hq hq25
    hactive).trans hleaf

/-- Unsharpened leaf interface, in the hypothesis shape of
`ResidualPsiScalarOwner`. -/
theorem residualPsiScalarBound_le_interiorCost_of_plain_leaf
    {a b E : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2)
    (hinfo : 1 / 100 < H ((a + b) / 2) - E)
    (hq : 0 < 1 - a - b)
    (hleaf : eta (1 - H ((a + b) / 2)) ≤ interiorCost a b) :
    residualPsiScalarBound a b E ≤ interiorCost a b :=
  (residualPsiScalarBound_le_eta_parentPlain (H_nonneg ha.le (hab.trans hb).le) hE hEcap
    (by linarith [ha, hab]) hq (by linarith [hinfo])).trans hleaf

#print axioms cornerThreshold_eq
#print axioms boundaryThreshold_eq
#print axioms twoBoundaryThreshold_eq
#print axioms cornerThreshold_sub_two_boundaryThreshold_pos
#print axioms psi_eq_eta_information
#print axioms residualPsi_profile_args_mem
#print axioms residualPsiScalarBound_le_psi
#print axioms residualPsiScalarBound_le_eta
#print axioms residualPsiScalarBound_le_interiorCost_of_oppositeCorner
#print axioms oppositeBoundary_corner_or_interval
#print axioms ParentEightDominance
#print axioms psi_lt_phi_of_parentEight
#print axioms meanEntropy_gt_eighth_of_activePsi
#print axioms residualPsiScalarBound_le_eta_parentEight
#print axioms residualPsiScalarBound_le_eta_parentPlain
#print axioms parentDeficit_mono
#print axioms residualPsiScalarBound_le_eta_parentEight_uniform
#print axioms residualPsiScalarBound_le_eta_parentPlain_uniform
#print axioms residualPsiScalarBound_le_interiorCost_of_parentEight_leaf
#print axioms residualPsiScalarBound_le_interiorCost_of_plain_leaf

end GeneralCK

end


