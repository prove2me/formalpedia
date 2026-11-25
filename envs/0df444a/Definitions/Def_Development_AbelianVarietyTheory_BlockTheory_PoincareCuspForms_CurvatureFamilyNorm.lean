-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_CurvatureFamilyNorm
-- name    : Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_CurvatureFamilyNorm
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:16:49.587311+00:00
-- url     : https://prove2.me/theorems/ad88a3eb-e113-413a-ac03-6312c3cb64e6
-- title:
--   Curvature Family Norm
-- statement:
--   Definitions and structural lemmas for Curvature Family Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/CurvatureFamilyNorm.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def de2 (X : Data E r) : Wt X.Ψ r := fun _ i => if (i : ℕ) < X.p0 then -1 else 1
def frameWt (X : Data E r) (a : Wt X.Ψ r) (h : ℤ) : Wt X.Ψ r := a + h • de2 X
def IsGap (X : Data E r) (i j : Fin r) : Prop := (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ X.p0
def rd (X : Data E r) : ℝ := |(discr E : ℝ)| ^ (1 / (2 * (X.Ψ.card : ℝ)))
def RR (X : Data E r) : ℝ := rd X ^ 7
def dp (X : Data E r) : ℝ := 2 * (X.Ψ.card : ℝ) * X.p0
def g0half (r : ℕ) : ℕ := 5 ^ 4 * r
def g0 (r : ℕ) : ℕ := 2 * g0half r
def a1 (X : Data E r) : ℝ := (X.Ψ.card : ℝ) / (5 ^ 4 * rd X ^ 2)
def bb (X : Data E r) : ℝ := 5 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2
def Crh (X : Data E r) : ℝ := ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ)
structure Shape (X : Data E r) : Prop where
  p0_pos : 0 < X.p0
  witt : 2 * X.p0 ≤ r
  r_ge : 8 ≤ r
  D_ge : 2 ≤ nd X
structure Weights (X : Data E r) where
  shape : Shape X
  T : ℕ
  i : ℕ
  c : ℝ
  hW : ℕ
  hF : ℕ
  aK : Wt X.Ψ r
  aW : Wt X.Ψ r
  i_pos : 0 < i
  c_pos : 0 < c
  T_cols : (nd X + 2) * (2 * hW) + 2 * r ≤ T
  T_forty : 40 * (nd X + 2) ≤ T
  T_sq : 11 * nd X ^ 2 ≤ T
  cols_lo : 8 * X.Ψ.card * r + 4 ≤ 2 * hF
  cols_hi : 2 * hF ≤ 2 * hW
  Tcg : (T : ℝ) * c * g0 r ≤ 1
  cRR : (g0 r : ℝ) * X.Ψ.card * (X.p0 : ℝ) ^ 3 * RR X ^ 2 * c ≤ 1
  b_cut : bb X < 3.8 * T - 2 * T
  b_onto : bb X ^ 2 * Crh X + bb X < 1.9 * ((nd X : ℝ) + 2) * T
  gap_big : ∀ τ a b, IsGap X a b →
    ((T : ℤ) + nd X + 2) * ((T : ℤ) + nd X + 2 + 2 * r) ≤ aK τ a - aK τ b + 2
  plus_big : ∀ τ (a : Fin r), (a : ℕ) + 1 = r → 2 * (T : ℤ) ^ 2 ≤ aK τ a
  minus_big : ∀ τ (a : Fin r), (a : ℕ) = 0 → 2 * (T : ℤ) ^ 2 ≤ -aK τ a
  gap_div : ∀ τ a b, IsGap X a b →
    aK τ a - aK τ b + 2 - ((T : ℤ) + nd X + 2) * (aW τ a - aW τ b) ∈ Set.Ico (0 : ℤ) (T + nd X + 2)
  plus_div : ∀ τ (a : Fin r), (a : ℕ) + 1 = r →
    aK τ a - ((T : ℤ) + nd X + 2) * aW τ a - ((nd X : ℤ) + 2) * (2 * hW) - 2 * r ∈
      Set.Ico (0 : ℤ) (T + nd X + 2)
  minus_div : ∀ τ (a : Fin r), (a : ℕ) = 0 →
    -aK τ a - ((T : ℤ) + nd X + 2) * (-aW τ a) ∈ Set.Ico (0 : ℤ) (T + nd X + 2)
namespace Weights
variable {X : Data E r} (w : Weights X)
def L : Wt X.Ψ r := frameWt X w.aW w.hW
def Fp : Wt X.Ψ r := frameWt X (w.aK - (w.T : ℤ) • w.aW) w.hF
def ka : Wt X.Ψ r := w.Fp + (w.T : ℤ) • w.L
def twoG₁ : Wt X.Ψ r := (2 : ℤ) • w.L - de2 X
def G₂ : Wt X.Ψ r := ((nd X : ℤ) + 4) • w.L - w.Fp
def n₁ : ℕ := w.i * g0 r
def wEt : Wt X.Ψ r := frameWt X 0 (w.i * g0half r : ℕ)
def rem : Wt X.Ψ r := w.Fp - ((nd X : ℤ) + 2) • w.L - kapW X
def c1 : ℝ := RR X * w.T * w.c * dp X ^ 2 * X.p0 / 2
def t : ℝ := 1 + w.c1 / a1 X
end Weights
def lev (X : Data E r) (x0 : Frame X.Ψ r) (u : Frame X.Ψ r → ℝ) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((u (cpt X x0 y) : ℝ) : ℂ)) z ξ).re
def curv (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  lev X x0 (phla X la) z ξ
def curvDe (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  curv X x0 (de2 X) z ξ / 2
def omRh (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((rhF X x0 y : ℝ) : ℂ)) z ξ).re
def IsInv (X : Data E r) (u : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (rmul x b) = u x) ∧ ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, u (lact γ x) = u x
def famNorm (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ j, X.pnorm la (w j) x ^ 2)
structure ThetaInputs (X : Data E r) extends Weights X where

  N : ℕ
  w : Fin N → Frame X.Ψ r → ℂ
  et : Frame X.Ψ r → ℂ
  th₁ : Frame X.Ψ r → ℂ
  th₂ : Frame X.Ψ r → ℂ
  thp : Frame X.Ψ r → ℂ
  phi : Frame X.Ψ r → ℝ
  mu : ℝ
  ps0 : Frame X.Ψ r → ℝ
  w_cusp : ∀ j, w j ∈ X.SS toWeights.L
  et_bdd : X.IsBddSec toWeights.wEt et
  et_ne : ∃ x ∈ X.dom, et x ≠ 0
  th₁_cusp : th₁ ∈ X.SS toWeights.twoG₁
  th₁_ne : ∃ x ∈ X.dom, th₁ x ≠ 0
  th₂_cusp : th₂ ∈ X.SS toWeights.G₂
  th₂_ne : ∃ x ∈ X.dom, th₂ x ≠ 0
  thp_cusp : thp ∈ X.SS toWeights.Fp
  thp_ne : ∃ x ∈ X.dom, thp x ≠ 0
  phi_inv : IsInv X phi
  phi_nonneg : ∀ x ∈ X.dom, 0 ≤ phi x
  phi_lower : ∀ x ∈ X.dom, X.la1 x < Real.sqrt X.Ψ.card * Real.exp (-mu) →
    1 ≤ 4 * RR X * dp X ^ 2 * X.la1 x ^ 2 * phi x
  phi_upper : ∀ x ∈ X.dom, 2 * X.la1 x ^ 2 * phi x ≤ X.p0 * dp X ^ 2
  w_lower : ∃ C : ℝ, ∀ x ∈ X.dom, Real.exp (-(C + c * phi x)) ≤ famNorm X toWeights.L w x
  et_upper : ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm toWeights.wEt et x ≤ Real.exp (-(i * (phi x - C)))
  potential_smooth : ContDiffOn ℝ ∞ ps0 X.dom
  potential_invariant : IsInv X ps0
  potential_bounded : ∃ C : ℝ, ∀ x ∈ X.dom, ps0 x ≤ C
  curvature_lower_bound : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ, -(r * curvDe X x0 z ξ) ≤ lev X x0 ps0 z ξ
  potential_decay : ∃ A : ℝ, ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ, X.IsIso ξ →
    (∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
    ps0 x ≤ C + A * Real.log (1 + 1 / X.la1 x) - 8 * Real.pi * (1 - 2 * η) * a1 X * ⨅ τ, X.tt ξ x τ
  curv_L : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ, ξ ≠ 0 → 0 < curv X x0 toWeights.L z ξ
  curv_G₁ : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ, ξ ≠ 0 →
    curvDe X x0 z ξ < curv X x0 toWeights.L z ξ
  margin_cut : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ,
    curv X x0 toWeights.L z ξ + 3.8 * T * omRh X x0 z ξ ≤
      curv X x0 ((2 : ℤ) • toWeights.L + toWeights.rem) z ξ
  margin_twist : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ,
    curv X x0 toWeights.L z ξ + (3.8 * T - 2 * T) * omRh X x0 z ξ ≤
      curv X x0 ((2 : ℤ) • toWeights.L + toWeights.rem) z ξ - toWeights.t * r * curvDe X x0 z ξ
  margin_onto : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ,
    1.9 * ((nd X : ℝ) + 2) * T * omRh X x0 z ξ ≤ curv X x0 (toWeights.Fp - kapW X) z ξ
end
end GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm


