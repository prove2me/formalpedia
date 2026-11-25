-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ThetaWeightedNorm
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_ThetaWeightedNorm
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:35.155026+00:00
-- url     : https://prove2.me/theorems/b006a9de-f66c-4d4e-937c-e903e9dcdeab
-- title:
--   Theta Weighted Norm
-- statement:
--   Definitions and structural lemmas for Theta Weighted Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ThetaWeightedNorm.lean

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def IsInv (X : Data E r) (φ : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧
    ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x
def levi (X : Data E r) (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((φ (cpt X x0 y) : ℝ) : ℂ)) z ξ).re
def rh (X : Data E r) (x : Frame X.Ψ r) : ℝ :=
  -∑ τ, Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖
def phK (X : Data E r) (x : Frame X.Ψ r) : ℝ :=
  -2 * ∑ τ, ∑ i : Fin r, Real.log ‖dmin X.Gm x τ i.castSucc‖
def Everywhere (X : Data E r) (p : ((Frame X.Ψ r → ℝ) → ℝ) → Prop) : Prop :=
  ∀ x0 : Frame X.Ψ r, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    p fun φ => levi X x0 φ z ξ
def EverywhereNe (X : Data E r) (p : ((Frame X.Ψ r → ℝ) → ℝ) → Prop) : Prop :=
  ∀ x0 : Frame X.Ψ r, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
    p fun φ => levi X x0 φ z ξ
def GapsGe (X : Data E r) (la : Wt X.Ψ r) (g : ℝ) : Prop :=
  ∀ (τ : X.Ψ) (i j : Fin r), (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → g ≤ ((la τ i - la τ j : ℤ) : ℝ)
def PairingGe (X : Data E r) (la : Wt X.Ψ r) (m : ℝ) : Prop :=
  ∀ (τ : X.Ψ) (i0 i1 : Fin r), (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → m ≤ ((la τ i1 - la τ i0 : ℤ) : ℝ)
def IsTwoDelta (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∀ (τ : X.Ψ) (i j : Fin r),
    (((i : ℕ) < X.p0 ↔ (j : ℕ) < X.p0) → la τ i = la τ j) ∧
    ((i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → la τ j = la τ i + 2)
def CuspDecay (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ, (∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)) ∧
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
      (∀ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
      ps x ≤ C + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ : X.Ψ, X.tt ξ x τ
def IsExtra (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  0 ≤ a ∧ IsInv X ps ∧ ContDiffOn ℝ ∞ ps X.dom ∧ (∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C) ∧
    CuspDecay X ps a
def wnorm (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ j, X.pnorm la (w j) x ^ 2)
def bb (X : Data E r) : ℝ := 5 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2
def Crh (X : Data E r) : ℝ := ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ)
structure ThetaIn (X : Data E r) where

  L : Wt X.Ψ r

  Fp : Wt X.Ψ r

  de2 : Wt X.Ψ r
  twoDelta_spec : IsTwoDelta X de2
  L_gaps : GapsGe X L 0
  L_pair : PairingGe X L 1
  Fp_gaps : GapsGe X Fp 0
  Fp_pair : PairingGe X Fp 1

  T : ℕ

  i : ℕ

  g0h : ℕ

  c : ℝ

  RR : ℝ
  dp : ℝ
  qp : ℝ

  a1 : ℝ

  η : ℝ
  two_le_D : 2 ≤ nd X
  T_ge : 11 * nd X ^ 2 ≤ T
  i_pos : 0 < i
  genusHeight_pos : 0 < g0h
  c_pos : 0 < c
  one_le_RR : 1 ≤ RR
  dp_pos : 0 < dp
  qp_pos : 0 < qp
  frame_theta_weight_pos : 0 < a1
  η_pos : 0 < η

  Tcg : (T : ℝ) * c * (2 * g0h) ≤ 1

  tr_le : (1 + RR * T * c * dp ^ 2 * qp / 2 / a1) * r ≤ 2 * T

  marginA : bb X < 19 / 5 * (T : ℝ) - 2 * T

  marginB : bb X ^ 2 * Crh X + bb X < 19 / 10 * ((nd X : ℝ) + 2) * T

  N : ℕ
  w : Fin N → Frame X.Ψ r → ℂ
  et : Frame X.Ψ r → ℂ
  th1 : Frame X.Ψ r → ℂ
  th2 : Frame X.Ψ r → ℂ
  thp : Frame X.Ψ r → ℂ
  w_bdd : ∀ j, X.IsBddSec L (w j)

  et_bdd : X.IsBddSec ((i * g0h) • de2) et

  firstTheta_bounded : X.IsBddSec (2 • L - de2) th1

  secondTheta_bounded : X.IsBddSec ((nd X + 4) • L - Fp) th2
  thp_bdd : X.IsBddSec Fp thp
  et_ne : ∃ x ∈ X.dom, et x ≠ 0
  firstTheta_ne_zero : ∃ x ∈ X.dom, th1 x ≠ 0
  secondTheta_ne_zero : ∃ x ∈ X.dom, th2 x ≠ 0
  thp_ne : ∃ x ∈ X.dom, thp x ≠ 0

  ph : Frame X.Ψ r → ℝ
  ph_inv : IsInv X ph
  ph_nonneg : ∀ x ∈ X.dom, 0 ≤ ph x

  w_lower : ∃ C : ℝ, ∀ x ∈ X.dom, Real.exp (-(C + c * ph x)) ≤ wnorm X L w x

  et_upper : ∃ P : ℝ, ∀ x ∈ X.dom,
    X.pnorm ((i * g0h) • de2) et x ≤ Real.exp (-((i : ℝ) * (ph x - P)))

  ph_lower : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, X.la1 x < ε →
    1 / (4 * RR * dp ^ 2 * X.la1 x ^ 2) ≤ ph x

  ph_upper : ∀ x ∈ X.dom, ph x ≤ qp * dp ^ 2 / (2 * X.la1 x ^ 2)

  ps0 : Frame X.Ψ r → ℝ
  extraDivisor_isExtra : IsExtra X ps0 a1

  curvature_lower_bound : Everywhere X fun Lv => -((r : ℝ) / 2 * Lv (phla X de2)) ≤ Lv ps0

  L_curv : EverywhereNe X fun Lv => 0 < Lv (phla X L)

  Lde_curv : EverywhereNe X fun Lv => 1 / 2 * Lv (phla X de2) < Lv (phla X L)

  curvA : Everywhere X fun Lv =>
    2 * η * Lv (phla X L) + 19 / 5 * (T : ℝ) * Lv (rh X) ≤
      Lv (phla X Fp) - Lv (phK X) - (nd X : ℝ) * Lv (phla X L)

  curvB : Everywhere X fun Lv =>
    19 / 10 * ((nd X : ℝ) + 2) * T * Lv (rh X) ≤ Lv (phla X Fp) - Lv (phK X)
namespace ThetaIn
variable {X : Data E r} (I : ThetaIn X)
def g0 : ℕ := 2 * I.g0h
def n1 : ℕ := I.i * I.g0
def c1 : ℝ := I.RR * I.T * I.c * I.dp ^ 2 * I.qp / 2
def t : ℝ := 1 + I.c1 / I.a1
def F0 : Wt X.Ψ r := I.Fp + nd X • I.L
def ka : Wt X.Ψ r := I.Fp + I.T • I.L
def be (x : Frame X.Ψ r) : ℂ := I.et x ^ 2 * I.th1 x ^ I.n1
def Explicit : Prop :=
  I.RR = rdE E ^ 7 ∧ I.qp = ((min X.p0 (r - X.p0) : ℕ) : ℝ) ∧
    I.dp = 2 * (X.Ψ.card : ℝ) * I.qp ∧ I.g0h = 5 ^ 4 * r ∧
    I.a1 = (X.Ψ.card : ℝ) / (5 ^ 4 * rdE E ^ 2)
end ThetaIn
def HidaSetting (X : Data E r) : Prop :=
  0 < X.p0 ∧ X.p0 < r ∧ 8 ≤ r ∧
    (∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1) ∧ PropDisc X
def MahlerCompact (X : Data E r) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧
    ∀ x ∈ X.dom, ε ≤ X.la1 x → ∃ γ ∈ X.Γ, ∃ y ∈ C, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul y b)
def WeightCurvStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → ∀ la : Wt X.Ψ r,
    (∀ m : ℝ, GapsGe X la 0 → PairingGe X la m →
      Everywhere X fun Lv => m * Lv (rh X) ≤ Lv (phla X la)) ∧
    (GapsGe X la 1 → PairingGe X la 1 → EverywhereNe X fun Lv => 0 < Lv (phla X la))
def TwistStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r), HidaSetting X → ∀ I : ThetaIn X,
    IsExtra X (fun x => I.t * I.ps0 x) (I.t * I.a1) ∧
    Everywhere X fun Lv =>
      2 * I.η * Lv (phla X I.L) + (19 / 5 * (I.T : ℝ) - 2 * I.T) * Lv (rh X) ≤
        Lv (phla X I.Fp) - Lv (phK X) - (nd X : ℝ) * Lv (phla X I.L) + Lv fun x => I.t * I.ps0 x
def BignessStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r), HidaSetting X → MahlerCompact X → ∀ I : ThetaIn X,
    ∃ x0 : Frame X.Ψ r, IsOrth X x0 ∧ ∃ z ∈ OmF X x0, ∃ (j0 : Fin I.N) (j : Fin (nd X) → Fin I.N),
      I.w j0 (cpt X x0 z) ≠ 0 ∧
      (fderiv ℂ (fun y : V (nd X) => (WithLp.toLp 2 fun k =>
        I.w (j k) (cpt X x0 y) / I.w j0 (cpt X x0 y) : V (nd X))) z).det ≠ 0
def BetaDecayStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r), HidaSetting X → ∀ I : ThetaIn X, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ X.dom, X.la1 x < δ →
      X.pnorm ((2 * I.n1) • I.L) I.be x ≤ ε * wnorm X I.L I.w x ^ (2 * I.n1)
def DeepBoundStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r), HidaSetting X → ∀ I : ThetaIn X, ∀ f ∈ X.SSgt I.ka I.c1,
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm I.ka f x ≤ C * wnorm X I.L I.w x ^ I.T
example (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) : rh X (cpt X x0 z) = rhF X x0 z := rfl
example (X : Data E r) (a : ℝ) : IsInv X fun _ => a := ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
end
end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm


