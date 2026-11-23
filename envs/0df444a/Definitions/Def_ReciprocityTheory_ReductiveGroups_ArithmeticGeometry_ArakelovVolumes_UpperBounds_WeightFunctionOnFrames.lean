-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:39.137614+00:00
-- url     : https://prove2.me/theorems/824c7c21-635e-43f3-90e2-c473bf143be5
-- title:
--   Weight Function On Frames
-- statement:
--   Definitions and structural lemmas for Weight Function On Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/WeightFunctionOnFrames.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def FinMu {r : ℕ} (X : Data E r) : Prop :=
  ∃ x0, IsOrth X x0 ∧ ∃ FF, IsFundSet X x0 FF ∧ muF X x0 FF < ⊤
def IsValBasisM {r δ m : ℕ} (X : Data E r) (xs : Fin m → Frame X.Ψ r) (t : Fin δ → Frame X.Ψ r → ℂ) :
    Prop :=
  (∀ v : Fin m → ℂ, ∃ a : Fin δ → ℂ, ∀ j, ∑ k, a k * t k (xs j) = v j) ∧
  ∀ a : Fin δ → ℂ, (∀ j, ∑ k, a k * t k (xs j) = 0) → a = 0
def leviO {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (g : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  leviM X g x0 z ξ
def leviRh {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re
def leviDens {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re
def InterpStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    ∀ v : Fin Fl.δ → ℂ, ∃ F ∈ X.SSgt Xa.Fp 0, ∀ j, F (Fl.xs j) = v j
def DivStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∀ P, X.IsBddSec (Xa.Fp + nd X • Xa.L) P → P ∈ X.SS (Xa.Fp + nd X • Xa.L)) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    (∀ P, X.IsBddSec (Xa.Fp + Xa.T • Xa.L) P → P ∈ X.SS (Xa.Fp + Xa.T • Xa.L)) →
    (∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x) →
    ∀ (δ : ℕ) (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsBddSec Xa.Fp (t k)) → IsValBasisM X Fl.xs t →
    ∀ x0, IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) f (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤ →
      ∃ (cc : (Fin (nd X) → ℕ) → Fin δ → ℂ) (h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ),
        (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
          h α ∈ X.SSgt (Xa.Fp + nd X • Xa.L) 0) ∧
        ∀ x ∈ X.dom, f x = leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x +
          ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), monoM X Fl.s α x * h α x
def ModeHalfStatement {r : ℕ} (X : Data E r) : Prop :=
  ∀ (la : Wt X.Ψ r) (F : Frame X.Ψ r → ℂ) (ps : Frame X.Ψ r → ℝ) (a : ℝ), X.IsSec la F →
    cfwM X ps a → 0 ≤ a →
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ENNReal.ofReal (X.pnorm la F x) ≤ ENNReal.ofReal C *
        ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
          ENNReal.ofReal (Real.exp (ps (cpt X x z) / 2))) →
    ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∑ τ, ν τ < a → ∀ x ∈ X.dom, X.fj la ξ ν F x = 0
def InterpCStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + (1 + Xa.c1 / Xa.a1) * leviO X x0 Xa.ps0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∃ C : ℝ, ∀ x ∈ X.dom, Xa.ps0 x ≤ C) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    ModeHalfStatement X →
    ∀ v : Fin Fl.δ → ℂ, ∃ F ∈ X.SSgt Xa.Fp Xa.c1, ∀ j, F (Fl.xs j) = v j
def KronHolPsiStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    ∀ ψ : Frame X.Ψ r → ℝ, IsInvFn X ψ →
    (∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) →
    (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 ψ z ξ) →
    (∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 ψ z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    ∀ j, ∃ (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (F : V (nd X) → ℂ)
      (P : Frame X.Ψ r → ℂ) (γ0 : GL (Fin r) E),
      IsOrth X x0 ∧ IsMetricW X Xa.Fp W ∧ WLower X Xa.Fp W ∧
      (∀ x ∈ X.dom, ENNReal.ofReal (Real.exp (-(phla X Xa.Fp x + ψ x))) ≤ W x) ∧
      4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X Xa.Fp P ∧
      (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ γ0 ∈ X.Γ ∧ P (lact γ0 (Fl.xs j)) ≠ 0 ∧
      ∀ γ ∈ X.Γ, ∀ j', (γ ≠ γ0 ∨ j' ≠ j) → P (lact γ (Fl.xs j')) = 0
def VanS {r δ : ℕ} (X : Data E r) (xs : Fin δ → Frame X.Ψ r) (s : Fin (nd X) → Frame X.Ψ r → ℂ)
    (a : ℕ) (g : Frame X.Ψ r → ℂ) : Prop :=
  ∀ j, ∃ ρ : ℝ, 0 < ρ ∧
    ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖g (cpt X (xs j) z)‖ ^ 2 *
      (∑ k, ‖s k (cpt X (xs j) z)‖ ^ 2) ^ (-((a : ℝ) + (nd X : ℝ) - 1 / 2))) < ⊤
def DivLeadStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (δ : ℕ)
    (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsSec Xa.Fp (t k)) → IsValBasisM X Fl.xs t →
    ∀ f, X.IsSec (Xa.Fp + Xa.T • Xa.L) f →
    ∃ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ,
      VanS X Fl.xs Fl.s (Xa.T - nd X) (fun x => f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x)
def DivCoreStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∀ P, X.IsBddSec (Xa.Fp + nd X • Xa.L) P → P ∈ X.SS (Xa.Fp + nd X • Xa.L)) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    (∀ P, X.IsBddSec (Xa.Fp + Xa.T • Xa.L) P → P ∈ X.SS (Xa.Fp + Xa.T • Xa.L)) →
    (∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x) →
    ∀ (δ : ℕ) (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsBddSec Xa.Fp (t k)) → IsValBasisM X Fl.xs t →
    ∀ x0, IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) f (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤ →
      ∀ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ,
      VanS X Fl.xs Fl.s (Xa.T - nd X) (fun x => f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x) →
      ∃ h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ,
        (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
          X.IsBddSec (Xa.Fp + nd X • Xa.L) (h α)) ∧
        ∀ x ∈ X.dom, f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x =
          ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), monoM X Fl.s α x * h α x
def DecayTStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X), PropDisc X →
    ∀ F ∈ X.SSgt (Xa.Fp + Xa.T • Xa.L) Xa.c1, ∃ C : ℝ, ∀ x ∈ X.dom,
      X.pnorm (Xa.Fp + Xa.T • Xa.L) F x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ Xa.T
def BigStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X), PropDisc X →
    ∃ x ∈ X.dom, ∃ (j0 : Fin Xa.N) (jj : Fin (nd X) → Fin Xa.N), Xa.w j0 x ≠ 0 ∧
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        Xa.w (jj k) (cpt X x z) / Xa.w j0 (cpt X x z) : V (nd X))) 0).det ≠ 0
def DivStepStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    ∀ x0, IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ (a : ℕ) (h : Frame X.Ψ r → ℂ),
      X.IsBddSec (Xa.Fp + (nd X + a + 1) • Xa.L) h →
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + (nd X + a + 1) • Xa.L) h (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-((nd X + a + 1 : ℕ) : ℝ))) ∂muF X x0 < ⊤ →
      VanS X Fl.xs Fl.s (a + 1) h →
      ∃ hh : Fin (nd X) → Frame X.Ψ r → ℂ,
        (∀ i, X.IsBddSec (Xa.Fp + (nd X + a) • Xa.L) (hh i)) ∧
        (∀ i, ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + (nd X + a) • Xa.L) (hh i) (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-((nd X + a : ℕ) : ℝ))) ∂muF X x0 < ⊤) ∧
        (∀ i, VanS X Fl.xs Fl.s a (hh i)) ∧
        ∀ x ∈ X.dom, h x = ∑ i, Fl.s i x * hh i x
def DivStartStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    ∀ (δ : ℕ) (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsBddSec Xa.Fp (t k)) →
    ∀ x0, IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) f (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤ →
      ∀ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ,
      X.IsBddSec (Xa.Fp + Xa.T • Xa.L) (fun x => f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x) ∧
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L)
        (fun x => f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x) (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤
def EtaStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X), ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 →
    ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ +
        leviO X x0 (fun x => (1 + Xa.c1 / Xa.a1) * Xa.ps0 x) z ξ
def DivQuotStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    ∀ x0, IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ (a : ℕ) (t : ℝ), (nd X : ℝ) - 1 < t →
    t ≤ (nd X : ℝ) + a →
    ∀ h : Frame X.Ψ r → ℂ, X.IsBddSec (Xa.Fp + (nd X + a + 1) • Xa.L) h →
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + (nd X + a + 1) • Xa.L) h (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-((nd X + a + 1 : ℕ) : ℝ)) *
        ((∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2) /
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2)) ^ (-(t + 1))) ∂muF X x0 < ⊤ →
      ∃ hh : Fin (nd X) → Frame X.Ψ r → ℂ,
        (∀ i, X.IsBddSec (Xa.Fp + (nd X + a) • Xa.L) (hh i)) ∧
        (∀ i, ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + (nd X + a) • Xa.L) (hh i) (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-((nd X + a : ℕ) : ℝ)) *
          ((∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2) /
            (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2)) ^ (-t)) ∂muF X x0 < ⊤) ∧
        ∀ x ∈ X.dom, h x = ∑ i, Fl.s i x * hh i x
def DivLocGlobStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    ∀ x0, IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ (a : ℕ) (h : Frame X.Ψ r → ℂ),
      X.IsBddSec (Xa.Fp + (nd X + a + 1) • Xa.L) h →
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + (nd X + a + 1) • Xa.L) h (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-((nd X + a + 1 : ℕ) : ℝ))) ∂muF X x0 < ⊤ →
      VanS X Fl.xs Fl.s (a + 1) h →
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + (nd X + a + 1) • Xa.L) h (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-((nd X + a + 1 : ℕ) : ℝ)) *
        ((∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2) /
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2)) ^ (-((a : ℝ) + (nd X : ℝ) + 1 / 2))) ∂muF X x0 < ⊤
def DivGlobLocStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    ∀ x0, IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ (a : ℕ) (h : Frame X.Ψ r → ℂ),
      X.IsBddSec (Xa.Fp + (nd X + a) • Xa.L) h →
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + (nd X + a) • Xa.L) h (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-((nd X + a : ℕ) : ℝ)) *
        ((∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2) /
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2)) ^ (-((a : ℝ) + (nd X : ℝ) - 1 / 2))) ∂muF X x0 < ⊤ →
      (∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + (nd X + a) • Xa.L) h (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-((nd X + a : ℕ) : ℝ))) ∂muF X x0 < ⊤) ∧
      VanS X Fl.xs Fl.s a h
def WSk {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  open Classical in
  if x ∈ X.dom then
  ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x)) *
    ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(Xa.T : ℝ)) *
    ENNReal.ofReal ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) / ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))
  else 0
def weightFunctionOnFrames {r : ℕ} (X : Data E r) (Xa : ArchInM X) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + nd X • Xa.L) x))
def UpDivStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    ∀ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
      bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m →
      (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    ∀ x0, IsOrth X x0 →
    ∀ F : V (nd X) → ℂ, DifferentiableOn ℂ F (OmF X x0) → InAt X x0 (WSk X Xa Fl) bb F →
      ∃ H : (Fin (nd X) → ℕ) → V (nd X) → ℂ,
        (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
          DifferentiableOn ℂ (H α) (OmF X x0) ∧ InAt X x0 (weightFunctionOnFrames X Xa) bb (H α)) ∧
        ∀ z ∈ OmF X x0, F z = ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
          (∏ k, Fl.s k (cpt X x0 z) ^ α k) * H α z
def OntoWeightStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    ∀ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
      bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m →
      (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    ∀ x0, IsOrth X x0 → ∀ FF, IsFundSet X x0 FF →
    ∃ (Ps : Frame X.Ψ r → ℝ) (g1 : V (nd X) → ℂ),
      IsMetricW X (Xa.Fp + Xa.T • Xa.L) (WSk X Xa Fl) ∧ WLower X (Xa.Fp + Xa.T • Xa.L) (WSk X Xa Fl) ∧
      DifferentiableOn ℂ g1 (OmF X x0) ∧ (∃ z ∈ OmF X x0, g1 z ≠ 0) ∧
      ContDiffOn ℝ ∞ (fun z => Ps (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} ∧
      (∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → WSk X Xa Fl (cpt X x0 z) = ENNReal.ofReal (Real.exp (-Ps (cpt X x0 z)))) ∧
      (∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → ∀ ξ : Fin (nd X) → ℂ,
        m * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re ≤
          (leviV (nd X) (fun w => ((Ps (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re) ∧
      ∀ g : Frame X.Ψ r → ℂ, g ∈ X.SS (Xa.Fp + Xa.T • Xa.L) →
        ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤ →
        VanS X Fl.xs Fl.s (Xa.T - nd X) g → InFF X x0 (WSk X Xa Fl) FF g
def LocalUnfoldStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ FF, IsFundSet X x0 FF →
    ∀ x1 ∈ X.dom, ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
    IsOpen {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
      x = lact γ (rmul (cpt X x1 z') b)} ∧
    ∃ K : ℝ≥0∞, K < ⊤ ∧
    ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, G (lact γ x) = G x) →
      (∫⁻ z in Metric.ball (0 : V (nd X)) ρ, G (cpt X x1 z) ≤
        K * ∫⁻ z in FF, G (cpt X x0 z) ∂muF X x0) ∧
      (∫⁻ z in FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
          cpt X x0 z = lact γ (rmul (cpt X x1 z') b)}, G (cpt X x0 z) ∂muF X x0 ≤
        K * ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, G (cpt X x1 z))
def LocalUnfoldBStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ FF, IsFundSet X x0 FF →
    ∀ x1 ∈ X.dom, ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
    IsOpen {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
      x = lact γ (rmul (cpt X x1 z') b)} ∧
    ∃ K : ℝ≥0∞, K < ⊤ ∧
    ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, G (lact γ x) = G x) →
      ∫⁻ z in FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
          cpt X x0 z = lact γ (rmul (cpt X x1 z') b)}, G (cpt X x0 z) ∂muF X x0 ≤
        K * ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, G (cpt X x1 z)
def CuspLeadingIndependent : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (δ : ℕ) (t : Fin δ → Frame X.Ψ r → ℂ),
    (∀ k, X.IsSec Xa.Fp (t k)) → IsValBasisM X Fl.xs t →
    ∀ (a0 : ℕ), a0 ≤ Xa.T + 1 → ∀ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ,
      VanS X Fl.xs Fl.s a0 (leadM X Fl.s Fl.w0 t Xa.T a0 cc) →
      ∀ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∀ k, cc α k = 0
def OrderAt {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) : Prop :=
  ∀ (m : ℕ) (P : Frame X.Ψ r → ℂ), X.IsSec (m • Xa.L) P →
    (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (m • Xa.L) P x ≤
      C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ ((m : ℝ) / 2)) →
    VanS X Fl.xs Fl.s (m + 1) P → ∀ x ∈ X.dom, P x = 0
def CuspSectionsUpperCount : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → OrderAt X Xa Fl →
    (∃ x ∈ X.dom, Xa.th1 x ≠ 0) → (∃ x ∈ X.dom, Xa.th2 x ≠ 0) → (∃ x ∈ X.dom, Xa.et x ≠ 0) →
    ∀ (rr : ℕ) (f : Fin rr → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Xa.Fp + Xa.T • Xa.L)) →
      (∀ a : Fin rr → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0) →
      rr ≤ Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X)
def CuspSectionsLowerCount : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    InterpCStatement (E := E) →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + (1 + Xa.c1 / Xa.a1) * leviO X x0 Xa.ps0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∃ C : ℝ, ∀ x ∈ X.dom, Xa.ps0 x ≤ C) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    ModeHalfStatement X →
    ∃ f : Fin (Fl.δ * (Xa.T + nd X).choose (nd X)) → Frame X.Ψ r → ℂ,
      (∀ q, f q ∈ X.SSgt (Xa.Fp + Xa.T • Xa.L) Xa.c1) ∧
      ∀ a : Fin (Fl.δ * (Xa.T + nd X).choose (nd X)) → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0
end
end ReciprocityTheory.ChartRestriction.G.AR.Up


