-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:27.17851+00:00
-- url     : https://prove2.me/theorems/ba336d0a-0564-4329-9442-1c1a64d55a31
-- title:
--   Fund Set Meas Statement
-- statement:
--   Definitions and structural lemmas for Fund Set Meas Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FundSetMeasStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
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
def phla {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) : ℝ := -2 * Real.log (X.nfac la x)
def IsMetric {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (Ps : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ps (rmul x b) = Ps x + Real.log (‖bchar la b‖ ^ 2)) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Ps (lact γ x) = Ps x
def IsBEq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ P X.dom ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x
def IsFundSet {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Prop :=
  MeasurableSet FF ∧ FF ⊆ OmF X x0 ∧
  (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r,
    cpt X x0 z' = lact γ (rmul (cpt X x0 z) b) → z = z') ∧
  ∀ᵐ z ∂muF X x0, ∃ z' ∈ FF, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
    cpt X x0 z = lact γ (rmul (cpt X x0 z') b)
def ExhaustFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ S : EtaleStein (nd X) (OmF X x0), S.z = Subtype.val ∧ S.e = fun y => eF X x0 y.1
def MeasInvStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 x0' : Frame X.Ψ r), IsOrth X x0 → IsOrth X x0' →
    ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 = ∫⁻ z, φ (cpt X x0' z) ∂muF X x0'
def ExtFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (F : V (nd X) → ℂ),
    DifferentiableOn ℂ F (OmF X x0) →
    (∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤) →
    ∃ P : Frame X.Ψ r → ℂ, IsBEq X la P ∧ ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z
def FundSetStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∃ FF : Set (V (nd X)), IsFundSet X x0 FF
def IsMetricW {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) : Prop :=
  Measurable W ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, W (rmul x b) = W x / ENNReal.ofReal (‖bchar la b‖ ^ 2)) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, W (lact γ x) = W x
def WLower {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x
def InAt {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (F : V (nd X) → ℂ) :
    Prop :=
  ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 < ⊤
def InFF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (FF : Set (V (nd X)))
    (f : Frame X.Ψ r → ℂ) : Prop :=
  ∫⁻ z in FF, ENNReal.ofReal (‖f (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0 < ⊤
def PoinStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ),
    IsMetricW X la W → WLower X la W → 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
    ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) → InAt X x0 W bb F →
    IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) →
    (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) ∧
    X.IsBddSec la (poin X la P) ∧
    (∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ENNReal.ofReal ‖poin X la P x‖ ≤ ENNReal.ofReal C *
        ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
          (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)) ∧
    ∀ (la' : Wt X.Ψ r) (g : Frame X.Ψ r → ℂ), X.IsSec la' g → ∀ x ∈ X.dom,
      poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x
def OntoStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞)
    (Ps : Frame X.Ψ r → ℝ) (g1 : V (nd X) → ℂ) (bb m : ℝ),
    IsMetricW X la W → WLower X la W → 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
    bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m →
    DifferentiableOn ℂ g1 (OmF X x0) → (∃ z ∈ OmF X x0, g1 z ≠ 0) →
    ContDiffOn ℝ ∞ (fun z => Ps (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} →
    (∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → W (cpt X x0 z) = ENNReal.ofReal (Real.exp (-Ps (cpt X x0 z)))) →
    (∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → ∀ ξ : Fin (nd X) → ℂ,
      m * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re ≤
        (leviV (nd X) (fun w => ((Ps (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re) →
    (∀ P, X.IsBddSec la P → P ∈ X.SS la) →
    ∀ FF, IsFundSet X x0 FF →
    (∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS la, InFF X x0 W FF f →
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x) →
    ∀ f ∈ X.SS la, InFF X x0 W FF f →
    ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧
      IsBEq X la P ∧ (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ ∀ x ∈ X.dom, poin X la P x = f x
def CuspStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (τ0 : X.Ψ), 0 < X.p0 → X.p0 < r →
    (∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ0 j ≤ la τ0 i) →
    (∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → la τ0 i0 < la τ0 i1) →
    ∀ P, X.IsBddSec la P → P ∈ X.SS la
def RhGradFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    Complex.normSq (∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j) ≤
      ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) *
        (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re
def ExhaustGStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ g1 : V (nd X) → ℂ,
    DifferentiableOn ℂ g1 (OmF X x0) →
    ∃ S : EtaleStein (nd X) {z | z ∈ OmF X x0 ∧ g1 z ≠ 0},
      S.z = Subtype.val ∧ S.e = fun y => eF X x0 y.1 + (‖g1 y.1‖ ^ 2)⁻¹
def KaUnfoldStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ FF, IsFundSet X x0 FF → ∀ bb : ℝ,
    4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ C : ℝ≥0∞, C < ⊤ ∧
    ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
      (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x) →
      ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0 ≤
        C * ∫⁻ z in FF, φ (cpt X x0 z) ∂muF X x0
def PairUnfoldStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ),
    IsMetricW X la W → WLower X la W → 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
    ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) → InAt X x0 W bb F →
    IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) →
    ∀ FF, IsFundSet X x0 FF → ∀ f0 ∈ X.SS la, InFF X x0 W FF f0 →
      ∫ z in FF, poin X la P (cpt X x0 z) * (starRingEnd ℂ) (f0 (cpt X x0 z)) *
          ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 =
        ∫ z, F z * (starRingEnd ℂ) (f0 (cpt X x0 z)) * ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0
def BigCellStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ),
    IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = 0) → ∀ x ∈ X.dom, P x = 0
def OmFConnStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → IsPreconnected (OmF X x0)
def OrthoStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∃ x1, IsOrth X x1 ∧ ∃ b ∈ Bor X.Ψ r, x = rmul x1 b
def VanishAtSStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), 0 < nd X → IsOrth X x1 → x1 ∈ X.dom →
    ∀ (u w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ρ : ℝ), 0 < ρ →
    DifferentiableOn ℂ (fun z => u (cpt X x1 z)) (Metric.ball 0 ρ) →
    (∀ k, DifferentiableOn ℂ (fun z => s k (cpt X x1 z)) (Metric.ball 0 ρ)) →
    DifferentiableOn ℂ (fun z => w0 (cpt X x1 z)) (Metric.ball 0 ρ) →
    w0 x1 ≠ 0 → (∀ k, s k x1 = 0) →
    (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X x1 z) / w0 (cpt X x1 z) : V (nd X))) 0).det ≠ 0 →
    ∫⁻ z in Metric.ball 0 ρ, ENNReal.ofReal (‖u (cpt X x1 z)‖ ^ 2 *
      (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ))) < ⊤ →
    u x1 = 0
def LUStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 →
    ∃ (Δ : Frame X.Ψ r → ℂ) (zOf : Frame X.Ψ r → V (nd X)) (bOf : Frame X.Ψ r → Frame X.Ψ r),
      Differentiable ℂ Δ ∧ (∀ x ∈ X.dom, ∀ ε > 0, ∃ y ∈ Metric.ball x ε, Δ y ≠ 0) ∧
      DifferentiableOn ℂ zOf {x | x ∈ X.dom ∧ Δ x ≠ 0} ∧
      DifferentiableOn ℂ bOf {x | x ∈ X.dom ∧ Δ x ≠ 0} ∧
      (∀ x ∈ X.dom, Δ x ≠ 0 → zOf x ∈ OmF X x0 ∧ bOf x ∈ Bor X.Ψ r ∧
        x = rmul (cpt X x0 (zOf x)) (bOf x)) ∧
      ∀ z ∈ OmF X x0, ∀ b ∈ Bor X.Ψ r, Δ (rmul (cpt X x0 z) b) ≠ 0 ∧
        zOf (rmul (cpt X x0 z) b) = z ∧ bOf (rmul (cpt X x0 z) b) = b
def FrameMeasStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ C : Set (Frame X.Ψ r), IsCompact C →
    C ⊆ X.dom → ∃ K : ℝ≥0∞, K < ⊤ ∧
    ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in C, G x ≤ K * ∫⁻ z in sat X x0 C, G (cpt X x0 z) ∂muF X x0
def FundSetMeasStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))), IsOrth X x0 → IsFundSet X x0 FF →
    (∃ x1, IsOrth X x1 ∧ ∃ CechHodgeFiltration, IsFundSet X x1 CechHodgeFiltration ∧ muF X x1 CechHodgeFiltration < ⊤) → muF X x0 FF < ⊤
end
end ReciprocityTheory.ChartRestriction.G.AR.Up


