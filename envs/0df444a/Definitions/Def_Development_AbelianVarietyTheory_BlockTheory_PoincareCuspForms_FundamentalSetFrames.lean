-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FundamentalSetFrames
-- name    : Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FundamentalSetFrames
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:17:03.032404+00:00
-- url     : https://prove2.me/theorems/610aafaf-46c2-4c53-9ca3-46b2e8c18ee4
-- title:
--   Fundamental Set Frames
-- statement:
--   Definitions and structural lemmas for Fundamental Set Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/FundamentalSetFrames.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory
open scoped ENNReal NNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def GapsNonneg (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, i ≤ j → (j : ℕ) < X.p0 → la τ j ≤ la τ i) ∧
    (∀ i j : Fin r, X.p0 ≤ (i : ℕ) → i ≤ j → la τ j ≤ la τ i)
def pairing (X : Data E r) (h0 : 0 < X.p0) (h1 : X.p0 < r) (la : Wt X.Ψ r) (τ : X.Ψ) : ℤ :=
  la τ ⟨r - 1, by omega⟩ - la τ ⟨0, by omega⟩
def IsInvWeight (X : Data E r) (u : Frame X.Ψ r → EReal) : Prop :=
  Measurable (fun x : X.dom => u x) ∧
  (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (lact γ (rmul x b)) = u x) ∧
  ∃ C : ℝ, ∀ x ∈ X.dom, u x ≤ (C : EReal)
def phi (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (z : V (nd X)) : ℝ :=
  -2 * Real.log (X.nfac la (cpt X x0 z))
def psi (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (z : V (nd X)) : EReal :=
  (phi X x0 la z : EReal) + u (cpt X x0 z)
def wsq (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (F : V (nd X) → ℂ) (z : V (nd X)) : ℝ≥0∞ :=
  ENNReal.ofReal (‖F z‖ ^ 2) * EReal.exp (-psi X x0 la u z)
def normSq (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (F : V (nd X) → ℂ) : ℝ≥0∞ :=
  ∫⁻ z, wsq X x0 la u F z * ENNReal.ofReal (kaF X x0 bb z)⁻¹ ∂muF X x0
def ATilde (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal) :
    Set (V (nd X) → ℂ) :=
  {F | DifferentiableOn ℂ F (OmF X x0) ∧ normSq X x0 bb la u F < ⊤}
def IsFundSet (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Prop :=
  MeasurableSet FF ∧ FF ⊆ OmF X x0 ∧
  (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r,
    lact γ (cpt X x0 z) = rmul (cpt X x0 z') b → γ = 1) ∧
  ∀ᵐ z ∂muF X x0, ∃ γ ∈ X.Γ, ∃ z' ∈ FF, ∃ b ∈ Bor X.Ψ r,
    cpt X x0 z = lact γ (rmul (cpt X x0 z') b)
def fundSq (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (FF : Set (V (nd X))) (f : Frame X.Ψ r → ℂ) : ℝ≥0∞ :=
  ∫⁻ z in FF, wsq X x0 la u (fun w => f (cpt X x0 w)) z ∂muF X x0
def ASpace (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (FF : Set (V (nd X))) : Set (Frame X.Ψ r → ℂ) :=
  {f | f ∈ X.SS la ∧ fundSq X x0 la u FF f < ⊤}
def IsExt (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)
    (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ P X.dom ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) ∧
  ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z
def rhoFrame (X : Data E r) (x0 x : Frame X.Ψ r) : ℝ :=
  ∑ τ, (-Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ +
    Real.log (‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2))
def kappaFrame (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (x : Frame X.Ψ r) : ℝ :=
  Real.exp (-bb * rhoFrame X x0 x)
def idFrame (X : Data E r) : Frame X.Ψ r := fun _ a b => if a = b then 1 else 0
def flagBall (X : Data E r) (ε : ℝ) (y : Frame X.Ψ r) : Set (Frame X.Ψ r) :=
  {y' | y' ∈ X.dom ∧ ∃ x, IsOrth X x ∧ (∃ b ∈ Bor X.Ψ r, y = rmul x b) ∧
    ∃ z : Frame X.Ψ r, ‖z‖ < ε ∧ y' = rmul x (idFrame X + z)}
def ballSup (X : Data E r) (ε : ℝ) (u : Frame X.Ψ r → EReal) (y : Frame X.Ψ r) : ℝ≥0∞ :=
  ⨆ y' ∈ flagBall X ε y, EReal.exp (u y') ^ (1 / 2 : ℝ)
def term (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (γ : X.Γ) (x : Frame X.Ψ r) : ℂ :=
  (X.χ la γ.1)⁻¹ * P (lact γ.1 x)
def ConvergesNormally (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ K : Set (Frame X.Ψ r), IsCompact K → K ⊆ X.dom →
    ∃ M : X.Γ → ℝ, Summable M ∧ ∀ γ, ∀ x ∈ K, ‖term X la P γ x‖ ≤ M γ
def PoincareStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 →
  ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∀ la : Wt X.Ψ r,
    (∀ u, IsInvWeight X u → ∀ F ∈ ATilde X x0 bb la u, ∃ P, IsExt X x0 la F P) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ u, IsInvWeight X u → ∀ F ∈ ATilde X x0 bb la u,
      ∀ P, IsExt X x0 la F P → ∀ y ∈ X.dom,
        ENNReal.ofReal (X.pnorm la P y) ≤ C * normSq X x0 bb la u F ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (Real.sqrt (kappaFrame X x0 bb y)) * ballSup X ε u y ∧
        ENNReal.ofReal (X.pnorm la (poin X la P) y) ≤
          C * normSq X x0 bb la u F ^ (1 / 2 : ℝ) * ballSup X ε u y) ∧
    ∀ u, IsInvWeight X u → ∀ F ∈ ATilde X x0 bb la u, ∀ P, IsExt X x0 la F P →
      ConvergesNormally X la P ∧ X.IsBddSec la (poin X la P) ∧
      (∀ FF, IsFundSet X x0 FF → fundSq X x0 la u FF (poin X la P) < ⊤) ∧
      ∀ (la' : Wt X.Ψ r) (g : Frame X.Ψ r → ℂ), X.IsSec la' g →
        ConvergesNormally X (la' + la) (g * P) ∧
        ∀ x ∈ X.dom, poin X (la' + la) (g * P) x = g x * poin X la P x
def CuspidalStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), GapsNonneg X la →
    (∀ (h0 : 0 < X.p0) (h1 : X.p0 < r), ∃ τ : X.Ψ, 0 < pairing X h0 h1 la τ) →
    ∀ P, X.IsBddSec la P → P ∈ X.SS la
def PoincareCuspidalStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  PoincareStatement (E := E) ∧ CuspidalStatement (E := E)
end
end GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames


