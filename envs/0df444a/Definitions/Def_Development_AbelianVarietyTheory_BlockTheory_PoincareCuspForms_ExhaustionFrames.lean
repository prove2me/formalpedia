-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
-- name    : Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:30:19.680131+00:00
-- url     : https://prove2.me/theorems/ce4a3402-1d85-465a-ad24-af3071c8f6a8
-- title:
--   Exhaustion Frames
-- statement:
--   Definitions and structural lemmas for Exhaustion Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/ExhaustionFrames.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def IsOrthonormalFrame (X : Data E r) (x0 : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x0 τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)
def Base (X : Data E r) : Type := {x0 : Frame X.Ψ r // IsOrthonormalFrame X x0}
instance instNonemptyBase (X : Data E r) : Nonempty (Base X) :=
  ⟨⟨fun τ => (X.signature τ).choose, fun τ => (X.signature τ).choose_spec.2⟩⟩
variable (X : Data E r)
def zBlock (z : V (nd X)) (τ : X.Ψ) :
    Matrix {a : Fin r // X.p0 ≤ (a : ℕ)} {b : Fin r // (b : ℕ) < X.p0} ℂ :=
  Matrix.of fun a b => nmat X z τ a.1 b.1
def zFrame (z : V (nd X)) : Frame X.Ψ r := fun τ a b =>
  if X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then nmat X z τ a b else if a = b then 1 else 0
def leviFrame (z : V (nd X)) : Frame X.Ψ r := fun τ a b =>
  if X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then 0 else nmat X z τ a b
def nFrame (z : V (nd X)) : Frame X.Ψ r := rmul (zFrame X z) (leviFrame X z)
def point (x0 : Base X) (z : V (nd X)) : Frame X.Ψ r := rmul x0.1 (nFrame X z)
def zNorm (z : V (nd X)) (τ : X.Ψ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (zBlock X z τ))‖
def Om : Set (V (nd X)) := {z | ∀ τ : X.Ψ, zNorm X z τ < 1}
def zDet (z : V (nd X)) (τ : X.Ψ) : ℝ := ((1 - (zBlock X z τ)ᴴ * zBlock X z τ).det).re
def rho (z : V (nd X)) : ℝ := ∑ τ : X.Ψ, -Real.log (zDet X z τ)
def pIdx : Fin (r + 1) := ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
def rel (x0 : Base X) (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (mat x0.1 τ)⁻¹ * mat x τ
def bigCell (x0 : Base X) (x : Frame X.Ψ r) : ℂ :=
  ∏ τ : X.Ψ, ∏ i : Fin r, lminor (rel X x0 x τ) i.succ
def rhoFrame (x0 : Base X) (x : X.dom) : ℝ :=
  ∑ τ : X.Ψ, (-Real.log ‖dmin X.Gm x.1 τ (pIdx X)‖ +
    Real.log (‖lminor (rel X x0 x.1 τ) (pIdx X)‖ ^ 2))
def leviSq (z : V (nd X)) (τ : X.Ψ) : ℝ :=
  ∑ a : Fin r, ∑ b : Fin r, if b < a then ‖leviFrame X z τ a b‖ ^ 2 else 0
def exhaustion (z : V (nd X)) : ℝ := rho X z + ∑ τ : X.Ψ, Real.log (1 + leviSq X z τ)
def OmOff (g : V (nd X) → ℂ) : Set (V (nd X)) := {z | z ∈ Om X ∧ g z ≠ 0}
def exhaustionOff (g : V (nd X) → ℂ) (z : V (nd X)) : ℝ := exhaustion X z + (‖g z‖ ^ 2)⁻¹
def density (x0 : Base X) (z : V (nd X)) : ℝ :=
  ∏ τ : X.Ψ, ∏ i : Fin r, (‖dmin X.Gm (point X x0 z) τ i.castSucc‖ ^ 2)⁻¹
def mu (x0 : Base X) : Measure (V (nd X)) :=
  (volume.restrict (Om X)).withDensity fun z => ENNReal.ofReal (density X x0 z)
def kappa (b : ℝ) (z : V (nd X)) : ℝ := Real.exp (-b * rho X z)
def kappaFrame (x0 : Base X) (b : ℝ) (x : X.dom) : ℝ := Real.exp (-b * rhoFrame X x0 x)
def image (x0 : Base X) (C : Set (Frame X.Ψ r)) : Set (V (nd X)) :=
  {z | z ∈ Om X ∧ ∃ b ∈ Bor X.Ψ r, rmul (point X x0 z) b ∈ C}
def evidence (x0 : Base X) (P : Frame X.Ψ r → ℂ) (z : V (nd X)) : ℂ := P (point X x0 z)
def phi (x0 : Base X) (la : Wt X.Ψ r) (z : V (nd X)) : ℝ :=
  ∑ τ : X.Ψ, ∑ i : Fin r, (la τ i : ℝ) *
    Real.log ‖dmin X.Gm (point X x0 z) τ i.succ / dmin X.Gm (point X x0 z) τ i.castSucc‖
def poincTerm (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (γ : X.Γ) (x : Frame X.Ψ r) : ℂ :=
  (X.χ la γ.1)⁻¹ * P (lact γ.1 x)
def poinc (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑' γ : X.Γ, poincTerm X la P γ x
def PoincConv (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ x ∈ X.dom, Summable fun γ : X.Γ => poincTerm X la P γ x
def PoincNormal (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ C ⊆ X.dom, IsCompact C → ∃ u : X.Γ → ℝ, Summable u ∧
    ∀ γ : X.Γ, ∀ x ∈ C, ‖poincTerm X la P γ x‖ ≤ u γ
end
end GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames


