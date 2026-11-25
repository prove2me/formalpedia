-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_LowSpanCombinations
-- name    : Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_LowSpanCombinations
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:16:49.555807+00:00
-- url     : https://prove2.me/theorems/1fe57d48-6271-4e34-84b2-ca109194a56c
-- title:
--   Low Span Combinations
-- statement:
--   Definitions and structural lemmas for Low Span Combinations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/LowSpanCombinations.lean

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def OnQuot {α : Type*} (X : Data E r) (φ : Frame X.Ψ r → α) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x
def SamePt (X : Data E r) (x y : Frame X.Ψ r) : Prop :=
  ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)
def levi (X : Data E r) (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((φ (cpt X x0 w) : ℝ) : ℂ)) z ξ).re
def hf (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) : ℝ :=
  X.c τ * X.maj x τ (Data.emb τ.1 ξ)
def ExtraBounds (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ,
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, hf X ξ x τ ≤ 1) →
      ps x ≤ C + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ) ∧
    ∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)
def Admissible (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  0 ≤ a ∧ OnQuot X ps ∧ ExtraBounds X ps a
def famNorm (X : Data E r) (L : Wt X.Ψ r) {ι : Type} [Fintype ι] (g : ι → Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ j, X.pnorm L (g j) x ^ 2)
def IsComb (X : Data E r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) (f : Frame X.Ψ r → ℂ) : Prop :=
  ∃ c : Fin N → ℂ, ∀ x ∈ X.dom, f x = ∑ j, c j * w j x
def zMap (X : Data E r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ)
    (x0 : Frame X.Ψ r) (u : V (nd X)) : V (nd X) :=
  WithLp.toLp 2 fun i => s i (cpt X x0 u) / w0 (cpt X x0 u)
structure IsFlat (X : Data E r) (L : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) {del : ℕ}
    (P : Fin del → Frame X.Ψ r) : Prop where
  w_sec : ∀ j, X.IsSec L (w j)
  base_weight_isComb : IsComb X w w0
  s_comb : ∀ i, IsComb X w (s i)
  w_pos : ∀ x ∈ X.dom, 0 < famNorm X L w x
  del_pos : 0 < del
  rep_mem : ∀ k, P k ∈ X.dom
  rep_inj : ∀ k k', SamePt X (P k) (P k') → k = k'
  zero_iff : ∀ x ∈ X.dom, (∀ i, s i x = 0) ↔ ∃ k, SamePt X (P k) x
  w0_ne : ∀ k, w0 (P k) ≠ 0
  coord : ∀ k, ∃ T : V (nd X) ≃L[ℂ] V (nd X),
    HasFDerivAt (zMap X w0 s (P k)) (T : V (nd X) →L[ℂ] V (nd X)) 0
  family_le_coords : ∀ U : Set (Frame X.Ψ r), IsOpen U → (∀ k, P k ∈ U) → ∃ C : ℝ, ∀ x ∈ X.dom,
    (∀ u ∈ U, u ∈ X.dom → ¬ SamePt X u x) → famNorm X L w x ≤ C * famNorm X L s x
  weight_le_base_weight : ∃ C : ℝ, ∀ x ∈ X.dom,
    famNorm X L w x ≤ C * famNorm X L (fun o : Option (Fin (nd X)) => o.elim w0 s) x
def lowIdx (D T : ℕ) : Finset (Fin D → ℕ) :=
  (Fintype.piFinset fun _ : Fin D => Finset.range T).filter fun al => ∑ i, al i + D < T
def gen {α : Type*} {D : ℕ} (T : ℕ) (w0 : α → ℂ) (s : Fin D → α → ℂ) (t : α → ℂ) (al : Fin D → ℕ)
    (x : α) : ℂ :=
  (∏ i, s i x ^ al i) * w0 x ^ (T - ∑ i, al i) * t x
def lowComb {α : Type*} {D del : ℕ} (T : ℕ) (w0 : α → ℂ) (s : Fin D → α → ℂ) (t : Fin del → α → ℂ)
    (c : (Fin D → ℕ) → Fin del → ℂ) (x : α) : ℂ :=
  ∑ al ∈ lowIdx D T, ∑ k, c al k * gen T w0 s (t k) al x
def InLowSpan (X : Data E r) (T : ℕ) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ)
    {del : ℕ} (t : Fin del → Frame X.Ψ r → ℂ) (f : Frame X.Ψ r → ℂ) : Prop :=
  ∃ c : (Fin (nd X) → ℕ) → Fin del → ℂ, ∀ x ∈ X.dom, f x = lowComb T w0 s t c x
example : lowIdx 1 3 = {![0], ![1]} := by decide
end
end GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations


