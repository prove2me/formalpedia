-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CountAsm
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CountAsm
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:35.080811+00:00
-- url     : https://prove2.me/theorems/6e23c743-9520-4a93-b442-79d0b51c30f0
-- title:
--   Count Asm
-- statement:
--   Definitions and structural lemmas for Count Asm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CountAsm.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CountRhoPArithStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open Classical in

def onDom {r : ℕ} (X : Data E r) (f : Frame X.Ψ r → ℂ) : Frame X.Ψ r → ℂ :=
  fun x => if x ∈ X.dom then f x else 0
def spanDom {r : ℕ} (X : Data E r) (S : Set (Frame X.Ψ r → ℂ)) : Submodule ℂ (Frame X.Ψ r → ℂ) :=
  Submodule.span ℂ (onDom X '' S)
def ZcM {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) : Submodule ℂ (Frame X.Ψ r → ℂ) :=
  spanDom X {g | ∃ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), ∃ θ ∈ X.SS (Xa.Fp + nd X • Xa.L),
    g = fun x => monoM X Fl.s α x * θ x}
def CountRhoPMStatement : Prop :=
  CuspSectionsUpperCount (E := E) → CuspSectionsLowerCount (E := E) →
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → OrderAt X Xa Fl →
    InterpCStatement (E := E) →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + (1 + Xa.c1 / Xa.a1) * leviO X x0 Xa.ps0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∃ C : ℝ, ∀ x ∈ X.dom, Xa.ps0 x ≤ C) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    ModeHalfStatement X →
    ((Module.finrank ℂ (spanDom X (X.SS (Xa.Fp + Xa.T • Xa.L))) : ℝ) -
        Module.finrank ℂ (spanDom X (X.SSgt (Xa.Fp + Xa.T • Xa.L) Xa.c1))) ≤
      (nd X : ℝ) * (nd X + 6) * Module.finrank ℂ (spanDom X (X.SS (Xa.Fp + Xa.T • Xa.L))) / Xa.T
def CountRhoMStatement : Prop :=
  CuspSectionsUpperCount (E := E) → CuspLeadingIndependent (E := E) →
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → OrderAt X Xa Fl →
    InterpCStatement (E := E) →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + (1 + Xa.c1 / Xa.a1) * leviO X x0 Xa.ps0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∃ C : ℝ, ∀ x ∈ X.dom, Xa.ps0 x ≤ C) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    ModeHalfStatement X →
    (Module.finrank ℂ (ZcM X Xa Fl) : ℝ) ≤
      22 * (nd X : ℝ) ^ 2 * Module.finrank ℂ (spanDom X (X.SS (Xa.Fp + Xa.T • Xa.L))) / Xa.T
end
end ReciprocityTheory.ChartRestriction.G.AR.Up


