-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_SpanSubtraction
-- name    : Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_SpanSubtraction
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:30:40.885592+00:00
-- url     : https://prove2.me/theorems/2d2ee4a2-33d8-4caf-84fa-a7cac61357ce
-- title:
--   Span Subtraction
-- statement:
--   Definitions and structural lemmas for Span Subtraction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/SpanSubtraction.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology Asymptotics
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def wtTop {X : Data E r} (Xa : ArchInM X) : Wt X.Ψ r := Xa.Fp + Xa.T • Xa.L
def wtLow {X : Data E r} (Xa : ArchInM X) : Wt X.Ψ r := Xa.Fp + nd X • Xa.L
def wNorm {X : Data E r} (Xa : ArchInM X) (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2)
def BddByPow {X : Data E r} (Xa : ArchInM X) (f : Frame X.Ψ r → ℂ) : Prop :=
  ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (wtTop Xa) f x ≤ C * wNorm Xa x ^ Xa.T
def BasisOnS {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa)
    (t : Fin Fl.δ → Frame X.Ψ r → ℂ) : Prop :=
  Function.Bijective fun (c : Fin Fl.δ → ℂ) (j : Fin Fl.δ) => ∑ i, c i * t i (Fl.xs j)
def zAt {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) (u : V (nd X)) : V (nd X) :=
  WithLp.toLp 2 fun k => Fl.s k (cpt X (Fl.xs j) u) / Fl.w0 (cpt X (Fl.xs j) u)
def VanOrd {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (a : ℕ) (f : Frame X.Ψ r → ℂ) : Prop :=
  ∀ j : Fin Fl.δ, (fun u : V (nd X) => f (cpt X (Fl.xs j) u)) =O[𝓝 0] fun u => ‖zAt Fl j u‖ ^ a
def FiniteVolume (X : Data E r) : Prop :=
  ∃ x0 : Frame X.Ψ r, IsOrth X x0 ∧ ∃ FF : Set (V (nd X)), IsFundSet X x0 FF ∧ muF X x0 FF < ⊤
def FiniteDimCusp (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS la, ∃ c : Fin K → ℂ,
    ∀ x ∈ X.dom, f x = ∑ i, c i * g i x
def GapsPairing (X : Data E r) (la : Wt X.Ψ r) (m : ℝ) : Prop :=
  ∀ τ : X.Ψ,
    (∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ j ≤ la τ i) ∧
    ∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → m ≤ ((la τ i1 - la τ i0 : ℤ) : ℝ)
def DivHyp {X : Data E r} (Xa : ArchInM X) : Prop :=
  0 < X.p0 ∧ X.p0 < r ∧ 8 ≤ r ∧ PropDisc X ∧ FiniteVolume X ∧ FiniteDimCusp X (wtTop Xa) ∧
    GapsPairing X (Xa.Fp - kapW X) (19 / 10 * ((nd X : ℝ) + 2) * Xa.T)
def lead {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (t : Fin Fl.δ → Frame X.Ψ r → ℂ)
    (cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ) : Frame X.Ψ r → ℂ :=
  leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc
def tail {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa)
    (h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), monoM X Fl.s α x * h α x
def SubtractStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (t : Fin Fl.δ → Frame X.Ψ r → ℂ),
    (∀ i, t i ∈ X.SS Xa.Fp) → BasisOnS Fl t →
    ∀ f, X.IsSec (wtTop Xa) f →
      ∃ cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ,
        VanOrd Fl (Xa.T - nd X) fun x => f x - lead Fl t cc x
def DivisionStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), DivHyp Xa →
    ∀ f ∈ X.SS (wtTop Xa), BddByPow Xa f → VanOrd Fl (Xa.T - nd X) f →
      ∃ h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ,
        (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), h α ∈ X.SS (wtLow Xa)) ∧
        ∀ x ∈ X.dom, f x = tail Fl h x
def InSpan {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (t : Fin Fl.δ → Frame X.Ψ r → ℂ)
    (f : Frame X.Ψ r → ℂ) : Prop :=
  ∃ (cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ) (h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ),
    (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), h α ∈ X.SS (wtLow Xa)) ∧
    ∀ x ∈ X.dom, f x = lead Fl t cc x + tail Fl h x
def SpanBoundStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), DivHyp Xa →
    ∀ t : Fin Fl.δ → Frame X.Ψ r → ℂ, (∀ i, t i ∈ X.SS Xa.Fp) → BasisOnS Fl t →
    ∀ f ∈ X.SS (wtTop Xa), BddByPow Xa f → InSpan Fl t f
def SpanStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), DivHyp Xa →
    ∀ t : Fin Fl.δ → Frame X.Ψ r → ℂ, (∀ i, t i ∈ X.SS Xa.Fp) → BasisOnS Fl t →
    ∀ f ∈ X.SSgt (wtTop Xa) Xa.c1, InSpan Fl t f
end
end GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction


