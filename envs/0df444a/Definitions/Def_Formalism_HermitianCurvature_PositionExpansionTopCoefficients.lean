-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
-- name    : Formalism_HermitianCurvature_PositionExpansionTopCoefficients
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:53.378294+00:00
-- url     : https://prove2.me/theorems/02b96950-5c7f-4eb3-b8be-589b2ea16ecc
-- title:
--   Position Expansion Top Coefficients
-- statement:
--   Definitions and structural lemmas for Position Expansion Top Coefficients, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/PositionExpansionTopCoefficients.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.FormPairingAction
open Finset Polynomial Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder
noncomputable section
structure Rep (A V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [Module A V] where

  β : F7.Sesq V

  adj : ∀ (a : A) (x y : V), β (a • x) y = β x (star a • y)
section Defs
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V]
def act (M : SlopeTestRemainingChoices S A) (X : Ix S → V) : Ix S → V := fun z => ∑ z', M z z' • X z'
def pair (ρ : Rep A V) (X X' : Ix S → V) : ℂ := ∑ z, ρ.β (X z) (X' z)
def frm (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) (X X' : Ix S → V) : ℂ := pair ρ (act M X) X'
def IsPos (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) : Prop :=
  ∀ X : Ix S → V, 0 ≤ (frm ρ M X X).re ∧ (frm ρ M X X).im = 0
def SupportedOnUsedSlots (w : List (Letter ℂ S)) (x : Ix S → V) : Prop :=
  ∀ z : Ix S, (∃ c, c ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ z c ≠ 0) → x z = 0
def evC (P : A[X]) (Y : ℂ) : A := P.eval (algebraMap ℂ A Y)
def placeV (P Q : A[X]) (a : S) (Y : ℂ) (X : Ix S → V) : Ix S → V :=
  fun z => (if z a = 0 then evC P Y else evC Q Y) • X (Function.update z a 0)
def letters (P Q : A[X]) : List (Letter ℂ S) → (Ix S → V) → (Ix S → V)
  | [], X => X
  | l :: L, X => placeV P Q l.intersection_update_fsHerm_neg_one l.pt (letters P Q L X)
end Defs
def Lp {S : Type} {K : ℕ} (sl : Fin K → S) (y : Fin K → ℝ) : List (Letter ℂ S) :=
  List.ofFn fun a => (⟨true, sl a, (y a : ℂ)⟩ : Letter ℂ S)
def normW {S : Type} (nn : ℝ → ℝ) (w : List (Letter ℂ S)) : ℝ := (w.map fun l => nn l.pt.re).prod
def G0 (α β : ℝ) (q : ℂ → ℂ) : Prop :=
  ∀ Y : ℝ, Y ∈ Set.Ioo α β → (q Y).im = 0 ∧ 0 < (q Y).re
def GrowthHypotheses {S : Type} (α β : ℝ) (w : List (Letter ℂ S)) : Prop :=
  (w.map Letter.intersection_update_fsHerm_neg_one).Nodup ∧
  (∀ l ∈ w, l.pt.im = 0 ∧ l.pt.re ∈ Set.Ioo α β ∧
    (if l.plus then l.pt.re + 1 else l.pt.re - 1) ∈ Set.Ioo α β) ∧
  ∀ i j : Fin w.length, i ≠ j →
    if (w.get j).plus then
      2 < |(w.get i).pt.re - (w.get j).pt.re| ∧ 2 < |(w.get i).pt.re - (w.get j).pt.re + 1| ∧
        2 < |(w.get i).pt.re - (w.get j).pt.re - 1|
    else
      2 < |(w.get j).pt.re - (w.get i).pt.re| ∧ 2 < |(w.get j).pt.re - (w.get i).pt.re - 1| ∧
        2 < |(w.get j).pt.re - (w.get i).pt.re - 2|
def cg {d : ℕ} (y : Fin (d + 1) → ℝ) : ℝ := ∑ k, |F7.lagCo y k|
def N0 {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] (ρ : Rep A V) (QQ : ℂ → M2 A) (nn : ℝ → ℝ)
    (w' : List (Letter ℂ S)) (X : Ix S → V) : ℝ :=
  (frm ρ (RRw QQ w') X X).re / normW nn w'
def WK {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] (ρ : Rep A V) (QQ : ℂ → M2 A) (f : A) (s : ℂ)
    (w : List (Letter ℂ S)) (vA vB vAv vBv : A[X]) {K : ℕ} (sl : Fin K → S) (y : Fin K → ℝ)
    (x : Ix S → V) : ℂ :=
  pair ρ (act (JL (Lp sl y) * RRw QQ w * Vw f s (Lp sl y ++ w)) (letters vA vB (Lp sl y) x))
    (letters vAv vBv ((Lp sl y).map dl) x)
def DualitySlotHypotheses {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
    (Ω : Set ℂ) (RR : SlopeTestRemainingChoices S A) (TT : ℂ → M2 (SlopeTestRemainingChoices S A)) (q : ℂ → ℂ) (a : S) (Y : ℝ) : Prop :=
  IsModule Ω RR TT q ∧ FreeOf a RR ∧ (∀ Y', FreeOf2 a (TT Y')) ∧ (Y : ℂ) ∈ Ω ∧ (Y : ℂ) + 1 ∈ Ω ∧
    q Y ≠ 0
def PairAdj : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (M N : SlopeTestRemainingChoices S A) (c : ℂ) (X X' : Ix S → V),
    act (M * N) X = act M (act N X) ∧ act (1 : SlopeTestRemainingChoices S A) X = X ∧ act (c • M) X = c • act M X ∧
      pair ρ (act M X) X' = pair ρ X (act (star M) X')
def CSPos : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (M : SlopeTestRemainingChoices S A) (X X' : Ix S → V),
    IsPos ρ M → ‖frm ρ M X X'‖ ^ 2 ≤ (frm ρ M X X).re * (frm ρ M X' X').re
def FormSesq : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (M : SlopeTestRemainingChoices S A), ∃ Ξ : F7.Sesq (Ix S → V), ∀ X X', Ξ X X' = frm ρ M X X'
def GramSum : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (R : F7.Sesq M) (ι : Type) [Fintype ι] (d : ℕ)
    (io : ι → Fin d → ℂ) (X X' : ι → M),
    (∑ h, ∑ h', (∑ k, io h k * starRingEnd ℂ (io h' k)) * R (X h) (X' h')) =
      ∑ k, R (∑ h, io h k • X h) (∑ h, io h k • X' h)
def GramPos : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (R : F7.Sesq M) (d : ℕ),
    (∀ m, 0 ≤ (R m m).re ∧ (R m m).im = 0) →
    ∀ x : Fin d → M, 0 ≤ (∑ k, R (x k) (x k)).re ∧ (∑ k, R (x k) (x k)).im = 0
def GramRealise : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (kap : Matrix ι ι ℂ), kap.PosSemidef →
    ∃ (d : ℕ) (io : ι → Fin d → ℂ), ∀ h h', kap h h' = ∑ k, io h k * starRingEnd ℂ (io h' k)
def DualityPairingFormula : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (Ω : Set ℂ) (RR : SlopeTestRemainingChoices S A) (TT : ℂ → M2 (SlopeTestRemainingChoices S A)) (q : ℂ → ℂ) (a : S) (Y : ℝ),
    DualitySlotHypotheses Ω RR TT q a Y →
    ∀ X₁ X₂ : Ix S → V,
      pair ρ (act (ins a (J (SlopeTestRemainingChoices S A)) * RR) X₁) X₂ =
        frm ρ (RR * ins a (TT Y)) X₁ (act (PsiP TT q a Y) X₂)
def DualityIsometry : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (Ω : Set ℂ) (RR : SlopeTestRemainingChoices S A) (TT : ℂ → M2 (SlopeTestRemainingChoices S A)) (q : ℂ → ℂ) (a : S) (Y : ℝ),
    DualitySlotHypotheses Ω RR TT q a Y →
    ∀ X₂ X₂' : Ix S → V,
      frm ρ (RR * ins a (TT Y)) (act (PsiP TT q a Y) X₂) (act (PsiP TT q a Y) X₂') =
        (q Y)⁻¹ * frm ρ (RR * ins a (TT (Y + 1))ᵀ) X₂ X₂'
def DualityCauchySchwarz : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (Ω : Set ℂ) (RR : SlopeTestRemainingChoices S A) (TT : ℂ → M2 (SlopeTestRemainingChoices S A)) (q : ℂ → ℂ) (a : S) (Y : ℝ),
    DualitySlotHypotheses Ω RR TT q a Y → IsPos ρ (RR * ins a (TT Y)) →
    ∀ X₁ X₂ : Ix S → V,
      (frm ρ (RR * ins a (TT Y)) X₁ X₁ * frm ρ (RR * ins a (TT (Y + 1))ᵀ) X₂ X₂ / q Y).im = 0 ∧
      ‖pair ρ (act (ins a (J (SlopeTestRemainingChoices S A)) * RR) X₁) X₂‖ ^ 2 ≤
        (frm ρ (RR * ins a (TT Y)) X₁ X₁ * frm ρ (RR * ins a (TT (Y + 1))ᵀ) X₂ X₂ / q Y).re
def LetterDuality : Prop := DualityPairingFormula ∧ DualityIsometry ∧ DualityCauchySchwarz
def LetterDualityOfParts : Prop := DualPlus → InsFree → PairAdj → CSPos → LetterDuality
def DKHyp {S : Type} [Fintype S] [DecidableEq S] (q : ℂ → ℂ) (w L : List (Letter ℂ S)) : Prop :=
  (∀ l ∈ L, l.plus = true) ∧ Good (L ++ w) ∧ Good (L.map dl ++ w) ∧
    L.Pairwise (fun l l' => l.pt - l'.pt ≠ 0 ∧ l.pt - l'.pt ≠ 1 ∧ l.pt - l'.pt ≠ -1) ∧
    ∀ l ∈ L, qw q w l.pt ≠ 0
def LemmaDK : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (QQ : ℂ → M2 A) (q : ℂ → ℂ) (w L : List (Letter ℂ S)),
    IsStart QQ q → DKHyp q w L → IsPos ρ (RRw QQ (L ++ w)) →
    ∀ X₁ X₂ : Ix S → V,
      (frm ρ (RRw QQ (L ++ w)) X₁ X₁ * frm ρ (RRw QQ (L.map dl ++ w)) X₂ X₂ /
          (L.map fun l => qw q w l.pt).prod).im = 0 ∧
      ‖pair ρ (act (JL L * RRw QQ w) X₁) X₂‖ ^ 2 ≤
        (frm ρ (RRw QQ (L ++ w)) X₁ X₁ * frm ρ (RRw QQ (L.map dl ++ w)) X₂ X₂ /
          (L.map fun l => qw q w l.pt).prod).re
def DKStep1 : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (QQ : ℂ → M2 A) (q : ℂ → ℂ) (w L : List (Letter ℂ S)),
    IsStart QQ q → DKHyp q w L →
    ∀ X₁ X₂ : Ix S → V,
      pair ρ (act (JL L * RRw QQ w) X₁) X₂ = frm ρ (RRw QQ (L ++ w)) X₁ (act (Ps QQ q w L) X₂)
def DKDualOK : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (q : ℂ → ℂ) (w L : List (Letter ℂ S)),
    DKHyp q w L → DualOK q w L
def DKStep4 : Prop :=
  ∀ (S : Type) (q : ℂ → ℂ) (w L : List (Letter ℂ S)),
    (∀ l ∈ L, l.plus = true) → kapF q w L = (L.map fun l => qw q w l.pt).prod
def LemmaDKOfParts : Prop :=
  DualityList → KapFormula → PairAdj → CSPos → DKDualOK → DKStep4 → LemmaDK
def gl (α β : ℝ) (N a : ℕ) : ℝ := α + (β - α) / 3 + (2 * (a : ℝ) - 2) * ((β - α) / (6 * N))
def GridSpacing : Prop :=
  ∀ (α β : ℝ) (N : ℕ), α < β → 1 ≤ N →
    (42 * (N : ℝ) ≤ β - α → (β - α) / (7 * N) ≤ (β - α) / (6 * N) - 1) ∧
    (∀ a ∈ Finset.Icc 1 N, ∀ y : ℝ, gl α β N a ≤ y → y ≤ gl α β N a + (β - α) / (6 * N) - 1 →
      α + (β - α) / 3 ≤ y ∧ y + 1 ≤ α + 2 * (β - α) / 3) ∧
    (∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N, a ≠ b → ∀ y y' : ℝ,
      gl α β N a ≤ y → y ≤ gl α β N a + (β - α) / (6 * N) - 1 →
      gl α β N b ≤ y' → y' ≤ gl α β N b + (β - α) / (6 * N) - 1 →
      ∀ e ∈ ({0, 1} : Finset ℝ), ∀ e' ∈ ({0, 1} : Finset ℝ),
        (β - α) / (6 * N) ≤ |(y + e) - (y' + e')|) ∧
    (6 * (N : ℝ) ^ 3 + 6 * N ≤ β - α → (N : ℝ) ^ 2 + 1 ≤ (β - α) / (6 * N))
def LogSmall : Prop := ∀ x : ℝ, |x| ≤ 1 / 2 → |Real.log (1 + x)| ≤ 2 * |x|
def QProduct : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (q : ℝ → ℝ) (w : List (Letter ℝ S)) (Y : ℝ), q Y ≠ 0 →
    (∀ l ∈ w, if l.plus then Y - l.pt ≠ 0 else l.pt - Y - 1 ≠ 0) →
    qw q w Y / q Y =
      (w.map fun l => if l.plus then 1 + 1 / (Y - l.pt) else 1 + 1 / (l.pt - Y - 1)).prod
def LemmaQ : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (q : ℝ → ℝ) (w : List (Letter ℝ S)) (N : ℕ) (dl Y : ℝ),
    4 ≤ N → w.length ≤ N → (N : ℝ) ^ 2 + 1 ≤ dl →
    (∀ l ∈ w, if l.plus then dl ≤ |Y - l.pt| else dl ≤ |Y - l.pt| ∧ dl ≤ |Y - (l.pt - 1)|) →
    q Y ≠ 0 →
    Real.exp (-(1 / 2)) ≤ qw q w Y / q Y ∧ qw q w Y / q Y ≤ Real.exp (1 / 2)
def LemmaQOfParts : Prop := QProduct → LogSmall → LemmaQ
def QwOfReal : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (q : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℝ),
    (q Y).im = 0 → (∀ l ∈ w, l.pt.im = 0) →
    qw q w (Y : ℂ) =
      ((qw (fun t : ℝ => (q t).re) (w.map fun l => (⟨l.plus, l.intersection_update_fsHerm_neg_one, l.pt.re⟩ : Letter ℝ S)) Y : ℝ) : ℂ)
def CauchySchwarzInvariantForm : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (RR W : SlopeTestRemainingChoices S A) (x : Ix S → V),
    IsPos ρ RR → star W * RR * W = RR → ‖frm ρ RR (act W x) x‖ ≤ (frm ρ RR x x).re
def PlaneWaveNormBound : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (QQ : ℂ → M2 A) (f fi : A) (s : ℂ) (nn : ℝ → ℝ) (w : List (Letter ℂ S)) (x : Ix S → V),
    IsWave f fi → WaveQQ QQ f fi s → (w.map Letter.intersection_update_fsHerm_neg_one).Nodup → IsPos ρ (RRw QQ w) →
    (∀ l ∈ w, 0 < nn l.pt.re) →
    ‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ / normW nn w ≤ N0 ρ QQ nn w x
def PlaneWaveBoundData {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {V : Type}
    [AddCommGroup V] [Module ℂ V] [Module A V]
    (QQ : ℂ → M2 A) (q : ℂ → ℂ) (f fi : A) (s : ℂ) (w : List (Letter ℂ S)) (n : ℕ)
    (vA vB vAv vBv : A[X]) {K : ℕ} (sl : Fin K → S) (x : Ix S → V) : Prop :=
  IsStart QQ q ∧ IsWave f fi ∧ WaveQQ QQ f fi s ∧ 1 ≤ K ∧ Function.Injective sl ∧
    (∀ a, sl a ∉ w.map Letter.intersection_update_fsHerm_neg_one) ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup ∧
    F7.Shape n vA vB ∧ F7.Shape n vAv vBv ∧
    (∀ P ∈ ({vA, vB, vAv, vBv} : Set A[X]), ∀ k, Commute f (P.coeff k)) ∧ SupportedOnUsedSlots w x
def PositionExpansionTopCoefficients : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (QQ : ℂ → M2 A) (q : ℂ → ℂ) (f fi : A) (s : ℂ) (w : List (Letter ℂ S)) (n : ℕ)
    (vA vB vAv vBv : A[X]) (K : ℕ) (sl : Fin K → S) (x : Ix S → V) (Ξ : F7.Sesq (Ix S → V))
    (y : Fin K → ℝ),
    PlaneWaveBoundData (V := V) QQ q f fi s w n vA vB vAv vBv sl x →
    (∀ X X', Ξ X X' = frm ρ (RRw QQ w * Vw f s w) X X') →
    WK ρ QQ f s w vA vB vAv vBv sl y x =
      F7.Fw Ξ x x (List.ofFn fun a => ((⟨vA, vB, vAv, vBv, s⟩ : F7.Dat A), y a)) 1 1
def GridDegreeIdentity : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (QQ : ℂ → M2 A) (q : ℂ → ℂ) (f fi : A) (s : ℂ) (w : List (Letter ℂ S)) (n : ℕ)
    (vA vB vAv vBv : A[X]) (K : ℕ) (sl : Fin K → S) (x : Ix S → V)
    (grid : Fin K → Fin (2 * n + 1) → ℝ),
    PlaneWaveBoundData (V := V) QQ q f fi s w n vA vB vAv vBv sl x → (∀ a, Function.Injective (grid a)) →
    s ^ K * frm ρ (RRw QQ w) (act (Vw f s w) x) x =
      ∑ j : Fin K → Fin (2 * n + 1), ((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) *
        WK ρ QQ f s w vA vB vAv vBv sl (fun a => grid a (j a)) x
def ImportP {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] (ρ : Rep A V) (QQ : ℂ → M2 A) (α β : ℝ) : Prop :=
  ∀ w' : List (Letter ℂ S), GrowthHypotheses α β w' → IsPos ρ (RRw QQ w')
def AdmDK : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (α β : ℝ) (q : ℂ → ℂ) (w L : List (Letter ℂ S)),
    (∀ l ∈ L, l.plus = true) → G0 α β q → GrowthHypotheses α β (L ++ w) → GrowthHypotheses α β (L.map dl ++ w) →
    DKHyp q w L ∧ ∀ l ∈ L, (qw q w l.pt).im = 0 ∧ 0 < (qw q w l.pt).re
def AdmissiblePointSizeBound : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (QQ : ℂ → M2 A) (q : ℂ → ℂ) (f fi : A) (s : ℂ) (w : List (Letter ℂ S)) (n : ℕ)
    (vA vB vAv vBv : A[X]) (K : ℕ) (sl : Fin K → S) (x : Ix S → V) (α β : ℝ) (y : Fin K → ℝ),
    PlaneWaveBoundData (V := V) QQ q f fi s w n vA vB vAv vBv sl x → G0 α β q → ImportP (S := S) ρ QQ α β →
    GrowthHypotheses α β (Lp sl y ++ w) → GrowthHypotheses α β ((Lp sl y).map dl ++ w) →
    ‖WK ρ QQ f s w vA vB vAv vBv sl y x‖ ^ 2 ≤
      (frm ρ (RRw QQ (Lp sl y ++ w)) (letters vA vB (Lp sl y) x) (letters vA vB (Lp sl y) x)).re *
        (frm ρ (RRw QQ ((Lp sl y).map dl ++ w)) (letters vAv vBv ((Lp sl y).map dl) x)
          (letters vAv vBv ((Lp sl y).map dl) x)).re /
        ∏ a, (qw q w (y a)).re
def CombinedDegreeSizeBound : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (QQ : ℂ → M2 A) (q : ℂ → ℂ) (f fi : A) (s : ℂ) (w : List (Letter ℂ S)) (n : ℕ)
    (vA vB vAv vBv : A[X]) (K : ℕ) (sl : Fin K → S) (x : Ix S → V) (α β : ℝ)
    (grid : Fin K → Fin (2 * n + 1) → ℝ),
    PlaneWaveBoundData (V := V) QQ q f fi s w n vA vB vAv vBv sl x → G0 α β q → ImportP (S := S) ρ QQ α β →
    (∀ a, Function.Injective (grid a)) →
    (∀ j : Fin K → Fin (2 * n + 1), GrowthHypotheses α β (Lp sl (fun a => grid a (j a)) ++ w) ∧
      GrowthHypotheses α β ((Lp sl (fun a => grid a (j a))).map dl ++ w)) →
    ‖s‖ ^ K * ‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ ≤
      ∑ j : Fin K → Fin (2 * n + 1), (∏ a, |F7.lagCo (grid a) (j a)|) *
        Real.sqrt ((frm ρ (RRw QQ (Lp sl (fun a => grid a (j a)) ++ w))
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)).re *
          (frm ρ (RRw QQ ((Lp sl (fun a => grid a (j a))).map dl ++ w))
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)).re /
          ∏ a, (qw q w (grid a (j a))).re)
def NormaliserLowerBound : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (QQ : ℂ → M2 A) (q : ℂ → ℂ) (f fi : A) (s : ℂ) (w : List (Letter ℂ S)) (n : ℕ)
    (vA vB vAv vBv : A[X]) (K : ℕ) (sl : Fin K → S) (x : Ix S → V) (α β : ℝ)
    (grid : Fin K → Fin (2 * n + 1) → ℝ) (nn : ℝ → ℝ) (Qw BBs : ℝ),
    PlaneWaveBoundData (V := V) QQ q f fi s w n vA vB vAv vBv sl x → G0 α β q → ImportP (S := S) ρ QQ α β →
    (∀ a, Function.Injective (grid a)) →
    (∀ j : Fin K → Fin (2 * n + 1), GrowthHypotheses α β (Lp sl (fun a => grid a (j a)) ++ w) ∧
      GrowthHypotheses α β ((Lp sl (fun a => grid a (j a))).map dl ++ w)) →
    (∀ t ∈ Set.Ioo α β, 0 < nn t) →
    (∀ a k, (q (grid a k)).re / (qw q w (grid a k)).re ≤ Qw) →
    (∀ a k, Real.sqrt (nn (grid a k) * nn (grid a k + 1) / (q (grid a k)).re) ≤ BBs) →
    ‖s‖ ^ K * (‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ / normW nn w) ≤
      (∏ a, cg (grid a) * Real.sqrt Qw * BBs) *
        ∑ j : Fin K → Fin (2 * n + 1), F7.thGrid grid j *
          (N0 ρ QQ nn (Lp sl (fun a => grid a (j a)) ++ w)
              (letters vA vB (Lp sl (fun a => grid a (j a))) x) +
            N0 ρ QQ nn ((Lp sl (fun a => grid a (j a))).map dl ++ w)
              (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)) / 2
def SmallParameterNormBound : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (QQ : ℂ → M2 A) (q : ℂ → ℂ) (f fi : A) (s : ℂ) (w : List (Letter ℂ S)) (n : ℕ)
    (vA vB vAv vBv : A[X]) (K : ℕ) (sl : Fin K → S) (x : Ix S → V) (α β : ℝ)
    (grid : Fin K → Fin (2 * n + 1) → ℝ) (nn : ℝ → ℝ) (Qw BBs X : ℝ),
    PlaneWaveBoundData (V := V) QQ q f fi s w n vA vB vAv vBv sl x → G0 α β q → ImportP (S := S) ρ QQ α β →
    (∀ a, Function.Injective (grid a)) → GrowthHypotheses α β w →
    (∀ j : Fin K → Fin (2 * n + 1), GrowthHypotheses α β (Lp sl (fun a => grid a (j a)) ++ w) ∧
      GrowthHypotheses α β ((Lp sl (fun a => grid a (j a))).map dl ++ w)) →
    (∀ t ∈ Set.Ioo α β, 0 < nn t) →
    (∀ a k, (q (grid a k)).re / (qw q w (grid a k)).re ≤ Qw) →
    (∀ a k, Real.sqrt (nn (grid a k) * nn (grid a k + 1) / (q (grid a k)).re) ≤ BBs) →
    (∀ a, cg (grid a) * Real.sqrt Qw * BBs ≤ X) →
    (‖s‖ ≤ X → ‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ / normW nn w ≤ N0 ρ QQ nn w x) ∧
    (X < ‖s‖ → ‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ / normW nn w ≤
      (X / ‖s‖) ^ K *
        ∑ j : Fin K → Fin (2 * n + 1), F7.thGrid grid j *
          (N0 ρ QQ nn (Lp sl (fun a => grid a (j a)) ++ w)
              (letters vA vB (Lp sl (fun a => grid a (j a))) x) +
            N0 ρ QQ nn ((Lp sl (fun a => grid a (j a))).map dl ++ w)
              (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)) / 2)
def PlaneWaveBoundAllPlaces : Prop := PlaneWaveNormBound ∧ GridDegreeIdentity ∧ CombinedDegreeSizeBound ∧ NormaliserLowerBound ∧ SmallParameterNormBound
def PlaneWaveNormBoundOfParts : Prop := PlaneWaveWord → CauchySchwarzInvariantForm → PlaneWaveNormBound
def DegreeIdentityOfParts : Prop := F7.PlaneWaveWord → FormSesq → PositionExpansionTopCoefficients → GridDegreeIdentity
def SizeBoundOfParts : Prop := LemmaDK → PlaneWaveWord → PairAdj → AdmDK → AdmissiblePointSizeBound
def CombinedBoundOfDegreeSize : Prop := GridDegreeIdentity → AdmissiblePointSizeBound → CombinedDegreeSizeBound
def NormaliserBoundOfParts : Prop := CombinedDegreeSizeBound → AdmDK → NormaliserLowerBound
def SmallParameterBoundOfParts : Prop := PlaneWaveNormBound → NormaliserLowerBound → SmallParameterNormBound
def PlaneWaveTheoremOfParts : Prop :=
  PlaneWaveWord → CauchySchwarzInvariantForm → F7.PlaneWaveWord → FormSesq → PositionExpansionTopCoefficients → LemmaDK → PairAdj → AdmDK →
  PlaneWaveBoundAllPlaces
def IsPosOn {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) (X : Submodule ℂ (Ix S → V)) :
    Prop :=
  ∀ x ∈ X, 0 ≤ (frm ρ M x x).re ∧ (frm ρ M x x).im = 0
def DualityPositiveSubspace : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (Ω : Set ℂ) (RR : SlopeTestRemainingChoices S A) (TT : ℂ → M2 (SlopeTestRemainingChoices S A)) (q : ℂ → ℂ) (a : S) (Y : ℝ)
    (X D : Submodule ℂ (Ix S → V)),
    DualitySlotHypotheses Ω RR TT q a Y → D ≤ X → (∀ x ∈ D, act (PsiP TT q a Y) x ∈ X) →
    IsPosOn ρ (RR * ins a (TT Y)) X →
    (∀ X₁ ∈ X, ∀ X₂ ∈ D,
      (frm ρ (RR * ins a (TT Y)) X₁ X₁ * frm ρ (RR * ins a (TT (Y + 1))ᵀ) X₂ X₂ / q Y).im = 0 ∧
      ‖pair ρ (act (ins a (J (SlopeTestRemainingChoices S A)) * RR) X₁) X₂‖ ^ 2 ≤
        (frm ρ (RR * ins a (TT Y)) X₁ X₁ * frm ρ (RR * ins a (TT (Y + 1))ᵀ) X₂ X₂ / q Y).re) ∧
    (0 < q Y → IsPosOn ρ (RR * ins a (TT (Y + 1))ᵀ) D)
def LemmaDKSub : Prop :=
  ∀ (A S V : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] (ρ : Rep A V)
    (QQ : ℂ → M2 A) (q : ℂ → ℂ) (w L : List (Letter ℂ S)) (X D : Submodule ℂ (Ix S → V)),
    IsStart QQ q → DKHyp q w L → D ≤ X → (∀ x ∈ D, act (Ps QQ q w L) x ∈ X) →
    IsPosOn ρ (RRw QQ (L ++ w)) X →
    (∀ X₁ ∈ X, ∀ X₂ ∈ D,
      (frm ρ (RRw QQ (L ++ w)) X₁ X₁ * frm ρ (RRw QQ (L.map dl ++ w)) X₂ X₂ /
          (L.map fun l => qw q w l.pt).prod).im = 0 ∧
      ‖pair ρ (act (JL L * RRw QQ w) X₁) X₂‖ ^ 2 ≤
        (frm ρ (RRw QQ (L ++ w)) X₁ X₁ * frm ρ (RRw QQ (L.map dl ++ w)) X₂ X₂ /
          (L.map fun l => qw q w l.pt).prod).re) ∧
    (0 < (L.map fun l => qw q w l.pt).prod → IsPosOn ρ (RRw QQ (L.map dl ++ w)) D)
end
end Formalism.FourierDecayAlt.FormPairingAction


