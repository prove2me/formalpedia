-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
-- name    : Formalism_HermitianCurvature_BigCellVanishingOfCommute
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:31:33.204688+00:00
-- url     : https://prove2.me/theorems/078a1093-56cd-4d9a-a44f-2a0376c26d6a
-- title:
--   Big Cell Vanishing Of Commute
-- statement:
--   Definitions and structural lemmas for Big Cell Vanishing Of Commute, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/BigCellVanishingOfCommute.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.C6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def sq2 {m : ℕ} (v : Fin m → ℂ) : ℝ := ∑ a, Complex.normSq (v a)
def unitOf {m : ℕ} (T Gv : ℝ) (v : Fin m → ℂ) : Fin m → ℂ := ((Real.sqrt (T / Gv) : ℝ) : ℂ) • v
def UnitWords (k r : ℕ) (u v : List (B.Mat k r)) (i : ℕ) : Prop :=
  (∀ X ∈ u, B.unitLie k r X) ∧ (∀ X ∈ v, B.unitLie k r X) ∧ u.length + v.length = i
def FibUnit : Prop :=
  ∀ (k r m : ℕ) (om : B.Mat k r → Fin m → ℂ) (Gp : B.Mat k r → ℝ) (T : ℝ),
    (∀ a, U.IsPolyDeg (r + 1) (fun g => om g a)) → U.IsPolyDeg (2 * r + 2) (fun g => (Gp g : ℂ)) → 0 < T →
    (∀ g ∈ B.GV k r, sq2 (om g) = Gp g / T) →
    ∀ ε : ℝ, 0 < ε → ∀ i : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), UnitWords k r u v i →
      ∀ g ∈ B.GV k r, ε ≤ Gp g →
        ‖B.dLR u v (fun g' => unitOf T (Gp g') (om g')) g‖ ≤ C * B.gN g ^ ((r + 1) * (2 * i + 1))
def FibCost : Prop :=
  ∀ (k r m m' : ℕ) (om : B.Mat k r → Fin m → ℂ) (om' : B.Mat k r → Fin m' → ℂ) (Gp : B.Mat k r → ℝ) (T T' : ℝ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Pi : (Fin m → ℂ) × (Fin m' → ℂ) → E)
    (O : Set ((Fin m → ℂ) × (Fin m' → ℂ))),
    (∀ a, U.IsPolyDeg (r + 1) (fun g => om g a)) → (∀ a, U.IsPolyDeg (r + 1) (fun g => om' g a)) →
    U.IsPolyDeg (2 * r + 2) (fun g => (Gp g : ℂ)) → 0 < T → 0 < T' →
    (∀ g ∈ B.GV k r, sq2 (om g) = Gp g / T) → (∀ g ∈ B.GV k r, sq2 (om' g) = Gp g / T') →
    IsOpen O → {w | sq2 w.1 = 1 ∧ sq2 w.2 = 1} ⊆ O → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pi O →
    ∀ ε : ℝ, 0 < ε → ∀ i : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), UnitWords k r u v i →
      ∀ g ∈ B.GV k r, ε ≤ Gp g →
        ‖B.dLR u v (fun g' => Pi (unitOf T (Gp g') (om g'), unitOf T' (Gp g') (om' g'))) g‖ ≤
          C * B.gN g ^ (3 * (r + 1) * i)
def FibCostOfParts : Prop := FibUnit → FibCost
def FibChainExp : Prop :=
  ∀ r i a : ℕ, 1 ≤ a → a ≤ i → (r + 1) * (2 * i + a) ≤ 3 * (r + 1) * i
def FibExpText : Prop :=
  ∀ r i : ℕ, 1 ≤ i → (r + 1) * (2 * i + 1) ≤ 3 * (r + 1) * i
def FibExpZeroFails : Prop :=
  ¬ ∀ r i : ℕ, (r + 1) * (2 * i + 1) ≤ 3 * (r + 1) * i
def SSNatHomog : Prop :=
  ∀ (m m' : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (OO : (Fin m → ℂ) → (Fin m' → ℂ) → E),
    (∀ (a : ℝ) w w', OO ((a : ℂ) • w) w' = (a : ℂ) • OO w w') →
    (∀ (a : ℝ) w w', OO w ((a : ℂ) • w') = (a : ℂ) • OO w w') →
    ∀ (w : Fin m → ℂ) (w' : Fin m' → ℂ) (Gv T T' : ℝ) (th : ℂ), 0 < Gv → 0 < T → 0 < T' →
      sq2 w = Gv / T → sq2 w' = Gv / T' →
      (th / (Gv : ℂ)) • OO w w' = (th / ((Real.sqrt (T * T') : ℝ) : ℂ)) • OO (unitOf T Gv w) (unitOf T' Gv w')
def DminPoly : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)), U.IsPolyDeg l.val (fun g => Dmin k r z z' g l)
def GfPoly : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), U.IsPolyDeg (2 * r + 2) (fun g => ((Gf k r z z' g : ℝ) : ℂ))
def GfDlast : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 0 ≤ Tz k r z → 0 ≤ Tz k r z' →
    ∀ (g : B.Mat k r) (ε : ℝ), ε ≤ Gf k r z z' g → ε ≤ Complex.normSq (Dmin k r z z' g (Fin.last (r + 1)))
abbrev EndH (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] := (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)
section ddplus
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def domL (D : B.RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ 0 < Gf k r D.z D.z' g ∧ ∀ l ∈ L, Dmin k r D.z D.z' g l ≠ 0}
def bigPos (D : B.RealPlaceData k r Wp Wq) : Set (B.Mat k r) := domL D Finset.univ
def monoM (D : B.RealPlaceData k r Wp Wq) (a b : Fin (r + 2) → ℕ) (c : ℕ) (g : B.Mat k r) : ℂ :=
  (∏ l, (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) *
    ((Gf k r D.z D.z' g : ℝ) : ℂ)⁻¹ ^ c
def Epart {nf : ℕ} (fib : Fin nf → B.Mat k r → EndH Wp Wq) (es : List (Fin nf × List (B.Mat k r)))
    (g : B.Mat k r) : EndH Wp Wq :=
  (es.map fun e => B.Rw e.2 (fib e.1) g).prod
def FibBound (D : B.RealPlaceData k r Wp Wq) (E : B.Mat k r → EndH Wp Wq) : Prop :=
  B.CkOn ⊤ (B.GPos D) E ∧ ∀ ε : ℝ, 0 < ε → ∀ i : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), UnitWords k r u v i →
    ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → ‖B.dLR u v E g‖ ≤ C * B.gN g ^ (3 * (r + 1) * i)
def InDDPlus (D : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → EndH Wp Wq)
    (L : Finset (Fin (r + 2))) (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq) : Prop :=
  B.SmoothCoef (domL D L) Θ ∧ B.Commutes D (domL D L) Θ ∧
  ∀ T ∈ Θ, ∃ (P : B.Mat k r → ℂ) (a b : Fin (r + 2) → ℕ) (c : ℕ)
      (es : List (Fin nf × List (B.Mat k r))), U.IsPolyDeg κ P ∧
      (∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) ∧
      T.word.length + (es.map fun e => e.2.length).sum ≤ o ∧ (∀ e ∈ es, ∀ X ∈ e.2, B.inLie k r X) ∧
      ∀ g ∈ domL D L, T.coef g = (P g * monoM D a b c g) • Epart fib es g
def IsCut0 (χ₀ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ₀ ∧ (∃ δ : ℝ, 0 < δ ∧ ∀ x, x < δ → χ₀ x = 0) ∧ ∀ x, 1 ≤ x → χ₀ x = 1
def chiAll (D : B.RealPlaceData k r Wp Wq) (χ₀ : ℝ → ℝ) (de : ℝ) (L : Finset (Fin (r + 2))) (g : B.Mat k r) : ℝ :=
  ∏ l ∈ L, χ₀ (Complex.normSq (Dmin k r D.z D.z' g l) / de)
def cutAll (D : B.RealPlaceData k r Wp Wq) (χ₀ : ℝ → ℝ) (de : ℝ) (L : Finset (Fin (r + 2)))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) : B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun g => ((chiAll D χ₀ de L g : ℝ) : ℂ) • F g
end ddplus
def ComposeDDPlus : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (nf : ℕ)
    (fib : Fin nf → B.Mat k r → EndH Wp Wq) (L : Finset (Fin (r + 2))) (o₁ κ₁ o₂ κ₂ : ℕ)
    (Θ₁ Θ₂ : B.DiffOp k r Wp Wq),
    (∀ j, FibBound D (fib j)) → InDDPlus D fib L o₁ κ₁ Θ₁ → InDDPlus D fib L o₂ κ₂ Θ₂ →
    ∃ Θ : B.DiffOp k r Wp Wq, InDDPlus D fib L (o₁ + o₂) (κ₁ + κ₂ + (2 * r + 2) * o₁) Θ ∧
      ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((o₁ + o₂ : ℕ) : ℕ∞) (B.GV k r) F →
        ∀ g ∈ domL D L, B.opApply Θ F g = B.opApply Θ₁ (B.opApply Θ₂ F) g
def BudgetClass : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (nf : ℕ)
    (fib : Fin nf → B.Mat k r → EndH Wp Wq) (L : Finset (Fin (r + 2))) (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq)
    (ε de : ℝ) (χ₀ : ℝ → ℝ) (A₀ : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    0 < ε → 0 < de → IsCut0 χ₀ → (∀ j, FibBound D (fib j)) → InDDPlus D fib L o κ Θ →
    (∀ mm : ℕ, B.InCC A₀ mm F) → (∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    ∀ mm : ℕ, B.InCC (A₀ - κ - 3 * ((r : ℝ) + 1) * ((mm : ℝ) + o)) mm (B.opApply Θ (cutAll D χ₀ de L F))
def AV (CV r n : ℕ) : ℝ := (CV : ℝ) * ((r : ℝ) ^ 3 * n + (n : ℝ) ^ 2 + (r : ℝ) ^ 4)
def mmV (CV r : ℕ) : ℕ := CV * (r ^ 2 + 1)
def BudgetArith : Prop :=
  ∀ (Cb : ℝ) (CV : ℕ), 0 ≤ Cb → ∃ C₀ : ℝ, ∀ (r n N o κ As : ℕ) (A₀ : ℝ), 1 ≤ r → 2 * r + 2 ≤ n →
    N * n ^ 2 ≤ As → n ^ 3 ≤ As → (o : ℝ) ≤ Cb * N * n → (κ : ℝ) ≤ Cb * ((r : ℝ) + 1) * o →
    C₀ * ((r : ℝ) + 1) ^ 4 * As ≤ A₀ →
    (r : ℝ) * AV CV r n ≤ A₀ - κ - 3 * ((r : ℝ) + 1) * ((mmV CV r : ℝ) + o)
def BigCellVanishingThreshold : Prop :=
  ∀ (c₃ Cb : ℝ), 0 ≤ c₃ → 0 ≤ Cb → ∃ C₀ : ℝ, ∀ (r n N o As : ℕ) (A₀ : ℝ), 1 ≤ r → 2 * r + 2 ≤ n →
    N * n ^ 2 ≤ As → n ^ 3 ≤ As → (o : ℝ) ≤ Cb * N * n → C₀ * ((r : ℝ) + 1) ^ 4 * As ≤ A₀ →
    c₃ * ((r : ℝ) + 1) ^ 2 * ((o : ℝ) + r * n + 1) ≤ A₀ - 3 * ((r : ℝ) + 1) * ((o : ℝ) + 1)
def DensThreshJ : Prop :=
  ∀ (C₁ c₃ : ℝ) (C₂ : ℕ), 0 ≤ C₁ → 0 ≤ c₃ → ∃ CV₀ : ℕ, ∀ CV : ℕ, CV₀ ≤ CV → ∀ (r n s : ℕ) (A : ℝ),
    1 ≤ r → 2 * r + 2 ≤ n → s ≤ r → (r : ℝ) * AV CV r n ≤ A →
    C₁ * (s : ℝ) ^ 2 ≤ U.a1 r A (C₂ * s ^ 2) 1 ∧
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1) ≤ U.a1 r A (C₂ * s ^ 2) 1 ∧
    2 * (r : ℝ) * n + 1 ≤ U.a1 r A (C₂ * s ^ 2) 1
def DensThreshTop : Prop :=
  ∀ (C₁ C : ℝ) (C₂ : ℕ), 0 ≤ C₁ → 0 ≤ C → ∃ CV₀ : ℕ, ∀ CV : ℕ, CV₀ ≤ CV → ∀ (r n s al : ℕ) (A : ℝ),
    1 ≤ r → 2 * r + 2 ≤ n → s ≤ r + 1 → al ≤ C₂ * s ^ 2 → (r : ℝ) * AV CV r n ≤ A →
    C₁ * (s : ℝ) ^ 2 + 2 * ((r : ℝ) + 1) ^ 2 ≤
      (A - C * ((n : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * al)) / (5 * ((r : ℝ) + 1)) - C * (r : ℝ) ^ 2 ∧
    C₂ * s ^ 2 + 1 ≤ mmV CV r
section radial
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def EquivOn (D : B.RealPlaceData k r Wp Wq) (UU : Set (B.Mat k r)) (J : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ p, D.inSS p → ∀ g ∈ UU, B.rho D p J g = (B.xiTau D (1, 1) p)⁻¹ • J g
def RadZero (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) : Prop :=
  ∀ J : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn (B.opOrder Θ : ℕ∞) (bigPos D) J → EquivOn D (bigPos D) J →
    ∀ g ∈ bigPos D, B.opApply Θ J g = 0
end radial
def JCommuteBig : Prop :=
  ∃ c₃ : ℝ, 0 ≤ c₃ ∧ ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    B.SmoothCoef (bigPos D) Θ → B.Commutes D (bigPos D) Θ →
    c₃ * ((r : ℝ) + 1) ^ 2 * ((B.opOrder Θ : ℝ) + r * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    B.InCC A (B.opOrder Θ + 1) F →
    B.CkOn (B.opOrder Θ : ℕ∞) (bigPos D) (B.JF D F) ∧ EquivOn D (bigPos D) (B.JF D F) ∧
      ∀ g ∈ bigPos D, B.JF D (B.opApply Θ F) g = B.opApply Θ (B.JF D F) g
def BigCellVanishing : Prop :=
  ∃ c₃ : ℝ, 0 ≤ c₃ ∧ ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    B.SmoothCoef (bigPos D) Θ → B.Commutes D (bigPos D) Θ → RadZero D Θ →
    c₃ * ((r : ℝ) + 1) ^ 2 * ((B.opOrder Θ : ℝ) + r * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    B.InCC A (B.opOrder Θ + 1) F → ∀ g ∈ bigPos D, B.JF D (B.opApply Θ F) g = 0
def BigCellVanishingOfCommute : Prop := JCommuteBig → BigCellVanishing
def meanDisc (f : ℂ → ℂ) (x₀ : ℂ) (R : ℝ) : ℂ :=
  ((volume (Metric.ball x₀ R)).toReal)⁻¹ • ∫ x in Metric.ball x₀ R, f x
def DiscMean : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∃ C : ℝ, ∀ (ξ x₀ : ℂ) (R : ℝ), ξ ≠ 0 → 0 < R →
    ‖meanDisc (fun x => G.psi β (ξ * x)) x₀ R‖ ≤ C * (R * ‖ξ‖) ^ (-(3 / 2 : ℝ))
def AveragingZero : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (p : Seminorm ℂ V) (s : ℕ) (w : Fin s → ℂ)
    (a : Fin s → V) (C' x₁ : ℝ), Function.Injective w →
    (∀ x : ℂ, x₁ ≤ ‖x‖ → p (∑ j, G.psi β (w j * x) • a j) ≤ C' / ‖x‖) → ∀ j, p (a j) = 0
def AveragingOfParts : Prop := DiscMean → AveragingZero
def RootFacts : Prop :=
  ∀ (s : ℕ) (D' : ℂ), 1 ≤ s → D' ≠ 0 →
    (G.rootSet s D').card = s ∧ ∀ z ∈ G.rootSet s D', ‖z‖ = ‖D'‖ ^ ((1 : ℝ) / s)
section orbit
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def Rset (γ : B.Mat k r) : Set (B.Mat k r) := {ρ | ρ ∈ Nset k r ∧ γ⁻¹ * ρ * γ ∈ Nset k r}
def IsRelevant (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : Prop :=
  γ ∈ B.GV k r ∧ ∀ ρ ∈ Rset γ, psi k r D.z cStd ρ = psi k r D.z' cStd (γ⁻¹ * ρ * γ)
def actR (γ ρ : B.Mat k r) (p : B.SS k r) : B.SS k r :=
  ((p.1.1, Matrix.of.symm (ρ * Matrix.of p.1.2)), (p.2.1, Matrix.of.symm (γ⁻¹ * ρ * γ * Matrix.of p.2.2)))
structure OrbData (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) where
  μR : Measure (Mt k r)
  haarR : B.IsHaarOn (Rset γ) μR
  J : (B.Mat k r → (Wq →L[ℂ] Wp)) → (Wq →L[ℂ] Wp)
  weil : ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (θ : B.SS k r → ℝ), Measurable θ → (∀ p, 0 ≤ θ p) →
    (∀ p, D.inSS p → ∫ x, θ (actR γ (Matrix.of x) p) ∂μR = 1) →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F γ)) D.μSS →
    ∫ p, θ p • (B.xiTau D (1, 1) p • B.rho D p F γ) ∂D.μSS = J F
end orbit
def LemmaDens : Prop :=
  ∃ CV : ℕ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (O : OrbData D γ),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) → (∀ g ∈ bigPos D, B.JF D F' g = 0) →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → O.J F' = 0
def Vanishing : Prop :=
  ∀ Cb : ℝ, 0 ≤ Cb → ∃ C₀ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (nf : ℕ) (fib : Fin nf → B.Mat k r → EndH Wp Wq) (L : Finset (Fin (r + 2)))
    (o κ N As : ℕ) (Θ : B.DiffOp k r Wp Wq) (ε de : ℝ) (χ₀ : ℝ → ℝ) (A₀ : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (γ : B.Mat k r) (O : OrbData D γ),
    1 ≤ r → 0 < ε → 0 < de → IsCut0 χ₀ → (∀ j, FibBound D (fib j)) → InDDPlus D fib L o κ Θ → RadZero D Θ →
    (o : ℝ) ≤ Cb * N * ((2 * r + k + 1 : ℕ) : ℝ) → (κ : ℝ) ≤ Cb * ((r : ℝ) + 1) * o →
    N * (2 * r + k + 1) ^ 2 ≤ As → (2 * r + k + 1) ^ 3 ≤ As → C₀ * ((r : ℝ) + 1) ^ 4 * As ≤ A₀ →
    (∀ mm : ℕ, B.InCC A₀ mm F) → (∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → O.J (B.opApply Θ (cutAll D χ₀ de L F)) = 0
def VanishingOfParts : Prop := BigCellVanishing → BudgetClass → BudgetArith → BigCellVanishingThreshold → LemmaDens → Vanishing
end Formalism.FourierDecayAlt.C6


