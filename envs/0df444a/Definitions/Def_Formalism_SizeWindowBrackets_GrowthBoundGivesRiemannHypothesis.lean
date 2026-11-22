-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
-- name    : Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:59.162221+00:00
-- url     : https://prove2.me/theorems/22e3dd79-df0a-4985-b383-d7e6f628808d
-- title:
--   Growth Bound Gives Riemann Hypothesis
-- statement:
--   Definitions and structural lemmas for Growth Bound Gives Riemann Hypothesis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_SizeWindowBrackets_PowerBoundGivesRiemannHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def psC : AddChar (E0 × H) ℂ where
  toFun g := if g.1.2 = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rcases a with ⟨⟨a1, a2⟩, ah⟩
    rcases b with ⟨⟨b1, b2⟩, bh⟩
    have key : ∀ x y : ZMod 2, (if x + y = 0 then (1 : ℂ) else -1)
        = (if x = 0 then 1 else -1) * (if y = 0 then 1 else -1) := by
      intro x y
      have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      rcases h2 x with rfl | rfl <;> rcases h2 y with rfl | rfl <;> simp [h11, h10]
    exact key a2 b2
def chpsC : AddChar (E0 × H) ℂ := chC * psC
def Gsig (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (y : ℝ) : ℂ :=
  GPsi D ell 0 y + GPsi D ell psC y - GPsi D ell chC y - GPsi D ell chpsC y
def CharacterSignsAtBaseClass : Prop :=
  (chC : AddChar (E0 × H) ℂ) sgc0 = -1 ∧ (psC : AddChar (E0 × H) ℂ) sgc0 = 1 ∧ (chpsC : AddChar (E0 × H) ℂ) sgc0 = -1
def fPl (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] : ℝ := ((PhiSet (H := H)).card : ℝ)
def delta2 (T2 : Finset H) : ℝ := (T2.card : ℝ) / (Fintype.card H : ℝ)
def ThickPartTranslateMean : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (T2 : Finset H) (t : H) (A b : ℝ), 0 < A → 0 < b →
    (1 / (Fintype.card H : ℂ)) * ∑ u0 : H, (1 / ((PhiSet (H := H)).card : ℂ)) *
        ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g ∧ IsThickAt T2 u0 (partner t g)),
          ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * (b : ℂ) * GPsi D ell ψ (A / b)
      = ((delta2 T2 * b / 2 : ℝ) : ℂ) * Gsig D ell (A / b)
def topExcess (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) : ℝ :=
  (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
    (ASK D N (a t) t (w u0 j) - (MAIN ell (a t) (w u0 j)).re)
def ThinScales (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (X' θ : ℝ) : Prop :=
  ∀ ψ : AddChar (E0 × H) ℂ, ∀ y : ℝ, X' / 3 ≤ y → ‖GPsi D ell ψ y‖ ≤ y * θ
def LipW (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) : Prop :=
  ∀ (ψ : AddChar (E0 × H) ℂ) (A w w' : ℝ), 0 < A → 0 < w → 0 < w' →
    ‖(w : ℂ) * GPsi D ell ψ (A / w) - (w' : ℂ) * GPsi D ell ψ (A / w')‖ ≤ 3 * A / min w w' * |w - w'|
def DerivInt (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (Cd : ℝ) : Prop :=
  (∀ ψ : AddChar (E0 × H) ℂ, ψ ≠ 0 → ∀ y z : ℝ, 1 ≤ y → 1 ≤ z →
      ‖GPsi D ell ψ y - GPsi D ell ψ z‖ ≤ |y - z| * (Real.log (max y z) + Cd + ‖ell ψ‖)) ∧
  (∀ y z : ℝ, 1 ≤ y → 1 ≤ z → |Gz y - Gz z| ≤ Cd * |y - z|)
def ValuesAtX (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (x ε CL : ℝ) : Prop :=
  ∀ ψ : AddChar (E0 × H) ℂ, (ψ = psC ∨ ψ = chC ∨ ψ = chpsC) →
    ‖GPsi D ell ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ ‖ell ψ‖ ≤ CL * Real.log x
def NodeSizes {m : ℕ} (T2 : Finset H) (b b' η : ℝ) (w : H → Fin m → E0 × H → ℝ) : Prop :=
  (∀ u0 j ρ, InPhi ρ → 0 < w u0 j ρ) ∧
  (∀ u0 j ρ, IsThickAt T2 u0 ρ → b ≤ w u0 j ρ ∧ w u0 j ρ ≤ b + η + 1) ∧
  (∀ u0 j ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → w u0 j ρ ≤ 2 * b')
def moveCost (x Cd CL : ℝ) : ℝ := Cd + 3 * (Real.log (x + 1) + Cd + CL * Real.log x)
def GrowthInequalityHypotheses (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) {m : ℕ} (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (x ε b b' η X' θ Cd CL Err : ℝ) : Prop :=
  3 ≤ x ∧ 0 < b ∧ 0 ≤ η ∧ 0 < X' ∧ 0 < b' ∧ b' * X' ≤ x * b ∧ 0 ≤ θ ∧ 0 ≤ Cd ∧
  (∀ t ∈ TT, |a t / b - x| ≤ 1) ∧
  NodeSizes T2 b b' η w ∧
  (∀ u0 j t ρ, t ∈ TT → InPhi ρ → a t / w u0 j ρ ≤ N) ∧
  topExcess D N ell TT a w ≤ Err ∧
  ThinScales D ell X' θ ∧ LipW D ell ∧ DerivInt D ell Cd ∧ ValuesAtX D ell x ε CL
def GrowthInequalityExplicit : Prop :=
  AskMainBalance (H := H) → ∀ (D : ArithData H), HostFacts D →
  ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (x ε b b' η X' θ Cd CL Err : ℝ),
    GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err →
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL)
      ≤ Err + (TT.card : ℝ) * m * (2 * fPl H * (x + 1) * b * θ)
        + (TT.card : ℝ) * m * (6 * fPl H * (x + 1) * (η + 1))
def SmallCosts (x ε f b η θ Cd CL : ℝ) : Prop :=
  moveCost x Cd CL ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ 2 * f * (x + 1) * θ ≤ 1 / x ∧ 6 * f * (x + 1) * (η + 1) ≤ b / x
def GrowthInequalityForm : Prop :=
  AskMainBalance (H := H) → ∀ (D : ArithData H), HostFacts D →
  ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (x ε b b' η X' θ Cd CL Err : ℝ),
    GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err → SmallCosts x ε (fPl H) b η θ Cd CL →
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 4 * x ^ ((1 : ℝ) / 2 + ε))
      ≤ Err + 2 * (TT.card : ℝ) * m * b / x
end
def SizeWindows (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err : ℝ) : Prop :=
  3 ≤ x ∧ 0 < ε ∧ 0 ≤ C ∧ 0 < n ∧ 0 < b ∧ 0 ≤ aE ∧ aE ≤ 2 * x * b ∧
  x ^ (-(ε / 8)) * n / 2 ≤ nT ∧
  x ^ (-ε) ≤ (nT2 : ℝ) / n ∧ nT2 ≤ n ∧
  x ^ ((1 : ℝ) / 2 - ε) ≤ m ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) ∧
  x * m ≤ k ∧ k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) ∧
  Err ≤ x ^ (C * ε) * ((nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
    + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))) ∧
  26 ≤ x ^ (3 * ε / 8)
def GrowthSizeBound : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err →
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x →
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε)
def GrowthInequalityDataExists (C ε x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H) (D : ArithData H)
    (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (b b' η X' θ Cd CL Err k aE : ℝ),
    HostFacts D ∧ GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err ∧ SmallCosts x ε (fPl H) b η θ Cd CL ∧
    SizeWindows C ε x (Fintype.card H) TT.card T2.card m b k aE Err
def RiemannHypothesisOfBalanceAndGrowthData : Prop :=
  (∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H], AskMainBalance (H := H)) →
  ∀ C ε₁ : ℝ, 0 < ε₁ → (∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → GrowthInequalityDataExists C ε x) →
    RiemannHypothesis
def GrowthBoundAtPoint : Prop :=
  ∀ C ε x : ℝ, GrowthInequalityDataExists C ε x → Gz x ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε)
def GrowthBoundGivesRiemannHypothesis : Prop :=
  ∀ C ε₁ : ℝ, 0 < ε₁ → (∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → GrowthInequalityDataExists C ε x) →
    RiemannHypothesis
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def LeadingTermTranslateMean : Prop :=
  ∀ {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (Dd : Formalism.RankGapBounds.WeightedMeanData.Data H W Top m f) (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ)
    (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (E : ℝ),
    (∀ τ, Dd.aT τ = a (eT τ)) → (∀ u0 j ρ, Dd.w u0 j ρ = w u0 j (eP ρ)) →
    Dd.gam = Real.eulerMascheroniConstant → Dd.LpL = (ell chC).re →
    (∀ u0, Dd.ASK u0 = ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)) →
    Formalism.RankGapBounds.WeightedMeanData.umean Dd.ASK ≤ Formalism.RankGapBounds.WeightedMeanData.umean Dd.Main + E → topExcess D N ell TT a w ≤ E
end
def LipWAll : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ),
    LipW D ell
def DerivIntAll : Prop :=
  ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H)
    (ell : AddChar (E0 × H) ℂ → ℂ), DerivInt D ell Cd
def ReducedGrowthInequalityDataExists (Cd C ε x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H) (D : ArithData H)
    (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (b b' η X' θ CL Err k aE : ℝ),
    HostFacts D ∧
    (3 ≤ x ∧ 0 < b ∧ 0 ≤ η ∧ 0 < X' ∧ 0 < b' ∧ b' * X' ≤ x * b ∧ 0 ≤ θ ∧
      (∀ t ∈ TT, |a t / b - x| ≤ 1) ∧
      NodeSizes T2 b b' η w ∧
      (∀ u0 j t ρ, t ∈ TT → InPhi ρ → a t / w u0 j ρ ≤ N) ∧
      topExcess D N ell TT a w ≤ Err ∧
      ThinScales D ell X' θ ∧ ValuesAtX D ell x ε CL) ∧
    SmallCosts x ε (fPl H) b η θ Cd CL ∧
    SizeWindows C ε x (Fintype.card H) TT.card T2.card m b k aE Err
def RiemannHypothesisOfReducedGrowthData : Prop :=
  ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ C ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ReducedGrowthInequalityDataExists Cd C ε x) → RiemannHypothesis
end Formalism.LFunctionChainParameters.ThickSetMeanBounds


