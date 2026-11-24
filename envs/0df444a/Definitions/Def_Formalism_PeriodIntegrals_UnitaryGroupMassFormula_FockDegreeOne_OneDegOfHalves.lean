-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:20.916956+00:00
-- url     : https://prove2.me/theorems/2f036eca-41cc-4fc2-8bdf-ed2b39302a9b
-- title:
--   One Deg Of Halves
-- statement:
--   Definitions and structural lemmas for One Deg Of Halves, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/OneDegOfHalves.lean

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
namespace PI.FockOneDegW
def Harm2 {p q r s : ℕ} (P : Pol p q r s) : Prop :=
  ∀ Z : Mat r s, IsPC Z → minusPart (fockAct2 p q r s Z) P = 0
def FirstHalf : Prop := ∀ p q r s : ℕ,
  ∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
    (∀ Z : Mat r s, IsPC Z → minusPart ((fockAct2 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d
def SecondHalf : Prop := ∀ p q r s : ℕ,
  ∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
    (∀ Z : Mat p q, IsPC Z → minusPart ((fockAct1 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d
def posOp {p q r s : ℕ} (a b : Ix p q) : Module.End ℂ (Pol p q r s) :=
  ∑ c : Ix r s, if linePos ((a, c) : Ln p q r s) = true then
    LinearMap.mulLeft ℂ (X ((a, c) : Ln p q r s)) ∘ₗ (pderiv ((b, c) : Ln p q r s)).toLinearMap
  else 0
def negOp {p q r s : ℕ} (a b : Ix p q) : Module.End ℂ (Pol p q r s) :=
  ∑ c : Ix r s, if linePos ((a, c) : Ln p q r s) = true then 0
  else LinearMap.mulLeft ℂ (X ((a, c) : Ln p q r s)) ∘ₗ (pderiv ((b, c) : Ln p q r s)).toLinearMap
def kShift (r s : ℕ) {p q : ℕ} : Ix p q → ℚ
  | .inl _ => cPair r s
  | .inr _ => -cPair r s
def lowOp {p q r s : ℕ} (c d : Ix r s) : Module.End ℂ (Pol p q r s) :=
  ∑ a : Ix p q, if linePos ((a, d) : Ln p q r s) = true then
    (pderiv ((a, c) : Ln p q r s)).toLinearMap ∘ₗ (pderiv ((a, d) : Ln p q r s)).toLinearMap
  else 0
def InnerFacts : Prop := ∀ (σ : Type) (P Q Q' : MvPolynomial σ ℂ) (c : ℂ),
  fockInner P (Q + Q') = fockInner P Q + fockInner P Q' ∧
  fockInner P (c • Q) = c * fockInner P Q ∧
  fockInner Q P = starRingEnd ℂ (fockInner P Q) ∧
  ((fockInner P P).im = 0 ∧ 0 ≤ (fockInner P P).re) ∧
  (fockInner P P = 0 → P = 0) ∧
  ∀ l : σ, fockInner (X l * P) Q = fockInner P (pderiv l Q)
def OpsK : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b →
  fockAct1 p q r s (Eab a b) =
    posOp a b - negOp b a +
      (if a = b then (((kShift r s a : ℚ) : ℂ) • (1 : Module.End ℂ (Pol p q r s))) else 0)
def HarmIff : Prop := ∀ p q r s : ℕ, ∀ P : Pol p q r s,
  Harm2 P ↔ ∀ c d : Ix r s, ¬ sameBlock c d → lowOp (p := p) (q := q) c d P = 0
def HwHarmDeg : Prop := ∀ p q r s : ℕ, ∀ (μ : Ix p q → ℚ) (e : ℕ) (v : Pol p q r s),
  v ∈ homog (Ix p q × Ix r s) e → IsHW (fockAct1 p q r s) μ v → Harm2 v →
    (e : ℚ) = degW (cPair r s) μ
def Reduction : Prop := HwHarmDeg → FirstHalf
def Swap : Prop := FirstHalf → SecondHalf
end PI.FockOneDegW


