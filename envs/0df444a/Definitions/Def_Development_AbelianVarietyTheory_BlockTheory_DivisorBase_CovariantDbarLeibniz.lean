-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:05.282105+00:00
-- url     : https://prove2.me/theorems/d418de01-cbbd-49cf-9d14-6943149c2bd0
-- title:
--   Covariant Dbar Leibniz
-- statement:
--   Definitions and structural lemmas for Covariant Dbar Leibniz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CovariantDbarLeibniz.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
section Defs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m l n k : Type*} [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l]
  [DecidableEq n]
def wedgeHolAnti {V p q : Type*} (A : V → Matrix p n ℂ) (B : V → Matrix n q ℂ) (ξ η : V) :
    Matrix p q ℂ := A ξ * B η
def wedgeAntiHol {V p q : Type*} (B : V → Matrix p n ℂ) (A : V → Matrix n q ℂ) (ξ η : V) :
    Matrix p q ℂ := -(B η * A ξ)
def covDbar (s : E → n → ℂ) (z η : E) : n → ℂ := fun a => dbar (fun x => s x a) z η
def homCovDel (A : E → Matrix m m ℂ) (B : E → Matrix l l ℂ) (T : E → Matrix l m ℂ) (z ξ : E) :
    Matrix l m ℂ := mdel T z ξ + conn B z ξ * T z - T z * conn A z ξ
def delOfAnti (A : E → Matrix m m ℂ) (B : E → Matrix l l ℂ) (β : E → E → Matrix l m ℂ)
    (z ξ η : E) : Matrix l m ℂ := homCovDel A B (fun x => β x η) z ξ
def delOfHol (A : E → Matrix m m ℂ) (B : E → Matrix l l ℂ) (γ : E → E → Matrix l m ℂ)
    (z ξ₁ ξ₂ : E) : Matrix l m ℂ :=
  homCovDel A B (fun x => γ x ξ₂) z ξ₁ - homCovDel A B (fun x => γ x ξ₁) z ξ₂
def dbarOfHol {p q : Type*} (γ : E → E → Matrix p q ℂ) (z ξ η : E) : Matrix p q ℂ :=
  -mdbar (fun x => γ x ξ) z η
def dbarOfAnti {p q : Type*} (β : E → E → Matrix p q ℂ) (z η₁ η₂ : E) : Matrix p q ℂ :=
  mdbar (fun x => β x η₂) z η₁ - mdbar (fun x => β x η₁) z η₂
def subField (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (x : E) : Matrix m m ℂ := subGram (H x)
def quotField (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (x : E) : Matrix l l ℂ := quotGram (H x)
def pairSection (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (s : E → m → ℂ) (q : E → l → ℂ) (x : E) :
    m ⊕ l → ℂ := incl m l *ᵥ s x + orthLift (H x) *ᵥ q x
def IsHolFormAt {p q : Type*} (A : E → E → Matrix p q ℂ) (z : E) : Prop :=
  IsLinearMap ℂ (A z) ∧ ∀ ξ, MContDiffAt ∞ (fun x => A x ξ) z
def IsAntiFormAt {p q : Type*} (B : E → E → Matrix p q ℂ) (z : E) : Prop :=
  (∀ η η', B z (η + η') = B z η + B z η') ∧ (∀ (c : ℂ) η, B z (c • η) = conj c • B z η) ∧
    ∀ η, MContDiffAt ∞ (fun x => B x η) z
def ConnBlocks (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (A : E → Matrix l m ℂ) (B : E → Matrix m l ℂ)
    (z : E) : Prop :=
  ∀ (s : E → m → ℂ) (q : E → l → ℂ), (∀ a, ContDiffAt ℝ 1 (fun x => s x a) z) →
    (∀ a, ContDiffAt ℝ 1 (fun x => q x a) z) → ∀ ξ : E,
      orthProj (H z) *ᵥ covDel H (pairSection H s q) z ξ = covDel (subField H) s z ξ ∧
      quotMap m l *ᵥ covDel H (pairSection H s q) z ξ =
        A ξ *ᵥ s z + covDel (quotField H) q z ξ ∧
      orthProj (H z) *ᵥ covDbar (pairSection H s q) z ξ = covDbar s z ξ + B ξ *ᵥ q z ∧
      quotMap m l *ᵥ covDbar (pairSection H s q) z ξ = covDbar q z ξ
def IsNonnegForm {V : Type*} [AddCommGroup V] [Module ℂ V] (α : V → V → ℂ) : Prop :=
  IsSesq α ∧ (∀ ξ η, conj (α ξ η) = -α η ξ) ∧ FormLe (fun _ _ => 0) α
def SubQuotAt (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : E) : Prop :=
  IsHolFormAt (secondForm H) z ∧ IsAntiFormAt (secondFormAdj H) z ∧
  (∀ ξ s q, form (quotField H z) (secondForm H z ξ *ᵥ s) q =
    form (subField H z) s (secondFormAdj H z ξ *ᵥ q)) ∧
  ConnBlocks H (secondForm H z) (fun η => -secondFormAdj H z η) z ∧
  (∀ ξ η, curv (subField H) z ξ η =
    blockSS (H z) (curv H z ξ η) + wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η) ∧
  (∀ ξ η, curv (quotField H) z ξ η =
    blockQQ (H z) (curv H z ξ η) + wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η) ∧
  ((H z).PosDef → ∀ ξ s,
    form (subField H z) (wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ ξ *ᵥ s) s =
      -((gnorm (quotField H z) (secondForm H z ξ *ᵥ s) ^ 2 : ℝ) : ℂ))
def ExtBlocksAt (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : E) : Prop :=
  IsAntiFormAt (extForm H) z ∧ IsHolFormAt (extFormAdj H) z ∧
  ConnBlocks H (fun ξ => -extFormAdj H z ξ) (extForm H z) z ∧
  (∀ ξ η, blockSS (H z) (curv H z ξ η) =
    curv (subField H) z ξ η - wedgeAntiHol (extForm H z) (extFormAdj H z) ξ η) ∧
  (∀ ξ η, blockSQ (H z) (curv H z ξ η) =
    delOfAnti (quotField H) (subField H) (extForm H) z ξ η) ∧
  (∀ ξ η, blockQS (curv H z ξ η) = -dbarOfHol (extFormAdj H) z ξ η) ∧
  (∀ ξ η, blockQQ (H z) (curv H z ξ η) =
    curv (quotField H) z ξ η - wedgeHolAnti (extFormAdj H z) (extForm H z) ξ η) ∧
  (∀ η₁ η₂, dbarOfAnti (extForm H) z η₁ η₂ = 0) ∧
  (∀ ξ₁ ξ₂, delOfHol (subField H) (quotField H) (extFormAdj H) z ξ₁ ξ₂ = 0)
def ChTwoAt (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : E) : Prop :=
  IsNonnegForm (extTrace H z) ∧
  ∀ ξ₁ η₁ ξ₂ η₂, ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ =
    chTwo (subField H) z ξ₁ η₁ ξ₂ η₂ + chTwo (quotField H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂
def vertForm [Unique m] [Unique l] (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ η : E) : ℂ :=
  kappa * (extFormAdj H z ξ default default * extForm H z η default default)
def RankTwoAt [Unique m] [Unique l] (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : E) : Prop :=
  IsNonnegForm (vertForm H z) ∧
  (∀ ξ₁ η₁ ξ₂ η₂, wedge (vertForm H z) (vertForm H z) ξ₁ η₁ ξ₂ η₂ = 0) ∧
  (∀ s : m → ℂ, s ≠ 0 → ∀ ξ η,
    chernOne (subField H) z ξ η = lineCurv H z (incl m l *ᵥ s) ξ η - vertForm H z ξ η ∧
    chernOne (quotField H) z ξ η =
      chernOne H z ξ η - lineCurv H z (incl m l *ᵥ s) ξ η + vertForm H z ξ η) ∧
  (∀ ξ₁ η₁ ξ₂ η₂, ddcForm (vertForm H) z ξ₁ η₁ ξ₂ η₂ = chernTwo H z ξ₁ η₁ ξ₂ η₂ -
    wedge (chernOne (subField H) z) (chernOne (quotField H) z) ξ₁ η₁ ξ₂ η₂) ∧
  vertForm H z = extTrace H z
end Defs
def SubQuotCurvature : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (m l : Type) [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    (U : Set E) (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ), IsHermFrame U H →
    (∀ z ∈ U, IsUnit (subField H z).det) →
      IsHermFrame U (subField H) ∧ IsHermFrame U (quotField H) ∧ ∀ z ∈ U, SubQuotAt H z
def AnyRankCurvature : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (m l : Type) [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    (U : Set E) (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ), IsPosFrame U H →
      ∀ z ∈ U, ExtBlocksAt H z ∧ ChTwoAt H z
def RankTwoCurvature : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (m l : Type) [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] [Unique m] [Unique l]
    (U : Set E) (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ), IsPosFrame U H →
      ∀ z ∈ U, ExtBlocksAt H z ∧ RankTwoAt H z
def Statement : Prop := SubQuotCurvature ∧ RankTwoCurvature ∧ AnyRankCurvature
section Basic₂
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m l k : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
def lorentzPairGram (z : ℂ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  fromBlocks (of fun _ _ => 1 - z * conj z) (of fun _ _ => -z) (of fun _ _ => -conj z) (-1)
end Basic₂
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz


