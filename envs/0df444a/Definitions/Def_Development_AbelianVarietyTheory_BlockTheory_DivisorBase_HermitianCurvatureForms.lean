-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCurvatureForms
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCurvatureForms
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:20.831687+00:00
-- url     : https://prove2.me/theorems/2bb46d03-0ac5-5a87-9d01-f93d307e1393
-- title:
--   Hermitian Curvature Forms
-- statement:
--   Definitions and structural lemmas for Hermitian Curvature Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/HermitianCurvatureForms.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_eventually_herm
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_one
import Theorems.Thm_GlobalTheory_HermFrame_extFormAdj_eq_neg_secondForm
import Theorems.Thm_GlobalTheory_HermFrame_extForm_eq_neg_secondFormAdj
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_IsPshC2On_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero


set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms
open GlobalTheory.HermFrame
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]
variable {m l n : Type*} [Fintype m] [Fintype l] [Fintype n]
  [DecidableEq m] [DecidableEq l] [DecidableEq n]
def secDbar (s : V → n → ℂ) (z η : V) : n → ℂ := fun a => dbar (fun x => s x a) z η
def splitSec (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (u : V → m → ℂ) (q : V → l → ℂ) (x : V) :
    m ⊕ l → ℂ := incl m l *ᵥ u x + orthLift (H x) *ᵥ q x
def homDel (A : V → Matrix m m ℂ) (B : V → Matrix n n ℂ) (T : V → Matrix n m ℂ) (z ξ : V) :
    Matrix n m ℂ := mdel T z ξ + conn B z ξ * T z - T z * conn A z ξ
def wedgeHolAnti {p r s : Type*} [Fintype r] (A : V → Matrix p r ℂ) (B : V → Matrix r s ℂ)
    (ξ η : V) : Matrix p s ℂ := A ξ * B η
def wedgeAntiHol {p r s : Type*} [Fintype r] (B : V → Matrix p r ℂ) (A : V → Matrix r s ℂ)
    (ξ η : V) : Matrix p s ℂ := -(B η * A ξ)
def covDelAnti (A : V → Matrix m m ℂ) (B : V → Matrix n n ℂ) (β : V → V → Matrix n m ℂ)
    (z ξ η : V) : Matrix n m ℂ := homDel A B (fun x => β x η) z ξ
def dbarAnti (β : V → V → Matrix n m ℂ) (z η₁ η₂ : V) : Matrix n m ℂ :=
  mdbar (fun x => β x η₂) z η₁ - mdbar (fun x => β x η₁) z η₂
def covDelHol (A : V → Matrix m m ℂ) (B : V → Matrix n n ℂ) (γ : V → V → Matrix n m ℂ)
    (z ξ₁ ξ₂ : V) : Matrix n m ℂ :=
  homDel A B (fun x => γ x ξ₂) z ξ₁ - homDel A B (fun x => γ x ξ₁) z ξ₂
def dbarHol (γ : V → V → Matrix n m ℂ) (z ξ η : V) : Matrix n m ℂ :=
  -mdbar (fun x => γ x ξ) z η
def IsNonnegForm {W : Type*} [AddCommGroup W] [Module ℂ W] (α : W → W → ℂ) : Prop :=
  IsSesq α ∧ (∀ ξ η, conj (α ξ η) = -α η ξ) ∧ FormLe (fun _ _ => 0) α
def gramS (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (x : V) : Matrix m m ℂ := subGram (H x)
def gramQ (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (x : V) : Matrix l l ℂ := quotGram (H x)
def ConnBlocks (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : V) (P : V → Matrix m l ℂ)
    (R : V → Matrix l m ℂ) : Prop :=
  ∀ (u : V → m → ℂ) (q : V → l → ℂ), (∀ a, DifferentiableAt ℝ (fun x => u x a) z) →
    (∀ a, DifferentiableAt ℝ (fun x => q x a) z) →
    (∀ ξ, orthProj (H z) *ᵥ covDel H (splitSec H u q) z ξ = covDel (gramS H) u z ξ) ∧
    (∀ ξ, quotMap m l *ᵥ covDel H (splitSec H u q) z ξ =
      R ξ *ᵥ u z + covDel (gramQ H) q z ξ) ∧
    (∀ η, orthProj (H z) *ᵥ secDbar (splitSec H u q) z η = secDbar u z η + P η *ᵥ q z) ∧
    (∀ η, quotMap m l *ᵥ secDbar (splitSec H u q) z η = secDbar q z η)
def FormTypes (P : V → V → Matrix m l ℂ) (R : V → V → Matrix l m ℂ) (z : V) : Prop :=
  (∀ η η', P z (η + η') = P z η + P z η') ∧ (∀ (c : ℂ) η, P z (c • η) = conj c • P z η) ∧
  (∀ ξ ξ', R z (ξ + ξ') = R z ξ + R z ξ') ∧ (∀ (c : ℂ) ξ, R z (c • ξ) = c • R z ξ) ∧
  (∀ η, MContDiffAt ∞ (fun x => P x η) z) ∧ (∀ ξ, MContDiffAt ∞ (fun x => R x ξ) z)
def SubQuotAt (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : V) : Prop :=
  (∀ ξ (T : Matrix (m ⊕ l) (m ⊕ l) ℂ), Tᵀ * H z = mdel H z ξ ↔ T = conn H z ξ) ∧
  FormTypes (secondFormAdj H) (secondForm H) z ∧
  (∀ ξ s q, form (gramQ H z) (secondForm H z ξ *ᵥ s) q =
    form (gramS H z) s (secondFormAdj H z ξ *ᵥ q)) ∧
  ConnBlocks H z (fun η => -secondFormAdj H z η) (secondForm H z) ∧
  (∀ ξ η, curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) +
    wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η) ∧
  (∀ ξ η, curv (gramQ H) z ξ η = blockQQ (H z) (curv H z ξ η) +
    wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η)
def SecondFormSignAt (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : V) : Prop :=
  ∀ ξ s, form (gramS H z) (wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ ξ *ᵥ s) s =
    -((gnorm (gramQ H z) (secondForm H z ξ *ᵥ s) ^ 2 : ℝ) : ℂ)
def ExtBlocksAt (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : V) : Prop :=
  FormTypes (extForm H) (extFormAdj H) z ∧
  (∀ ξ q s, form (gramS H z) (extForm H z ξ *ᵥ q) s =
    form (gramQ H z) q (extFormAdj H z ξ *ᵥ s)) ∧
  ConnBlocks H z (extForm H z) (fun ξ => -extFormAdj H z ξ) ∧
  (∀ ξ η, blockSS (H z) (curv H z ξ η) =
    curv (gramS H) z ξ η - wedgeAntiHol (extForm H z) (extFormAdj H z) ξ η) ∧
  (∀ ξ η, blockSQ (H z) (curv H z ξ η) = covDelAnti (gramQ H) (gramS H) (extForm H) z ξ η) ∧
  (∀ ξ η, blockQS (curv H z ξ η) = -dbarHol (extFormAdj H) z ξ η) ∧
  (∀ ξ η, blockQQ (H z) (curv H z ξ η) =
    curv (gramQ H) z ξ η - wedgeHolAnti (extFormAdj H z) (extForm H z) ξ η) ∧
  (∀ η₁ η₂, dbarAnti (extForm H) z η₁ η₂ = 0) ∧
  (∀ ξ₁ ξ₂, covDelHol (gramS H) (gramQ H) (extFormAdj H) z ξ₁ ξ₂ = 0)
def AnyRankAt (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : V) : Prop :=
  IsNonnegForm (extTrace H z) ∧
  (∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η) ∧
  (∀ ξ₁ η₁ ξ₂ η₂, ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ =
    chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂)
def RankTwoAt (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : V) : Prop :=
  IsNonnegForm (extTrace H z) ∧
  (∀ ξ₁ η₁ ξ₂ η₂, wedge (extTrace H z) (extTrace H z) ξ₁ η₁ ξ₂ η₂ = 0) ∧
  (∀ u : m → ℂ, u ≠ 0 → ∀ ξ η,
    chernOne (gramS H) z ξ η = lineCurv H z (incl m l *ᵥ u) ξ η - extTrace H z ξ η ∧
    chernOne (gramQ H) z ξ η =
      chernOne H z ξ η - lineCurv H z (incl m l *ᵥ u) ξ η + extTrace H z ξ η) ∧
  (∀ ξ₁ η₁ ξ₂ η₂, ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ =
    chernTwo H z ξ₁ η₁ ξ₂ η₂ - wedge (chernOne (gramS H) z) (chernOne (gramQ H) z) ξ₁ η₁ ξ₂ η₂)
def SubQuotCurvature : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    [FiniteDimensional ℂ V] (m l : Type) [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    (U : Set V) (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ),
    (IsHermFrame U H → (∀ z ∈ U, IsUnit (subGram (H z)).det) →
      IsHermFrame U (gramS H) ∧ IsHermFrame U (gramQ H) ∧ ∀ z ∈ U, SubQuotAt H z) ∧
    (IsPosFrame U H →
      IsPosFrame U (gramS H) ∧ IsPosFrame U (gramQ H) ∧
      (∀ z ∈ U, SecondFormSignAt H z ∧ ExtBlocksAt H z ∧ AnyRankAt H z) ∧
      (Fintype.card m = 1 → Fintype.card l = 1 → ∀ z ∈ U, RankTwoAt H z))
theorem isPosFrame_tautPairGram : IsPosFrame Set.univ tautPairGram := by
  have hc : ContDiff ℝ ∞ fun z : ℂ => conj z := conjCLE.contDiff
  refine ⟨isOpen_univ, ?_, fun z _ => posDef_iff.2 ⟨?_, fun v hv => ?_⟩⟩
  · rintro (a | a) (b | b)
    · exact (contDiff_const.add (contDiff_id.mul hc)).contDiffOn
    · exact contDiff_id.contDiffOn
    · exact hc.contDiffOn
    · exact contDiff_const.contDiffOn
  · ext (a | a) (b | b) <;> simp [tautPairGram, mul_comm]
  · have e : form (tautPairGram z) v v =
        ((normSq (v (.inl ())) + normSq (v (.inl ()) * z + v (.inr ())) : ℝ) : ℂ) := by
      simp only [form_eq_sum, ofReal_add, ← mul_conj]
      simp [tautPairGram]; ring
    rw [e, ← ofReal_zero, real_lt_real]
    by_cases h : v (.inl ()) = 0
    · have h' : v (.inr ()) ≠ 0 := fun h' => hv (by funext a; rcases a with a | a <;> assumption)
      simpa [h] using h'
    · exact add_pos_of_pos_of_nonneg (normSq_pos.2 h) (normSq_nonneg _)
example (ξ η : ℂ) : extTrace tautPairGram 0 ξ η = kappa * (ξ * conj η) := by
  have hf := isPosFrame_tautPairGram.isHermFrame
  have h : tautPairGram 0 = 1 := by
    rw [← fromBlocks_one]; ext (a | a) (b | b) <;> simp [tautPairGram]
  have hb : ∀ ξ : ℂ, secondForm tautPairGram 0 ξ () () = ξ := fun ξ => by
    rw [secondForm_eq, conn, h, transpose_one, inv_one, Matrix.one_mul]
    change del (fun x : ℂ => x) 0 ξ = ξ
    rw [del_eq_fderiv differentiableAt_fun_id]; simp
  have hs : subGram (tautPairGram 0) = 1 := by rw [h]; ext; simp [subGram, toBlocks₁₁]
  have hq : quotGram (tautPairGram 0) = 1 := by
    rw [h]; ext; simp [quotGram, toBlocks₂₂, toBlocks₂₁, mul_apply]
  have hu : IsUnit (subGram (tautPairGram 0)).det := by simp [hs]
  rw [extTrace, extFormAdj_eq_neg_secondForm (hf.one trivial) (hf.eventually_herm trivial)
      (hf.isUnit 0 trivial) hu, extForm_eq_neg_secondFormAdj (hf.one trivial)
      (hf.eventually_herm trivial) (hf.isUnit 0 trivial) hu, secondFormAdj, adj, hs, hq]
  simp [trace, mul_apply, hb]
end GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms


