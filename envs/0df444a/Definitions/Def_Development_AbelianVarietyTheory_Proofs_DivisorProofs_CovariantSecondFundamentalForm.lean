-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovariantSecondFundamentalForm
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovariantSecondFundamentalForm
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:32.096115+00:00
-- url     : https://prove2.me/theorems/80344493-79bb-54e2-af0f-48aa24998904
-- title:
--   Covariant Second Fundamental Form
-- statement:
--   Definitions and structural lemmas for Covariant Second Fundamental Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovariantSecondFundamentalForm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HermitianCurvatureForms
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]
variable {m l n : Type*} [Fintype m] [Fintype l] [Fintype n]
  [DecidableEq m] [DecidableEq l] [DecidableEq n]
def SameJet {k : Type*} (u u' : V → k → ℂ) (z : V) : Prop :=
  ∀ a, u z a = u' z a ∧ ∃ D : V →L[ℝ] ℂ,
    HasFDerivAt (fun x => u x a) D z ∧ HasFDerivAt (fun x => u' x a) D z
section Jet
variable {k : Type*} {u u' v v' : V → k → ℂ} {z : V}
end Jet
variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}
def BodyA (U : Set V) (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) : Prop :=
  (IsHermFrame U H → (∀ z ∈ U, IsUnit (subGram (H z)).det) →
    IsHermFrame U (HermitianCurvatureForms.gramS H) ∧ IsHermFrame U (HermitianCurvatureForms.gramQ H) ∧
      ∀ z ∈ U, HermitianCurvatureForms.SubQuotAt H z) ∧
  (IsPosFrame U H →
    IsPosFrame U (HermitianCurvatureForms.gramS H) ∧ IsPosFrame U (HermitianCurvatureForms.gramQ H) ∧
    (∀ z ∈ U, HermitianCurvatureForms.SecondFormSignAt H z ∧ HermitianCurvatureForms.ExtBlocksAt H z ∧ HermitianCurvatureForms.AnyRankAt H z) ∧
    (Fintype.card m = 1 → Fintype.card l = 1 → ∀ z ∈ U, HermitianCurvatureForms.RankTwoAt H z))
def BodyB (U : Set V) (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) : Prop :=
  (IsHermFrame U H → (∀ z ∈ U, IsUnit (CovariantDbarLeibniz.subField H z).det) →
    IsHermFrame U (CovariantDbarLeibniz.subField H) ∧ IsHermFrame U (CovariantDbarLeibniz.quotField H) ∧
      ∀ z ∈ U, CovariantDbarLeibniz.SubQuotAt H z) ∧
  (∀ [Unique m] [Unique l], IsPosFrame U H →
    ∀ z ∈ U, CovariantDbarLeibniz.ExtBlocksAt H z ∧ CovariantDbarLeibniz.RankTwoAt H z) ∧
  (IsPosFrame U H → ∀ z ∈ U, CovariantDbarLeibniz.ExtBlocksAt H z ∧ CovariantDbarLeibniz.ChTwoAt H z)
section Pull
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W]
  [IsScalarTower ℝ ℂ W] (L : W →L[ℂ] V) {w : W}
variable {K : V → Matrix n n ℂ}
variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det)
include h
include hs
end Pull
section Smooth
variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) (hz : z ∈ U)
include h hs hz
end Smooth
def Above (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : V)
    (P : ((Fin 5 → ℂ) → Matrix (m ⊕ l) (m ⊕ l) ℂ) → (Fin 5 → ℂ) → Prop) : Prop :=
  ∀ (L : (Fin 5 → ℂ) →L[ℂ] V) (w : Fin 5 → ℂ), L w = z → P (fun x => H (L x)) w
section Descend
variable {p q : Type*}
variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) (hz : z ∈ U)
include h hs hz
end Descend
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm


