-- Prove2me | Definitions.Def_TunnellMap_Solution
-- name    : TunnellMap_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T16:57:27.46981+00:00
-- url     : https://prove2.me/theorems/9afe9b88-2900-4a50-a70a-cff0498c878f
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean

import Definitions.Def_TunnellMap_BranchSpec
import Theorems.Thm_P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
import Theorems.Thm_P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
import Theorems.Thm_P2M_TunnellMap_reduceFrame_e__0c16366f5bcb
import Theorems.Thm_P2M_TunnellMap_reduceFrame_e__3405bfd3c173
import Theorems.Thm_TunnellMap_BlockGen_remainingTrace_initial
import Theorems.Thm_TunnellMap_FreeInvolution_orbit_canonicalRepresentative
import Theorems.Thm_TunnellMap_FreeInvolution_orbit_signAct
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_neg_one
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_one
import Theorems.Thm_TunnellMap_FreeInvolution_signOf_canonicalRepresentative
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_apply
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
import Theorems.Thm_TunnellMap_OrderedGenerator_mem_orderedIndexList
import Theorems.Thm_TunnellMap_RecordDA_framesExec_apply
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_directTargetUsed_iff
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_isqrtK_eq
import Theorems.Thm_TunnellMap_keyLeExec_iff
import Theorems.Thm_TunnellMap_keyLtExec_iff
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_orbit_canonicalAResidualRepresentative
import Theorems.Thm_TunnellMap_orbit_canonicalBResidualRepresentative
import Theorems.Thm_TunnellMap_orbit_signActA
import Theorems.Thm_TunnellMap_orbit_signActB
import Theorems.Thm_TunnellMap_orthogonalFrameExec_z
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_primitiveDirection_idem
import Theorems.Thm_TunnellMap_primitiveDirection_negTriple
import Theorems.Thm_TunnellMap_primitiveDirection_two_vsmul
import Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
import Theorems.Thm_TunnellMap_primitivePartTriple_two_vsmul
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_qForm_vsmul
import Theorems.Thm_TunnellMap_reduceFrame_z
import Theorems.Thm_TunnellMap_representativeEdgeKey_eq_orbitEdgeKey
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
import Theorems.Thm_TunnellMap_residualSourceLift_neg
import Theorems.Thm_TunnellMap_residualTargetLift_neg
import Theorems.Thm_TunnellMap_residual_orbit_card_eq
import Theorems.Thm_TunnellMap_signActA_neg_one
import Theorems.Thm_TunnellMap_signActA_one
import Theorems.Thm_TunnellMap_signActB_neg_one
import Theorems.Thm_TunnellMap_signActB_one
import Theorems.Thm_TunnellMap_tripleContent_negTriple
import Theorems.Thm_TunnellMap_tripleContent_orientDirection
import Theorems.Thm_TunnellMap_tripleContent_primitiveDirection
import Theorems.Thm_TunnellMap_tripleContent_primitivePartTriple
import Theorems.Thm_TunnellMap_tripleLexLtExec_iff
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
attribute [local simp] P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
attribute [local simp] P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
attribute [local simp] P2M_TunnellMap_reduceFrame_e__0c16366f5bcb
attribute [local simp] P2M_TunnellMap_reduceFrame_e__3405bfd3c173
attribute [local simp] TunnellMap.BlockGen.remainingTrace_initial
attribute [local simp] TunnellMap.FreeInvolution.orbit_signAct
attribute [local simp] TunnellMap.FreeInvolution.signAct_neg_one
attribute [local simp] TunnellMap.FreeInvolution.signAct_one
attribute [local simp] TunnellMap.FreeInvolution.signOf_canonicalRepresentative
attribute [local simp] TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
attribute [local simp] TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList
attribute [local simp] TunnellMap.OrderedGenerator.mem_orderedIndexList
attribute [local simp] TunnellMap.RecordDA.framesExec_apply
attribute [local simp] TunnellMap.assemble_inl
attribute [local simp] TunnellMap.assemble_inr
attribute [local simp] TunnellMap.directionKey_negTriple
attribute [local simp] TunnellMap.directionKey_primitiveDirection
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.isqrtK_eq
attribute [local simp] TunnellMap.keyLeExec_iff
attribute [local simp] TunnellMap.keyLtExec_iff
attribute [local simp] TunnellMap.minusVector_neg_source
attribute [local simp] TunnellMap.minusVector_neg_target
attribute [local simp] TunnellMap.orbit_canonicalAResidualRepresentative
attribute [local simp] TunnellMap.orbit_canonicalBResidualRepresentative
attribute [local simp] TunnellMap.orbit_signActA
attribute [local simp] TunnellMap.orbit_signActB
attribute [local simp] TunnellMap.orthogonalFrameExec_z
attribute [local simp] TunnellMap.plusVector_neg_source
attribute [local simp] TunnellMap.plusVector_neg_target
attribute [local simp] TunnellMap.polynomialTriple_neg
attribute [local simp] TunnellMap.polynomialTriple_triplePolynomial
attribute [local simp] TunnellMap.primitiveDirection_idem
attribute [local simp] TunnellMap.primitiveDirection_negTriple
attribute [local simp] TunnellMap.primitiveDirection_two_vsmul
attribute [local simp] TunnellMap.primitivePartTriple_negTriple
attribute [local simp] TunnellMap.primitivePartTriple_two_vsmul
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau
attribute [local simp] TunnellMap.qForm_vsmul
attribute [local simp] TunnellMap.reduceFrame_z
attribute [local simp] TunnellMap.representativeEdgeKey_neg_source
attribute [local simp] TunnellMap.representativeEdgeKey_neg_target
attribute [local simp] TunnellMap.residualSourceLift_neg
attribute [local simp] TunnellMap.residualTargetLift_neg
attribute [local simp] TunnellMap.signActA_neg_one
attribute [local simp] TunnellMap.signActA_one
attribute [local simp] TunnellMap.signActB_neg_one
attribute [local simp] TunnellMap.signActB_one
attribute [local simp] TunnellMap.tripleContent_negTriple
attribute [local simp] TunnellMap.tripleContent_orientDirection
attribute [local simp] TunnellMap.tripleContent_primitiveDirection
attribute [local simp] TunnellMap.tripleContent_primitivePartTriple
attribute [local simp] TunnellMap.tripleLexLtExec_iff
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul


set_option autoImplicit true
namespace TunnellChallenge
set_option maxHeartbeats 1000000
def BRep (n : ℤ) : Type :=
  {p : ℤ × ℤ × ℤ // 2 * p.1 ^ 2 + p.2.1 ^ 2 + 8 * p.2.2 ^ 2 = n}
def ARep (n : ℤ) : Type :=
  {p : ℤ × ℤ × ℤ // 2 * p.1 ^ 2 + p.2.1 ^ 2 + 32 * p.2.2 ^ 2 = n}
def DirectTargetUsed {n : ℤ} (p : ARep n) : Prop :=
  (∃ q : ℤ, Odd q ∧ p.1.1 + 4 * p.1.2.2 - p.1.2.1 = 4 * q) ∨
    (∃ q : ℤ, Odd q ∧ p.1.1 - 4 * p.1.2.2 + p.1.2.1 = 4 * q) ∨
    (∃ q : ℤ, Odd q ∧ p.1.1 = 2 * q)
def AResidual (n : ℤ) : Type := {p : ARep n // ¬ DirectTargetUsed p}
def BOddRep (n : ℤ) : Type := {p : BRep n // Odd p.1.2.2}
def DirectSourceUsed {n : ℤ} (p : BOddRep n) : Prop :=
  (∃ q : ℤ, p.1.1.1 + 2 * p.1.1.2.2 + p.1.1.2.1 = 8 * q) ∨
    (∃ q : ℤ, p.1.1.2.1 - p.1.1.1 + 2 * p.1.1.2.2 = 8 * q) ∨
    (∃ q : ℤ, p.1.1.1 = 4 * q)
def BResidual (n : ℤ) : Type := {p : BOddRep n // ¬ DirectSourceUsed p}
def negBResidual {n : ℤ} (p : BResidual n) : BResidual n := by
  refine ⟨⟨⟨(-p.1.1.1.1, -p.1.1.1.2.1, -p.1.1.1.2.2), ?_⟩, p.1.2.neg⟩, ?_⟩
  · simpa using p.1.1.2
  · intro h
    apply p.2
    rcases h with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
    · exact Or.inl ⟨-q, by dsimp at hq ⊢; linarith⟩
    · exact Or.inr (Or.inl ⟨-q, by dsimp at hq ⊢; linarith⟩)
    · exact Or.inr (Or.inr ⟨-q, by dsimp at hq ⊢; linarith⟩)
def negAResidual {n : ℤ} (p : AResidual n) : AResidual n := by
  refine ⟨⟨(-p.1.1.1, -p.1.1.2.1, -p.1.1.2.2), ?_⟩, ?_⟩
  · simpa using p.1.2
  · intro h
    apply p.2
    rcases h with ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩
    · exact Or.inl ⟨-q, hq.neg, by dsimp at heq ⊢; linarith⟩
    · exact Or.inr (Or.inl ⟨-q, hq.neg, by dsimp at heq ⊢; linarith⟩)
    · exact Or.inr (Or.inr ⟨-q, hq.neg, by dsimp at heq ⊢; linarith⟩)
abbrev Triple := ℤ × ℤ × ℤ
abbrev TripleLexKey := ℤ ×ₗ (ℤ ×ₗ ℤ)
abbrev DirectionKey := ℤ ×ₗ (ℤ ×ₗ (ℤ ×ₗ ℤ))
def tripleLexKey (v : Triple) : TripleLexKey :=
  toLex (v.1, toLex (v.2.1, v.2.2))
def CanonicalB (n : ℤ) : Type :=
  {p : BResidual n // tripleLexKey p.1.1.1 < tripleLexKey (negBResidual p).1.1.1}
def CanonicalA (n : ℤ) : Type :=
  {p : AResidual n // tripleLexKey p.1.1 < tripleLexKey (negAResidual p).1.1}
open Polynomial
noncomputable def triplePolynomial (v : Triple) : ℤ[X] :=
  C v.1 + C v.2.1 * X + C v.2.2 * X ^ 2
def polynomialTriple (f : ℤ[X]) : Triple :=
  (f.coeff 0, f.coeff 1, f.coeff 2)
def FirstNonzeroPositive (v : Triple) : Prop :=
  0 < v.1 ∨ (v.1 = 0 ∧ 0 < v.2.1) ∨
    (v.1 = 0 ∧ v.2.1 = 0 ∧ 0 < v.2.2)
instance firstNonzeroPositiveDecidable (v : Triple) :
    Decidable (FirstNonzeroPositive v) := by
  unfold FirstNonzeroPositive
  infer_instance
def negTriple (v : Triple) : Triple := (-v.1, -v.2.1, -v.2.2)
def orientDirection (v : Triple) : Triple :=
  if FirstNonzeroPositive v then v else negTriple v
noncomputable def primitiveDirection (v : Triple) : Triple :=
  orientDirection (polynomialTriple (triplePolynomial v).primPart)
def qForm (v : Triple) : ℤ := 2 * v.1 ^ 2 + v.2.1 ^ 2 + 2 * v.2.2 ^ 2
noncomputable def directionKey (v : Triple) : DirectionKey :=
  let d := primitiveDirection v
  toLex (qForm d, toLex (d.1, toLex (d.2.1, d.2.2)))
def residualSourceLift {n : ℤ} (s : BResidual n) : Triple :=
  (s.1.1.1.1, s.1.1.1.2.1, 2 * s.1.1.1.2.2)
def residualTargetLift {n : ℤ} (t : AResidual n) : Triple :=
  (t.1.1.1, t.1.1.2.1, 4 * t.1.1.2.2)
def plusVector {n : ℤ} (s : BResidual n) (t : AResidual n) : Triple :=
  let E := residualSourceLift s
  let F := residualTargetLift t
  (E.1 + F.1, E.2.1 + F.2.1, E.2.2 + F.2.2)
def minusVector {n : ℤ} (s : BResidual n) (t : AResidual n) : Triple :=
  let E := residualSourceLift s
  let F := residualTargetLift t
  (E.1 - F.1, E.2.1 - F.2.1, E.2.2 - F.2.2)
noncomputable def residualEdgeKey {n : ℤ} (s : BResidual n) (t : AResidual n) :
    DirectionKey :=
  min (directionKey (plusVector s t)) (directionKey (minusVector s t))
def StableResidualMatching {n : ℤ} (M : CanonicalB n ≃ CanonicalA n) : Prop :=
  ∀ s t, ¬ (residualEdgeKey s.1 t.1 < residualEdgeKey s.1 (M s).1 ∧
    residualEdgeKey s.1 t.1 < residualEdgeKey (M.symm t).1 t.1)
noncomputable def preferredTarget {n : ℤ} (s : BResidual n)
    (t : AResidual n) : AResidual n :=
  if directionKey (plusVector s t) < directionKey (minusVector s t) then
    t
  else
    negAResidual t
def bEquiv (n : ℤ) : BRep n ≃ TunnellMap.BRep n where
  toFun p := ⟨⟨p.1.1, p.1.2.1, p.1.2.2⟩, p.2⟩
  invFun q := ⟨(q.1.x, q.1.y, q.1.z), q.2⟩
  left_inv := by rintro ⟨⟨a, b, c⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, h⟩; rfl
def aEquiv (n : ℤ) : ARep n ≃ TunnellMap.ARep n where
  toFun p := ⟨⟨p.1.1, p.1.2.1, p.1.2.2⟩, p.2⟩
  invFun q := ⟨(q.1.x, q.1.y, q.1.z), q.2⟩
  left_inv := by rintro ⟨⟨a, b, c⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, h⟩; rfl
theorem directTargetUsed_iff {n : ℤ} (p : ARep n) :
    DirectTargetUsed p ↔ TunnellMap.DirectTargetUsed (aEquiv n p) :=
  Iff.rfl
def arEquiv (n : ℤ) : AResidual n ≃ TunnellMap.AResidual n :=
  (aEquiv n).subtypeEquiv fun p => not_congr (directTargetUsed_iff p)
theorem card_bRep (n : ℤ) : Nat.card (BRep n) = Nat.card (TunnellMap.BRep n) :=
  Nat.card_congr (bEquiv n)
theorem card_aRep (n : ℤ) : Nat.card (ARep n) = Nat.card (TunnellMap.ARep n) :=
  Nat.card_congr (aEquiv n)
theorem balance_transport {n : ℤ}
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    Nat.card (TunnellMap.BRep n) = 2 * Nat.card (TunnellMap.ARep n) := by
  rw [← card_bRep n, ← card_aRep n]; exact hbalance
def boEquiv (n : ℤ) : BOddRep n ≃ TunnellMap.BOddRep n where
  toFun p := ⟨⟨p.1.1.1, p.1.1.2.1, p.1.1.2.2⟩, p.1.2, p.2⟩
  invFun q := ⟨⟨(q.1.x, q.1.y, q.1.z), q.2.1⟩, q.2.2⟩
  left_inv := by rintro ⟨⟨⟨a, b, c⟩, h⟩, ho⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, h, ho⟩; rfl
theorem directSourceUsed_iff {n : ℤ} (p : BOddRep n) :
    DirectSourceUsed p ↔ TunnellMap.DirectSourceUsed (boEquiv n p) :=
  Iff.rfl
def brEquiv (n : ℤ) : BResidual n ≃ TunnellMap.BResidual n :=
  (boEquiv n).subtypeEquiv fun p => not_congr (directSourceUsed_iff p)
@[simp] theorem brEquiv_neg {n : ℤ} (p : BResidual n) :
    brEquiv n (negBResidual p) = TunnellMap.negBResidual (brEquiv n p) := rfl
@[simp] theorem arEquiv_neg {n : ℤ} (p : AResidual n) :
    arEquiv n (negAResidual p) = TunnellMap.negAResidual (arEquiv n p) := rfl
def coreTriple (v : Triple) : TunnellMap.Triple := ⟨v.1, v.2.1, v.2.2⟩
@[simp] theorem tripleLexKey_brEquiv {n : ℤ} (s : BResidual n) :
    tripleLexKey s.1.1.1 = TunnellMap.bResidualLexKey (brEquiv n s) := rfl
@[simp] theorem tripleLexKey_arEquiv {n : ℤ} (t : AResidual n) :
    tripleLexKey t.1.1 = TunnellMap.aResidualLexKey (arEquiv n t) := rfl
theorem canonicalBRepresentative_lt_neg {n : ℤ}
    (q : (TunnellMap.bResidualInvolution n).Orbit) :
    TunnellMap.bResidualLexKey (TunnellMap.canonicalBResidualRepresentative q) <
      TunnellMap.bResidualLexKey
        (TunnellMap.negBResidual (TunnellMap.canonicalBResidualRepresentative q)) := by
  induction q using Quotient.inductionOn with
  | _ x =>
      change TunnellMap.bResidualLexKey
          ((TunnellMap.bResidualInvolution n).canonicalPoint
            TunnellMap.bResidualLexKey x) <
        TunnellMap.bResidualLexKey
          (TunnellMap.negBResidual
            ((TunnellMap.bResidualInvolution n).canonicalPoint
              TunnellMap.bResidualLexKey x))
      have hne : TunnellMap.bResidualLexKey x ≠
          TunnellMap.bResidualLexKey (TunnellMap.negBResidual x) := by
        intro h
        exact (TunnellMap.bResidualInvolution n).no_fixed x
          (TunnellMap.bResidualLexKey_injective h).symm
      change TunnellMap.bResidualLexKey
          (if TunnellMap.bResidualLexKey x <
              TunnellMap.bResidualLexKey (TunnellMap.negBResidual x) then x
            else TunnellMap.negBResidual x) <
        TunnellMap.bResidualLexKey
          (TunnellMap.negBResidual
            (if TunnellMap.bResidualLexKey x <
                TunnellMap.bResidualLexKey (TunnellMap.negBResidual x) then x
              else TunnellMap.negBResidual x))
      by_cases hlt : TunnellMap.bResidualLexKey x <
          TunnellMap.bResidualLexKey (TunnellMap.negBResidual x)
      · simp [hlt]
      · have hrev : TunnellMap.bResidualLexKey (TunnellMap.negBResidual x) <
            TunnellMap.bResidualLexKey x :=
          lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
        simp [hlt, hrev]
theorem canonicalARepresentative_lt_neg {n : ℤ} (hpos : 0 < n)
    (q : (TunnellMap.aResidualInvolution n hpos).Orbit) :
    TunnellMap.aResidualLexKey
        (TunnellMap.canonicalAResidualRepresentative hpos q) <
      TunnellMap.aResidualLexKey
        (TunnellMap.negAResidual
          (TunnellMap.canonicalAResidualRepresentative hpos q)) := by
  induction q using Quotient.inductionOn with
  | _ x =>
      change TunnellMap.aResidualLexKey
          ((TunnellMap.aResidualInvolution n hpos).canonicalPoint
            TunnellMap.aResidualLexKey x) <
        TunnellMap.aResidualLexKey
          (TunnellMap.negAResidual
            ((TunnellMap.aResidualInvolution n hpos).canonicalPoint
              TunnellMap.aResidualLexKey x))
      have hne : TunnellMap.aResidualLexKey x ≠
          TunnellMap.aResidualLexKey (TunnellMap.negAResidual x) := by
        intro h
        exact (TunnellMap.aResidualInvolution n hpos).no_fixed x
          (TunnellMap.aResidualLexKey_injective h).symm
      change TunnellMap.aResidualLexKey
          (if TunnellMap.aResidualLexKey x <
              TunnellMap.aResidualLexKey (TunnellMap.negAResidual x) then x
            else TunnellMap.negAResidual x) <
        TunnellMap.aResidualLexKey
          (TunnellMap.negAResidual
            (if TunnellMap.aResidualLexKey x <
                TunnellMap.aResidualLexKey (TunnellMap.negAResidual x) then x
              else TunnellMap.negAResidual x))
      by_cases hlt : TunnellMap.aResidualLexKey x <
          TunnellMap.aResidualLexKey (TunnellMap.negAResidual x)
      · simp [hlt]
      · have hrev : TunnellMap.aResidualLexKey (TunnellMap.negAResidual x) <
            TunnellMap.aResidualLexKey x :=
          lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
        simp [hlt, hrev]
noncomputable def canonicalBOfOrbit {n : ℤ}
    (q : (TunnellMap.bResidualInvolution n).Orbit) : CanonicalB n :=
  ⟨(brEquiv n).symm (TunnellMap.canonicalBResidualRepresentative q), by
    simpa using canonicalBRepresentative_lt_neg q⟩
noncomputable def canonicalAOfOrbit {n : ℤ} (hpos : 0 < n)
    (q : (TunnellMap.aResidualInvolution n hpos).Orbit) : CanonicalA n :=
  ⟨(arEquiv n).symm (TunnellMap.canonicalAResidualRepresentative hpos q), by
    simpa using canonicalARepresentative_lt_neg hpos q⟩
noncomputable def canonicalBOrbitEquiv (n : ℤ) :
    CanonicalB n ≃ (TunnellMap.bResidualInvolution n).Orbit where
  toFun s := (TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1)
  invFun := canonicalBOfOrbit
  left_inv := by
    intro s
    apply Subtype.ext
    apply (brEquiv n).injective
    change brEquiv n ((brEquiv n).symm
        (TunnellMap.canonicalBResidualRepresentative
          ((TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1)))) = brEquiv n s.1
    rw [Equiv.apply_symm_apply]
    change TunnellMap.canonicalBResidualRepresentative
        ((TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1)) = brEquiv n s.1
    change (TunnellMap.bResidualInvolution n).canonicalPoint
        TunnellMap.bResidualLexKey (brEquiv n s.1) = brEquiv n s.1
    have hslt : TunnellMap.bResidualLexKey (brEquiv n s.1) <
        TunnellMap.bResidualLexKey
          ((TunnellMap.bResidualInvolution n).neg (brEquiv n s.1)) := by
      change tripleLexKey s.1.1.1.1 < tripleLexKey (negBResidual s.1).1.1.1
      exact s.2
    rw [TunnellMap.FreeInvolution.canonicalPoint, if_pos hslt]
  right_inv := by
    intro q
    change (TunnellMap.bResidualInvolution n).orbit
      (TunnellMap.canonicalBResidualRepresentative q) = q
    exact (TunnellMap.bResidualInvolution n).orbit_canonicalRepresentative
      TunnellMap.bResidualLexKey TunnellMap.bResidualLexKey_injective q
noncomputable def canonicalAOrbitEquiv {n : ℤ} (hpos : 0 < n) :
    CanonicalA n ≃ (TunnellMap.aResidualInvolution n hpos).Orbit where
  toFun t := (TunnellMap.aResidualInvolution n hpos).orbit (arEquiv n t.1)
  invFun := canonicalAOfOrbit hpos
  left_inv := by
    intro t
    apply Subtype.ext
    apply (arEquiv n).injective
    change arEquiv n ((arEquiv n).symm
        (TunnellMap.canonicalAResidualRepresentative hpos
          ((TunnellMap.aResidualInvolution n hpos).orbit (arEquiv n t.1)))) = arEquiv n t.1
    rw [Equiv.apply_symm_apply]
    change TunnellMap.canonicalAResidualRepresentative hpos
        ((TunnellMap.aResidualInvolution n hpos).orbit (arEquiv n t.1)) = arEquiv n t.1
    change (TunnellMap.aResidualInvolution n hpos).canonicalPoint
        TunnellMap.aResidualLexKey (arEquiv n t.1) = arEquiv n t.1
    have htlt : TunnellMap.aResidualLexKey (arEquiv n t.1) <
        TunnellMap.aResidualLexKey
          ((TunnellMap.aResidualInvolution n hpos).neg (arEquiv n t.1)) := by
      change tripleLexKey t.1.1.1 < tripleLexKey (negAResidual t.1).1.1
      exact t.2
    rw [TunnellMap.FreeInvolution.canonicalPoint, if_pos htlt]
  right_inv := by
    intro q
    change (TunnellMap.aResidualInvolution n hpos).orbit
      (TunnellMap.canonicalAResidualRepresentative hpos q) = q
    exact (TunnellMap.aResidualInvolution n hpos).orbit_canonicalRepresentative
      TunnellMap.aResidualLexKey TunnellMap.aResidualLexKey_injective q
theorem primitiveDirection_bridge (v : Triple) :
    coreTriple (primitiveDirection v) =
      TunnellMap.primitiveDirection (coreTriple v) := by
  let w := polynomialTriple (triplePolynomial v).primPart
  change coreTriple (orientDirection w) = TunnellMap.orientDirection (coreTriple w)
  by_cases h : FirstNonzeroPositive w
  · have hc : TunnellMap.FirstNonzeroPositive (coreTriple w) := h
    simp only [orientDirection, TunnellMap.orientDirection, if_pos h, if_pos hc]
  · have hc : ¬ TunnellMap.FirstNonzeroPositive (coreTriple w) := h
    simp only [orientDirection, TunnellMap.orientDirection, if_neg h, if_neg hc]
    rfl
theorem directionKey_bridge (v : Triple) :
    directionKey v =
      TunnellMap.DirectionKey.toLexKey (TunnellMap.directionKey (coreTriple v)) := by
  unfold directionKey TunnellMap.directionKey TunnellMap.DirectionKey.toLexKey
  rw [← primitiveDirection_bridge]
  rfl
@[simp] theorem plusVector_bridge {n : ℤ} (s : BResidual n) (t : AResidual n) :
    coreTriple (plusVector s t) =
      TunnellMap.plusVector (brEquiv n s) (arEquiv n t) := rfl
@[simp] theorem minusVector_bridge {n : ℤ} (s : BResidual n) (t : AResidual n) :
    coreTriple (minusVector s t) =
      TunnellMap.minusVector (brEquiv n s) (arEquiv n t) := rfl
theorem residualEdgeKey_bridge {n : ℤ} (s : BResidual n) (t : AResidual n) :
    residualEdgeKey s t =
      TunnellMap.DirectionKey.toLexKey
        (TunnellMap.representativeEdgeKey (brEquiv n s) (arEquiv n t)) := by
  rw [residualEdgeKey, TunnellMap.representativeEdgeKey, directionKey_bridge,
    directionKey_bridge, plusVector_bridge, minusVector_bridge]
  exact (show Monotone TunnellMap.DirectionKey.toLexKey from fun _ _ h => h).map_min.symm
theorem residualEdgeKey_orbit_bridge {n : ℤ} (hpos : 0 < n)
    (s : BResidual n) (t : AResidual n) :
    residualEdgeKey s t = TunnellMap.DirectionKey.toLexKey
      (TunnellMap.orbitEdgeKey hpos
        ((TunnellMap.bResidualInvolution n).orbit (brEquiv n s))
        ((TunnellMap.aResidualInvolution n hpos).orbit (arEquiv n t))) := by
  rw [residualEdgeKey_bridge,
    TunnellMap.representativeEdgeKey_eq_orbitEdgeKey]
theorem coreResidualOrbitCardEq {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    Fintype.card (TunnellMap.bResidualInvolution n).Orbit =
      Fintype.card (TunnellMap.aResidualInvolution n hpos).Orbit :=
  TunnellMap.residual_orbit_card_eq hodd hpos
    (TunnellMap.odd_card_eq_of_full_balance
      (TunnellMap.fintype_balance_of_nat_card (balance_transport hbalance)))
noncomputable def registeredResidualMatching {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    CanonicalB n ≃ CanonicalA n :=
  (canonicalBOrbitEquiv n).trans
    ((TunnellMap.residualOrbitMatching hpos
      (coreResidualOrbitCardEq hodd hpos hbalance)).trans
        (canonicalAOrbitEquiv hpos).symm)
noncomputable def registeredResidualRanking {n : ℤ} (hpos : 0 < n) :
    TunnellMap.GloballyRanked DirectionKey (CanonicalB n) (CanonicalA n) where
  rank := fun s t => residualEdgeKey s.1 t.1
  source_injective := by
    intro s t₁ t₂ hkey
    apply (canonicalAOrbitEquiv hpos).injective
    apply (TunnellMap.residualOrbitRanking hpos).source_injective
    apply TunnellMap.DirectionKey.toLexKey_injective
    exact (residualEdgeKey_orbit_bridge hpos s.1 t₁.1).symm.trans
      (hkey.trans (residualEdgeKey_orbit_bridge hpos s.1 t₂.1))
  target_injective := by
    intro t s₁ s₂ hkey
    apply (canonicalBOrbitEquiv n).injective
    apply (TunnellMap.residualOrbitRanking hpos).target_injective
    apply TunnellMap.DirectionKey.toLexKey_injective
    exact (residualEdgeKey_orbit_bridge hpos s₁.1 t.1).symm.trans
      (hkey.trans (residualEdgeKey_orbit_bridge hpos s₂.1 t.1))
def tunnellMap {n : ℤ} (hodd : Odd n) (hpos : 0 < n) (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    BRep n → ARep n := fun p =>
  (aEquiv n).symm
    (TunnellMap.paperTunnellMapTotal hodd hpos hsq (balance_transport hbalance)
      (bEquiv n p))
def tunnellResidualMap {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    BResidual n → AResidual n := fun s =>
  (arEquiv n).symm
    (TunnellMap.RecordDA.residualMapExecTotal hodd hpos hsq
      (coreResidualOrbitCardEq hodd hpos hbalance) (brEquiv n s))
def tunnellResidualInverse {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    AResidual n → BResidual n := fun t =>
  (brEquiv n).symm
    (TunnellMap.RecordDA.inverseByRerunExecTotal hodd hpos hsq
      (coreResidualOrbitCardEq hodd hpos hbalance) (arEquiv n t))
end TunnellChallenge


