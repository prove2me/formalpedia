-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaOriginalInputs
-- name    : Submission_Weighted_Global_TernaryArenaOriginalInputs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:20:08.986704+00:00
-- url     : https://prove2.me/theorems/34402dfa-0581-480b-8830-68b8b2be7c8f
-- title:
--   Ternary Arena Original Inputs
-- statement:
--   Definitions and structural lemmas for Ternary Arena Original Inputs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaOriginalInputs.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedData
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPrefixInputs
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData TernaryExtensionEncoding
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
structure Originals (I : Input) (A : Inputs) (seedCount featureBound tagBound positionCap : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seeds : ℕ→E×E)
    (L R O : ℕ→ℕ→ℤ) (initial : ℕ→ℤ) : Prop where
  BEnd : A.Bmatrix+I.nB*(A.J+2)≤I.free
  CEnd : A.Cmatrix+I.nC*(A.J+2)≤I.free
  OEnd : A.Omatrix+I.requesterCount*(A.J+2)≤I.free
  menuEnd : A.menu+seedCount*(A.J+2)≤I.free
  positionEnd : A.positions+I.requesterCount≤I.free
  leftEnd : A.leftTagged+I.nB*(A.J+2)≤I.free
  rightEnd : A.rightTagged+I.nC*(A.J+2)≤I.free
  feature : featureBound<p
  BBound : ∀i<I.nB,∀t<A.J+2, |L i t|≤(featureBound : ℤ)
  CBound : ∀i<I.nC,∀t<A.J+2, |R i t|≤(featureBound : ℤ)
  OBound : ∀i<I.requesterCount,∀t<A.J+2, |O i t|≤(featureBound : ℤ)
  leftBound : ∀i<I.nB,∀t<A.J+2, |L i t|≤(tagBound : ℤ)
  rightBound : ∀i<I.nC,∀t<A.J+2, |R i t|≤(tagBound : ℤ)
  BRead : ∀i<I.nB,∀k<A.J+2, initial (A.Bmatrix+i*(A.J+2)+k)=
    physical (J := A.J) (fun i t => L i t.val) i k
  CRead : ∀i<I.nC,∀k<A.J+2, initial (A.Cmatrix+i*(A.J+2)+k)=
    physical (J := A.J) (fun i t => R i t.val) i k
  ORead : ∀i<I.requesterCount,∀k<A.J+2, initial (A.Omatrix+i*(A.J+2)+k)=
    physical (J := A.J) (fun i t => O i t.val) i k
  menuRead : ∀ordinal<seedCount,∀(k : ℕ) (hk : k<A.J+2),
    initial (A.menu+ordinal*(A.J+2)+k)=
      (TernaryOriginalRowMenu.seedRow (A.J+2) ℓ (seeds ordinal) (digitOrder A.J ⟨k,hk⟩)).val
  positionRead : ∀i<I.requesterCount,initial (A.positions+i)=(I.positions i : ℤ)
  positionBound : ∀i<I.requesterCount,I.positions i≤positionCap
  leftRead : ∀i<I.nB,∀t<A.J+2,
    initial (A.leftTagged+i*(A.J+2)+TernarySignedLayout.offset A.J t)=L i t
  rightRead : ∀i<I.nC,∀t<A.J+2,
    initial (A.rightTagged+i*(A.J+2)+TernarySignedLayout.offset A.J t)=R i t
end ThreeSum.WeightedGlobalArenaPrefixInputs


