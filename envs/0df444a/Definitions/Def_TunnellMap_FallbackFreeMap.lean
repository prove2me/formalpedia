-- Prove2me | Definitions.Def_TunnellMap_FallbackFreeMap
-- name    : TunnellMap_FallbackFreeMap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T16:52:51.834966+00:00
-- url     : https://prove2.me/theorems/7ab4c130-d038-5592-96e5-9b5ab7cb8b29
-- title:
--   Fallback Free Map
-- statement:
--   Definitions and structural lemmas for Fallback Free Map, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean

import Definitions.Def_TunnellMap_ComputableFullMap
import Theorems.Thm_P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
import Theorems.Thm_P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
import Theorems.Thm_P2M_TunnellMap_reduceFrame_e__0c16366f5bcb
import Theorems.Thm_P2M_TunnellMap_reduceFrame_e__3405bfd3c173
import Theorems.Thm_TunnellMap_BlockGen_remainingTrace_initial
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
import Theorems.Thm_TunnellMap_RecordDA_aResidualOfTriple_residualTargetLift
import Theorems.Thm_TunnellMap_RecordDA_bResidualSignExec_eq
import Theorems.Thm_TunnellMap_RecordDA_canonicalBExec_eq
import Theorems.Thm_TunnellMap_RecordDA_framesExec_apply
import Theorems.Thm_TunnellMap_RecordDA_terminalRunExec_eq
import Theorems.Thm_TunnellMap_RecordDA_terminalRun_assigned
import Theorems.Thm_TunnellMap_RecordDA_terminalRun_held_sign
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_canonicalResidualMapOf_eq_residualEquivOfOrbitCard
import Theorems.Thm_TunnellMap_canonicalTargetLift_eq
import Theorems.Thm_TunnellMap_directMapExec_eq
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_etaPointExec_eq
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_isqrtK_eq
import Theorems.Thm_TunnellMap_keyLeExec_iff
import Theorems.Thm_TunnellMap_keyLtExec_iff
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_oddEquivOfBalance_apply_direct
import Theorems.Thm_TunnellMap_oddEquivOfBalance_apply_residual
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
namespace TunnellMap
variable {n : ℤ}
namespace RecordDA
def residualMapExecOpt (hnpos : 0 < n) (hsq : Squarefree n) (x : BResidual n) :
    Option (AResidual n) :=
  match (terminalRunExec (framesExec hsq)).assigned (canonicalBExec x) with
  | none => none
  | some r =>
      match aResidualOfTriple n r.target with
      | none => none
      | some F =>
          some (signActA hnpos
            (bResidualSignExec x * etaPointExec (canonicalBExec x) F) F)
section Agreement
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
theorem residualMapExecOpt_eq_some (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    residualMapExecOpt hnpos hsq x =
      some (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x) := by
  set M := residualOrbitMatching hnpos hcard with hM
  set q := (bResidualInvolution n).orbit x with hq
  set F := canonicalAResidualRepresentative hnpos (M q) with hF
  obtain ⟨r, hassign, hrt⟩ :=
    terminalRun_assigned hn hnpos (framesExec hsq) hcard q
  have hE : canonicalBExec x = canonicalBResidualRepresentative q :=
    canonicalBExec_eq x
  have hassign' : (terminalRunExec (framesExec hsq)).assigned
      (canonicalBExec x) = some r := by
    rw [terminalRunExec_eq, hE]; exact hassign
  have hdecode : aResidualOfTriple n r.target = some F := by
    rw [hrt]
    exact aResidualOfTriple_residualTargetLift F
  rw [residualMapExecOpt, hassign']
  dsimp only
  rw [hdecode]
  dsimp only
  rw [etaPointExec_eq, bResidualSignExec_eq, hE]
  rfl
@[macro_inline]
def residualMapExecTotal (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) : AResidual n :=
  (residualMapExecOpt hnpos hsq x).get (by
    rw [residualMapExecOpt_eq_some hn hnpos hsq hcard x]
    rfl)
end Agreement
def inverseByRerunExecOpt (hsq : Squarefree n) (y : AResidual n) :
    Option (BResidual n) :=
  ((terminalRunExec (framesExec hsq)).held
      (canonicalTargetLift (residualTargetLift y))).map
    fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1
section InverseAgreement
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
theorem inverseByRerunExecOpt_eq_some_value (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (y : AResidual n) :
    inverseByRerunExecOpt hsq y =
      some (signActB (targetLiftSign (residualTargetLift y) *
          canonicalEta hnpos
            ((residualOrbitMatching hnpos hcard).symm
              ((aResidualInvolution n hnpos).orbit y))
            ((aResidualInvolution n hnpos).orbit y))
        (canonicalBResidualRepresentative
          ((residualOrbitMatching hnpos hcard).symm
            ((aResidualInvolution n hnpos).orbit y)))) := by
  set M := residualOrbitMatching hnpos hcard with hM
  set o := (aResidualInvolution n hnpos).orbit y with ho
  obtain ⟨r, hheld, -, hsign⟩ :=
    terminalRun_held_sign hn hnpos (framesExec hsq) hcard (M.symm o)
  rw [Equiv.apply_symm_apply] at hheld hsign
  have hlift : canonicalTargetLift (residualTargetLift y) =
      BlockGen.orbitTargetLift hnpos o := canonicalTargetLift_eq hnpos y
  rw [inverseByRerunExecOpt, terminalRunExec_eq, hlift, hheld]
  simp only [Option.map_some]
  rw [hsign]
theorem inverseByRerunExecOpt_isSome (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (y : AResidual n) :
    (inverseByRerunExecOpt hsq y).isSome = true := by
  rw [inverseByRerunExecOpt_eq_some_value hn hnpos hsq hcard y]
  rfl
@[macro_inline]
def inverseByRerunExecTotal (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (y : AResidual n) : BResidual n :=
  (inverseByRerunExecOpt hsq y).get
    (inverseByRerunExecOpt_isSome hn hnpos hsq hcard y)
end InverseAgreement
end RecordDA
def oddMapExecOpt (hnpos : 0 < n) (hsq : Squarefree n) (q : BOddRep n) :
    Option (ARep n) :=
  if hd : SourceUsedTriple q.1 then
    directMapExec q
  else
    (RecordDA.residualMapExecOpt hnpos hsq
      ⟨q, fun hc => hd ((directSourceUsed_iff q).mp hc)⟩).map Subtype.val
section OddAgreement
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
theorem oddMapExecOpt_eq_some (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbal : Fintype.card (BOddRep n) = Fintype.card (ARep n)) (q : BOddRep n) :
    oddMapExecOpt hnpos hsq q = some (oddEquivOfBalance hn hnpos hbal q) := by
  by_cases hd : DirectSourceUsed q
  · have hd' : SourceUsedTriple q.1 := (directSourceUsed_iff q).mp hd
    rw [oddEquivOfBalance_apply_direct hn hnpos hbal q hd, oddMapExecOpt,
      dif_pos hd', directMapExec_eq hn q hd]
  · have hd' : ¬ SourceUsedTriple q.1 := fun hc =>
      hd ((directSourceUsed_iff q).mpr hc)
    rw [oddEquivOfBalance_apply_residual hn hnpos hbal q hd, oddMapExecOpt,
      dif_neg hd', RecordDA.residualMapExecOpt_eq_some hn hnpos hsq
        (residual_orbit_card_eq hn hnpos hbal)]
    rw [Option.map_some]
    congr 1
    exact congrArg Subtype.val
      (canonicalResidualMapOf_eq_residualEquivOfOrbitCard hnpos
        (residual_orbit_card_eq hn hnpos hbal) _)
end OddAgreement
def paperTunnellMapExecOpt (hnpos : 0 < n) (hsq : Squarefree n) (p : BRep n) :
    Option (ARep n) :=
  if h : p.1.z % 2 = 0 then
    some (evenEquiv n (evenRepToParam ⟨p, Int.even_iff.mpr h⟩))
  else
    oddMapExecOpt hnpos hsq ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩
section FullAgreement
variable [Fintype (BRep n)] [Fintype (ARep n)]
theorem paperTunnellMapExecOpt_eq_some (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n))
    (p : BRep n) :
    paperTunnellMapExecOpt hnpos hsq p =
      some (paperTunnellMap hn hnpos hbalance p) := by
  classical
  show _ = some (conditionalTunnellMap (paperOddEquiv hn hnpos hbalance)
    ((Equiv.sumCongr (evenRepParamEquiv n)
        ((Equiv.subtypeEquivRight (fun p : BRep n => Int.not_even_iff_odd)).trans
          (bOddSubtypeEquiv n)))
      ((Equiv.sumCompl (fun p : BRep n => Even p.1.z)).symm p)))
  by_cases h : p.1.z % 2 = 0
  · have he : (fun p : BRep n => Even p.1.z) p := Int.even_iff.mpr h
    rw [Equiv.sumCompl_symm_apply_of_pos (p := fun p : BRep n => Even p.1.z) he,
      paperTunnellMapExecOpt, dif_pos h]
    rfl
  · have he : ¬ (fun p : BRep n => Even p.1.z) p := fun hc => h (Int.even_iff.mp hc)
    rw [Equiv.sumCompl_symm_apply_of_neg (p := fun p : BRep n => Even p.1.z) he,
      paperTunnellMapExecOpt, dif_neg h]
    show oddMapExecOpt hnpos hsq _ =
      some (paperOddEquiv hn hnpos hbalance ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩)
    exact oddMapExecOpt_eq_some hn hnpos hsq (odd_card_eq_of_full_balance hbalance) _
end FullAgreement
theorem fintype_balance_of_nat_card
    (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    Fintype.card (BRep n) = 2 * Fintype.card (ARep n) := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hbal
theorem paperTunnellMapExecOpt_isSome (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n)) (p : BRep n) :
    (paperTunnellMapExecOpt hnpos hsq p).isSome = true := by
  rw [paperTunnellMapExecOpt_eq_some hn hnpos hsq
    (fintype_balance_of_nat_card hbal) p]
  rfl
def paperTunnellMapTotal (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n)) (p : BRep n) : ARep n :=
  (paperTunnellMapExecOpt hnpos hsq p).get
    (paperTunnellMapExecOpt_isSome hn hnpos hsq hbal p)
end TunnellMap


