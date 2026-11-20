-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:31:19.682184+00:00
-- url     : https://prove2.me/theorems/74e68e10-6a91-4f66-9caf-fca35d1a1f83
-- title:
--   Boundary Tail Invariance
-- statement:
--   Definitions and structural lemmas for Boundary Tail Invariance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta0
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_binary_add_eq_zero_iff
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_indexedDecoderData_selected_rx
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_step
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_step_rz
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_differential0_eq
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_raw_boundary_iff
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_delta0_coordinates
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_lowerError_coordinates
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_BDL26CochainFamily_coboundary1_comp_coboundary0
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26BoundaryTailInvariance
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26TannerLocalRegularity
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26TransposedStoppedDecoder PauliSymplectic
open scoped Classical
abbrev W (S : OddScale) (n : Nat) (a : LevelIndex n) :=
  (SuffixData S n).family.Cochain1 a
abbrev V (S : OddScale) (n : Nat) (a : LevelIndex n) :=
  (SuffixData S n).family.Cochain0 a
theorem word_eq_of_add_zero {I : Type} (u v : Word BDL26Field I)
    (h : u+v=0) : u=v := by
  funext i
  exact (binary_add_eq_zero_iff _ _).mp (congrFun h i)
theorem inputs_eq (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (a : LevelIndex n) (u : LocalizedWord S n sigma tau a) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=u.word) :
    actualInputs S n sigma a=actualInputs S n tau a := by
  have hz : (SuffixData S n).family.coboundary1 a u.word=0 := by
    rw [← hp]
    exact LinearMap.congr_fun ((SuffixData S n).family.coboundary1_comp_coboundary0 a) p
  exact Subtype.ext (word_eq_of_add_zero _ _ (u.syndrome.symm.trans hz))
theorem output_eq (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) (p : V S n i.succ)
    (hp : (SuffixData S n).family.coboundary0 i.succ p=u.word) :
    actualOutput S n sigma i=actualOutput S n tau i := by
  unfold actualOutput
  rw [inputs_eq S n sigma tau i.succ u p hp]
theorem step_boundary_equation (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) (p : V S n i.succ)
    (hp : (SuffixData S n).family.coboundary0 i.succ p=u.word) :
    ((SuffixData S n).selectedMap i).map1 (step S n sigma tau i u).lower.word=
      (SuffixData S n).family.coboundary0 i.succ
        (p+(step S n sigma tau i u).potential) := by
  have hc := congrArg (fun out : AssemblyStepOutput (SuffixData S n) i => out.correction)
    (output_eq S n sigma tau i u p hp)
  rw [(step S n sigma tau i u).equation,← hp,hc,map_add]
  calc
    _ = (SuffixData S n).family.coboundary0 i.succ p+
        ((actualOutput S n tau i).correction+(actualOutput S n tau i).correction)+
        (SuffixData S n).family.coboundary0 i.succ (step S n sigma tau i u).potential := by abel
    _ = _ := by rw [word_add_self,add_zero]
theorem rx_reflection_transport (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (U : TannerSquarePresentation) (e : U=BDL26RXLocalReplacement.rxReplacementPresentation P S)
    (f : Word BDL26Field P.Q →ₗ[BDL26Field] Word BDL26Field U.Q)
    (hf : HEq f (BDL26ReplacementCochainMaps.rxMap1Coord P S))
    (v : Word BDL26Field P.Q) (p : Word BDL26Field U.X)
    (hp : tannerCoboundary0 U p=f v) :
    ∃ q : Word BDL26Field P.X, tannerCoboundary0 P q=v := by
  cases e
  have hm : f=BDL26ReplacementCochainMaps.rxMap1Coord P S := eq_of_heq hf
  rw [hm,BDL26RXCohomology.differential0_eq P A R S] at hp
  exact (BDL26RXCohomology.raw_boundary_iff P A.toTannerSquareAdmissible S v).mp ⟨p,hp⟩
theorem rx_indexed_reflection (S : OddScale) (d : Nat) (i : StepIndex d)
    (he : i.val%2=0) (v : (indexedFamily S d).Cochain1 i.castSucc)
    (p : (indexedFamily S d).Cochain0 i.succ)
    (hp : (indexedFamily S d).coboundary0 i.succ p=
      ((indexedDecoderData S d).selectedMap i).map1 v) :
    ∃ q : (indexedFamily S d).Cochain0 i.castSucc,
      (indexedFamily S d).coboundary0 i.castSucc q=v := by
  have e : (state S (i.val+1)).presentation=
      BDL26RXLocalReplacement.rxReplacementPresentation (state S i.val).presentation S := by
    change (nextState S i.val (state S i.val)).presentation=(rxState S (state S i.val)).presentation
    exact congrArg ConstructionState.presentation (if_pos he)
  have hp0 : tannerCoboundary0 (state S (i.val+1)).presentation p=
      ((indexedDecoderData S d).selectedMap i).map1 v := by
    funext r
    exact (congrFun (LinearMap.congr_fun (indexedFamily_coboundary0 S d i.succ) p) r).symm.trans
      (congrFun hp r)
  obtain ⟨q,hq⟩ := rx_reflection_transport (state S i.val).presentation
    (state S i.val).admissible (state S i.val).regular S _ e
    ((indexedDecoderData S d).selectedMap i).map1
    (indexedDecoderData_selected_rx S d i he).2.1 v p hp0
  refine ⟨q,?_⟩
  funext r
  exact (congrFun (LinearMap.congr_fun (indexedFamily_coboundary0 S d i.castSucc) q) r).trans
    (congrFun hq r)
theorem rx_lower_exists (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (he : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) (p : V S n i.succ)
    (hp : (SuffixData S n).family.coboundary0 i.succ p=u.word) :
    ∃ q : V S n i.castSucc, (SuffixData S n).family.coboundary0 i.castSucc q=
      (step S n sigma tau i u).lower.word := by
  have hs := step_boundary_equation S n sigma tau i u p hp
  rw [LevelTwoHistory.suffix_selected_map1,LevelTwoHistory.suffix_coboundary0] at hs
  obtain ⟨q,hq⟩ := rx_indexed_reflection S (n+2) (Edge n i) he _ _ hs.symm
  refine ⟨q,?_⟩
  change (SuffixData S n).family.coboundary0 i.castSucc q=
    (step S n sigma tau i u).lower.word at hq
  exact hq
def rzLowerPotential (S : OddScale) (n : Nat) (i : StepIndex n)
    (ho : ¬(Edge n i).val%2=0) (p : V S n i.succ) : V S n i.castSucc :=
  BDL26LevelTwoDistance.rzOldXParity
    (BDL26RZFiniteBlockTransport.Old S (n+2) (Edge n i)) S
    (BDL26RZFiniteBlockTransport.read0 S (n+2) (Edge n i) ho p)
theorem rz_lower_spec (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (ho : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) (p : V S n i.succ)
    (hp : (SuffixData S n).family.coboundary0 i.succ p=u.word) :
    (SuffixData S n).family.coboundary0 i.castSucc (rzLowerPotential S n i ho p)=
      (step S n sigma tau i u).lower.word := by
  have hl : (step S n sigma tau i u).lower.word=
      BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) ho
        (first S n sigma i) (second S n sigma tau i u) := by
    rw [step_rz S n sigma tau i ho u]
    rfl
  have hp' : (indexedFamily S (n+2)).coboundary0 (Edge n i).succ p=u.word := by
    change (SuffixData S n).family.coboundary0 i.succ p=u.word
    exact hp
  have hd := BDL26RZFiniteBlockTransport.delta0_coordinates S (n+2) (Edge n i) ho p
  have hq := BDL26LevelTwoDistance.rzQParity_coboundary
    (BDL26RZFiniteBlockTransport.Old S (n+2) (Edge n i))
    (state S (Edge n i).val).admissible S
    (BDL26RZFiniteBlockTransport.read0 S (n+2) (Edge n i) ho p)
  rw [← hd,hp'] at hq
  rw [hl,BDL26RZFiniteBlockTransport.lowerError_coordinates,
    representatives_difference S n sigma tau i u]
  rw [suffix_delta0]
  exact hq.symm
def lowerPotential (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) (p : V S n i.succ)
    (hp : (SuffixData S n).family.coboundary0 i.succ p=u.word) : V S n i.castSucc :=
  if he : (Edge n i).val%2=0 then Classical.choose (rx_lower_exists S n sigma tau i he u p hp)
  else rzLowerPotential S n i he p
theorem lower_potential_spec (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (u : LocalizedWord S n sigma tau i.succ) (p : V S n i.succ)
    (hp : (SuffixData S n).family.coboundary0 i.succ p=u.word) :
    (SuffixData S n).family.coboundary0 i.castSucc (lowerPotential S n sigma tau i u p hp)=
      (step S n sigma tau i u).lower.word := by
  unfold lowerPotential
  split
  · rename_i he
    exact Classical.choose_spec (rx_lower_exists S n sigma tau i he u p hp)
  · rename_i ho
    exact rz_lower_spec S n sigma tau i ho u p hp
theorem tail_exists_nat (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : Nat) (ha : a≤n)
    (p : V S n ⟨a,Nat.lt_succ_of_le ha⟩)
    (hp : (SuffixData S n).family.coboundary0 ⟨a,Nat.lt_succ_of_le ha⟩ p=
      (path S n sigma tau top ⟨a,Nat.lt_succ_of_le ha⟩).word)
    (b : LevelIndex n) (hb : b.val≤a) :
    ∃ q : V S n b, (SuffixData S n).family.coboundary0 b q=(path S n sigma tau top b).word := by
  cases a with
  | zero =>
      have h : b=⟨0,Nat.lt_succ_of_le ha⟩ := Fin.ext (by change b.val=0; omega)
      subst b
      exact ⟨p,hp⟩
  | succ a =>
      by_cases h : b.val=a+1
      · have h' : b=⟨a+1,Nat.lt_succ_of_le ha⟩ := Fin.ext h
        subst b
        exact ⟨p,hp⟩
      · let j : StepIndex n := ⟨a,by omega⟩
        let v := path S n sigma tau top j.succ
        let q := lowerPotential S n sigma tau j v p hp
        have hq : (SuffixData S n).family.coboundary0 j.castSucc q=
            (path S n sigma tau top j.castSucc).word := by
          rw [path_step S n sigma tau top j]
          exact lower_potential_spec S n sigma tau j v p hp
        exact tail_exists_nat S n sigma tau top a (by omega) q hq b (by omega)
termination_by a
def tailPotential (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word)
    (b : LevelIndex n) (hb : b.val≤a.val) : V S n b :=
  Classical.choose (tail_exists_nat S n sigma tau top a.val (Nat.le_of_lt_succ a.isLt) p hp b hb)
def fullPotential (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word) : V S n (TopIndex n) :=
  intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
    (tailPotential S n sigma tau top a p hp 0 (Nat.zero_le _))+
      intervalPotential S n sigma tau top 0 (TopIndex n)
theorem physical_supported (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    hammingSupport (BDL26ActualFailureReadout.flip S n q) ⊆ star S n (TopIndex n) (elementaryCenter S n q) := by
  rw [flip_eq_basis]
  exact elementary_support S n q
def physicalTop (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n) (q : Physical S (n+2)) :=
  BDL26LocalizedHistoryErrorDescent.initial S n (input S n u) (BDL26ActualFailureReadout.flip S n q)
    (elementaryCenter S n q) (physical_supported S n q)
def snapshot (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n) (q : Physical S (n+2)) (a : LevelIndex n) :=
  path S n (input S n u) (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) (physicalTop S n u q) a
def physicalPotential (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word) : V S n (TopIndex n) :=
  fullPotential S n _ _ (physicalTop S n u q) a p hp
open QEC.Semantics BDL26PairedDecoderPhase
end QEC.Coding.BDL26BoundaryTailInvariance


