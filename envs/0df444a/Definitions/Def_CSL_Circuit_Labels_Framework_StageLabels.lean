-- Prove2me | Definitions.Def_CSL_Circuit_Labels_Framework_StageLabels
-- name    : CSL_Circuit_Labels_Framework_StageLabels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:58:57.053119+00:00
-- url     : https://prove2.me/theorems/0e3869df-b9c9-49b5-8321-b80dbe60a881
-- title:
--   Coded sorting library: Circuit / Labels / Framework / StageLabels
-- statement:
--   Module `CodedSorting.Circuit.Labels.Framework.StageLabels` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   The concrete program network's subdivided wire edges carry exactly the
--   matrix rank budget established in TensorLabels.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Labels.Framework.StageLabels

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Labels_Framework_TensorLabels
import Definitions.Def_CSL_Circuit_NetworkModel_Framework_ProgramNetwork
import Definitions.Def_CSL_NetworkCoding_Model_NetworkRates
import Definitions.Def_CSL_Shared_Programs_NormalizationComplete

/-! The concrete program network's subdivided wire edges carry exactly the
matrix rank budget established in TensorLabels. -/

namespace CSL.StageLabels
open CSL.TensorLabels
open CSL.CircuitProgram
open CSL.ProgramNetwork
open scoped BigOperators

variable {d : ℕ}

theorem stageLabels_length {G : Type*} (active : G → Bool) (label : G → Label d)
    (P : Label d) (gs : List G) : (stageLabels active label P gs).length = gs.length := by
  induction gs generalizing P with
  | nil => rfl
  | cons g gs ih => simp [stageLabels, ih]

theorem stageLabels_get_active {G : Type*} (active : G → Bool) (label : G → Label d)
    (P : Label d) (gs : List G) (i : Fin gs.length) (hi : active (gs.get i) = true) :
    (stageLabels active label P gs).get ⟨i.val, by simp [stageLabels_length]⟩ =
      label (gs.get i) := by
  induction gs generalizing P with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      simp only [List.get_cons_zero] at hi
      simp [stageLabels, hi]
    · intro hj
      simpa [stageLabels] using ih (if active g then label g else P) j hj

/-- A chain's recursive cost equals the finite sum of its consecutive edges. -/
theorem chainCost_sum (P : Label d) (qs : List (Label d)) :
    chainCost P qs = ∑ i : Fin qs.length,
      ((qs.get i) - ((P :: qs).get ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)).rank := by
  induction qs generalizing P with
  | nil => simp [chainCost]
  | cons Q qs ih =>
    simp only [List.length_cons]
    rw [chainCost, Fin.sum_univ_succ, ih]
    simp

section NetworkLabels

variable {Reg G : Type*} [DecidableEq Reg]
variable (gs : List G) (gate : G → XorGate Reg) (label : G → Label d)
variable (src dst : Reg → Label d)

noncomputable def wireTrace (r : Reg) : List (Label d) :=
  stageLabels (fun u => decide (r ∈ (gate u).ports)) label (src r) gs

@[simp] theorem wireTrace_length (r : Reg) :
    (wireTrace gs gate label src r).length = gs.length :=
  stageLabels_length _ _ _ _

/-- Actual node labels: gates share one label, while every private pass
vertex retains the label currently carried on its own register. -/
noncomputable def vertexLabel : Vertex Reg (gs.map gate).length → Label d
  | .source r => src r
  | .gate t => label (gs.get ⟨t.val, by simpa using t.isLt⟩)
  | .pass t r => (wireTrace gs gate label src r).get
      ⟨t.val, by simpa using t.isLt⟩
  | .sink r => dst r

theorem label_stageVertex (t : Fin (gs.map gate).length) (r : Reg) :
    vertexLabel gs gate label src dst (stageVertex (gs.map gate) t r) =
      (wireTrace gs gate label src r).get ⟨t.val, by simpa using t.isLt⟩ := by
  unfold stageVertex
  split_ifs with h
  · try dsimp [vertexLabel, wireTrace]
    symm
    have ht : t.val < gs.length := by simpa using t.isLt
    have ha : decide (r ∈ (gate (gs.get ⟨t.val,ht⟩)).ports) = true := by simpa using h
    simpa only [List.get_eq_getElem] using
      stageLabels_get_active (fun u => decide (r ∈ (gate u).ports)) label
        (src r) gs ⟨t.val,ht⟩ ha
  · rfl

theorem label_wireHead (i : Fin ((gs.map gate).length + 1)) (r : Reg) :
    vertexLabel gs gate label src dst (wireHead (gs.map gate) (i,r)) =
      ((wireTrace gs gate label src r) ++ [dst r]).get
        ⟨i.val, by simpa using i.isLt⟩ := by
  unfold wireHead
  split_ifs with h
  · simp only [List.length_map] at h
    simp [vertexLabel, List.get_eq_getElem, List.getElem_append, h]
  · rw [label_stageVertex]
    have hi : i.val < gs.length := by simpa using (Nat.lt_of_le_of_ne
      (Nat.le_of_lt_succ i.isLt) h)
    simp [List.get_eq_getElem, List.getElem_append, hi]

theorem label_wireTail (i : Fin ((gs.map gate).length + 1)) (r : Reg) :
    vertexLabel gs gate label src dst (wireTail (gs.map gate) (i,r)) =
      (src r :: (wireTrace gs gate label src r) ++ [dst r]).get
        ⟨i.val, by simp only [List.length_cons, List.length_append, wireTrace_length,
          List.length_singleton]; have := i.isLt; simp only [List.length_map] at this; omega⟩ := by
  unfold wireTail
  split_ifs with h
  · change i.val = 0 at h
    simp [vertexLabel, List.get_eq_getElem, h]
  · change i.val ≠ 0 at h
    rw [label_stageVertex]
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero h
    have hi : j < gs.length := by
      have := i.isLt
      simp only [List.length_map] at this
      omega
    simp [List.get_eq_getElem, List.getElem_append, hj, hi]

/-- Sum over the actual physical wire edges of the program network. -/
theorem wire_rank_sum (r : Reg) :
    (∑ i : Fin ((gs.map gate).length + 1),
      (vertexLabel gs gate label src dst (wireHead (gs.map gate) (i,r)) -
       vertexLabel gs gate label src dst (wireTail (gs.map gate) (i,r))).rank) =
      chainCost (src r) (wireTrace gs gate label src r ++ [dst r]) := by
  rw [chainCost_sum]
  have hlen : (gs.map gate).length + 1 = (wireTrace gs gate label src r ++ [dst r]).length := by simp
  apply Fintype.sum_equiv (finCongr hlen)
  intro i
  rw [label_wireHead, label_wireTail]
  rfl

variable [Fintype Reg]

noncomputable def networkRank : ℕ :=
  ∑ e : Wire Reg (gs.map gate).length,
    (vertexLabel gs gate label src dst (wireHead (gs.map gate) e) -
     vertexLabel gs gate label src dst (wireTail (gs.map gate) e)).rank

theorem networkRank_eq_stageCosts :
    networkRank gs gate label src dst =
      ∑ r : Reg, chainCost (src r) (wireTrace gs gate label src r ++ [dst r]) := by
  unfold networkRank
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  exact wire_rank_sum gs gate label src dst r

theorem networkRank_eq_filtered :
    networkRank gs gate label src dst =
      ∑ r : Reg, chainCost (src r)
        ((gs.filter (fun u => decide (r ∈ (gate u).ports))).map label ++ [dst r]) := by
  rw [networkRank_eq_stageCosts]
  apply Finset.sum_congr rfl
  intro r _
  exact stageLabels_cost _ _ _ _ _

end NetworkLabels

open CSL.Circuit CSL.CircuitCounts

/-- This node list is exactly `globalProgram`, by `globalGateOrder_program`. -/
noncomputable abbrev paperProgram (d : ℕ) := (globalGateOrder d).map globalNodeGate

noncomputable def paperLabel (d : ℕ) : Vertex (GlobalReg d) (paperProgram d).length → Label d :=
  vertexLabel (globalGateOrder d) globalNodeGate globalNodeLabel globalSource globalSink

/-- The actual program graph's physical-edge rank sum, including all private
pass subdivisions, equals the rank total proved from the tensor construction. -/
theorem paper_networkRank :
    networkRank (globalGateOrder d) globalNodeGate globalNodeLabel globalSource globalSink =
      totalRank d := by
  rw [networkRank_eq_stageCosts]
  exact programStage_totalRank

theorem paper_edgeRank_budget (hd : 0 < d) :
    (∑ e : Wire (GlobalReg d) (paperProgram d).length,
      (paperLabel d (wireHead (paperProgram d) e) -
       paperLabel d (wireTail (paperProgram d) e)).rank) =
      Fintype.card (GlobalReg d) * d^3 - (d.choose 3)^3 + 6 * (d.choose 3)^2 * d^2 := by
  change networkRank _ _ _ _ _ = _
  rw [paper_networkRank, totalRank_budget hd]

theorem paper_endpoint_identity (r : GlobalReg d) :
    paperLabel d (.sink (partner r)) - paperLabel d (.source r) = 1 :=
  global_endpoint_identity r

theorem partner_eq_globalSwap (r : GlobalReg d) : partner r = globalSwap r := by
  rcases r with (a | a) | a <;> rfl


section Transport
variable {Reg : Type*} [DecidableEq Reg]
variable {p q : List (XorGate Reg)}

noncomputable def transportLabel (h : p = q)
    (f : Vertex Reg p.length → Label d) : Vertex Reg q.length → Label d := h ▸ f

@[simp] theorem transportLabel_source (h : p = q)
    (f : Vertex Reg p.length → Label d) (r : Reg) :
    transportLabel h f (.source r) = f (.source r) := by cases h; rfl

@[simp] theorem transportLabel_sink (h : p = q)
    (f : Vertex Reg p.length → Label d) (r : Reg) :
    transportLabel h f (.sink r) = f (.sink r) := by cases h; rfl

variable [Fintype Reg]
noncomputable def physicalRank (p : List (XorGate Reg))
    (f : Vertex Reg p.length → Label d) : ℕ :=
  ∑ e : Wire Reg p.length, (f (wireHead p e) - f (wireTail p e)).rank

theorem physicalRank_transport (h : p = q) (f : Vertex Reg p.length → Label d) :
    physicalRank q (transportLabel h f) = physicalRank p f := by cases h; rfl
end Transport

/-- Labels on precisely the actual network used by the executable code. -/
noncomputable def actualLabel (d : ℕ) :
    Vertex (GlobalReg d) (globalProgram d).length → Label d :=
  transportLabel globalGateOrder_program (paperLabel d)

theorem actual_edgeRank_sum :
    physicalRank (globalProgram d) (actualLabel d) = totalRank d := by
  unfold actualLabel
  rw [physicalRank_transport]
  exact paper_networkRank

theorem actual_endpoint_identity (r : GlobalReg d) :
    actualLabel d (.sink (globalSwap r)) - actualLabel d (.source r) = 1 := by
  unfold actualLabel
  rw [transportLabel_sink, transportLabel_source, ← partner_eq_globalSwap]
  exact paper_endpoint_identity r

-- Lean 4.19 provides the structural sum BEq but not its lawfulness instance.
-- This proof lets us compare structural and decidable-equality edge counts.
local instance {α β : Type*} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] :
    LawfulBEq (α ⊕ β) where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b
    · congr 1; exact eq_of_beq h
    · cases h
    · cases h
    · congr 1; exact eq_of_beq h
  rfl := by
    intro a
    cases a with
    | inl a => change (a == a) = true; simp
    | inr b => change (b == b) = true; simp

/-- Structural equality and decidable equality count the same physical edges. -/
theorem actual_wire_beq_eq (d : ℕ) :
    (inferInstance : BEq (Wire (GlobalReg d) (globalProgram d).length)) =
      instBEqOfDecidableEq := lawful_beq_subsingleton _ _

/-- Every finite fractional routing on the same actual undirected network
obeys the rank bound. Both directions of each physical edge share capacity. -/
theorem actual_routing_bound {Path : Type*} [Fintype Path]
    (owner : Path → GlobalReg d)
    (walk : ∀ p, CSL.GraphRouting.Walk (actualNetwork d)
      (.source (owner p)) (.sink (globalSwap (owner p))))
    (flow : Path → ℝ) (rate : ℝ)
    (hd : 0 < d) (hW : 0 < Fintype.card (GlobalReg d))
    (hflow : ∀ p, 0 ≤ flow p)
    (capacity : ∀ e, ∑ p, flow p * ((walk p).edges.count e : ℝ) ≤ 1)
    (sessions : ∀ i, rate ≤ ∑ p, if owner p = i then flow p else 0) :
    rate ≤ (totalRank d : ℝ) / ((Fintype.card (GlobalReg d) : ℝ) * (d^3 : ℝ)) := by
  have hI : 0 < Fintype.card (H d) := by
    simp only [H, Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos hd (Nat.mul_pos hd hd)
  have capacity' : ∀ e, ∑ p, flow p *
      (@List.count _ instBEqOfDecidableEq e (walk p).edges : ℝ) ≤ 1 := by
    intro e
    have h := capacity e
    rw [← actual_wire_beq_eq d]
    exact h
  have hb := CSL.GraphRouting.common_routing_bound (actualNetwork d) (actualLabel d)
    (fun r => .source r) (fun r => .sink (globalSwap r)) actual_endpoint_identity
    owner walk flow rate hI hW hflow capacity' sessions
  have hsum : (∑ e, (CSL.GraphRouting.edgeLength (actualNetwork d)
      (actualLabel d) e : ℝ)) = (totalRank d : ℝ) := by
    exact_mod_cast actual_edgeRank_sum (d := d)
  rw [hsum] at hb
  simpa [H, pow_succ, mul_assoc] using hb

theorem actual_routing_strict_46 {Path : Type*} [Fintype Path]
    (owner : Path → GlobalReg 46)
    (walk : ∀ p, CSL.GraphRouting.Walk (actualNetwork 46)
      (.source (owner p)) (.sink (globalSwap (owner p))))
    (flow : Path → ℝ) (rate : ℝ)
    (hflow : ∀ p, 0 ≤ flow p)
    (capacity : ∀ e, ∑ p, flow p * ((walk p).edges.count e : ℝ) ≤ 1)
    (sessions : ∀ i, rate ≤ ∑ p, if owner p = i then flow p else 0) : rate < 1 := by
  have hW : 0 < Fintype.card (GlobalReg 46) := by
    rw [all_registers_card]
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  have hb := actual_routing_bound owner walk flow rate (by norm_num) hW hflow capacity sessions
  have hden : 0 < (Fintype.card (GlobalReg 46) : ℝ) * (46^3 : ℝ) :=
    mul_pos (by exact_mod_cast hW) (by norm_num)
  apply lt_of_le_of_lt hb
  apply (div_lt_one hden).mpr
  exact_mod_cast concrete_strict_saving

/-- The paper's session count counts precisely the concrete register type. -/
theorem actual_sessions_card :
    Fintype.card (GlobalReg Parameters.d) = Parameters.W := by
  rw [all_registers_card]
  rfl

/-- The tensor matrix dimension is precisely the paper's `m`. -/
theorem actual_matrix_card : Fintype.card (H Parameters.d) = Parameters.m := by
  simp [H, Parameters.m, pow_succ, mul_assoc]

/-- The numerical parameter `S` is the rank total of the concrete labels. -/
theorem actual_totalRank_eq_S : totalRank Parameters.d = Parameters.S := by
  rw [totalRank_budget (by norm_num [Parameters.d]), actual_sessions_card]
  simp only [Parameters.S, Parameters.m, Parameters.v, Parameters.delta]
  ring

/-- Exact correspondence between `S` and physical edges of the actual network. -/
theorem actual_edgeRank_eq_S :
    physicalRank (globalProgram Parameters.d) (actualLabel Parameters.d) = Parameters.S := by
  rw [actual_edgeRank_sum, actual_totalRank_eq_S]

/-- The normalized physical rank budget is the stated exact routing bound. -/
theorem actual_rank_ratio_eq_one_sub_eta :
    (totalRank 46 : ℝ) / ((Fintype.card (GlobalReg 46) : ℝ) * ((46 : ℕ) : ℝ)^3) =
      1 - (Parameters.eta : ℝ) := by
  have hm : ((46 : ℕ) : ℝ)^3 = (Parameters.m : ℝ) := by norm_num [Parameters.m_value]
  rw [hm]
  change (totalRank Parameters.d : ℝ) /
    ((Fintype.card (GlobalReg Parameters.d) : ℝ) * (Parameters.m : ℝ)) = _
  rw [actual_totalRank_eq_S, actual_sessions_card]
  norm_num [Parameters.S_value, Parameters.W_value, Parameters.m_value, Parameters.eta]

/-- The exact advertised routing gap holds on the actual physical network,
for all finite fractional routings by undirected walks. -/
theorem actual_routing_bound_eta_46 {Path : Type*} [Fintype Path]
    (owner : Path → GlobalReg 46)
    (walk : ∀ p, CSL.GraphRouting.Walk (actualNetwork 46)
      (.source (owner p)) (.sink (globalSwap (owner p))))
    (flow : Path → ℝ) (rate : ℝ)
    (hflow : ∀ p, 0 ≤ flow p)
    (capacity : ∀ e, ∑ p, flow p * ((walk p).edges.count e : ℝ) ≤ 1)
    (sessions : ∀ i, rate ≤ ∑ p, if owner p = i then flow p else 0) :
    rate ≤ 1 - (Parameters.eta : ℝ) := by
  have hW : 0 < Fintype.card (GlobalReg 46) := by
    change 0 < Fintype.card (GlobalReg Parameters.d)
    rw [actual_sessions_card, Parameters.W_value]
    norm_num
  have hb := actual_routing_bound owner walk flow rate (by norm_num) hW hflow capacity sessions
  simpa only [actual_rank_ratio_eq_one_sub_eta] using hb

end CSL.StageLabels


