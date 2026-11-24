-- Prove2me | Definitions.Def_CSL_Circuit_NetworkModel_NetworkAdapter
-- name    : CSL_Circuit_NetworkModel_NetworkAdapter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:58:00.984814+00:00
-- url     : https://prove2.me/theorems/8ea31cf7-8b40-434b-afa0-932ab8f284c3
-- title:
--   Coded sorting library: Circuit / NetworkModel / NetworkAdapter
-- statement:
--   Module `CodedSorting.Circuit.NetworkModel.NetworkAdapter` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Network interfaces for the Construction replacement
--
--   The register graph can contain temporary registers without treating their
--   initial values as independent messages. `restrictCode` keeps the same graph
--   and local computations, sets omitted inputs to zero, and retains only the
--   selected sessions. Correctness needs to be proved only at those sinks.
--
--   The routing interface accepts full-rank endpoint differences. In particular,
--   an idempotent matrix `P` gives a full-rank difference `1 - 2 • P`.
--
--   These reusable interfaces connect session restrictions and endpoint ranks
--   to coding and routing bounds for a supplied physical program.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.NetworkModel.NetworkAdapter

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_NetworkCoding_Model_NetworkRates
import Definitions.Def_CSL_Circuit_NetworkModel_Framework_ProgramNetwork
import Mathlib.Tactic.NoncommRing

/-!
# Network interfaces for the Construction replacement

The register graph can contain temporary registers without treating their
initial values as independent messages. `restrictCode` keeps the same graph
and local computations, sets omitted inputs to zero, and retains only the
selected sessions. Correctness needs to be proved only at those sinks.

The routing interface accepts full-rank endpoint differences. In particular,
an idempotent matrix `P` gives a full-rank difference `1 - 2 • P`.

These reusable interfaces connect session restrictions and endpoint ranks
to coding and routing bounds for a supplied physical program.
-/

set_option autoImplicit false

namespace CSL.Construction.NetworkAdapter

open CSL.Circuit CSL.CircuitProgram
open CSL.NetworkProtocol CSL.ProgramNetwork
open CSL.GraphRouting
open scoped BigOperators Matrix

section TemporaryCopies

variable {Reg : Type*} [DecidableEq Reg]

/-- Overwrite a temporary register using the existing XOR instruction:
the old destination occurs once in the controls and cancels itself. -/
def overwriteCopy (destination source : Reg) : XorGate Reg where
  ports := {destination, source}
  targets := {destination}
  controls _ := {destination, source}
  targets_subset := by
    intro r hr
    simp only [Finset.mem_singleton] at hr
    subst r
    simp
  controls_subset := by
    intro _ _ _ h
    exact h

theorem overwriteCopy_at_destination (destination source : Reg)
    (hne : destination ≠ source) (state : Reg → Bit) :
    (overwriteCopy destination source).eval state destination = state source := by
  have hself : state destination + state destination = 0 :=
    (by decide : ∀ b : Bit, b + b = 0) (state destination)
  simp [overwriteCopy, XorGate.eval, hne, ← add_assoc, hself]

theorem overwriteCopy_away (destination source : Reg) (state : Reg → Bit)
    (r : Reg) (hr : r ≠ destination) :
    (overwriteCopy destination source).eval state r = state r := by
  simp [overwriteCopy, XorGate.eval, hr]

end TemporaryCopies

section SelectedSessions

variable {Node Edge Reg : Type*}
variable (net : RankedNetwork Node Edge) (code : LinearCode net Reg)
variable (active : Reg → Prop) [DecidablePred active]

/-- Independent messages reside only on the selected original registers.
Temporary registers have fixed zero inputs and introduce no extra sessions. -/
def extendMessages (input : {r : Reg // active r} → Bit) : Reg → Bit :=
  fun r => if h : active r then input ⟨r, h⟩ else 0

@[simp] theorem extendMessages_active
    (input : {r : Reg // active r} → Bit) (r : {r : Reg // active r}) :
    extendMessages active input r.val = input r := by
  simp [extendMessages, r.property]

@[simp] theorem extendMessages_inactive
    (input : {r : Reg // active r} → Bit) (r : Reg) (h : ¬ active r) :
    extendMessages active input r = 0 := by
  simp [extendMessages, h]

/-- Supply the original local map with the retained local source bits and
zeros for omitted source bits. All incoming edge ports are unchanged. -/
def extendLocalInputs (v : Node) :
    (({i : {r : Reg // active r} // code.source i.val = v} ⊕
      {e : Edge // net.head e = v}) → Bit) →ₗ[Bit]
    (({r : Reg // code.source r = v} ⊕
      {e : Edge // net.head e = v}) → Bit) :=
  LinearMap.pi (fun port => match port with
    | .inl r => if h : active r.val then
        LinearMap.proj (.inl ⟨⟨r.val, h⟩, r.property⟩)
      else 0
    | .inr e => LinearMap.proj (.inr e))

/-- A code on exactly the same physical network, with fewer independent
messages. Removing sessions does not remove, duplicate, or add any edge. -/
def restrictCode : LinearCode net {r : Reg // active r} where
  source r := code.source r.val
  sink r := code.sink r.val
  localMap v := (code.localMap v).comp (extendLocalInputs net code active v)
  decoder r := code.decoder r.val

/-- Local execution after restriction agrees with execution of the original
code on the zero-extended message vector. This does not assume that the
original code recovers messages from temporary registers. -/
theorem restrictCode_edgeValue (input : {r : Reg // active r} → Bit)
    (e : Edge) :
    edgeValue net (restrictCode net code active) input e =
      edgeValue net code (extendMessages active input) e := by
  apply edgeValue_unique net (restrictCode net code active) input
    (edgeValue net code (extendMessages active input))
  intro edge
  rw [edgeValue_local]
  change code.localMap (net.tail edge) _ ⟨edge, rfl⟩ =
    code.localMap (net.tail edge)
      (extendLocalInputs net code active (net.tail edge) _) ⟨edge, rfl⟩
  apply congrArg (fun values => code.localMap (net.tail edge) values ⟨edge, rfl⟩)
  funext port
  cases port with
  | inl r =>
    by_cases h : active r.val <;>
      · simp only [extendLocalInputs]
        erw [LinearMap.pi_apply]
        simp [extendMessages, h]; try rfl
  | inr incoming => rfl

/-- Only selected sinks must recover their independent messages. -/
theorem restrictCode_correct
    (hselected : ∀ (input : {r : Reg // active r} → Bit)
      (r : {r : Reg // active r}),
      code.decoder r.val (fun incoming =>
        edgeValue net code (extendMessages active input) incoming.val) = input r) :
    Correct net (restrictCode net code active) := by
  intro input r
  change code.decoder r.val (fun incoming =>
    edgeValue net (restrictCode net code active) input incoming.val) = input r
  simp only [restrictCode_edgeValue]
  exact hselected input r

end SelectedSessions

section SelectedProgramSessions

variable {Reg : Type*} [DecidableEq Reg]
variable (program : List (XorGate Reg)) (σ : Equiv.Perm Reg)
variable (active : Reg → Prop) [DecidablePred active]

/-- The executable XOR program need only recover the original registers.
There is no restoration obligation on the omitted temporary registers. -/
theorem selected_program_correct
    (hprogram : ∀ (input : {r : Reg // active r} → Bit)
      (r : {r : Reg // active r}),
      runProgram program (extendMessages active input) (σ r.val) = input r) :
    Correct (network program)
      (restrictCode (network program) (code program σ) active) := by
  apply restrictCode_correct
  intro input r
  change edgeValue (network program) (code program σ)
    (extendMessages active input) (sinkWire program (σ r.val)) = input r
  rw [network_edgeValue, wireValue_sink]
  exact hprogram input r

end SelectedProgramSessions

section FullRankEndpoints

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A projection gives an involution, including at nonzero source labels. -/
theorem reflection_square (P : Matrix I I ℚ) (hP : P * P = P) :
    (1 - P - P) * (1 - P - P) = 1 := by
  noncomm_ring [hP]

/-- Full rank follows from the explicit two-sided inverse. -/
theorem reflection_full_rank (P : Matrix I I ℚ) (hP : P * P = P) :
    (1 - P - P).rank = Fintype.card I := by
  apply le_antisymm (Matrix.rank_le_card_width _) ?_
  have h := Matrix.rank_mul_le_left (1 - P - P) (1 - P - P)
  simpa only [reflection_square P hP, Matrix.rank_one] using h

/-- Paper notation for the same full-rank endpoint difference. -/
theorem one_sub_two_smul_full_rank (P : Matrix I I ℚ) (hP : P * P = P) :
    (1 - (2 : ℚ) • P).rank = Fintype.card I := by
  have heq : 1 - (2 : ℚ) • P = 1 - P - P := by
    rw [two_smul]
    abel
  rw [heq]
  exact reflection_full_rank P hP

variable {Node Edge Session Path : Type*}
variable (net : RankedNetwork Node Edge) (label : Node → Matrix I I ℚ)

/-- Identity endpoint differences are sufficient but unnecessary: routing
uses only the actual rank distance between a session's endpoints. -/
theorem walk_length_bound_of_full_rank [Fintype Edge] [DecidableEq Edge]
    {s t : Node} (w : Walk net s t)
    (hend : (label t - label s).rank = Fintype.card I) :
    Fintype.card I ≤ ∑ e, edgeLength net label e * w.edges.count e := by
  have h := walk_rank_bound net label w
  rw [hend, list_weight_eq_count_sum] at h
  exact h

/-- The denominator counts `Session`, independently of the number of
registers or source leaves retained in the physical program graph. -/
theorem common_routing_bound_of_full_rank
    [Fintype Edge] [DecidableEq Edge]
    [Fintype Session] [DecidableEq Session] [Fintype Path]
    (source sink : Session → Node)
    (endpoints : ∀ i, (label (sink i) - label (source i)).rank = Fintype.card I)
    (owner : Path → Session)
    (walk : ∀ p, Walk net (source (owner p)) (sink (owner p)))
    (flow : Path → ℝ) (rate : ℝ)
    (hI : 0 < Fintype.card I) (hS : 0 < Fintype.card Session)
    (hflow : ∀ p, 0 ≤ flow p)
    (capacity : ∀ e, ∑ p, flow p * ((walk p).edges.count e : ℝ) ≤ 1)
    (sessions : ∀ i, rate ≤ ∑ p, if owner p = i then flow p else 0) :
    rate ≤ (∑ e, (edgeLength net label e : ℝ)) /
      ((Fintype.card Session : ℝ) * (Fintype.card I : ℝ)) := by
  have paths (p : Path) : (Fintype.card I : ℝ) ≤
      ∑ e, (edgeLength net label e : ℝ) * ((walk p).edges.count e : ℝ) := by
    exact_mod_cast walk_length_bound_of_full_rank net label (walk p) (endpoints (owner p))
  have ht := CSL.RankMetric.session_total_flow owner flow rate sessions
  have hi : (0 : ℝ) < Fintype.card I := by exact_mod_cast hI
  have hs : (0 : ℝ) < Fintype.card Session := by exact_mod_cast hS
  have hb := CSL.RankMetric.common_rate_bound flow
    (fun e => (edgeLength net label e : ℝ)) (fun _ => 1)
    (fun p e => (walk p).edges.count e)
    (Fintype.card I : ℝ) (Fintype.card Session : ℝ) rate hi hs hflow
    (fun e => Nat.cast_nonneg _) paths capacity ht
  simpa only [mul_one] using hb

end FullRankEndpoints

end CSL.Construction.NetworkAdapter


