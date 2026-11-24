-- Prove2me | Definitions.Def_CSL_NetworkCoding_Model_NetworkProtocol
-- name    : CSL_NetworkCoding_Model_NetworkProtocol
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:20:46.785806+00:00
-- url     : https://prove2.me/theorems/b710e965-1420-4328-b215-1a65c0008948
-- title:
--   Coded sorting library: NetworkCoding / Model / NetworkProtocol
-- statement:
--   Module `CodedSorting.NetworkCoding.Model.NetworkProtocol` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # A real finite-message pipeline for a feed-forward binary linear code
--
--   An edge is one physical unit-capacity edge. Its chosen orientation describes
--   how this protocol uses it; no second reverse-direction capacity is created.
--   The one-batch edge values below are recursively COMPUTED by the local linear
--   maps from the source bits resident at that vertex and from incoming edges.
--   They are not supplied as a globally correct transcript.
--
--   The pipeline sends batch `j` on edge `e` at time `j + rank(tail e)`. The file
--   checks actual packet values, local causality, unit edge occupancy, recovery,
--   and a finite completion horizon. Instantiating the network/linear-code data
--   from the manuscript's particular circuit graph is a separate interface.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.NetworkCoding.Model.NetworkProtocol

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Framework_Circuit
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Finset.Card

/-!
# A real finite-message pipeline for a feed-forward binary linear code

An edge is one physical unit-capacity edge. Its chosen orientation describes
how this protocol uses it; no second reverse-direction capacity is created.
The one-batch edge values below are recursively COMPUTED by the local linear
maps from the source bits resident at that vertex and from incoming edges.
They are not supplied as a globally correct transcript.

The pipeline sends batch `j` on edge `e` at time `j + rank(tail e)`. The file
checks actual packet values, local causality, unit edge occupancy, recovery,
and a finite completion horizon. Instantiating the network/linear-code data
from the manuscript's particular circuit graph is a separate interface.
-/

set_option autoImplicit false

namespace CSL.NetworkProtocol

open CSL.Circuit

variable {Node Edge Session : Type*}

structure RankedNetwork (Node Edge : Type*) where
  tail : Edge → Node
  head : Edge → Node
  rank : Node → ℕ
  forward : ∀ e, rank (tail e) < rank (head e)

/-- Every local map sees only source bits resident at this vertex and
incoming edge bits. It outputs one bit for each outgoing edge. -/
structure LinearCode (net : RankedNetwork Node Edge) (Session : Type*) where
  source : Session → Node
  sink : Session → Node
  localMap : (v : Node) →
    (({i : Session // source i = v} ⊕ {e : Edge // net.head e = v}) → Bit) →ₗ[Bit]
      ({e : Edge // net.tail e = v} → Bit)
  decoder : (i : Session) →
    ({e : Edge // net.head e = sink i} → Bit) →ₗ[Bit] Bit

variable (net : RankedNetwork Node Edge) (code : LinearCode net Session)

/-- The linear map from all independent input bits to an edge's transmitted
bit, constructed by well-founded recursion along strictly increasing ranks. -/
noncomputable def edgeMap (e : Edge) : (Session → Bit) →ₗ[Bit] Bit :=
  ((LinearMap.proj ⟨e, rfl⟩).comp (code.localMap (net.tail e))).comp
    (LinearMap.pi (fun port => match port with
      | .inl i => LinearMap.proj i.val
      | .inr incoming => edgeMap incoming.val))
termination_by net.rank (net.tail e)
decreasing_by
  have h := net.forward incoming.val
  simpa only [incoming.property] using h

noncomputable def edgeValue (input : Session → Bit) (e : Edge) : Bit :=
  edgeMap net code e input

theorem edgeValue_local (input : Session → Bit) (e : Edge) :
    edgeValue net code input e =
      code.localMap (net.tail e)
        (fun port => match port with
          | .inl i => input i.val
          | .inr incoming => edgeValue net code input incoming.val) ⟨e, rfl⟩ := by
  unfold edgeValue
  rw [edgeMap]
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  apply congrArg (fun values => code.localMap (net.tail e) values ⟨e, rfl⟩)
  funext port
  cases port <;> rfl

theorem edgeValue_add (x y : Session → Bit) (e : Edge) :
    edgeValue net code (x + y) e =
      edgeValue net code x e + edgeValue net code y e :=
  (edgeMap net code e).map_add x y

theorem edgeValue_smul (a : Bit) (x : Session → Bit) (e : Edge) :
    edgeValue net code (a • x) e = a • edgeValue net code x e :=
  (edgeMap net code e).map_smul a x

/-- A candidate obtained from a concrete circuit evaluation agrees with the
recursive local network execution if it satisfies the actual local maps.
This is proved from acyclicity, not supplied as an extra protocol axiom. -/
theorem edgeValue_unique (input : Session → Bit) (values : Edge → Bit)
    (hlocal : ∀ e, values e = code.localMap (net.tail e)
      (fun port => match port with
        | .inl i => input i.val
        | .inr incoming => values incoming.val) ⟨e, rfl⟩) :
    ∀ e, edgeValue net code input e = values e := by
  intro e
  induction e using (measure (fun e => net.rank (net.tail e))).wf.induction with
  | h e ih =>
    rw [edgeValue_local, hlocal e]
    apply congrArg (fun v => code.localMap (net.tail e) v ⟨e, rfl⟩)
    funext port
    cases port with
    | inl i => rfl
    | inr incoming =>
      apply ih incoming.val
      change net.rank (net.tail incoming.val) < net.rank (net.tail e)
      simpa only [incoming.property] using net.forward incoming.val

/-- One-shot correctness is the remaining circuit-to-network interface. -/
def Correct : Prop := ∀ (input : Session → Bit) (i : Session),
  code.decoder i (fun incoming => edgeValue net code input incoming.val) = input i

def sendTime {k : ℕ} (batch : Fin k) (e : Edge) : ℕ :=
  batch.val + net.rank (net.tail e)

/-- At each edge/time there is either no packet or exactly one binary value.
The batch index is determined by the public schedule, not sent as a header. -/
noncomputable def packet {k : ℕ} (inputs : Fin k → Session → Bit)
    (e : Edge) (time : ℕ) : Option Bit :=
  if h : net.rank (net.tail e) ≤ time ∧ time - net.rank (net.tail e) < k then
    some (edgeValue net code (inputs ⟨time - net.rank (net.tail e), h.2⟩) e)
  else none

theorem packet_at_sendTime {k : ℕ} (inputs : Fin k → Session → Bit)
    (batch : Fin k) (e : Edge) :
    packet net code inputs e (sendTime net batch e) =
      some (edgeValue net code (inputs batch) e) := by
  simp [packet, sendTime, Nat.le_add_left, batch.isLt]

/-- Distinct independent instances never compete for the same edge/time. -/
theorem sendTime_injective {k : ℕ} (e : Edge) :
    Function.Injective (fun batch : Fin k => sendTime net batch e) := by
  intro a b h
  apply Fin.ext
  exact Nat.add_right_cancel h

theorem edge_capacity {k : ℕ} (e : Edge) (time : ℕ) :
    (Finset.univ.filter (fun batch : Fin k => sendTime net batch e = time)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact sendTime_injective net e
    ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)

/-- A gate's required packet from this SAME batch arrives strictly before
the outgoing packet; packets from other batches are never substituted. -/
theorem incoming_before_outgoing {k : ℕ} (batch : Fin k) (e incoming : Edge)
    (hconnect : net.head incoming = net.tail e) :
    sendTime net batch incoming < sendTime net batch e := by
  unfold sendTime
  apply Nat.add_lt_add_left
  simpa only [hconnect] using net.forward incoming

/-- The scheduled transmitted bit can actually be computed from local
source bits and earlier incoming packets, using the original local map. -/
theorem transmitted_bit_is_local {k : ℕ} (inputs : Fin k → Session → Bit)
    (batch : Fin k) (e : Edge) :
    (packet net code inputs e (sendTime net batch e)).getD 0 =
      code.localMap (net.tail e)
        (fun port => match port with
          | .inl i => inputs batch i.val
          | .inr incoming =>
            (packet net code inputs incoming.val
              (sendTime net batch incoming.val)).getD 0) ⟨e, rfl⟩ := by
  simp only [packet_at_sendTime, Option.getD_some]
  exact edgeValue_local net code (inputs batch) e

theorem every_packet_before_horizon {k D : ℕ}
    (hdepth : ∀ e, net.rank (net.tail e) ≤ D) (batch : Fin k) (e : Edge) :
    sendTime net batch e < k + D := by
  unfold sendTime
  exact Nat.add_lt_add_of_lt_of_le batch.isLt (hdepth e)

/-- Each decoder recovers its entire k-bit message from the actual packets.
This is universal over the independent input vector, including every source. -/
theorem pipeline_recovers {k : ℕ} (hcorrect : Correct net code)
    (inputs : Fin k → Session → Bit) (batch : Fin k) (i : Session) :
    code.decoder i (fun incoming =>
      (packet net code inputs incoming.val
        (sendTime net batch incoming.val)).getD 0) = inputs batch i := by
  simp only [packet_at_sendTime, Option.getD_some]
  exact hcorrect (inputs batch) i

/-- Finite, causal, unit-capacity protocol delivering k bits per source
within k+D time slots. This packages execution properties, not rate algebra. -/
theorem finite_pipeline {k D : ℕ} (hcorrect : Correct net code)
    (hdepth : ∀ e, net.rank (net.tail e) ≤ D)
    (inputs : Fin k → Session → Bit) :
    (∀ e time,
      (Finset.univ.filter (fun batch : Fin k => sendTime net batch e = time)).card ≤ 1) ∧
    (∀ (batch : Fin k) e incoming,
      net.head incoming = net.tail e →
      sendTime net batch incoming < sendTime net batch e) ∧
    (∀ (batch : Fin k) e, sendTime net batch e < k + D) ∧
    (∀ (batch : Fin k) i, code.decoder i (fun incoming =>
      (packet net code inputs incoming.val
        (sendTime net batch incoming.val)).getD 0) = inputs batch i) :=
  ⟨edge_capacity net,
    incoming_before_outgoing net,
    every_packet_before_horizon net hdepth,
    pipeline_recovers net code hcorrect inputs⟩

end CSL.NetworkProtocol


