-- Prove2me | Definitions.Def_DetDLP_S8H0_GateAgree
-- name    : DetDLP_S8H0_GateAgree
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T09:17:31.729928+00:00
-- url     : https://prove2.me/theorems/5b6b9631-7fc9-487f-bb51-13f7e4bd585a
-- title:
--   Tag 0 factor-gate incidence order and local tensor reduction
-- statement:
--   Proves that subdivision and CopyCycle preserve ascending incidence order at original factor gates, characterizes M5 half-edge ordering, and reduces port evaluation to block-local gate agreement.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8H0_PortEval

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace DetDLP.S8H0.GateAgree
open Groundwork w4_M5Network

def port : List Bool → List Bool := S8C.portPacket PortEval.check

theorem port_poly : Groundwork.PolyT port := PortEval.port_poly

private theorem split_range (n m : ℕ) : List.finRange (n+m) =
    (List.finRange n).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd n) := by
  simp only [← List.ofFn_id, List.map_ofFn]
  exact List.ofFn_add

private theorem disjoint_parts {n m : ℕ} (a : Fin m) (b : Fin n) :
    Fin.natAdd n a ≠ Fin.castAdd m b := by
  intro h; have he := congrArg Fin.val h; simp only [Fin.val_natAdd, Fin.val_castAdd] at he; omega

def gateEdges (A : w3_FactorLayout) (g : Fin A.ng) :=
  (List.finRange A.ne).filter (fun e => decide (A.gate e = g))

/-- Subdivision preserves ascending incidence order at an original factor gate. -/
theorem gate_ports (A : w3_FactorLayout) (g : Fin A.ng) :
    let G := w3_factorGraph A
    G.subdivision.ports (G.oldVertex (Fin.castAdd A.nb g)) =
      (gateEdges A g).map G.leftHalf := by
  let G := w3_factorGraph A
  let v := Fin.castAdd A.nb g
  let test := fun e : Fin (A.ne+A.ne) => decide
    ((G.subdivision.endpoints e).1 = G.oldVertex v ∨ (G.subdivision.endpoints e).2 = G.oldVertex v)
  change (List.finRange (A.ne+A.ne)).filter test = _
  rw [split_range, List.filter_append, List.filter_map, List.filter_map]
  have hl (e : Fin A.ne) : (test ∘ Fin.castAdd A.ne) e = decide (A.gate e = g) := by
    simp only [Function.comp_apply,test,G,v,w3_factorGraph,WireGraph.subdivision,WireGraph.oldVertex,
      Fin.addCases_left,Fin.castAdd_inj,disjoint_parts,or_false]
  have hr (e : Fin A.ne) : (test ∘ Fin.natAdd A.ne) e = false := by
    simp only [Function.comp_apply,test,G,v,w3_factorGraph,WireGraph.subdivision,WireGraph.oldVertex,
      Fin.addCases_right,Fin.castAdd_inj,disjoint_parts,or_false,decide_false]
  have hnil : (List.finRange A.ne).filter (test ∘ Fin.natAdd A.ne) = [] :=
    List.filter_eq_nil_iff.mpr (fun x _ => by rw [hr]; decide)
  rw [List.filter_congr (fun x _ => hl x), hnil, List.map_nil, List.append_nil]; rfl

private theorem idx_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (x : α) (l : List α) : (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => rfl
  | cons h t ih => by_cases hh : h = x <;> simp_all [hf.eq_iff, eq_comm]

/-- At factor gates the abstract port index is exactly its rank among matching edges. -/
theorem gate_index (A : w3_FactorLayout) (g : Fin A.ng) (e : Fin A.ne) (h : A.gate e = g) :
    let G := w3_factorGraph A; let v := Fin.castAdd A.nb g
    (G.oldPort v (G.portIndex v e (w3_gateInc A g e h))).val = (gateEdges A g).idxOf e := by
  let G := w3_factorGraph A; let v := Fin.castAdd A.nb g
  change (G.subdivision.ports (G.oldVertex v)).idxOf (G.incidentHalf v
    ((G.ports v).get (G.portIndex v e _))) = _
  rw [G.get_portIndex v e (w3_gateInc A g e h),gate_ports A g]
  have hh : (G.endpoints e).1 = v := congrArg (Fin.castAdd A.nb) h
  have hi : G.incidentHalf v e = G.leftHalf e := if_pos hh
  rw [hi]
  exact idx_map _ (fun _ _ he => Fin.castAdd_inj.mp he) _ _

/-- Evaluate a factor gate using its local ports in increasing incidence order. -/
def localCheck (A : w3_FactorLayout) (t : w3_factorTest A) (g : Fin A.ng) (a : List Bool) :=
  t g fun e => a.getD ((gateEdges A g).idxOf e.val) false

theorem local_eq (A : w3_FactorLayout) (t : w3_factorTest A) (g : Fin A.ng) (a) :
    let G := w3_factorGraph A; let v := G.oldVertex (Fin.castAdd A.nb g)
    localCheck A t g (List.ofFn a) = G.subdivisionTensor (w3_factorChecks A t) v a := by
  dsimp only; rw [(w3_factorGraph A).subdivisionTensor_oldVertex (w3_factorChecks A t) (Fin.castAdd A.nb g) a]; simp only [w3_factorChecks, Fin.addCases_left,localCheck]
  congr 1; funext e; rw [← gate_index A g e.val e.property]
  simp [List.getD_eq_getElem?_getD]


open S8J.CircuitRealizes in
theorem cycle_local {k : ℕ} (B : Block) (W : Wiring B.A.ne k) (g : Fin B.A.ng) (a : List Bool) :
    localCheck (circuit B W) (test B W) (Fin.castAdd B.A.ne g) a = localCheck B.A B.t g a := by
  let n := B.A.ne
  let U := circuit B W
  let pred := fun e : Fin (n+(n+n)) => @decide _ ((inferInstance : DecidableEq (Fin (B.A.ng+n))) (U.gate e) (Fin.castAdd n g))
  have hl (e : Fin n) : (pred ∘ Fin.castAdd (n+n)) e = decide (B.A.gate e = g) := by
    simp only [Function.comp_apply,pred,U,n,circuit,S8H.CopyCycle.layout,Fin.addCases_left,Fin.castAdd_inj]
  have hr (e : Fin (n+n)) : (pred ∘ Fin.natAdd n) e = false := by
    induction e using Fin.addCases <;> simp only [Function.comp_apply,pred,U,n,circuit,S8H.CopyCycle.layout,
      Fin.addCases_right,Fin.addCases_left,disjoint_parts,decide_false]
  have he : gateEdges U (Fin.castAdd n g) = (gateEdges B.A g).map (Fin.castAdd (n+n)) := by
    change (List.finRange (n+(n+n))).filter pred = _
    rw [split_range, List.filter_append, List.filter_map, List.filter_map]
    have hnil : (List.finRange (n+n)).filter (pred ∘ Fin.natAdd n) = [] :=
      List.filter_eq_nil_iff.mpr (fun x _ => by rw [hr]; decide)
    rw [List.filter_congr (fun x _ => hl x), hnil, List.map_nil, List.append_nil]; rfl
  simp only [localCheck, test, S8H.CopyCycle.checks, Fin.addCases_left]
  congr 1; funext e
  change a.getD ((gateEdges U (Fin.castAdd n g)).idxOf (Fin.castAdd (n+n) e.val)) false = _
  rw [he,idx_map _ (fun _ _ h => Fin.castAdd_inj.mp h)]

open S8J.CircuitRealizes in
theorem core_tensor {k : ℕ} (B : Block) (W : Wiring B.A.ne k) (g : Fin B.A.ng) (a) :
    let A := circuit B W; let v := (G B W).oldVertex (Fin.castAdd A.nb (Fin.castAdd B.A.ne g))
    localCheck B.A B.t g (List.ofFn a) = (G B W).subdivisionTensor (T B W) v a := by
  exact (cycle_local B W g _).symm.trans (local_eq _ _ _ _)

/-- At an M5 factor, the two ordered lists are precisely the lists of incident
source and destination wires; each is mapped to its corresponding half-edge. -/
theorem mul_gateEdges (G : WireGraph) (g : Fin G.nV) : gateEdges (w3_m5Layout G) g =
    ((List.finRange G.nE).filter (fun e => decide ((G.endpoints e).1 = g))).map G.leftHalf ++
    ((List.finRange G.nE).filter (fun e => decide ((G.endpoints e).2 = g))).map G.rightHalf := by
  change (List.finRange (G.nE+G.nE)).filter (fun e => decide (w3_m5HalfGate G e = g)) = _
  rw [split_range, List.filter_append, List.filter_map, List.filter_map]
  simp only [Function.comp_def, w3_m5HalfGate, Fin.addCases_left, Fin.addCases_right]
  rfl

section Packet
variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
local notation "B" => PointGraph.C p (GateSemantics.coeff E)
local notation "W" => PointGraph.W p (GateSemantics.coeff E)
local notation "G" => S8J.CircuitRealizes.G B W
local notation "T" => S8J.CircuitRealizes.T B W

theorem port_eval_of_local
    (h : ∀ (g : Fin (B).A.ng) (bits : List Bool),
      CoreCheck.gate (PortEval.fields (OrderPacket.word E)) g.val bits = localCheck (B).A (B).t g bits)
    (v : Fin (G).subdivision.nV) (a : Fin ((G).subdivision.deg v) → Bool) :
    port (encodePortQuery (OrderPacket.word E) v.val (List.ofFn a)) =
      encodeNatListBin [if (G).subdivisionTensor T v a then 1 else 0] := by
  unfold port; rw [S8C.portPacket_eq]
  suffices hh : PortEval.check (OrderPacket.word E,v.val,List.ofFn a) = (G).subdivisionTensor T v a by rw [hh]
  by_cases hv : v.val < (B).A.ng
  · let g : Fin (B).A.ng := ⟨v.val,hv⟩
    have H := core_tensor B W g a
    have hp : PortEval.prime (OrderPacket.word E) = p := by simp [PortEval.prime,List.getD]
    change PortEval.dispatch PortEval.numericGate _ = _
    simp only [PortEval.dispatch,hp, PortEval.gateCount_eq p (GateSemantics.coeff E), if_pos hv]
    exact (h g _).trans H
  · exact PortEval.check_eq_nongate E v a (Nat.le_of_not_lt hv)
end Packet

end DetDLP.S8H0.GateAgree


