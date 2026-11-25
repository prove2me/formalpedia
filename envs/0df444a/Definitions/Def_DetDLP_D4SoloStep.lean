-- Prove2me | Definitions.Def_DetDLP_D4SoloStep
-- name    : DetDLP_D4SoloStep
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T21:54:07.858803+00:00
-- url     : https://prove2.me/theorems/2174cf09-6e68-46f7-afcf-44a4c53e615a
-- title:
--   Solo Active-Step Child Node Construction and Packet Certificate Preservation
-- statement:
--   Constructs child SoloNode records for each active branching step in the Appendix D.4 solo rank unrolling, preserving sorted boundary-pin lists, host injectivity, positive pinned vertex degrees, edge and degree bounds, and polynomial-time packet evaluator certificates from DetDLP.D4SoloRoot.
-- source:
--   prove2me_m14_solo/Definitions/Def_DetDLP_D4SoloStep.lean

import Definitions.Def_DetDLP_D4SoloRoot
import Theorems.Thm_DetDLP_d4_active_node_preconditions
import Theorems.Thm_DetDLP_d4_balanced_node_rank_machine

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace DetDLP.D4SoloStep

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

section ActiveStep

noncomputable section

private theorem cast_tensor_apply {G : BipartiteMultigraph} {R : Type} {u w : Fin G.nV}
    (h : u = w) (g : (Fin (G.deg u) → Bool) → R) (β : Fin (G.deg w) → Bool) :
    (h ▸ g) β = g (fun i => β (i.cast (congrArg G.deg h))) := by
  subst h; rfl

private theorem match_tensor_inl {G : BipartiteMultigraph} {a : ℕ} {lbl : Label a G}
    {pk : Packing lbl} {i g} {R R' : Type} (c : Child pk i g R') (up : R → R')
    (T : Tensor G R) (w : Fin c.graph.nV) (z : {v : Fin G.nV // lbl i v = g} ⊕ Fin pk.count)
    (h : c.oldOrPacket.symm z = w) (v : {v : Fin G.nV // lbl i v = g}) (hv : z = .inl v)
    (β : Fin (c.graph.deg w) → Bool) :
    ((fun q : {v : Fin G.nV // lbl i v = g} ⊕ Fin pk.count =>
      (match q with
      | .inl v => fun α => up (T v.val (α ∘ c.ports v))
      | .inr r => c.entry r : (Fin (c.graph.deg (c.oldOrPacket.symm q)) → Bool) → R')) z)
      (fun j => β (j.cast (congrArg c.graph.deg h))) =
      up (T v.val (fun j => β ((c.ports v j).cast (congrArg c.graph.deg (by rw [← hv]; exact h))))) := by
  subst hv; rfl

private theorem match_tensor_inr {G : BipartiteMultigraph} {a : ℕ} {lbl : Label a G}
    {pk : Packing lbl} {i g} {R R' : Type} (c : Child pk i g R') (up : R → R')
    (T : Tensor G R) (w : Fin c.graph.nV) (z : {v : Fin G.nV // lbl i v = g} ⊕ Fin pk.count)
    (h : c.oldOrPacket.symm z = w) (r : Fin pk.count) (hr : z = .inr r)
    (β : Fin (c.graph.deg w) → Bool) :
    ((fun q : {v : Fin G.nV // lbl i v = g} ⊕ Fin pk.count =>
      (match q with
      | .inl v => fun α => up (T v.val (α ∘ c.ports v))
      | .inr r => c.entry r : (Fin (c.graph.deg (c.oldOrPacket.symm q)) → Bool) → R')) z)
      (fun j => β (j.cast (congrArg c.graph.deg h))) =
      c.entry r (fun j => β (j.cast (congrArg c.graph.deg (by rw [← hr]; exact h)))) := by
  subst hr; rfl

theorem child_tensor_inl {G : BipartiteMultigraph} {a : ℕ} {lbl : Label a G}
    {pk : Packing lbl} {i g} {R R' : Type} (c : Child pk i g R') (up : R → R')
    (T : Tensor G R) (w : Fin c.graph.nV) (v : {v : Fin G.nV // lbl i v = g})
    (hcw : c.oldOrPacket w = .inl v) (β : Fin (c.graph.deg w) → Bool) :
    c.tensor up T w β =
      up (T v.val (fun j => β ((c.ports v j).cast (congrArg c.graph.deg (by rw [← hcw, c.oldOrPacket.symm_apply_apply]))))) := by
  unfold Child.tensor
  rw [cast_tensor_apply (c.oldOrPacket.symm_apply_apply w)]
  exact match_tensor_inl c up T w (c.oldOrPacket w) (c.oldOrPacket.symm_apply_apply w) v hcw β

theorem child_tensor_inr {G : BipartiteMultigraph} {a : ℕ} {lbl : Label a G}
    {pk : Packing lbl} {i g} {R R' : Type} (c : Child pk i g R') (up : R → R')
    (T : Tensor G R) (w : Fin c.graph.nV) (r : Fin pk.count)
    (hcw : c.oldOrPacket w = .inr r) (β : Fin (c.graph.deg w) → Bool) :
    c.tensor up T w β =
      c.entry r (fun j => β (j.cast (congrArg c.graph.deg (by rw [← hcw, c.oldOrPacket.symm_apply_apply])))) := by
  unfold Child.tensor
  rw [cast_tensor_apply (c.oldOrPacket.symm_apply_apply w)]
  exact match_tensor_inr c up T w (c.oldOrPacket w) (c.oldOrPacket.symm_apply_apply w) r hcw β

theorem shift_le_level_solo (S j : ℕ) : D3Stopped.shift S j ≤ D3Stopped.level S :=
  shift_le_level S j

theorem node_preconditions_hold {C c : ℕ} (x : Input C c)
    {f : ℤ[X]} {PktOK : PktPred f x.l} (nd : SoloNode x f PktOK)
    (L₀_act : ℕ)
    (hact_spec : ∀ (M Δ p : ℕ),
      L₀_act ≤ D3Stopped.level x.S → D3Stopped.threshold x.S < M → M ≤ x.S / 8 ^ nd.d →
      let a := D3Stopped.shift x.S nd.d
      let u := D3Stopped.width x.S nd.d
      let last := if nd.d = 0 then 0 else D3Stopped.shift x.S (nd.d - 1)
      Δ ≤ max (C * Nat.ceil ((x.b : ℝ) ^ ((3 : ℝ) / 4))) (2 * 2 ^ last) →
      p ≤ x.p + 80 * x.S * 2 ^ last →
      1 ≤ u ∧ u ≤ a ∧ u ≤ M ∧ 1 ≤ x.l ∧
      points M a ≤ 2 ^ (4 * D3Stopped.level x.S) ∧
      2 ^ a * 64 ^ (2 * a) ≤ M ∧ (a + 2) * 64 ^ (4 * a) * max 1 Δ ≤ M ∧
      max Δ (2 * 2 ^ a) ≤ D3Stopped.cap x.S ∧
      (∀ i < u, p + increase M a u i ≤ 64 * M * tileScale a i / u) ∧
      ∀ i, p + increase M a u i ≤ x.p + 80 * x.S * 2 ^ a)
    (hL : L₀_act ≤ D3Stopped.level x.S) (hM : D3Stopped.threshold x.S < nd.G.nE) :
    let a := D3Stopped.shift x.S nd.d
    let u := D3Stopped.width x.S nd.d
    1 ≤ u ∧ u ≤ a ∧ u ≤ nd.G.nE ∧ 1 ≤ x.l ∧
    points nd.G.nE a ≤ 2 ^ (4 * D3Stopped.level x.S) ∧
    2 ^ a * 64 ^ (2 * a) ≤ nd.G.nE ∧ (a + 2) * 64 ^ (4 * a) * max 1 nd.G.maxDeg ≤ nd.G.nE ∧
    max nd.G.maxDeg (2 * 2 ^ a) ≤ D3Stopped.cap x.S ∧
    (∀ i < u, nd.pCurr + increase nd.G.nE a u i ≤ 64 * nd.G.nE * tileScale a i / u) ∧
    ∀ i, nd.pCurr + increase nd.G.nE a u i ≤ x.p + 80 * x.S * 2 ^ a :=
  hact_spec nd.G.nE nd.G.maxDeg nd.pCurr hL hM nd.edges_le
    (nd.deg_le.trans (max_le_max le_rfl (by split_ifs <;> simp)))
    (nd.hp_le.trans (by split_ifs <;> simp))

def finCastEquiv {m n : ℕ} (h : m = n) : Fin m ≃ Fin n where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

noncomputable def childPins {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
    (nd : SoloNode x f PktOK) {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a}
    (s : Step lbl hu f x.l nd.pCurr) (ν : Branch s) (g : Fin 64) :
    List (Fin (4 * x.m * x.k) × Fin (s.child ν.1 ν.2.1 ν.2.2 g).graph.nV) :=
  let ch := s.child ν.1 ν.2.1 ν.2.2 g
  let kept := nd.pins.filter (fun pv => decide (lbl (coord hu ν.1) pv.2 = g))
  kept.attach.map fun ⟨pv, hpv⟩ =>
    (pv.1, ch.oldOrPacket.symm (.inl ⟨pv.2, of_decide_eq_true (List.mem_filter.mp hpv).2⟩))

theorem childPins_length {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
    (nd : SoloNode x f PktOK) {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a}
    (s : Step lbl hu f x.l nd.pCurr) (ν : Branch s) (g : Fin 64) :
    (childPins x nd s ν g).length =
      (nd.pins.filter (fun pv => decide (lbl (coord hu ν.1) pv.2 = g))).length := by
  simp [childPins]

theorem childPins_get {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
    (nd : SoloNode x f PktOK) {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a}
    (s : Step lbl hu f x.l nd.pCurr) (ν : Branch s) (g : Fin 64)
    (k : Fin (childPins x nd s ν g).length) :
    let kept := nd.pins.filter (fun pv => decide (lbl (coord hu ν.1) pv.2 = g))
    have hk : k.val < kept.length := k.isLt.trans_eq (childPins_length x nd s ν g)
    let pv := kept[k.val]'hk
    (childPins x nd s ν g).get k =
      (pv.1, (s.child ν.1 ν.2.1 ν.2.2 g).oldOrPacket.symm
        (.inl ⟨pv.2, of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hk)).2⟩)) := by
  rw [List.get_eq_getElem]
  simp [childPins]

private noncomputable def childVertAux {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (oe : Fin E_pkt.tapeCount) (K_loc : ℕ)
    (nd : SoloNode x f (pktOKOf E_pkt oe K_loc x f hf))
    {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a} (s : Step lbl hu f x.l nd.pCurr)
    (ha_eq : a = D3Stopped.shift x.S nd.d)
    (hinc_le : ∀ i, nd.pCurr + increase nd.G.nE a u i ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d)
    (hpkt_eval : ∀ t k β g r α,
      let c := s.child t k β g
      let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
      RunsWithin E_pkt oe (Encoding.encodeList id [c.descriptor r, List.ofFn α])
        (residue f x.l _ hf (c.entry r α))
        (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (ν : Branch s) (g : Fin 64) (w : Fin (s.child ν.1 ν.2.1 ν.2.2 g).graph.nV)
    (z : {v : Fin nd.G.nV // lbl (coord hu ν.1) v = g} ⊕ Fin s.pk.count)
    (hw_eq : (s.child ν.1 ν.2.1 ν.2.2 g).oldOrPacket.symm z = w) :
    SoloVert x (s.child ν.1 ν.2.1 ν.2.2 g).graph f (pktOKOf E_pkt oe K_loc x f hf)
      (nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val)) (nd.d + 1) w :=
  let c := s.child ν.1 ν.2.1 ν.2.2 g
  let p' := nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val)
  match z, hw_eq with
  | .inl v, hw_eq =>
    let pe : Fin (nd.G.deg v.val) ≃ Fin (c.graph.deg w) :=
      (c.ports v).trans (finCastEquiv (congrArg c.graph.deg hw_eq))
    (nd.verts v.val).pushChild p' (Nat.le_add_right ..) pe
  | .inr r, hw_eq =>
    SoloVert.pkt nd.d p' (c.graph.deg (c.oldOrPacket.symm (.inr r))) (c.descriptor r)
      (Nat.lt_succ_self nd.d) le_rfl (c.entry r) (by
        have hrun := hpkt_eval ν.1 ν.2.1 ν.2.2 g r
        have hdeg_r : c.graph.deg (c.oldOrPacket.symm (.inr r)) ≤ 2 * 2 ^ D3Stopped.shift x.S nd.d :=
          ha_eq ▸ c.packetDeg r
        have hp_ge1 : 1 ≤ p' := le_trans (le_trans (x.hp) nd.hp_ge) (Nat.le_add_right ..)
        have hp_le : p' ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d := hinc_le _
        have hinc_big : nd.G.nE ≤ increase nd.G.nE a u (AppendixD4.level ν.1.val) := by
          unfold increase tileScale AppendixD4.mult
          have : 1 ≤ a + 1 := Nat.succ_pos _
          nlinarith [Nat.zero_le (8 * ((3 * nd.G.nE + u - 1) / u) * 2 ^ (a - AppendixD4.level ν.1.val))]
        have hn_le : nd.G.nE + nd.pCurr + f.natDegree + x.l + 2 ≤ p' + 4 * D3Stopped.level x.S + x.l + 2 := by
          rw [hdeg_f]; dsimp only [p']; omega
        have hraw_len : (c.descriptor r).length ≤
            (Encoding.encodeList id [c.descriptor r, List.ofFn (fun _ : Fin (c.graph.deg (c.oldOrPacket.symm (.inr r))) => false)]).length := by
          have flen (z : Bits) : (Encoding.frame z).length = 2 * z.length + 1 := by
            induction z with
            | nil => simp [Encoding.frame]
            | cons _ tail ih =>
              change (true :: _ :: Encoding.frame tail).length = _
              simp [ih]; omega
          simp [Encoding.encodeList, flen]; omega
        have hpb_mono : polyBound K_loc (nd.G.nE + nd.pCurr + f.natDegree + x.l + 2) ≤
            polyBound K_loc (p' + 4 * D3Stopped.level x.S + x.l + 2) := by
          unfold polyBound; gcongr
        have hraw_pb : ((c.descriptor r).length : ℝ) ≤ polyBound K_loc (p' + 4 * D3Stopped.level x.S + x.l + 2) :=
          (by exact_mod_cast hraw_len : ((c.descriptor r).length : ℝ) ≤ _).trans
            ((runsWithin_input_len_le (hrun (fun _ => false))).trans hpb_mono)
        refine ⟨hp_ge1, hp_le, hdeg_r, hraw_pb, fun α => ?_⟩
        have hr0 := hrun α
        have hn_pos : (0 : ℝ) < (nd.G.nE + nd.pCurr + f.natDegree + x.l + 2 : ℕ) := by positivity
        have hlog_le : Real.log ((nd.G.nE + nd.pCurr + f.natDegree + x.l + 2 : ℕ) : ℝ) ≤
            Real.log ((p' + 4 * D3Stopped.level x.S + x.l + 2 : ℕ) : ℝ) :=
          Real.log_le_log hn_pos (by exact_mod_cast hn_le)
        have hexp_le : Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log ((nd.G.nE + nd.pCurr + f.natDegree + x.l + 2 : ℕ) : ℝ)) ≤
            Real.exp ((K_loc : ℝ) * (2 ^ D3Stopped.shift x.S nd.d : ℕ) * Real.log ((p' + 4 * D3Stopped.level x.S + x.l + 2 : ℕ) : ℝ)) := by
          rw [ha_eq]
          apply Real.exp_le_exp.mpr
          gcongr
        exact DetDLP.PolyTBridge.runsWithin_mono_local hr0 hexp_le hpb_mono)
      none (congrArg c.graph.deg hw_eq)

private theorem childVertAux_congr {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (oe : Fin E_pkt.tapeCount) (K_loc : ℕ)
    (nd : SoloNode x f (pktOKOf E_pkt oe K_loc x f hf))
    {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a} (s : Step lbl hu f x.l nd.pCurr)
    (ha_eq : a = D3Stopped.shift x.S nd.d)
    (hinc_le : ∀ i, nd.pCurr + increase nd.G.nE a u i ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d)
    (hpkt_eval : ∀ t k β g r α,
      let c := s.child t k β g
      let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
      RunsWithin E_pkt oe (Encoding.encodeList id [c.descriptor r, List.ofFn α])
        (residue f x.l _ hf (c.entry r α))
        (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (ν : Branch s) (g : Fin 64) (w : Fin (s.child ν.1 ν.2.1 ν.2.2 g).graph.nV)
    {z₁ z₂ : {v : Fin nd.G.nV // lbl (coord hu ν.1) v = g} ⊕ Fin s.pk.count} (hz : z₁ = z₂)
    (h₁ : (s.child ν.1 ν.2.1 ν.2.2 g).oldOrPacket.symm z₁ = w)
    (h₂ : (s.child ν.1 ν.2.1 ν.2.2 g).oldOrPacket.symm z₂ = w) :
    childVertAux x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w z₁ h₁ =
      childVertAux x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w z₂ h₂ := by
  subst hz; rfl

noncomputable def childVert {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (oe : Fin E_pkt.tapeCount) (K_loc : ℕ)
    (nd : SoloNode x f (pktOKOf E_pkt oe K_loc x f hf))
    {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a} (s : Step lbl hu f x.l nd.pCurr)
    (ha_eq : a = D3Stopped.shift x.S nd.d)
    (hinc_le : ∀ i, nd.pCurr + increase nd.G.nE a u i ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d)
    (hpkt_eval : ∀ t k β g r α,
      let c := s.child t k β g
      let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
      RunsWithin E_pkt oe (Encoding.encodeList id [c.descriptor r, List.ofFn α])
        (residue f x.l _ hf (c.entry r α))
        (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (ν : Branch s) (g : Fin 64) (w : Fin (s.child ν.1 ν.2.1 ν.2.2 g).graph.nV) :
    SoloVert x (s.child ν.1 ν.2.1 ν.2.2 g).graph f (pktOKOf E_pkt oe K_loc x f hf)
      (nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val)) (nd.d + 1) w :=
  childVertAux x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w
    ((s.child ν.1 ν.2.1 ν.2.2 g).oldOrPacket w)
    ((s.child ν.1 ν.2.1 ν.2.2 g).oldOrPacket.symm_apply_apply w)

theorem childVert_inl {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (oe : Fin E_pkt.tapeCount) (K_loc : ℕ)
    (nd : SoloNode x f (pktOKOf E_pkt oe K_loc x f hf))
    {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a} (s : Step lbl hu f x.l nd.pCurr)
    (ha_eq : a = D3Stopped.shift x.S nd.d)
    (hinc_le : ∀ i, nd.pCurr + increase nd.G.nE a u i ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d)
    (hpkt_eval : ∀ t k β g r α,
      let c := s.child t k β g
      let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
      RunsWithin E_pkt oe (Encoding.encodeList id [c.descriptor r, List.ofFn α])
        (residue f x.l _ hf (c.entry r α))
        (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (ν : Branch s) (g : Fin 64) (w : Fin (s.child ν.1 ν.2.1 ν.2.2 g).graph.nV)
    (v : {v : Fin nd.G.nV // lbl (coord hu ν.1) v = g})
    (hcw : (s.child ν.1 ν.2.1 ν.2.2 g).oldOrPacket w = .inl v) :
    let ch := s.child ν.1 ν.2.1 ν.2.2 g
    let p' := nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val)
    let hw_eq : ch.oldOrPacket.symm (.inl v) = w := by rw [← hcw, ch.oldOrPacket.symm_apply_apply]
    let pe : Fin (nd.G.deg v.val) ≃ Fin (ch.graph.deg w) :=
      (ch.ports v).trans (finCastEquiv (congrArg ch.graph.deg hw_eq))
    childVert x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w =
      (nd.verts v.val).pushChild p' (Nat.le_add_right ..) pe :=
  childVertAux_congr x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w hcw
    ((s.child ν.1 ν.2.1 ν.2.2 g).oldOrPacket.symm_apply_apply w)
    (by rw [← hcw, (s.child ν.1 ν.2.1 ν.2.2 g).oldOrPacket.symm_apply_apply])

theorem childVert_inr {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (oe : Fin E_pkt.tapeCount) (K_loc : ℕ)
    (nd : SoloNode x f (pktOKOf E_pkt oe K_loc x f hf))
    {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a} (s : Step lbl hu f x.l nd.pCurr)
    (ha_eq : a = D3Stopped.shift x.S nd.d)
    (hinc_le : ∀ i, nd.pCurr + increase nd.G.nE a u i ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d)
    (hpkt_eval : ∀ t k β g r α,
      let c := s.child t k β g
      let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
      RunsWithin E_pkt oe (Encoding.encodeList id [c.descriptor r, List.ofFn α])
        (residue f x.l _ hf (c.entry r α))
        (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (ν : Branch s) (g : Fin 64) (w : Fin (s.child ν.1 ν.2.1 ν.2.2 g).graph.nV)
    (r : Fin s.pk.count) (hcw : (s.child ν.1 ν.2.1 ν.2.2 g).oldOrPacket w = .inr r) :
    ∃ hpkt,
      let ch := s.child ν.1 ν.2.1 ν.2.2 g
      let p' := nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val)
      let hw_eq : ch.oldOrPacket.symm (.inr r) = w := by rw [← hcw, ch.oldOrPacket.symm_apply_apply]
      childVert x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w =
        SoloVert.pkt nd.d p' (ch.graph.deg (ch.oldOrPacket.symm (.inr r))) (ch.descriptor r)
          (Nat.lt_succ_self nd.d) le_rfl (ch.entry r) hpkt none (congrArg ch.graph.deg hw_eq) :=
  ⟨_, childVertAux_congr x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w hcw
    ((s.child ν.1 ν.2.1 ν.2.2 g).oldOrPacket.symm_apply_apply w)
    (by rw [← hcw, (s.child ν.1 ν.2.1 ν.2.2 g).oldOrPacket.symm_apply_apply])⟩

def childSoloNode {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (oe : Fin E_pkt.tapeCount) (K_loc : ℕ)
    (nd : SoloNode x f (pktOKOf E_pkt oe K_loc x f hf))
    {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a} (s : Step lbl hu f x.l nd.pCurr)
    (ha_eq : a = D3Stopped.shift x.S nd.d)
    (hbal : D2.Balanced nd.host 1 lbl)
    (hM_le : nd.G.nE ≤ x.S)
    (hinc_le : ∀ i, nd.pCurr + increase nd.G.nE a u i ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d)
    (hpkt_eval : ∀ t k β g r α,
      let c := s.child t k β g
      let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
      RunsWithin E_pkt oe (Encoding.encodeList id [c.descriptor r, List.ofFn α])
        (residue f x.l _ hf (c.entry r α))
        (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (_hu_pos : 1 ≤ u) (_hu_le_M : u ≤ nd.G.nE)
    (ν : Branch s) (g : Fin 64) :
    SoloNode x f (pktOKOf E_pkt oe K_loc x f hf) :=
  let c := s.child ν.1 ν.2.1 ν.2.2 g
  let p' := nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val)
  let kept := nd.pins.filter (fun pv => decide (lbl (coord hu ν.1) pv.2 = g))
  let pins' := childPins x nd s ν g
  have hkept_sub : ∀ pv ∈ kept, ∃ k_old : Fin nd.pins.length, nd.pins.get k_old = pv := by
    intro pv hpv
    have hmem := (List.mem_filter.mp hpv).1
    obtain ⟨k_old, rfl⟩ := List.mem_iff_get.mp hmem
    exact ⟨k_old, rfl⟩
  { d := nd.d + 1
    G := c.graph
    pCurr := p'
    pins := pins'
    pins_sorted := by
      have hfilt : kept.Pairwise (fun a b => a.1.val < b.1.val) := nd.pins_sorted.filter _
      have hatt : kept.attach.Pairwise (fun a b => a.1.1.val < b.1.1.val) := by
        have hmap : (kept.map fun a => a.1.val).Pairwise LT.lt := List.pairwise_map.mpr hfilt
        have heq : kept.attach.map (fun b => b.1.1.val) = kept.map (fun a => a.1.val) := by
          apply List.ext_getElem <;> simp
        exact List.pairwise_map.mp (heq ▸ hmap)
      dsimp only [pins', childPins, kept]
      rw [List.pairwise_map]
      exact hatt.imp (fun {x₁ x₂} hx => hx)
    host_inj := by
      intro k₁ k₂ hk
      have hk₁ : k₁.val < kept.length := k₁.isLt.trans_eq (childPins_length x nd s ν g)
      have hk₂ : k₂.val < kept.length := k₂.isLt.trans_eq (childPins_length x nd s ν g)
      have hk_eq : (kept[k₁.val]'hk₁).2 = (kept[k₂.val]'hk₂).2 := by
        have hget1 := congrArg Prod.snd (childPins_get x nd s ν g k₁)
        have hget2 := congrArg Prod.snd (childPins_get x nd s ν g k₂)
        change (pins'.get k₁).2 = _ at hget1
        change (pins'.get k₂).2 = _ at hget2
        rw [hget1, hget2] at hk
        exact congrArg Subtype.val (Sum.inl.inj (c.oldOrPacket.symm.injective hk))
      have hnd_vals : (kept.map Prod.snd).Nodup := by
        have hnd_orig : (nd.pins.map Prod.snd).Nodup := by
          refine List.nodup_iff_getElem?_ne_getElem?.mpr ?_
          intro i j hij hjlen heq
          have hjlen' : j < nd.pins.length := by simpa using hjlen
          have hilen : i < nd.pins.length := hij.trans hjlen'
          have hmi : i < (nd.pins.map Prod.snd).length := by simpa using hilen
          have hmj : j < (nd.pins.map Prod.snd).length := by simpa using hjlen'
          rw [List.getElem?_eq_getElem hmi, List.getElem?_eq_getElem hmj,
            List.getElem_map, List.getElem_map, Option.some.injEq] at heq
          have heq' : nd.host ⟨i, hilen⟩ = nd.host ⟨j, hjlen'⟩ := by
            simpa [SoloNode.host, List.get_eq_getElem] using heq
          have hinj := nd.host_inj ⟨i, hilen⟩ ⟨j, hjlen'⟩ heq'
          exact absurd (congrArg Fin.val hinj) (Nat.ne_of_lt hij)
        exact hnd_orig.sublist (List.Sublist.map _ List.filter_sublist)
      have helem : (kept.map Prod.snd).get ⟨k₁.val, by simp only [List.length_map]; exact hk₁⟩ =
          (kept.map Prod.snd).get ⟨k₂.val, by simp only [List.length_map]; exact hk₂⟩ := by
        simp only [List.get_eq_getElem, List.getElem_map]
        exact hk_eq
      exact Fin.ext (Fin.mk.inj (hnd_vals.injective_get helem))
    pinned_deg_pos := by
      intro k
      have hk : k.val < kept.length := k.isLt.trans_eq (childPins_length x nd s ν g)
      let pv := kept[k.val]'hk
      have hpv : pv ∈ kept := List.getElem_mem hk
      obtain ⟨k_old, hk_old⟩ := hkept_sub pv hpv
      have hpos : 1 ≤ nd.G.deg pv.2 := by rw [← hk_old]; exact nd.pinned_deg_pos k_old
      have hlbl : lbl (coord hu ν.1) pv.2 = g := of_decide_eq_true (List.mem_filter.mp hpv).2
      have hcard := Fintype.card_congr (c.ports ⟨pv.2, hlbl⟩)
      simp only [Fintype.card_fin] at hcard
      have hget := congrArg Prod.snd (childPins_get x nd s ν g k)
      change (pins'.get k).2 = _ at hget
      rw [hget, ← hcard]
      exact hpos
    pins_len_le := by
      have hbal_g := hbal (coord hu ν.1) g
      have hcard_kept : (Finset.univ.filter fun j : Fin nd.pins.length => lbl (coord hu ν.1) (nd.host j) = g).card =
          kept.length := by
        have hnd : (List.finRange nd.pins.length).Nodup := List.nodup_finRange _
        have h1 : (Finset.univ.filter fun j : Fin nd.pins.length => lbl (coord hu ν.1) (nd.host j) = g).card =
            ((List.finRange nd.pins.length).filter fun j => decide (lbl (coord hu ν.1) (nd.host j) = g)).length := by
          rw [← List.toFinset_card_of_nodup (hnd.filter _)]
          congr 1; ext j; simp
        rw [h1]
        have h2 : kept = ((List.finRange nd.pins.length).filter fun j =>
            decide (lbl (coord hu ν.1) (nd.host j) = g)).map (fun j => nd.pins.get j) := by
          dsimp only [kept]
          conv_lhs => rw [← List.map_get_finRange (l := nd.pins)]
          rw [List.filter_map]
          congr 1
        rw [h2, List.length_map]
      rw [hcard_kept] at hbal_g
      have ha_le : a ≤ D3Stopped.level x.S := ha_eq ▸ shift_le_level_solo x.S nd.d
      have hprev := nd.pins_len_le
      have hpins_len : pins'.length = kept.length := childPins_length x nd s ν g
      rw [hpins_len]
      have hdiv : (4 * x.m * x.k) / 32 ^ nd.d =
          32 * ((4 * x.m * x.k) / 32 ^ (nd.d + 1)) + ((4 * x.m * x.k) / 32 ^ nd.d) % 32 := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul]
        exact (Nat.div_add_mod _ 32).symm
      have hmod_lt : ((4 * x.m * x.k) / 32 ^ nd.d) % 32 ≤ 31 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
      have h32 : 32 * kept.length ≤ 32 * ((4 * x.m * x.k) / 32 ^ (nd.d + 1)) + 32 * (31 * (D3Stopped.level x.S + 2)) := by
        nlinarith only [hbal_g, hprev, hdiv, hmod_lt, ha_le]
      omega
    verts := childVert x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g
    pin_sync := by
      intro w
      dsimp only [pinSyncProp]
      cases h_w : c.oldOrPacket w with
      | inl v =>
        have hsync := nd.pin_sync v.val
        have hw_eq : c.oldOrPacket.symm (.inl v) = w := by rw [← h_w, c.oldOrPacket.symm_apply_apply]
        rw [childVert_inl x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w v h_w]
        cases hsv : nd.verts v.val with
        | pkt dCr pCr oD rD hdL hpL e0 hpkt pm hp =>
          cases pm <;>
          · simp only [SoloVert.pushChild]
            intro k hk
            have hk' : k.val < kept.length := k.isLt.trans_eq (childPins_length x nd s ν g)
            let pv := kept[k.val]'hk'
            have hget := congrArg Prod.snd (childPins_get x nd s ν g k)
            change (pins'.get k).2 = _ at hget
            rw [hget, ← hw_eq] at hk
            have hv_eq : pv.2 = v.val := congrArg Subtype.val (Sum.inl.inj (c.oldOrPacket.symm.injective hk))
            obtain ⟨k_old, hk_old⟩ := hkept_sub pv (List.getElem_mem hk')
            have : (nd.pins.get k_old).2 = v.val := by rw [hk_old, hv_eq]
            have hsync' := hsync; rw [hsv] at hsync'
            exact hsync' k_old this
        | orig v₀ hv₀ pinPort portMap hlen hports =>
          simp only [SoloVert.pushChild]
          have hsync' := hsync; rw [hsv] at hsync'
          dsimp only [pinSyncProp] at hsync'
          rw [hsync']
          constructor
          · rintro ⟨k_old, hk_old⟩
            have hmem : nd.pins.get k_old ∈ kept :=
              List.mem_filter.mpr ⟨List.get_mem _ _, decide_eq_true (by rw [hk_old]; exact v.property)⟩
            obtain ⟨k_idx, hk_idx, hk_eq⟩ := List.mem_iff_getElem.mp hmem
            have hk_idx' : k_idx < pins'.length := hk_idx.trans_eq (childPins_length x nd s ν g).symm
            refine ⟨⟨k_idx, hk_idx'⟩, ?_⟩
            have hget := congrArg Prod.snd (childPins_get x nd s ν g ⟨k_idx, hk_idx'⟩)
            change (pins'.get _).2 = _ at hget
            rw [hget, ← hw_eq]
            apply congrArg c.oldOrPacket.symm
            apply congrArg Sum.inl; apply Subtype.ext
            dsimp only; rw [hk_eq, hk_old]
          · rintro ⟨k, hk⟩
            have hk' : k.val < kept.length := k.isLt.trans_eq (childPins_length x nd s ν g)
            let pv := kept[k.val]'hk'
            have hget := congrArg Prod.snd (childPins_get x nd s ν g k)
            change (pins'.get k).2 = _ at hget
            rw [hget, ← hw_eq] at hk
            have hv_eq : pv.2 = v.val := congrArg Subtype.val (Sum.inl.inj (c.oldOrPacket.symm.injective hk))
            obtain ⟨k_old, hk_old⟩ := hkept_sub pv (List.getElem_mem hk')
            exact ⟨k_old, by rw [hk_old, hv_eq]⟩
      | inr r =>
        have hw_eq : c.oldOrPacket.symm (.inr r) = w := by rw [← h_w, c.oldOrPacket.symm_apply_apply]
        obtain ⟨hpkt, hr_eq⟩ := childVert_inr x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w r h_w
        rw [hr_eq]
        intro k
        have hget := congrArg Prod.snd (childPins_get x nd s ν g k)
        change (pins'.get k).2 = _ at hget
        rw [hget, ← hw_eq]
        intro h
        have := c.oldOrPacket.symm.injective h
        cases this
    hp_ge := nd.hp_ge.trans (Nat.le_add_right ..)
    hp_le := by simpa using hinc_le (AppendixD4.level ν.1.val)
    edges_le := by
      have h1 : c.graph.nE ≤ 3 * nd.G.nE / 32 := c.edges
      have h2 : 3 * nd.G.nE / 32 ≤ 3 * (x.S / 8 ^ nd.d) / 32 := by
        exact Nat.div_le_div_right (Nat.mul_le_mul_left 3 nd.edges_le)
      have hmul : 8 ^ nd.d * (x.S / 8 ^ nd.d) ≤ x.S := Nat.mul_div_le x.S (8 ^ nd.d)
      have hstep : 8 * (3 * (x.S / 8 ^ nd.d) / 32) ≤ x.S / 8 ^ nd.d := by omega
      have hcomb : 8 ^ (nd.d + 1) * c.graph.nE ≤ x.S := by
        calc 8 ^ (nd.d + 1) * c.graph.nE
            = 8 ^ nd.d * (8 * c.graph.nE) := by rw [pow_succ]; ring
          _ ≤ 8 ^ nd.d * (8 * (3 * (x.S / 8 ^ nd.d) / 32)) := by gcongr; exact h1.trans h2
          _ ≤ 8 ^ nd.d * (x.S / 8 ^ nd.d) := Nat.mul_le_mul_left _ hstep
          _ ≤ x.S := hmul
      exact (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).mpr (by simpa [mul_comm] using hcomb)
    verts_le := by
      have hcard := Fintype.card_congr c.oldOrPacket
      simp only [Fintype.card_fin, Fintype.card_sum] at hcard
      have hsub : Fintype.card {v : Fin nd.G.nV // lbl (coord hu ν.1) v = g} ≤ nd.G.nV := by
        simpa using Fintype.card_subtype_le (fun v : Fin nd.G.nV => lbl (coord hu ν.1) v = g)
      have ha_pos : 1 ≤ 2 ^ a := Nat.pow_pos (by decide)
      have hpkt_le : s.pk.count ≤ 3 * x.S := by
        calc s.pk.count ≤ s.pk.count * 2 ^ a := Nat.le_mul_of_pos_right _ ha_pos
          _ ≤ 3 * nd.G.nE := s.pk.bounded
          _ ≤ 3 * x.S := Nat.mul_le_mul_left 3 hM_le
      have hndv := nd.verts_le
      rw [hcard]
      calc Fintype.card {v : Fin nd.G.nV // lbl (coord hu ν.1) v = g} + s.pk.count
          ≤ nd.G.nV + 3 * x.S := Nat.add_le_add hsub hpkt_le
        _ ≤ x.G.nV + nd.d * (3 * x.S) + 3 * x.S := Nat.add_le_add_right hndv _
        _ = x.G.nV + (nd.d + 1) * (3 * x.S) := by ring
    deg_le := by
      apply Finset.sup_le
      intro w _
      cases h_w : c.oldOrPacket w with
      | inl v =>
        have hw_eq : c.oldOrPacket.symm (.inl v) = w := by rw [← h_w, c.oldOrPacket.symm_apply_apply]
        have hcard := Fintype.card_congr (c.ports v)
        simp only [Fintype.card_fin, hw_eq] at hcard
        have hle : nd.G.deg v.val ≤ nd.G.maxDeg := Finset.le_sup (Finset.mem_univ v.val)
        rw [← hcard]
        refine hle.trans (nd.deg_le.trans ?_)
        apply max_le_max le_rfl
        simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        split_ifs with hd0
        · exact Nat.zero_le _
        · exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) (shift_mono_solo x.S (by omega)))
      | inr r =>
        have hw_eq : c.oldOrPacket.symm (.inr r) = w := by rw [← h_w, c.oldOrPacket.symm_apply_apply]
        have hpd : c.graph.deg w ≤ 2 * 2 ^ D3Stopped.shift x.S nd.d :=
          ha_eq ▸ (hw_eq ▸ c.packetDeg r)
        simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        exact hpd.trans (le_max_right _ _) }

end

end ActiveStep

end DetDLP.D4SoloStep


