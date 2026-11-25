-- Prove2me | Definitions.Def_DetDLP_D4SoloStepEq
-- name    : DetDLP_D4SoloStepEq
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T22:06:10.933069+00:00
-- url     : https://prove2.me/theorems/7e840177-a50d-4520-b8df-c7158d581328
-- title:
--   Bit-Encoding and Tensor Contraction Equivalence for Solo Child Nodes
-- statement:
--   Proves bit-level equality between childSoloNode work-item encodings and D4RankWalker.childWord, shows D4RankWalker.children reconstructs all 64 child node encodings, and proves tensor contraction preservation between childSoloNode and Step.child under boundary assignment lifting.
-- source:
--   prove2me_m14_solo/Definitions/Def_DetDLP_D4SoloStepEq.lean

import Definitions.Def_DetDLP_D4SoloStep

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace DetDLP.D4SoloStepEq

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

section StepEquivalence

noncomputable section

private theorem idxOf_eq_of_first {xs : List ℕ} {a i : ℕ} (hi : i < xs.length)
    (hget : xs[i]'hi = a) (hfirst : ∀ j (hj : j < i), xs[j]'(lt_trans hj hi) ≠ a) :
    xs.idxOf a = i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hget
      subst hget
      simp [List.idxOf, List.findIdx_cons]
    | succ i =>
      have hne : x ≠ a := by
        simpa using hfirst 0 (Nat.zero_lt_succ i)
      have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
      have hget' : xs[i]'hi' = a := by simpa using hget
      have hfirst' : ∀ j (hj : j < i), xs[j]'(lt_trans hj hi') ≠ a := fun j hj => by
        simpa using hfirst (j + 1) (Nat.succ_lt_succ hj)
      change (x :: xs).findIdx (· == a) = i + 1
      rw [List.findIdx_cons, beq_eq_false_iff_ne.mpr hne]
      exact congrArg (· + 1) (ih hi' hget' hfirst')

theorem childSoloNode_bits_eq {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (oe : Fin E_pkt.tapeCount) (K_loc : ℕ)
    (nd : SoloNode x f (pktOKOf E_pkt oe K_loc x f hf))
    {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a} (s : Step lbl hu f x.l nd.pCurr)
    (ha_eq : a = D3Stopped.shift x.S nd.d)
    (hbal : D2.Balanced nd.host 1 lbl) (hM_le : nd.G.nE ≤ x.S)
    (hinc_le : ∀ i, nd.pCurr + increase nd.G.nE a u i ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d)
    (hpkt_eval : ∀ t k β g r α,
      let c := s.child t k β g
      let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
      RunsWithin E_pkt oe (Encoding.encodeList id [c.descriptor r, List.ofFn α])
        (residue f x.l _ hf (c.entry r α))
        (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (hu_pos : 1 ≤ u) (hu_le_M : u ≤ nd.G.nE)
    (ν : Branch s) (g : Fin 64) :
    (childSoloNode x hf E_pkt oe K_loc nd s ha_eq hbal hM_le hinc_le hpkt_eval hdeg_f hu_pos hu_le_M ν g).toWorkItem.bits =
      childWord nd.toWorkItem.bits (nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val))
        ((s.child ν.1 ν.2.1 ν.2.2 g).bits) := by
  let ch := s.child ν.1 ν.2.1 ν.2.2 g
  let p' := nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val)
  let cnd := childSoloNode x hf E_pkt oe K_loc nd s ha_eq hbal hM_le hinc_le hpkt_eval hdeg_f hu_pos hu_le_M ν g
  let kept := nd.pins.filter (fun pv => decide (lbl (coord hu ν.1) pv.2 = g))
  let records := unpack (fld ch.bits 1)
  have hrecords : records = List.ofFn fun w : Fin ch.graph.nV => match ch.oldOrPacket w with
      | .inl v => Encoding.encodeList id [[false], countWord v.val.val,
          encodeNatListBin (List.ofFn fun j => (ch.ports v j).val)]
      | .inr r => Encoding.encodeList id [[true], countWord r.val, ch.descriptor r] := by
    dsimp only [records, Child.bits]
    change unpack (fld (pack [ch.graph.encode, pack (List.ofFn _)]) 1) = _
    simp only [fld_pack, List.getD_cons_succ, List.getD_cons_zero, unpack_pack]
    congr 1; funext w
    cases ch.oldOrPacket w <;> rfl
  have hkeys : (records.map fun r => if (fld r 0).headD false then 0 else num r 1 + 1) =
      List.ofFn fun w : Fin ch.graph.nV => match ch.oldOrPacket w with
        | .inl v => v.val.val + 1
        | .inr _ => 0 := by
    rw [hrecords, List.map_ofFn]
    congr 1; funext w
    dsimp only [Function.comp_apply]
    cases ch.oldOrPacket w with
    | inl v =>
      change (if (fld (pack [[false], countWord v.val.val,
          encodeNatListBin (List.ofFn fun j => (ch.ports v j).val)]) 0).headD false then 0 else
        num (pack [[false], countWord v.val.val,
          encodeNatListBin (List.ofFn fun j => (ch.ports v j).val)]) 1 + 1) = v.val.val + 1
      simp [fld_pack, num]
    | inr r =>
      change (if (fld (pack [[true], countWord r.val, ch.descriptor r]) 0).headD false then 0 else
        num (pack [[true], countWord r.val, ch.descriptor r]) 1 + 1) = 0
      simp [fld_pack]
  have hdepth : num nd.toWorkItem.bits 0 = nd.d := by
    simp [SoloNode.toWorkItem, WorkItem.bits, num, fld_pack]
  have hch_g : fld ch.bits 0 = ch.graph.encode := by
    change fld (pack [ch.graph.encode, _]) 0 = ch.graph.encode
    simp [fld_pack]
  have h3 : (childPins x nd s ν g).map (fun pv => encodeNatListBin [pv.1.val, pv.2.val]) =
      ((unpack (fld nd.toWorkItem.bits 3)).filter fun h =>
        (records.map fun r => if (fld r 0).headD false then 0 else num r 1 + 1).any
          (fun k => k == num h 1 + 1)).map
        fun h => encodeNatListBin [num h 0,
          (records.map fun r => if (fld r 0).headD false then 0 else num r 1 + 1).idxOf (num h 1 + 1)] := by
    have hnd_pins : unpack (fld nd.toWorkItem.bits 3) =
        nd.pins.map (fun pv => encodeNatListBin [pv.1.val, pv.2.val]) := by
      simp [SoloNode.toWorkItem, WorkItem.bits, fld_pack, unpack_pack]
    rw [hnd_pins, List.filter_map]
    have hflt_eq : (nd.pins.filter fun pv =>
        (records.map fun r => if (fld r 0).headD false then 0 else num r 1 + 1).any
          (fun k => k == num (encodeNatListBin [pv.1.val, pv.2.val]) 1 + 1)) = kept := by
      apply List.filter_congr
      intro pv _
      rw [hkeys]
      have hnum : num (encodeNatListBin [pv.1.val, pv.2.val]) 1 = pv.2.val := by
        simp [num, fld_pack,
          show encodeNatListBin [pv.1.val, pv.2.val] = pack [countWord pv.1.val, countWord pv.2.val] from rfl]
      rw [hnum]
      apply Bool.eq_iff_iff.mpr
      rw [List.any_eq_true]
      simp only [List.mem_ofFn, beq_iff_eq]
      constructor
      · rintro ⟨_, ⟨w, rfl⟩, hw⟩
        cases hcw : ch.oldOrPacket w with
        | inl v =>
          rw [hcw] at hw
          have hv_eq : v.val = pv.2 := Fin.ext (Nat.succ.inj hw)
          exact decide_eq_true (hv_eq ▸ v.property)
        | inr r => simp [hcw] at hw
      · intro hdec
        have hlbl : lbl (coord hu ν.1) pv.2 = g := of_decide_eq_true hdec
        refine ⟨_, ⟨ch.oldOrPacket.symm (.inl ⟨pv.2, hlbl⟩), rfl⟩, ?_⟩
        simp [ch.oldOrPacket.apply_symm_apply]
    simp only [Function.comp_def]
    rw [hflt_eq, List.map_map]
    have hattach : (childPins x nd s ν g).map (fun pv => encodeNatListBin [pv.1.val, pv.2.val]) =
        kept.attach.map (fun ⟨pv, hpv⟩ =>
          encodeNatListBin [pv.1.val, (ch.oldOrPacket.symm (.inl ⟨pv.2,
            of_decide_eq_true (List.mem_filter.mp hpv).2⟩)).val]) := by
      simp [childPins, kept, ch]
    rw [hattach]
    apply List.ext_getElem
    · simp
    · intro k hk₁ hk₂
      simp only [List.length_map, List.length_attach] at hk₁ hk₂
      simp only [List.getElem_map, List.getElem_attach, Function.comp_apply]
      let pv := kept[k]'hk₁
      have hpv : pv ∈ kept := List.getElem_mem hk₁
      have hlbl : lbl (coord hu ν.1) pv.2 = g := of_decide_eq_true (List.mem_filter.mp hpv).2
      have hnum0 : num (encodeNatListBin [pv.1.val, pv.2.val]) 0 = pv.1.val := by
        simp [num, show encodeNatListBin [pv.1.val, pv.2.val] = pack [countWord pv.1.val, countWord pv.2.val] from rfl,
          fld_pack]
      have hnum1 : num (encodeNatListBin [pv.1.val, pv.2.val]) 1 = pv.2.val := by
        simp [num, show encodeNatListBin [pv.1.val, pv.2.val] = pack [countWord pv.1.val, countWord pv.2.val] from rfl,
          fld_pack]
      rw [hnum0, hnum1, hkeys]
      let keysFn : Fin ch.graph.nV → ℕ := fun w => match ch.oldOrPacket w with
        | .inl v => v.val.val + 1
        | .inr _ => 0
      let w₀ : Fin ch.graph.nV := ch.oldOrPacket.symm (.inl ⟨pv.2, hlbl⟩)
      have hw₀_lt : w₀.val < (List.ofFn keysFn).length := by simp [w₀.isLt]
      have hw₀_val : (List.ofFn keysFn)[w₀.val]'hw₀_lt = pv.2.val + 1 := by
        simp [keysFn, w₀, ch.oldOrPacket.apply_symm_apply]
      have hunique : ∀ k' (hk' : k' < w₀.val), (List.ofFn keysFn)[k']'(lt_trans hk' hw₀_lt) ≠ pv.2.val + 1 := by
        intro k' hk' heq
        have hk'_lt : k' < ch.graph.nV := lt_trans hk' w₀.isLt
        simp only [List.getElem_ofFn] at heq
        cases hck : ch.oldOrPacket ⟨k', hk'_lt⟩ with
        | inr r => simp [keysFn, hck] at heq
        | inl v =>
          simp only [keysFn, hck, Nat.succ.injEq] at heq
          have hv_eq : v = ⟨pv.2, hlbl⟩ := Subtype.ext (Fin.ext heq)
          have hfin_eq : (⟨k', hk'_lt⟩ : Fin ch.graph.nV) = w₀ := by
            rw [← ch.oldOrPacket.symm_apply_apply ⟨k', hk'_lt⟩, hck, hv_eq]
          have : k' = w₀.val := congrArg Fin.val hfin_eq
          omega
      have hidx_eq : (List.ofFn keysFn).idxOf (pv.2.val + 1) = w₀.val :=
        idxOf_eq_of_first hw₀_lt hw₀_val hunique
      rw [hidx_eq]
  have h4 : (List.ofFn fun w => (childVert x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w).specBits) =
      records.map fun r => if (fld r 0).headD false then pack [[true], fld r 2]
        else mapped (fld (fld nd.toWorkItem.bits 4) (num r 1)) (fld r 2) := by
    rw [hrecords, List.map_ofFn]
    apply List.ext_getElem
    · simp [ch]
    · intro wIdx hw₁ hw₂
      have hw_ch : wIdx < ch.graph.nV := by simpa only [List.length_ofFn] using hw₁
      let w : Fin ch.graph.nV := ⟨wIdx, hw_ch⟩
      simp only [List.getElem_ofFn, Function.comp_apply]
      cases hcw : ch.oldOrPacket w with
      | inl v =>
        have hw_eq : ch.oldOrPacket.symm (.inl v) = w := by rw [← hcw, ch.oldOrPacket.symm_apply_apply]
        let pe : Fin (nd.G.deg v.val) ≃ Fin (ch.graph.deg w) :=
          (ch.ports v).trans (finCastEquiv (congrArg ch.graph.deg hw_eq))
        have hinl := childVert_inl x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w v hcw
        dsimp only at hinl
        rw [hinl]
        have hpe_eq : (List.ofFn fun j => (pe j).val) = List.ofFn fun j => (ch.ports v j).val := by
          apply List.ext_getElem
          · simp
          · intro j hj₁ hj₂
            simp [pe, finCastEquiv]
        have hnd_v : fld (fld nd.toWorkItem.bits 4) v.val.val = (nd.verts v.val).specBits := by
          simp only [SoloNode.toWorkItem, WorkItem.bits, fld_pack, List.getD_cons_succ,
            List.getD_cons_zero]
          have hlen : v.val.val < (List.ofFn fun u : Fin nd.G.nV => (nd.verts u).specBits).length := by
            simp [v.val.isLt]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, List.getElem_ofFn, Option.getD_some]
        change ((nd.verts v.val).pushChild p' (Nat.le_add_right ..) pe).specBits =
          if (fld (pack [[false], countWord v.val.val, encodeNatListBin (List.ofFn fun j => (ch.ports v j).val)]) 0).headD false then _
          else mapped (fld (fld nd.toWorkItem.bits 4)
            (num (pack [[false], countWord v.val.val, encodeNatListBin (List.ofFn fun j => (ch.ports v j).val)]) 1))
            (fld (pack [[false], countWord v.val.val, encodeNatListBin (List.ofFn fun j => (ch.ports v j).val)]) 2)
        have hhd_f : ¬((fld (pack [[false], countWord v.val.val, encodeNatListBin (List.ofFn fun j => (ch.ports v j).val)]) 0).headD false = true) := by
          simp [fld_pack]
        have hnum_v : num (pack [[false], countWord v.val.val, encodeNatListBin (List.ofFn fun j => (ch.ports v j).val)]) 1 =
            v.val.val := by
          simp [num, fld_pack]
        have hfld_p : fld (pack [[false], countWord v.val.val, encodeNatListBin (List.ofFn fun j => (ch.ports v j).val)]) 2 =
            encodeNatListBin (List.ofFn fun j => (ch.ports v j).val) := by
          simp [fld_pack]
        rw [if_neg hhd_f, SoloVert.pushChild_specBits, hpe_eq, hnum_v, hfld_p, hnd_v]
      | inr r =>
        obtain ⟨hpkt, hr_eq⟩ := childVert_inr x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w r hcw
        dsimp only at hr_eq
        rw [hr_eq]
        change (SoloVert.pkt _ _ _ (ch.descriptor r) _ _ _ _ none _).specBits =
          if (fld (pack [[true], countWord r.val, ch.descriptor r]) 0).headD false then
            pack [[true], fld (pack [[true], countWord r.val, ch.descriptor r]) 2]
          else _
        simp [SoloVert.specBits, fld_pack]
  have hcnd_bits := soloNode_toWorkItem_bits cnd (nd.d + 1) ch.graph p' (childPins x nd s ν g)
    (childVert x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g)
    rfl rfl rfl HEq.rfl HEq.rfl
  rw [hcnd_bits]
  unfold childWord
  rw [hdepth, hch_g]
  dsimp only [records] at h3 h4
  rw [h3, h4]

theorem childSoloNode_children_eq {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (oe : Fin E_pkt.tapeCount) (K_loc : ℕ)
    (nd : SoloNode x f (pktOKOf E_pkt oe K_loc x f hf))
    {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a} (s : Step lbl hu f x.l nd.pCurr)
    (ha_eq : a = D3Stopped.shift x.S nd.d)
    (hbal : D2.Balanced nd.host 1 lbl) (hM_le : nd.G.nE ≤ x.S)
    (hinc_le : ∀ i, nd.pCurr + increase nd.G.nE a u i ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d)
    (hpkt_eval : ∀ t k β g r α,
      let c := s.child t k β g
      let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
      RunsWithin E_pkt oe (Encoding.encodeList id [c.descriptor r, List.ofFn α])
        (residue f x.l _ hf (c.entry r α))
        (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (hu_pos : 1 ≤ u) (hu_le_M : u ≤ nd.G.nE)
    (ν : Branch s) :
    List.ofFn (fun g : Fin 64 =>
      (childSoloNode x hf E_pkt oe K_loc nd s ha_eq hbal hM_le hinc_le hpkt_eval hdeg_f hu_pos hu_le_M ν g).toWorkItem.bits) =
      children nd.toWorkItem.bits (s.bits hf ν) := by
  unfold children Step.bits
  have hp : num (fld (Encoding.encodeList id [encodeNatListBin [ν.1.val.val, ν.2.1.val, ν.2.2.val,
      AppendixD4.level ν.1.val, nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val)],
      residue f x.l (nd.pCurr + AppendixD4.loss nd.G.nE a u 0) hf (AdjoinRoot.of _ (s.weight ν.1 ν.2.1)),
      encodeNatListBin (List.ofFn fun z => ((s.modes ν.1).tuples ν.2.2).val z |>.val),
      Encoding.encodeList id (List.ofFn fun g => (s.child ν.1 ν.2.1 ν.2.2 g).bits)]) 0) 4 =
      nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val) := by
    change num (fld (pack [encodeNatListBin [_, _, _, _, _], _, _, _]) 0) 4 = _
    simp [fld_pack, num, show ∀ xs : List ℕ, encodeNatListBin xs = pack (xs.map countWord) from fun xs => by
      induction xs with | nil => rfl | cons _ _ ih => simp [encodeNatListBin, Encoding.encodeList, pack] at *; exact ih]
  rw [hp]
  apply List.ext_getElem
  · simp
  · intro g hg₁ hg₂
    have hg : g < 64 := by simpa using hg₁
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    have hch : fld (fld (Encoding.encodeList id [encodeNatListBin [ν.1.val.val, ν.2.1.val, ν.2.2.val,
        AppendixD4.level ν.1.val, nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val)],
        residue f x.l (nd.pCurr + AppendixD4.loss nd.G.nE a u 0) hf (AdjoinRoot.of _ (s.weight ν.1 ν.2.1)),
        encodeNatListBin (List.ofFn fun z => ((s.modes ν.1).tuples ν.2.2).val z |>.val),
        Encoding.encodeList id (List.ofFn fun g => (s.child ν.1 ν.2.1 ν.2.2 g).bits)]) 3) g =
        (s.child ν.1 ν.2.1 ν.2.2 ⟨g, hg⟩).bits := by
      change fld (fld (pack [_, _, _, pack (List.ofFn fun g : Fin 64 => (s.child ν.1 ν.2.1 ν.2.2 g).bits)]) 3) g = _
      simp only [fld_pack, List.getD_cons_succ, List.getD_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hg]), List.getElem_ofFn, Option.getD_some]
    rw [hch]
    exact childSoloNode_bits_eq x hf E_pkt oe K_loc nd s ha_eq hbal hM_le hinc_le hpkt_eval hdeg_f hu_pos hu_le_M ν ⟨g, hg⟩

set_option backward.isDefEq.respectTransparency false in
private theorem pin_openTensor_child {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree)
    (E_pkt : PrimitiveMachine) (oe : Fin E_pkt.tapeCount) (K_loc : ℕ)
    (nd : SoloNode x f (pktOKOf E_pkt oe K_loc x f hf))
    {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a} (s : Step lbl hu f x.l nd.pCurr)
    (ha_eq : a = D3Stopped.shift x.S nd.d)
    (hbal : D2.Balanced nd.host 1 lbl) (hM_le : nd.G.nE ≤ x.S)
    (hinc_le : ∀ i, nd.pCurr + increase nd.G.nE a u i ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d)
    (hpkt_eval : ∀ t k β g r α,
      let c := s.child t k β g
      let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
      RunsWithin E_pkt oe (Encoding.encodeList id [c.descriptor r, List.ofFn α])
        (residue f x.l _ hf (c.entry r α))
        (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (hu_pos : 1 ≤ u) (hu_le_M : u ≤ nd.G.nE)
    (ν : Branch s) (g : Fin 64) (η : Fin (4 * x.m * x.k) → Bool)
    (w : Fin (s.child ν.1 ν.2.1 ν.2.2 g).graph.nV)
    (β : Fin ((s.child ν.1 ν.2.1 ν.2.2 g).graph.deg w) → Bool) :
    let ch := s.child ν.1 ν.2.1 ν.2.2 g
    let p' := nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val)
    let cnd := childSoloNode x hf E_pkt oe K_loc nd s ha_eq hbal hM_le hinc_le hpkt_eval hdeg_f hu_pos hu_le_M ν g
    pin (cnd.openTensor hf) (fun k => η (cnd.pins.get k).1) w β =
      ch.tensor (lift hf p') (pin (nd.openTensor hf) (fun k => η (nd.pins.get k).1)) w β := by
  intro ch p' cnd
  have hcnd_v : cnd.verts w = childVert x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w := rfl
  cases hcw : ch.oldOrPacket w with
  | inl v =>
    rw [child_tensor_inl ch (lift hf p') (pin (nd.openTensor hf) (fun k => η (nd.pins.get k).1)) w v hcw β]
    unfold pin SoloNode.openTensor
    dsimp only
    rw [hcnd_v]
    have hw_eq : ch.oldOrPacket.symm (.inl v) = w := by rw [← hcw, ch.oldOrPacket.symm_apply_apply]
    let pe : Fin (nd.G.deg v.val) ≃ Fin (ch.graph.deg w) :=
      (ch.ports v).trans (finCastEquiv (congrArg ch.graph.deg hw_eq))
    have hinl := childVert_inl x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w v hcw
    dsimp only at hinl
    rw [hinl]
    rw [SoloVert.pushChild_eval hf hdeg nd.hp_ge p' (Nat.le_add_right ..) pe]
    have hpin_eq :
        (if h : ∃ k : Fin cnd.pins.length, cnd.host k = w then
          η (cnd.pins.get (Classical.choose h)).1 else false) =
        (if h : ∃ k : Fin nd.pins.length, nd.host k = v.val then
          η (nd.pins.get (Classical.choose h)).1 else false) := by
      by_cases h1 : ∃ k : Fin cnd.pins.length, cnd.host k = w
      · have h2 : ∃ k : Fin nd.pins.length, nd.host k = v.val := by
          obtain ⟨k, hk⟩ := h1
          have hk' : k.val < (nd.pins.filter fun pv => decide (lbl (coord hu ν.1) pv.2 = g)).length := by
            simpa [cnd, childSoloNode, childPins_length] using k.isLt
          let kept := nd.pins.filter fun pv => decide (lbl (coord hu ν.1) pv.2 = g)
          let pv := kept[k.val]'hk'
          have hpv_mem := List.getElem_mem hk'
          obtain ⟨k_old, hk_old⟩ := List.mem_iff_get.mp (List.mem_filter.mp hpv_mem).1
          have hget_cnd := congrArg Prod.snd (childPins_get x nd s ν g k)
          change cnd.host k = _ at hget_cnd
          rw [hget_cnd, ← hw_eq] at hk
          have hv_eq : pv.2 = v.val := congrArg Subtype.val (Sum.inl.inj (ch.oldOrPacket.symm.injective hk))
          exact ⟨k_old, by unfold SoloNode.host; rw [hk_old]; exact hv_eq⟩
        rw [dif_pos h1, dif_pos h2]
        let k1 := Classical.choose h1
        let k2 := Classical.choose h2
        have hk1 : cnd.host k1 = w := Classical.choose_spec h1
        have hk2 : nd.host k2 = v.val := Classical.choose_spec h2
        have h1_pin : (cnd.pins.get k1).1 = (nd.pins.get k2).1 := by
          have hk1' : k1.val < (nd.pins.filter fun pv => decide (lbl (coord hu ν.1) pv.2 = g)).length := by
            simpa [cnd, childSoloNode, childPins_length] using k1.isLt
          let kept := nd.pins.filter fun pv => decide (lbl (coord hu ν.1) pv.2 = g)
          let pv := kept[k1.val]'hk1'
          have hpv_mem := List.getElem_mem hk1'
          obtain ⟨k_old, hk_old⟩ := List.mem_iff_get.mp (List.mem_filter.mp hpv_mem).1
          have hget1_1 := congrArg Prod.fst (childPins_get x nd s ν g k1)
          have hget1_2 := congrArg Prod.snd (childPins_get x nd s ν g k1)
          change (cnd.pins.get k1).1 = pv.1 at hget1_1
          change cnd.host k1 = _ at hget1_2
          rw [hget1_2, ← hw_eq] at hk1
          have hv_eq : pv.2 = v.val := congrArg Subtype.val (Sum.inl.inj (ch.oldOrPacket.symm.injective hk1))
          have hk_eq : k_old = k2 := nd.host_inj k_old k2 (by
            have hko : (nd.pins.get k_old).2 = v.val := by rw [hk_old]; exact hv_eq
            exact hko.trans hk2.symm)
          have hpv1 : pv.1 = (nd.pins.get k_old).1 := congrArg Prod.fst hk_old.symm
          rw [hget1_1, hpv1, hk_eq]
        exact congrArg η h1_pin
      · have h2 : ¬ ∃ k : Fin nd.pins.length, nd.host k = v.val := by
          rintro ⟨k_old, hk_old⟩
          let kept := nd.pins.filter fun pv => decide (lbl (coord hu ν.1) pv.2 = g)
          have hk_old2 : (nd.pins.get k_old).2 = v.val := hk_old
          have hmem : nd.pins.get k_old ∈ kept :=
            List.mem_filter.mpr ⟨List.get_mem _ _, decide_eq_true (by rw [hk_old2]; exact v.property)⟩
          obtain ⟨k_idx, hk_idx, hkeq⟩ := List.mem_iff_getElem.mp hmem
          apply h1
          refine ⟨⟨k_idx, by simpa [cnd, childSoloNode, childPins_length] using hk_idx⟩, ?_⟩
          have hget := congrArg Prod.snd (childPins_get x nd s ν g ⟨k_idx, by simpa [cnd, childSoloNode, childPins_length] using hk_idx⟩)
          change cnd.host _ = _ at hget
          rw [hget, ← hw_eq]
          apply congrArg ch.oldOrPacket.symm
          apply congrArg Sum.inl; apply Subtype.ext
          dsimp only; rw [hkeq]; exact hk_old
        rw [dif_neg h1, dif_neg h2]
    rw [hpin_eq]
    rfl
  | inr r =>
    rw [child_tensor_inr ch (lift hf p') (pin (nd.openTensor hf) (fun k => η (nd.pins.get k).1)) w r hcw β]
    unfold pin SoloNode.openTensor
    dsimp only
    rw [hcnd_v]
    obtain ⟨hpkt, hr_eq⟩ := childVert_inr x hf E_pkt oe K_loc nd s ha_eq hinc_le hpkt_eval hdeg_f ν g w r hcw
    dsimp only at hr_eq
    rw [hr_eq]
    change lift hf p' (ch.entry r fun i => β (Fin.cast _ i)) = _
    rw [self_lift hf]

theorem childSoloNode_tensor_eq {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree)
    (E_pkt : PrimitiveMachine) (oe : Fin E_pkt.tapeCount) (K_loc : ℕ)
    (nd : SoloNode x f (pktOKOf E_pkt oe K_loc x f hf))
    {a u : ℕ} {lbl : Label a nd.G} {hu : u ≤ a} (s : Step lbl hu f x.l nd.pCurr)
    (ha_eq : a = D3Stopped.shift x.S nd.d)
    (hbal : D2.Balanced nd.host 1 lbl) (hM_le : nd.G.nE ≤ x.S)
    (hinc_le : ∀ i, nd.pCurr + increase nd.G.nE a u i ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d)
    (hpkt_eval : ∀ t k β g r α,
      let c := s.child t k β g
      let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
      RunsWithin E_pkt oe (Encoding.encodeList id [c.descriptor r, List.ofFn α])
        (residue f x.l _ hf (c.entry r α))
        (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (hu_pos : 1 ≤ u) (hu_le_M : u ≤ nd.G.nE)
    (ν : Branch s) (g : Fin 64) (η : Fin (4 * x.m * x.k) → Bool) :
    let ch := s.child ν.1 ν.2.1 ν.2.2 g
    let p' := nd.pCurr + increase nd.G.nE a u (AppendixD4.level ν.1.val)
    let cnd := childSoloNode x hf E_pkt oe K_loc nd s ha_eq hbal hM_le hinc_le hpkt_eval hdeg_f hu_pos hu_le_M ν g
    pin (cnd.openTensor hf) (fun k => η (cnd.pins.get k).1) =
      ch.tensor (lift hf p') (pin (nd.openTensor hf) (fun k => η (nd.pins.get k).1)) := by
  intro ch p' cnd
  funext w β
  exact pin_openTensor_child x hf hdeg E_pkt oe K_loc nd s ha_eq hbal hM_le hinc_le hpkt_eval hdeg_f hu_pos hu_le_M ν g η w β

end

end StepEquivalence

end DetDLP.D4SoloStepEq


