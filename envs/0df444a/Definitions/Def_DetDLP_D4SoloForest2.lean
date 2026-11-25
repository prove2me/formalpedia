-- Prove2me | Definitions.Def_DetDLP_D4SoloForest2
-- name    : DetDLP_D4SoloForest2
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T22:49:35.226822+00:00
-- url     : https://prove2.me/theorems/b2f1202b-2e9e-4279-8a8b-bb3187fc3d8b
-- title:
--   Leaf Certificates, Slot/Leaf Accounting, and Fuel-Bounded Unrolling
-- statement:
--   Establishes boundary-pin partition uniqueness, defines SoloLeafData and WorkCertItem, implements fuel-bounded prefix-peeling unrollCertFuel with its remaining-slot and remaining-leaf invariants.
-- source:
--   prove2me_m14_solo/Definitions/Def_DetDLP_D4SoloForest2.lean

import Definitions.Def_DetDLP_D4SoloForest
import Definitions.Def_DetDLP_D4RawGuard
import Definitions.Def_DetDLP_D4UnrollBudget
import Definitions.Def_DetDLP_D4WalkerTranscriptV2
import Theorems.Thm_DetDLP_d4_raw_weight_cleared_identity
import Theorems.Thm_DetDLP_d4_unroll_tree_bit_budget

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace DetDLP.D4SoloForest

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4GuardTree.Expansion DetDLP.D4SoloRaw DetDLP.D4SoloNode
open DetDLP.D4SoloRoot DetDLP.D4SoloStep DetDLP.D4SoloStepEq DetDLP.D4SoloTree
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

noncomputable section

section PinPartition

def pinFirsts {C c : ℕ} {x : Input C c} {f : ℤ[X]} {PktOK : PktPred f x.l}
    (ns : List (SoloNode x f PktOK)) : List (Fin (4 * x.m * x.k)) :=
  ns.flatMap fun nd => nd.pins.map Prod.fst

private theorem flatMap_finRange_cons {α : Type} (n : ℕ) (g₀ : Fin n) (a : α)
    (L : Fin n → List α) :
    List.Perm ((List.finRange n).flatMap fun g => if g = g₀ then a :: L g else L g)
      (a :: (List.finRange n).flatMap L) := by
  have hmem : g₀ ∈ List.finRange n := List.mem_finRange g₀
  have hnodup : (List.finRange n).Nodup := List.nodup_finRange n
  revert hmem hnodup
  generalize List.finRange n = gs
  intro hmem hnodup
  induction gs with
  | nil => cases hmem
  | cons g gs ih =>
    rw [List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · simp only [List.flatMap_cons, ↓reduceIte, List.cons_append]
      apply List.Perm.cons
      have heq : (gs.flatMap fun g' => if g' = g₀ then a :: L g' else L g') = gs.flatMap L := by
        apply List.flatMap_congr
        intro g' hg'
        have hne : g' ≠ g₀ := fun h => hnodup.1 (h ▸ hg')
        simp [hne]
      rw [heq]
    · have hne : g ≠ g₀ := fun h => hnodup.1 (h ▸ hmem')
      simp only [List.flatMap_cons, hne, ↓reduceIte]
      exact (List.Perm.append_left (L g) (ih hmem' hnodup.2)).trans List.perm_middle

private theorem filter_bucket_perm {α β : Type} (n : ℕ) (cls : α → Fin n) (f : α → β)
    (xs : List α) :
    List.Perm ((List.finRange n).flatMap fun g => (xs.filter (fun z => decide (cls z = g))).map f)
      (xs.map f) := by
  induction xs with
  | nil => simp
  | cons z zs ih =>
    have hcongr : ((List.finRange n).flatMap fun g =>
        ((z :: zs).filter (fun w => decide (cls w = g))).map f) =
      ((List.finRange n).flatMap fun g =>
        if g = cls z then f z :: (zs.filter (fun w => decide (cls w = g))).map f
        else (zs.filter (fun w => decide (cls w = g))).map f) := by
      apply List.flatMap_congr
      intro g _
      by_cases h : cls z = g
      · simp [h]
      · have hne : g ≠ cls z := Ne.symm h
        simp [h, hne]
    rw [hcongr, List.map_cons]
    exact (flatMap_finRange_cons n (cls z) (f z) _).trans (ih.cons (f z))

theorem childPins_pinFirsts_perm {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
    (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd)
    (ν : Branch cert.s) :
    List.Perm (pinFirsts (List.ofFn fun g : Fin 64 => cert.childNode ν g))
      (nd.pins.map Prod.fst) := by
  unfold pinFirsts
  rw [List.ofFn_eq_map, List.flatMap_map]
  have hmap : ∀ g : Fin 64, (cert.childNode ν g).pins.map Prod.fst =
      (nd.pins.filter (fun pv => decide (cert.lbl (coord cert.hu ν.1) pv.2 = g))).map Prod.fst := by
    intro g
    change (childPins x nd cert.s ν g).map Prod.fst = _
    unfold childPins
    rw [List.map_attach_eq_pmap, List.map_pmap]
    exact List.pmap_eq_map _
  have hfg : ((List.finRange 64).flatMap fun g => (cert.childNode ν g).pins.map Prod.fst) =
      ((List.finRange 64).flatMap fun g =>
        (nd.pins.filter (fun pv => decide (cert.lbl (coord cert.hu ν.1) pv.2 = g))).map Prod.fst) :=
    List.flatMap_congr (fun g _ => hmap g)
  rw [hfg]
  exact filter_bucket_perm 64 (fun pv => cert.lbl (coord cert.hu ν.1) pv.2) Prod.fst nd.pins

theorem unique_leaf_of_pinFirsts_perm {C c : ℕ} {x : Input C c} {f : ℤ[X]} {PktOK : PktPred f x.l}
    (ns : List (SoloNode x f PktOK))
    (hperm : List.Perm (pinFirsts ns) (List.finRange (4 * x.m * x.k))) :
    ∀ bi : Fin (4 * x.m * x.k), ∃! j : Fin ns.length,
      ∃ kp : Fin (ns.get j).pins.length, ((ns.get j).pins.get kp).1 = bi := by
  have hnodup : (pinFirsts ns).Nodup := hperm.nodup_iff.mpr (List.nodup_finRange _)
  intro bi
  have hmem : bi ∈ pinFirsts ns := hperm.mem_iff.mpr (List.mem_finRange bi)
  unfold pinFirsts at hmem hnodup
  rw [List.mem_flatMap] at hmem
  obtain ⟨nd, hnd_mem, hbi_mem⟩ := hmem
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hnd_mem
  obtain ⟨pv, hpv_mem, hpv_eq⟩ := List.mem_map.mp hbi_mem
  obtain ⟨kp, rfl⟩ := List.mem_iff_get.mp hpv_mem
  refine ⟨j, ⟨kp, hpv_eq⟩, ?_⟩
  rintro j' ⟨kp', hkp'⟩
  by_contra hne
  have hlt_or_gt : j'.val < j.val ∨ j.val < j'.val := Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne)
  have hdup_pair : ∀ (a b : Fin ns.length), a.val < b.val →
      bi ∈ (ns.get a).pins.map Prod.fst → bi ∈ (ns.get b).pins.map Prod.fst → False := by
    intro a b hab ha hb
    have hsplit1 : ns = ns.take (a.val + 1) ++ ns.drop (a.val + 1) := (List.take_append_drop _ ns).symm
    have hnodup' : ((ns.take (a.val + 1)).flatMap (fun nd => nd.pins.map Prod.fst) ++
        (ns.drop (a.val + 1)).flatMap (fun nd => nd.pins.map Prod.fst)).Nodup := by
      rw [← List.flatMap_append, ← hsplit1]; exact hnodup
    have hdisj := (List.nodup_append.mp hnodup').2.2
    have hmem_left : bi ∈ (ns.take (a.val + 1)).flatMap (fun nd => nd.pins.map Prod.fst) := by
      rw [List.mem_flatMap]
      refine ⟨ns.get a, ?_, ha⟩
      rw [List.mem_iff_getElem]
      refine ⟨a.val, by simp [a.isLt], by simp⟩
    have hmem_right : bi ∈ (ns.drop (a.val + 1)).flatMap (fun nd => nd.pins.map Prod.fst) := by
      rw [List.mem_flatMap]
      refine ⟨ns.get b, ?_, hb⟩
      rw [List.mem_iff_getElem]
      refine ⟨b.val - (a.val + 1), by simp; omega, ?_⟩
      simp only [List.getElem_drop, List.get_eq_getElem]
      congr 1; omega
    exact hdisj bi hmem_left bi hmem_right rfl
  have hbi_j : bi ∈ (ns.get j).pins.map Prod.fst :=
    hpv_eq ▸ List.mem_map_of_mem (List.get_mem _ kp)
  have hbi_j' : bi ∈ (ns.get j').pins.map Prod.fst :=
    hkp' ▸ List.mem_map_of_mem (List.get_mem _ kp')
  rcases hlt_or_gt with h1 | h2
  · exact hdup_pair j' j h1 hbi_j' hbi_j
  · exact hdup_pair j j' h2 hbi_j hbi_j'

end PinPartition

section CertTree

def treeAll {α : Type} (P : α → Prop) : D4RankCode.Tree α → Prop
  | .leaf a => P a
  | .choice _ next => ∀ d, treeAll P (next d)

theorem treeAll_read {α : Type} {P : α → Prop} {t : D4RankCode.Tree α}
    (h : treeAll P t) (b j : ℕ) {a : α} (hr : t.read b j = some a) : P a := by
  induction t generalizing b j with
  | leaf z =>
    unfold D4RankCode.Tree.read at hr
    split_ifs at hr with hz
    · injection hr with heq; exact heq ▸ h
  | choice n next ih =>
    unfold D4RankCode.Tree.read at hr
    dsimp only at hr
    split_ifs at hr with hwb hmod
    exact ih ⟨j % 2 ^ Nat.clog 2 n, hmod⟩ (h _) (b - Nat.clog 2 n) (j / 2 ^ Nat.clog 2 n) hr

structure SoloLeafData {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc guard : ℕ) where
  doneNodes : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf))
  accVal : B f x.l (guard + x.p)
  lossSum : ℕ

def SoloLeafData.Valid {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {E_pkt : PrimitiveMachine} {o_pkt : Fin E_pkt.tapeCount} {K_loc guard : ℕ}
    (lf : SoloLeafData x hf E_pkt o_pkt K_loc guard) : Prop :=
  lf.lossSum ≤ guard ∧
  lf.doneNodes.length ≤ 64 ^ Nat.clog 32 (4 * x.m) ∧
  (∀ nd ∈ lf.doneNodes, Nat.clog 32 (4 * x.m) ≤ nd.d ∨ nd.G.nE ≤ D3Stopped.threshold x.S) ∧
  List.Perm (pinFirsts lf.doneNodes) (List.finRange (4 * x.m * x.k))

def SoloLeafData.weight {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {E_pkt : PrimitiveMachine} {o_pkt : Fin E_pkt.tapeCount} {K_loc guard : ℕ}
    (lf : SoloLeafData x hf E_pkt o_pkt K_loc guard) : B f x.l (guard + x.p) :=
  (2 : B f x.l (guard + x.p)) ^ (guard - lf.lossSum) * lf.accVal

def SoloLeafData.toBits {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {E_pkt : PrimitiveMachine} {o_pkt : Fin E_pkt.tapeCount} {K_loc guard : ℕ}
    (ctx : Wd) (lf : SoloLeafData x hf E_pkt o_pkt K_loc guard) : Wd :=
  pack [finishWt ctx (residue f x.l (guard + x.p) hf lf.accVal) lf.lossSum,
    pack (lf.doneNodes.map (·.toWorkItem.bits))]

def SoloNode.pinnedVal {C c : ℕ} {x : Input C c} {f : ℤ[X]} {PktOK : PktPred f x.l}
    (hf : f.Monic) (q : ℕ) (η : Fin (4 * x.m * x.k) → Bool)
    (nd : SoloNode x f PktOK) : B f x.l q :=
  lift hf q (BTNContract nd.G (pin (nd.openTensor hf) (fun kp => η (nd.pins.get kp).1)))

def SoloLeafData.doneProd {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {E_pkt : PrimitiveMachine} {o_pkt : Fin E_pkt.tapeCount} {K_loc guard : ℕ}
    (η : Fin (4 * x.m * x.k) → Bool)
    (lf : SoloLeafData x hf E_pkt o_pkt K_loc guard) : B f x.l (guard + x.p) :=
  (lf.doneNodes.map (SoloNode.pinnedVal hf (guard + x.p) η)).prod

abbrev WorkCertItem {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ) : Type :=
  Σ (k : ℕ) (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)),
    SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc k nd

def remSlots {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) : ℕ :=
  (todo.map fun it => D4GuardTree.slots it.1).sum

def remLeaves {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) : ℕ :=
  (todo.map fun it => 64 ^ it.1).sum

def todoNodes {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) :
    List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)) :=
  todo.map fun it => it.2.1

def peelCert {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ} :
    List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) →
      List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)) ×
      List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)
  | [] => ([], [])
  | ⟨0, nd, _⟩ :: rest =>
    let p := peelCert rest
    (nd :: p.1, p.2)
  | ⟨_ + 1, nd, PSum.inl _⟩ :: rest =>
    let p := peelCert rest
    (nd :: p.1, p.2)
  | (⟨k + 1, nd, PSum.inr r⟩) :: rest =>
    ([], ⟨k + 1, nd, PSum.inr r⟩ :: rest)

def unrollCertFuel {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc guard : ℕ) :
    ℕ → List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) →
    List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)) →
    B f x.l (guard + x.p) → ℕ →
    D4RankCode.Tree (SoloLeafData x hf E_pkt o_pkt K_loc guard)
  | 0, todo, done, accVal, lossSum =>
    let p := peelCert todo
    .leaf ⟨done ++ p.1, accVal, lossSum⟩
  | fuel + 1, todo, done, accVal, lossSum =>
    let p := peelCert todo
    match p.2 with
    | ⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩ :: tail =>
      let loss₀ := AppendixD4.loss nd.G.nE (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d) 0
      .choice cert.nBranches fun d =>
        let ν := cert.order d
        let w_val : B f x.l (guard + x.p) :=
          lift hf (guard + x.p) (AdjoinRoot.of _ (cert.s.weight ν.1 ν.2.1) : B f x.l (nd.pCurr + loss₀))
        unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel
          ((List.ofFn fun g : Fin 64 => ⟨k, cert.childNode ν g, sub ν g⟩) ++ tail)
          (done ++ p.1) (accVal * w_val) (lossSum + loss₀)
    | _ =>
      .leaf ⟨done ++ p.1, accVal, lossSum⟩

theorem peelCert_nodes_eq {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) :
    (peelCert todo).1 ++ todoNodes (peelCert todo).2 = todoNodes todo := by
  induction todo with
  | nil => rfl
  | cons it rest ih =>
    rcases it with ⟨k, nd, u⟩
    cases k with
    | zero =>
      simp only [peelCert, todoNodes, List.map_cons, List.cons_append]
      exact congrArg (nd :: ·) ih
    | succ k =>
      cases u with
      | inl _ =>
        simp only [peelCert, todoNodes, List.map_cons, List.cons_append]
        exact congrArg (nd :: ·) ih
      | inr _ => rfl

theorem peelCert_stopped {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) :
    ∀ nd ∈ (peelCert todo).1, Nat.clog 32 (4 * x.m) ≤ nd.d ∨ nd.G.nE ≤ D3Stopped.threshold x.S := by
  induction todo with
  | nil => intro _ h; cases h
  | cons it rest ih =>
    rcases it with ⟨k, nd, u⟩
    cases k with
    | zero =>
      rcases u with ⟨hstop⟩
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hrest
      · exact hstop
      · exact ih m hrest
    | succ k =>
      cases u with
      | inl hs =>
        rcases hs with ⟨hstop⟩
        intro m hm
        rcases List.mem_cons.mp hm with rfl | hrest
        · exact hstop
        · exact ih m hrest
      | inr _ => intro _ h; cases h

theorem peelCert_remSlots_le {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) :
    remSlots (peelCert todo).2 ≤ remSlots todo := by
  induction todo with
  | nil => exact le_rfl
  | cons it rest ih =>
    rcases it with ⟨k, nd, u⟩
    cases k with
    | zero => simpa [peelCert, remSlots, D4GuardTree.slots] using ih
    | succ k =>
      cases u with
      | inl _ =>
        simp only [peelCert, remSlots, List.map_cons, List.sum_cons]
        exact ih.trans (Nat.le_add_left _ _)
      | inr _ => exact le_rfl

theorem peelCert_remLeaves_le {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) :
    (peelCert todo).1.length + remLeaves (peelCert todo).2 ≤ remLeaves todo := by
  induction todo with
  | nil => simp [peelCert, remLeaves]
  | cons it rest ih =>
    rcases it with ⟨k, nd, u⟩
    cases k with
    | zero =>
      unfold remLeaves at ih
      simp only [peelCert, remLeaves, List.length_cons, List.map_cons, pow_zero, List.sum_cons]
      omega
    | succ k =>
      cases u with
      | inl _ =>
        unfold remLeaves at ih
        have h1 : 1 ≤ 64 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
        simp only [peelCert, remLeaves, List.length_cons, List.map_cons, List.sum_cons]
        omega
      | inr _ => simp [peelCert]

theorem peelCert_rem_shape {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) :
    (peelCert todo).2 = [] ∨
      ∃ k nd cert sub tail, (peelCert todo).2 = ⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩ :: tail := by
  induction todo with
  | nil => exact Or.inl rfl
  | cons it rest ih =>
    rcases it with ⟨k, nd, u⟩
    cases k with
    | zero => exact ih
    | succ k =>
      cases u with
      | inl _ => exact ih
      | inr r =>
        rcases r with ⟨cert, sub⟩
        exact Or.inr ⟨k, nd, cert, sub, rest, rfl⟩

theorem peelCert_bits_split {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ} (guard : ℕ)
    (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) :
    let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
    let rawTodo := (todoNodes todo).map (·.toWorkItem.bits)
    let idx := (rawTodo.map (small ctx)).idxOf false
    (peelCert todo).1.map (·.toWorkItem.bits) = rawTodo.take idx ∧
      (todoNodes (peelCert todo).2).map (·.toWorkItem.bits) = rawTodo.drop idx := by
  intro ctx
  induction todo with
  | nil => simp [peelCert, todoNodes]
  | cons it rest ih =>
    rcases it with ⟨k, nd, u⟩
    have hstop_case : (Nat.clog 32 (4 * x.m) ≤ nd.d ∨ nd.G.nE ≤ D3Stopped.threshold x.S) →
        small ctx nd.toWorkItem.bits = true := by
      intro hs
      rw [small_ctx_eq]
      rcases hs with h1 | h2
      · simp [h1]
      · simp [h2]
    cases k with
    | zero =>
      rcases u with ⟨hs⟩
      have hsm := hstop_case hs
      have hidx : (((todoNodes (⟨0, nd, ⟨hs⟩⟩ :: rest)).map (·.toWorkItem.bits)).map (small ctx)).idxOf false =
          1 + (((todoNodes rest).map (·.toWorkItem.bits)).map (small ctx)).idxOf false := by
        simp [todoNodes, hsm, List.idxOf, List.findIdx_cons, Nat.add_comm]
      simp only [peelCert, List.map_cons, hidx]
      refine ⟨?_, ?_⟩
      · rw [ih.1]; simp [todoNodes, Nat.add_comm 1, List.take_succ_cons]
      · rw [ih.2]; simp [todoNodes, Nat.add_comm 1]
    | succ k =>
      cases u with
      | inl hs_box =>
        rcases hs_box with ⟨hs⟩
        have hsm := hstop_case hs
        have hidx : (((todoNodes (⟨k + 1, nd, PSum.inl ⟨hs⟩⟩ :: rest)).map (·.toWorkItem.bits)).map (small ctx)).idxOf false =
            1 + (((todoNodes rest).map (·.toWorkItem.bits)).map (small ctx)).idxOf false := by
          simp [todoNodes, hsm, List.idxOf, List.findIdx_cons, Nat.add_comm]
        simp only [peelCert, List.map_cons, hidx]
        refine ⟨?_, ?_⟩
        · rw [ih.1]; simp [todoNodes, Nat.add_comm 1, List.take_succ_cons]
        · rw [ih.2]; simp [todoNodes, Nat.add_comm 1]
      | inr r =>
        rcases r with ⟨cert, sub⟩
        have hsm : small ctx nd.toWorkItem.bits = false := by
          rw [small_ctx_eq]
          simp [Nat.not_le.mpr cert.hd, Nat.not_le.mpr cert.hM]
        have hidx : (((todoNodes (⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩ :: rest)).map (·.toWorkItem.bits)).map (small ctx)).idxOf false = 0 := by
          simp [todoNodes, hsm, List.idxOf, List.findIdx_cons]
        dsimp only [peelCert]
        rw [hidx]
        exact ⟨rfl, rfl⟩

end CertTree

end

end DetDLP.D4SoloForest


