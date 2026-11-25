-- Prove2me | Definitions.Def_DetDLP_S8G_Bounds
-- name    : DetDLP_S8G_Bounds
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:50:21.059728+00:00
-- url     : https://prove2.me/theorems/b2d40f81-106e-4671-ae4b-1cbc5f0d64e0
-- title:
--   Tag 1 anchored moment graph edge, gate, and degree bounds
-- statement:
--   **Graph bounds.** Let $b=\operatorname{bitLen}(p)$, $m=\operatorname{blockCount}(b)$, and $s=65536m(b+2)$. For each of the four Tag 1 moment queries with $|\eta|\le 2mb$, the anchored layout satisfies $2n_E<s$ and $n_G\le s$. Every vertex of its factor graph has degree at most $\max\{12,\lceil136(b+2)^{3/4}\rceil\}$. The edge count uses the exact multiplier graph formula to bound a width-$d$ multiplier graph by $320(d+1)$ edges before accounting for register anchors and copy cycles.
--
--   **Realization.** For prime $p$ and $T\le p$, the assignment equivalence and transcript erasure identify the witness count with the selected moment value. At packet constant $200000$, it remains only to prove the descriptor equation for `make` and the encoded local-test equation for `port`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_ChainSliceEquiv
import Definitions.Def_DetDLP_S8H0_GraphDegree
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace DetDLP.S8G.Bounds
attribute [-simp] Fin.natAdd_eq_addNat
open S8H0 S8H0.RegisterMap S8H0.NamedBlocks S8H0.GraphDegree S8J S8H SeedAndAtomBank Routes FpAtomRows M89S1 S8C
open RangeRows GateRoutes HashRows ResidueWires
open w4_MulParams w4_M5GraphBounds in
private theorem raw {d : ℕ} (hd : 1 ≤ d) : (graph d hd).nE ≤ 320*(d+1) := by
  by_cases h : d < 16
  · rw [graph_nE]; interval_cases d <;> decide
  have hJ := J_upper hd; have hJ' : J d ≤ 4*(d+1) := by by_contra! hh; nlinarith [Nat.mul_self_le_mul_self hh.le, Nat.mul_le_mul_left (d+1) (show 16 ≤ d+1 by omega)]
  have hn := n0_covers_tightly hd; have hk := four_mul_k hd; have hL := L_upper hd
  have hN : n0 d ≤ d+1 := by have := n0_upper hd; omega
  rw [graph_nE]; apply (Nat.add_le_add_left (Nat.mul_le_mul_right _ (show 6*L d+8*n0 d-2 ≤ 32*n0 d by omega)) _).trans
  have hjn : n0 d * J d < 4*d + J d := by rw [← hk]; nlinarith only [hn.2]
  nlinarith only [hjn,hJ',hN]
private theorem allEdges {s n C} (f : Fin n → B (Shape.size s+1)) (h : ∀ i, (f i).core.A.ne ≤ C) : (allRows n f).core.A.ne ≤ n*C := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => induction n with
              | zero => simpa [allRows,many] using h 0
              | succ n ih => have H := ih (fun i => f i.succ) (fun i => h i.succ); have := h 0
                             simp only [allRows,many,joinB,join,Nat.succ_mul] at *; omega
private theorem orEdges {s} (n : ℕ) (x : Fin n → Ref s) (b : Ref s) (t : Fin n → Ref s) : (orRows n x b t).core.A.ne ≤ 3*n+1 := by
  induction n generalizing b with
  | zero => exact Nat.le_refl 1
  | succ n ih => simp only [orRows,joinB,join,rows,mapped]; specialize ih (x ∘ Fin.succ) (t 0) (t ∘ Fin.succ); omega
private theorem joinEdges {k a b} (A B' : B k) (ha : A.core.A.ne ≤ a) (hb : B'.core.A.ne ≤ b) : (joinB A B').core.A.ne ≤ a+b := Nat.add_le_add ha hb
variable (p m : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool)
private theorem size (hm : 1 ≤ m) (hη : η.length ≤ m*2*bitLen p) : 2*(Semantics.layout p m j T η).ne < FpMoment.scale m (bitLen p) := by
  let d := bitLen p+1; let hd : 1 ≤ d := Nat.succ_pos _; let e := edges hd
  have he : e ≤ 320*(d+1) := raw hd
  have hc : copies j ≤ 2 := min_le_right ..
  have ho : outputs j ≤ 1 := by simp [outputs]; split <;> decide
  change 2*((_+1+(Semantics.net p m j T η).core.A.ne)+((_+1+(Semantics.net p m j T η).core.A.ne)+(_+1+(Semantics.net p m j T η).core.A.ne))) < _
  apply Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.add_le_add ?H (Nat.add_le_add ?H ?H)))
  case H =>
    apply Nat.add_le_add_left
    unfold Semantics.net Routes.network seedBlock seedSlotBlock atomBankBlock atomSlotBlock chainBlock stageAt stageBlock stageProducts stageSum HashRows.block product eqs checker sumRows
    dsimp only
    repeat' first | with_reducible apply joinEdges | with_reducible apply allEdges; intro i | apply orEdges | (simp only [rows,mapped,PointGraph.zeroLast,AnchoredLayout.anchors,NamedBlocks.add,AddLayout.layout,w3_fpMulLayout,w3_m5Layout,w3_forgetSides]; apply le_refl)
  simp only [Semantics.shape,Routes.bank,seedShape,seedSlot,atomBankShape,atomSlot,productShape,chainShape,stageShape,run,triple,RegisterMap.mul,auxShape,Shape.size]
  change _ < 65536*m*(bitLen p+2)
  have hi : (if m-1 = 0 then bitLen p+1 else 0) ≤ bitLen p+1 := by split <;> omega
  dsimp only [d,e,hd] at he
  grw [hc,ho,he,hη,hi,Nat.sub_le (m-1) 1,Nat.sub_le m 1]
  have hb := Nat.le_mul_of_pos_left (bitLen p) hm
  have hme := Nat.mul_le_mul_left m he
  simp only [edges] at hme; ring_nf at hb hme ⊢; omega

theorem edgeBudget (hη : η.length ≤ blockCount (bitLen p)*2*bitLen p) :
    2*(Semantics.layout p (blockCount (bitLen p)) j T η).ne < FpMoment.scale (blockCount (bitLen p)) (bitLen p) :=
  size p _ j T η ((by decide : 1 ≤ 2).trans (le_max_left ..)) hη

theorem gateBudget (hη : η.length ≤ blockCount (bitLen p)*2*bitLen p) :
    (Semantics.layout p (blockCount (bitLen p)) j T η).ng ≤ FpMoment.scale (blockCount (bitLen p)) (bitLen p) := by
  have h := (w3_incDims _ (Semantics.gate_surj p (blockCount (bitLen p)) j T η)).1
  have := edgeBudget p j T η hη; omega

private theorem all_ok {s n D} (f : Fin n → B (Shape.size s+1)) (h : ∀ i, good (f i) (cap D)) : good (allRows n f) (cap D) := by
  cases n with
  | zero => exact mono (row_ok _ 0 _ _) (small D _ (by decide))
  | succ n => induction n with
              | zero => exact h 0
              | succ n ih => exact join_ok _ _ (h 0) (ih _ fun i => h i.succ)
private theorem or_ok {s} (D n : ℕ) (x : Fin n → Ref s) (b : Ref s) (t : Fin n → Ref s) : good (orRows n x b t) (cap D) := by
  induction n generalizing b with
  | zero => exact mono (row_ok _ _ _ _) (small D _ (by decide))
  | succ n ih => exact join_ok _ _ (mono (row_ok _ _ _ _) (small D _ (by decide))) (ih _ _ _)
theorem degree (v : Fin (w3_factorGraph (Semantics.layout p m j T η)).nV) : (w3_factorGraph (Semantics.layout p m j T η)).deg v ≤ cap p := by
  have h : good (Semantics.net p m j T η) (cap p) := by
    unfold Semantics.net Routes.network seedBlock seedSlotBlock atomBankBlock atomSlotBlock chainBlock stageAt stageBlock stageProducts stageSum HashRows.block product eqs checker sumRows
    dsimp only
    repeat' first | with_reducible apply join_ok | with_reducible apply all_ok; intro i | apply or_ok | exact mul_ok p _ | exact mono (add_ok _ _ _ _ _) (small p _ (by decide)) | exact mono (row_ok _ _ _ _) (small p _ (by decide)) | exact anchors_ok 1 _ (small p _ (by decide))
  let b := (Semantics.net p m j T η).core; let f := (Semantics.net p m j T η).name
  let K := (Semantics.shape p m j).size+1
  induction v using Fin.addCases with
  | left i => induction i using Fin.addCases with
              | left g => apply (NamedWires.oldDegree (AnchoredLayout.signal b f) (AnchoredLayout.block b K).A.gate g).le.trans
                          change degreeOf (AnchoredLayout.block b K).A.gate g ≤ cap p
                          induction g using Fin.addCases with
                          | left i => exact (S8J.degree_left (AnchoredLayout.anchors K).gate b.A.gate i).le.trans (anchors_ok K _ (small p 1 (by decide)) i)
                          | right i => exact (S8J.degree_right (AnchoredLayout.anchors K).gate b.A.gate i).le.trans (h i)
              | right i => exact (NamedWires.eqDegree (AnchoredLayout.signal b f) (AnchoredLayout.block b K).A.gate i).le.trans (small p _ (by decide))
  | right i => exact (CopyCycle.bitDegree _ _ i).le.trans (small p _ (by decide))

section Packet
variable {p T : ℕ} [Fact p.Prime]
private noncomputable abbrev A := Semantics.layout p (blockCount (bitLen p)) j T η
private noncomputable abbrev test := Semantics.tests p (blockCount (bitLen p)) j T η
/-- For a legal moment query only the descriptor and the encoded local test remain to be supplied. -/
theorem realizes_of_eval (hT : T ≤ p) (hη : η.length ≤ blockCount (bitLen p)*2*bitLen p)
    (make port : List Bool → List Bool)
    (build : make (FpMoment.word p j T η) = encodeBTNInstance (FpMoment.word p j T η)
      (w3_factorGraph (A (p:=p) (T:=T) j η)).subdivision (FpMoment.scale (blockCount (bitLen p)) (bitLen p)) (FpMoment.scale (blockCount (bitLen p)) (bitLen p)) 1)
    (eval : ∀ v a, port (encodePortQuery (FpMoment.word p j T η) v.val (List.ofFn a)) = encodeNatListBin
      [if (w3_factorGraph (A (p:=p) (T:=T) j η)).subdivisionTensor (w3_factorChecks _ (test (p:=p) (T:=T) j η)) v a then 1 else 0]) :
    S8C.Realizes make port 200000 (FpMoment.word p j T η) (bitLen p) (FpMoment.value p (blockCount (bitLen p)) T η j) := by
  have hm : 2 ≤ blockCount (bitLen p) := le_max_left ..
  refine FpMoment.ofLayout j η hT hη _ _ (Semantics.gate_surj p _ j T η) make port
    ((ChainSliceEquiv.runs j hT η hη).trans (FpMoment.erase _ _ _ η DetDLP.w3_m5_modmul_r2 j)) ?_
    (edgeBudget p j T η hη) (degree p _ j T η) build eval
  simpa only [show blockCount (bitLen p)-1+1 = blockCount (bitLen p) by omega] using FpMoment.target_card p (blockCount (bitLen p)-1) T η j
end Packet
end DetDLP.S8G.Bounds


