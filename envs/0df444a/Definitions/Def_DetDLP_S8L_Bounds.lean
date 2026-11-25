-- Prove2me | Definitions.Def_DetDLP_S8L_Bounds
-- name    : DetDLP_S8L_Bounds
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T09:12:50.762509+00:00
-- url     : https://prove2.me/theorems/87549dc8-cab3-4e60-8143-b4b02fb145ea
-- title:
--   Tag 5 anchored graph vertex, edge, and degree bounds
-- statement:
--   ## Tag 5 anchored graph vertex, edge, and degree bounds
--
--   For the Tag 5 packet construction, let $p$ be prime, $m\ge 1$, and let $\eta$ satisfy $|\eta|\le 2m\,\mathrm{bitLen}(p)$. The layout is the network assembled from the anchored signal block, the routed atom and stage rows, and the range-check rows. Write $N_e$ and $N_g$ for its edge and gate counts.
--
--   The bounds establish that $2N_e < 250000m(\mathrm{bitLen}(p)+2)$ and $N_g\le 250000m(\mathrm{bitLen}(p)+2)$. Every vertex in the associated factor graph has degree at most $\max\{12,\lceil136(\mathrm{bitLen}(p)+2)^{3/4}\rceil\}$. The proof combines row-wise size estimates with the anchored-graph degree lemmas and the degree bounds for the copied cycle.
--
--   These estimates feed the Tag 5 realization theorem: with packet scale $s=250000m(\mathrm{bitLen}(p)+2)$ and the stated witness and query conditions, the graph satisfies the required edge, vertex, degree, and encoding-length budgets.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_Semantics
import Definitions.Def_DetDLP_S8H0_GraphDegree
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace DetDLP.S8L.Bounds
attribute [-simp] Fin.natAdd_eq_addNat
open S8H0 S8H0.NamedBlocks S8H0.RegisterMap S8H0.GraphDegree S8G.FpAtomRows S8J S8H M89S1 S8C
private abbrev cost {k : ℕ} (b : B k) := b.core.A.ne + b.core.A.ng
private theorem count {k n C : ℕ} (f : Fin n → B (k+1)) (h : ∀ i, cost (f i) ≤ C) : cost (Routes.allRows n f) ≤ n*C := by
  induction n with
  | zero => simp [Routes.allRows,cost,eqs,rows,mapped]
  | succ n ih => have := ih (fun j => f j.succ) (fun j => h j.succ); have := h 0
                 simp only [Routes.allRows,cost,joinB,join,Nat.succ_mul] at *; omega
abbrev packetScale (m b : ℕ) := 250000*m*(b+2)
variable (p m T X : ℕ) (cs : Fin m → ℕ × ℕ) (η : List Bool)
private theorem sizes (hm : 1 ≤ m) (hη : η.length ≤ 2*m*bitLen p) :
    2*(Semantics.layout p m T X cs η).ne < packetScale m (bitLen p) ∧ (Semantics.layout p m T X cs η).ng ≤ packetScale m (bitLen p) := by
  let d := Semantics.width p; let hd := Semantics.width_pos p; let e := Routes.G hd
  have he := w4_M5GraphBounds.graph_edge_bound hd; have hv := GraphBudget.baseV hd
  have calcCost {k n : ℕ} (f : Fin n → B (k+1)) (C : ℕ) (hn : n ≤ 2*m) (h : ∀ i, cost (f i) ≤ C*(d+1)) := (count f h).trans (Nat.mul_le_mul_right _ hn)
  have a := calcCost (Routes.atomRows hd p T cs) 6000 (le_refl _) (by
    intro i; simp only [Routes.atomRows,HashRows.block,HashRows.product,eqs,HashRows.sumRows,RangeRows.checker,NamedBlocks.add,rows,mapped,joinB,join,cost,S8C.AddLayout.layout,w3_fpMulLayout,w3_m5Layout,w3_forgetSides,d]; omega)
  have b := calcCost (Routes.stage (m:=m) hd p X) 6000 (by omega) (by
    intro i; simp only [Routes.stage,stageBlock,stageProducts,stageSum,HashRows.product,eqs,HashRows.sumRows,NamedBlocks.add,rows,mapped,joinB,join,cost,S8C.AddLayout.layout,w3_fpMulLayout,w3_m5Layout,w3_forgetSides,d]; omega)
  have c := calcCost (fun i => RangeRows.checker p (Routes.intermediate (d:=d) (e:=e) (m:=m) i)) 8 (by omega) (by intro i; simp only [RangeRows.checker,NamedBlocks.add,mapped,cost,S8C.AddLayout.layout]; omega)
  have regs : (Semantics.shape p m).size ≤ 2*m*(4600*(d+1)) := by
    simp only [Semantics.shape,Routes.bank,Routes.atom,Routes.extra,run,triple,RegisterMap.mul,GateRoutes.auxShape,stageShape,Shape.size]
    apply (Nat.add_le_add_left (Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.sub_le (2*m) 1)) (Nat.mul_le_mul_right _ (Nat.sub_le (2*m) 2))) _).trans
    rw [← Nat.mul_add,← Nat.mul_add]; apply Nat.mul_le_mul_left; dsimp [Routes.G,d,hd] at *; omega
  change 2*((_+1+(Semantics.net p m T X cs η).core.A.ne)+((_+1+(Semantics.net p m T X cs η).core.A.ne)+(_+1+(Semantics.net p m T X cs η).core.A.ne))) < _ ∧ (_+1+(Semantics.net p m T X cs η).core.A.ng)+(_+1+(Semantics.net p m T X cs η).core.A.ne) ≤ _
  simp only [Semantics.net,Routes.network,Routes.prefixRows,PointGraph.zeroLast,AnchoredLayout.anchors,joinB,join,rows,mapped,cost] at a b c ⊢
  dsimp only [d,Semantics.width,packetScale] at *; ring_nf at a b c regs hη ⊢; constructor <;> omega

theorem edgeBudget (hm : 1 ≤ m) (hη : η.length ≤ 2*m*bitLen p) : 2*(Semantics.layout p m T X cs η).ne < FpPair.scale m (bitLen p) :=
  (sizes p m T X cs η hm hη).1.trans_le (by unfold packetScale FpPair.scale; gcongr; decide)
theorem gateBudget (hm : 1 ≤ m) (hη : η.length ≤ 2*m*bitLen p) : (Semantics.layout p m T X cs η).ng ≤ FpPair.scale m (bitLen p) :=
  (sizes p m T X cs η hm hη).2.trans (by unfold packetScale FpPair.scale; gcongr; decide)
private theorem all_ok {k n D : ℕ} (f : Fin n → B (k+1)) (h : ∀ i, good (f i) (cap D)) : good (Routes.allRows n f) (cap D) := by
  induction n with
  | zero => exact mono (row_ok _ 2 _ _) (small D _ (by decide))
  | succ n ih => exact join_ok _ _ (h 0) (ih _ fun j => h j.succ)
theorem degree (v : Fin (w3_factorGraph (Semantics.layout p m T X cs η)).nV) :
    (w3_factorGraph (Semantics.layout p m T X cs η)).deg v ≤ cap p := by
  have h : good (Semantics.net p m T X cs η) (cap p) := by
    unfold Semantics.net Routes.network
    refine join_ok _ _ (anchors_ok 1 _ (small p _ (by decide))) (join_ok _ _ (all_ok _ fun i => ?_) (join_ok _ _ (all_ok _ fun i => ?_) (join_ok _ _ (all_ok _ fun i => ?_) ?_)))
    all_goals simp only [Routes.atomRows,Routes.stage,Routes.prefixRows,stageBlock,stageProducts,stageSum,HashRows.block,HashRows.product,HashRows.sumRows,RangeRows.checker,eqs]
    all_goals repeat' apply join_ok
    all_goals first | exact mul_ok p _ | exact mono (add_ok _ _ _ _ _) (small p _ (by decide)) | exact mono (row_ok _ _ _ _) (small p _ (by decide))
  let b := (Semantics.net p m T X cs η).core; let f := (Semantics.net p m T X cs η).name
  let K := (Semantics.shape p m).size+1
  induction v using Fin.addCases with
  | left i => induction i using Fin.addCases with
              | left g => apply (NamedWires.oldDegree (AnchoredLayout.signal b f) (AnchoredLayout.block b K).A.gate g).le.trans
                          change degreeOf (AnchoredLayout.block b K).A.gate g ≤ cap p
                          induction g using Fin.addCases with
                          | left i => exact (S8J.degree_left (AnchoredLayout.anchors K).gate b.A.gate i).le.trans (anchors_ok K _ (small p 1 (by decide)) i)
                          | right i => exact (S8J.degree_right (AnchoredLayout.anchors K).gate b.A.gate i).le.trans (h i)
              | right j => exact (NamedWires.eqDegree (AnchoredLayout.signal b f) (AnchoredLayout.block b K).A.gate j).le.trans (small p _ (by decide))
  | right j => exact (CopyCycle.bitDegree _ _ j).le.trans (small p _ (by decide))

private theorem packet_length {m b n : ℕ} (hb : 1 ≤ b) (hw : n ≤ 256*m*b) : packetScale m b + n ≤ 800000*m*b := by
  have h : packetScale m b ≤ 250000*m*(3*b) := Nat.mul_le_mul_left _ (by omega)
  calc _ ≤ 250000*m*(3*b) + 256*m*b := Nat.add_le_add h hw
       _ = 750256*m*b := by ring
       _ ≤ _ := by gcongr <;> decide

section Packet
variable {p T : ℕ} [Fact p.Prime] (S : FpSeed p (blockCount (bitLen p))) (Y : (ZMod p)ˣ)
private noncomputable abbrev A := Semantics.layout p (blockCount (bitLen p)) T (Y : ZMod p).val (AtomLift.coeff S) η
private noncomputable abbrev test := Semantics.tests p (blockCount (bitLen p)) T (Y : ZMod p).val (AtomLift.coeff S) η
/-- The smaller packet scale leaves room for the descriptor even at the smallest prime. -/
theorem realizes_of_eval (hT : T ≤ p) (hη : η.length ≤ 2*blockCount (bitLen p)*bitLen p)
    (make port : List Bool → List Bool)
    (build : make (FpPair.word T S Y η) = encodeBTNInstance (FpPair.word T S Y η)
      (w3_factorGraph (A (T:=T) η S Y)).subdivision (packetScale (blockCount (bitLen p)) (bitLen p)) (packetScale (blockCount (bitLen p)) (bitLen p)) 1)
    (eval : ∀ v a, port (encodePortQuery (FpPair.word T S Y η) v.val (List.ofFn a)) = encodeNatListBin
      [if (w3_factorGraph (A (T:=T) η S Y)).subdivisionTensor (w3_factorChecks _ (test (T:=T) η S Y)) v a then 1 else 0]) :
    Realizes make port 800000 (FpPair.word T S Y η) (bitLen p) (FpPair.value T S Y η) := by
  let b := bitLen p; let m := blockCount b; let s := packetScale m b; let w := FpPair.word T S Y η
  let L := A (T:=T) η S Y; let t := test (T:=T) η S Y
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left _ _)
  have hs : b+2 ≤ s := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) hm)
  obtain ⟨he,hg⟩ : 2*L.ne < s ∧ L.ng ≤ s := sizes p m T _ _ η hm hη
  have hn : L.nb ≤ L.ne := by simpa using Fintype.card_le_of_injective L.rep (Function.RightInverse.injective L.rep_bit)
  have hv : L.ng+L.nb+L.ne ≤ 2*s := by omega
  have hw : w.length ≤ 256*m*b := FpPair.wordLen S Y η hm hT hη
  have hb : 1 ≤ b := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have h1 : s+w.length ≤ 800000*m*b := packet_length hb hw
  rw [← Semantics.witness_card η S Y hm hη (AtomLift.coeff S) (fun _ => rfl)]
  apply wireRealizes make port 800000 s b w (w3_factorGraph L) (w3_factorChecks L t) (w3_factorEquiv L t) (by omega) (by omega) he
  · change L.ng+L.nb+L.ne ≤ s^800000
    calc _ ≤ 2*s := hv
         _ ≤ s^2 := by rw [pow_two]; exact Nat.mul_le_mul_right s (by omega)
         _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 800000)
  · apply (max_le (Finset.sup_le (fun v _ => degree _ _ _ _ _ _ v)) ((by decide : 2 ≤ 12).trans (le_max_left _ _))).trans
    apply (S8G.FpMoment.degreeBudget hm).trans; apply Nat.ceil_mono; apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    exact_mod_cast (show S8G.FpMoment.scale m b ≤ s by unfold S8G.FpMoment.scale s packetScale; gcongr; decide)
  · exact h1
  · apply h1.trans; rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left
    exact ((Nat.mul_le_mul_right b (S8G.FpMoment.blockUpper b)).trans (by nlinarith : (b+2)*b ≤ (b+1)^2)).trans (Nat.pow_le_pow_right (by omega) (by omega))
  · exact build
  · intro v a; refine ⟨?_,eval v a⟩
    have hi : v.val < 2*s := v.isLt.trans_le hv
    have hd : ((w3_factorGraph L).subdivision.deg v) ≤ 2*L.ne := (List.length_filter_le ..).trans (List.length_finRange.le.trans ((w3_factorGraph L).subdivision_nE.le))
    have hc := w3_queryIndexLength v.val; rw [w3_queryExactLength,List.length_ofFn]
    exact (by omega : _ ≤ 10*(s+w.length+1)).trans (Nat.mul_le_mul (by decide) (Nat.le_self_pow (by decide) _))
end Packet
end DetDLP.S8L.Bounds


