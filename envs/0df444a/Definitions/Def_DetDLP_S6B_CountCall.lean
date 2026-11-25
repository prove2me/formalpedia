-- Prove2me | Definitions.Def_DetDLP_S6B_CountCall
-- name    : DetDLP_S6B_CountCall
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:26:34.074213+00:00
-- url     : https://prove2.me/theorems/73bc5023-2d07-4314-b7a7-463f16d2914b
-- title:
--   One contraction machine for all prefix counts
-- statement:
--   Fix a polynomial-time local evaluator for the doubly pinned multiplication graph. The contraction hypothesis yields one machine, independent of the input width, product and pins, returning the encoded number of compatible products. At width $d$ its running time is at most $2^{Kd/\sqrt{\log_{\rm safe} d}}$ and its space usage is polynomial in $d$. The supplied graph is the explicit numbered multiplication graph; no advice giving a graph for each width is required.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proposition 2.6 (pp. 10–11)

import Definitions.Def_DetDLP_W4_M5PortTensor
import Definitions.Def_DetDLP_W4_M5QueryBridge
import Definitions.Def_DetDLP_W5_M6PinnedCount

set_option autoImplicit false
namespace DetDLP.S6BCountCall
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open w4_M5GraphBounds w4_M5PortTensor w5_M6DivisorConstraints w5_M6PinnedCount

abbrev instanceWord {d : ℕ} (hd : 1 ≤ d) (N : ℕ) (pin : Fin (4*d) → Option Bool) :=
  encodeBTNInstance (pinnedDesc d N pin) (graph d hd) (scale d) ((graph d hd).nE+1) 1

def entrySpec (f : List Bool → List Bool) :=
  ∀ (d : ℕ) (hd : 1 ≤ d) (N : ℕ) (pin : Fin (4*d) → Option Bool)
    (v : Fin (graph d hd).nV) (a : Fin ((graph d hd).deg v) → Bool),
    EncodesTruncPoly ((graph d hd).nE+1) 1
      (f (encodePortQuery (pinnedDesc d N pin) v.val (List.ofFn a)))
      (productEntry (graph d hd) (tensor hd) (ext hd) N pin v a)

private theorem queryLength {d : ℕ} (hd : 1 ≤ d) (N : ℕ) (pin : Fin (4*d) → Option Bool)
    (v : Fin (graph d hd).nV) (a : Fin ((graph d hd).deg v) → Bool) :
    (encodePortQuery (pinnedDesc d N pin) v.val (List.ofFn a)).length + 1 ≤ 4096*(d+1) := by
  have he := graph_edge_bound hd
  have hv := v.isLt.trans_le (w4_M5QueryBridge.vertices_le hd)
  have hc := w4_M5QueryBridge.length_countWord_le v.val
  have hdeg : (graph d hd).deg v ≤ (graph d hd).nE := by
    unfold BipartiteMultigraph.deg BipartiteMultigraph.ports
    exact (List.length_filter_le ..).trans List.length_finRange.le
  simp only [encodePortQuery,Encoding.encodeList,id_eq,List.length_cons,List.length_nil,
    List.length_append,w4_M5QueryBridge.length_frame,pinnedDesc_length,List.length_ofFn]
  omega

/-- The contraction machine is chosen before the width, product, and partial assignment. -/
theorem uniform (hc : ContractProp) (f : List Bool → List Bool) (hf : Groundwork.PolyT f)
    (hs : entrySpec f) : ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (K : ℕ),
      ∀ (d : ℕ) (hd : 1 ≤ d) (N : ℕ) (hN : N < 2^d) (pin : Fin (4*d) → Option Bool),
        RunsWithin M o (instanceWord hd N pin) (encodeNatListBin [completionCount (ProductIs N) pin])
          ((2:ℝ)^((K:ℝ)*d/Real.sqrt (logSafe d))) (polyBound K d) := by
  obtain ⟨E,outE,c,run⟩ := PolyTBridge.polyT_listBool_runsWithin f hf
  let B := max c (c*4096^c)
  obtain ⟨M,o,K,call⟩ := pinned_count_runsWithin hc 256 B E outE
  refine ⟨M,o,2336*K,?_⟩
  intro d hd N hN pin
  have hr := call d N (graph d hd) (tensor hd) (ext hd) pin (pinnedDesc d N pin)
    (hN.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    (graph_edge_bound hd) (graph_maxDeg_bound hd) (graph_vertex_bound hd) (parsimonious hd) (by
      intro v a
      let w := encodePortQuery (pinnedDesc d N pin) v.val (List.ofFn a)
      have hb : polyBound c w.length ≤ polyBound B d := w4_M5QueryBridge.absorb
        (queryLength hd N pin v a) (le_max_left ..) (le_max_right ..)
      exact ⟨f w, hs d hd N pin v a, PolyTBridge.runsWithin_mono_local (run w) hb hb⟩)
  rw [pinnedDesc_length] at hr
  exact PolyTBridge.runsWithin_mono_local hr (scaled_time K d hd)
    ((scaled_space K d hd).trans (w4_M5QueryBridge.polyBound_monoK (by omega)))
end DetDLP.S6BCountCall


