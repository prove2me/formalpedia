-- Prove2me | Definitions.Def_DetDLP_S8H0_GraphBudget
-- name    : DetDLP_S8H0_GraphBudget
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:52:03.915365+00:00
-- url     : https://prove2.me/theorems/e9285216-7880-4772-918b-d7b497422630
-- title:
--   Size and incidence bounds for the point-check graph
-- statement:
--   Bounds the register, gate and edge counts of the elliptic-curve point-check graph by explicit functions of the modulus bit length.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_PointGraph
import Definitions.Def_DetDLP_S8H0_OrderPacket

set_option autoImplicit false
namespace DetDLP.S8H0.GraphBudget
open PointGraph GateSemantics GateRoutes RegisterMap NamedBlocks RangeRows
open w4_MulParams w4_M5GraphBounds S8H.PointAddresses

def sizeE (d e : ℕ) := 80*(d+1) + 7*(4*e+16*d + 5*(2*d) + 10*(d+1)) + 5*d + 1
def sizeG (d v : ℕ) := 16*(d+1) + 7*(2*v+8*d+2*d+2*(d+1)) + d + 1

theorem netE (p : ℕ) (c : Coeff) : (net p c).core.A.ne = sizeE (d p) (e p) := by
  simp only [net,network,RangeRows.block,CurveRows.block,HashRows.block,many,joinB,HashRows.product,eqs,
    HashRows.sumRows,checker,NamedBlocks.add,rows,mapped,S8J.join,S8C.AddLayout.layout,PointGraph.zeroLast,
    AnchoredLayout.anchors,w3_fpMulLayout,w3_m5Layout,w3_forgetSides,sizeE,e]; omega

theorem netG (p : ℕ) (c : Coeff) : (net p c).core.A.ng = sizeG (d p) (graph (d p) (hd p)).nV := by
  simp only [net,network,RangeRows.block,CurveRows.block,HashRows.block,many,joinB,HashRows.product,eqs,
    HashRows.sumRows,checker,NamedBlocks.add,rows,mapped,S8J.join,S8C.AddLayout.layout,PointGraph.zeroLast,
    AnchoredLayout.anchors,w3_fpMulLayout,w3_m5Layout,w3_forgetSides,sizeG]; omega

theorem baseV {d : ℕ} (hd : 1 ≤ d) : (graph d hd).nV ≤ 256*(d+1) := by
  have := J_lt_linear hd; have := n0_upper hd; have := L_le_half_J hd
  have := L1_le_L d; have := L2_le_L d; rw [graph_nV hd]; omega

theorem anchorSize (p : ℕ) : (S (d p) (e p)).size = regs (d p) := by
  unfold regs; rw [wires_eq (hd p)]

theorem edgeBudget (p : ℕ) (c : Coeff) : 2*(layout p c).ne < OrderPacket.scale (bitLen p) := by
  have h1 := netE p c; have h2 := regs_linear (hd p); have h3 := graph_edge_bound (hd p)
  change 2*((((S (d p) (e p)).size+1)+(net p c).core.A.ne) + ((((S (d p) (e p)).size+1)+(net p c).core.A.ne)+(((S (d p) (e p)).size+1)+(net p c).core.A.ne))) < _
  rw [h1,anchorSize]; simp only [sizeE,d,hd,e,OrderPacket.scale,S8H.ECPointArithmetic.width] at *; omega

theorem gateBudget (p : ℕ) (c : Coeff) : (layout p c).ng ≤ OrderPacket.scale (bitLen p) := by
  have h1 := netE p c; have h2 := regs_linear (hd p); have h3 := graph_edge_bound (hd p); have h4 := baseV (hd p)
  change ((S (d p) (e p)).size+1+(net p c).core.A.ng)+((S (d p) (e p)).size+1+(net p c).core.A.ne) ≤ _
  rw [h1,netG,anchorSize]; simp only [sizeE,sizeG,d,hd,e,OrderPacket.scale,S8H.ECPointArithmetic.width] at *; omega

end DetDLP.S8H0.GraphBudget


