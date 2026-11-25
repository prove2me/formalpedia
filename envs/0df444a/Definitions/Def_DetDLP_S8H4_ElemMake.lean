-- Prove2me | Definitions.Def_DetDLP_S8H4_ElemMake
-- name    : DetDLP_S8H4_ElemMake
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T02:48:26.601749+00:00
-- url     : https://prove2.me/theorems/a059fdeb-1ccd-547b-bf49-fda9f1e4547a
-- title:
--   EC element packet constructor correctness
-- statement:
--   On valid tag-4 words, the polynomial constructor produces the exact semantic graph packet.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H4_TracksSpec
import Definitions.Def_DetDLP_S8H4_ElemMakePoly
set_option autoImplicit false
namespace DetDLP.S8H4.ElemMake
open S8H0 GateSemantics NamedBlocks S8H S8C DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
/-- On a valid element word, the polynomial builder writes the semantic graph, edge for edge. -/
theorem make_word {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (T : ℕ)
    (S : ECSeed p m) (i : Fin m) (η : List Bool) (hη : η.length ≤ 2*bitLen p+1) :
    let w := ElemDecoder.word E T S i η
    make w = encodeBTNInstance w (w3_factorGraph (Semantics.layout p T
      ((S i false).1.val+1) (S i false).2.val ((S i true).1.val+1) (S i true).2.val (coeff E) η)).subdivision
      (OrderPacket.scale (bitLen p)) (OrderPacket.scale (bitLen p)) 1 := by
  let a := (S i false).1.val+1; let b := (S i false).2.val
  let a' := (S i true).1.val+1; let b' := (S i true).2.val
  let N := joinB (PointGraph.zeroLast (Routes.bank (d p) (e p)).size) (Routes.network (hd p) p T a b a' b' (coeff E) η)
  obtain ⟨hp,_,_,_,hpre,_⟩ := ElemDecoder.fields E T S i η
  have M := CycleCode.packetEndpoints (BaseCode.models p T a b a' b' (coeff E) η) (names p η.length)
  dsimp only at M
  have spec := TracksSpec.sigNat_spec p T a b a' b' (coeff E) η
  have hn := AnchoredLayout.next_congr (fun j : Fin (AnchoredLayout.block N.core ((Routes.bank (d p) (e p)).size+1)).A.ne => names p η.length j.val) (AnchoredLayout.signal N.core N.name) (by intro j k; unfold names; rw [spec j,spec k]; exact Fin.val_inj)
  rw [hn] at M
  simp only [make,len,hp,hpre,Nat.min_eq_left hη,code]; rw [M.1,M.2.1,WirePacket.packet_eq _ _ _ M.2.2.1 M.2.2.2]; exact outerPacket_eq ..
end DetDLP.S8H4.ElemMake


