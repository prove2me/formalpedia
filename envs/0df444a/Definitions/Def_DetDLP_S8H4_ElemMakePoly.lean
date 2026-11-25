-- Prove2me | Definitions.Def_DetDLP_S8H4_ElemMakePoly
-- name    : DetDLP_S8H4_ElemMakePoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T02:07:12.02681+00:00
-- url     : https://prove2.me/theorems/b5be3e00-4087-51c9-ab8b-1c0228223958
-- title:
--   Polynomial EC element packet builder
-- statement:
--   Constructs the cycle-coded wire packet and proves a polynomial-time bound on arbitrary input words.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H4_TracksPoly
import Definitions.Def_DetDLP_S8H4_ElemDecoder
set_option autoImplicit false
namespace DetDLP.S8H4.ElemMake
open Groundwork S8H0 S8H.PointAddresses GateSemantics DetDLP_W1_Queries M89S1 S8H S8C
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open ElemDecoder (prime pfx)
attribute [local fun_prop] PolyT.mul PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.id' PolyT.ite' PolyT.decide_lt w4_M5Evaluator.clog2_poly
private def field (w : W) := first (second w)
def len (w : W) := min (pfx w).length (2*bitLen (prime w)+1)
abbrev names (p l : ℕ) := TracksPoly.sigNat (d p) (e p) (bitLen p) l
abbrev code (p l : ℕ) := CycleCode.code (BaseCode.elemCode p l) (names p l)
def make (w : W) := let p := prime w; let a := code p (len w); outerPacket w (WirePacket.packet (a.ng+a.nb) a.ne a.gate (fun i => a.ng+a.bit i)) (OrderPacket.scale (bitLen p))
private theorem small {f : W → ℕ} (h : PolyT f) (b : ∀ w, f w ≤ 4*OrderPacket.scale (bitLen (prime w))) : Unary f := by
  have hf : PolyT field := first_poly (first_poly (more_poly PolyT.id'))
  let l (w : W) := ((field w)++[false,false]).flatMap fun _ => List.replicate 4194304 (); have hl : PolyT l := PolyT.flatMap (PolyT.const _) (PolyT.append hf (PolyT.const _))
  have H (w : W) : f w ≤ (l w).length := by
    have hb : bitLen (prime w) ≤ (field w).length := Nat.clog_le_of_le_pow (PolyT.bval_lt (field w)).le; specialize b w
    simp only [l,List.length_flatMap,List.map_const',List.sum_replicate_nat,List.length_replicate,List.length_append,List.length_cons,List.length_nil] ; change f w ≤ ((field w).length+2)*4194304; apply b.trans; unfold OrderPacket.scale; rw [← Nat.mul_assoc,Nat.mul_comm ((field w).length+2)]; exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hb 2)
  simpa only [Nat.min_eq_left (H _)] using PolyT.unary_min_length h hl
theorem make_poly : PolyT make := by
  have hp : PolyT prime := S8M.ECPair.Packet.prime_poly
  have hl : PolyT len := by
    have P : PolyT (fun w => (pfx w).length) := PolyT.length S8M.ECPair.Packet.prefix_poly
    have B : PolyT fun w => bitLen (prime w) := w4_M5Evaluator.clog2_poly hp
    have Q := PolyT.add (PolyT.mul (PolyT.const 2) B) (PolyT.const 1)
    exact (PolyT.ite' (PolyT.decide_lt P Q) P Q).congr fun w => by simp only [len]; split <;> omega
  let f := fun w => BaseCode.elemCode (prime w) (len w)
  have g := BaseCode.uniform.ng hp hl; have n := BaseCode.uniform.ne hp hl; have ga := PolyT.add g n
  have N := PolyT.add n (PolyT.add n n); have V := PolyT.add ga n
  have bound (w : W) : let a := f w; a.ng+a.ne ≤ OrderPacket.scale (bitLen (prime w)) ∧ 2*(a.ne+(a.ne+a.ne)) < OrderPacket.scale (bitLen (prime w)) := by
    let p := prime w; let η := (pfx w).take (2*bitLen p+1)
    have hη : η.length ≤ 2*bitLen p+1 := by simp [η]
    have hlen : η.length = len w := by simp [η,len,p,Nat.min_comm]
    let c : GateRoutes.Coeff := ⟨0,0,0,0,0⟩
    have M := BaseCode.models p 0 0 0 0 0 c η
    have G := Semantics.gateBudget p 0 0 0 0 0 c η hη
    have E := Semantics.edgeBudget p 0 0 0 0 0 c η hη
    change (BaseCode.elemCode p (len w)).ng+_ ≤ _ ∧ _
    dsimp only [f]; rw [← hlen,M.ng,M.ne]; exact ⟨G,E⟩
  have bo {a b s : ℕ} (h : a+b ≤ s ∧ 2*(b+(b+b))<s) : b≤4*s ∧ a+b+b+(b+(b+b))≤4*s ∧ (b+(b+b))+(b+(b+b))≤4*s := by omega
  have hs : PolyT fun z : W × ℕ => names (prime z.1) (len z.1) z.2 := by
    have h : PolyT fun z : W × ℕ => d (prime z.1) := by unfold d ECPointArithmetic.width bitLen; fun_prop
    apply TracksPoly.sigNat_poly h _ _ (PolyT.comp hl (PolyT.fst PolyT.id')) (PolyT.snd PolyT.id')
    · exact (mul_poly.nb h).congr fun z => wires_eq (hd _)
    · unfold bitLen; fun_prop
  have H := CycleCode.endpoints_poly (c:=f) (name:=fun w => names (prime w) (len w)) g n (small n fun w => (bo (bound w)).1) (BaseCode.uniform.gate (PolyT.comp hp (PolyT.fst PolyT.id')) (PolyT.comp hl (PolyT.fst PolyT.id')) (PolyT.snd PolyT.id')) hs
  have s : PolyT fun w => OrderPacket.scale (bitLen (prime w)) := by unfold OrderPacket.scale bitLen; fun_prop
  have gg := PolyT.comp ga (PolyT.fst (PolyT.id' (α:=W × ℕ))); have dst := PolyT.add gg H.2
  exact outerPacket_poly PolyT.id' (WirePacket.packet_poly (src:=fun w => (code (prime w) (len w)).gate) (dst:=fun w i => (code (prime w) (len w)).ng+(code (prime w) (len w)).bit i) V N (small (PolyT.add V N) fun w => (bo (bound w)).2.1) (small (PolyT.add N N) fun w => (bo (bound w)).2.2) H.1 dst) s
end DetDLP.S8H4.ElemMake


