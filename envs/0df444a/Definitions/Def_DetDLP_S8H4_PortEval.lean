-- Prove2me | Definitions.Def_DetDLP_S8H4_PortEval
-- name    : DetDLP_S8H4_PortEval
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T12:59:19.452975+00:00
-- url     : https://prove2.me/theorems/a3afb07f-e2c1-4602-a013-bd9432ef6471
-- title:
--   Port evaluation
-- statement:
--   Polynomial-time bound for port evaluation
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H_PortCombinators
import Definitions.Def_DetDLP_S8H4_Semantics
import Definitions.Def_DetDLP_S8H4_ElemDecoder
import Definitions.Def_DetDLP_S8H4_PortPoly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DetDLP.S8H4.PortEval
open S8H0 S8H.PortCombinators GateSemantics S8J S8J.CircuitRealizes NamedBlocks RegisterMap GateRoutes Groundwork LocalGateEq
open ElemDecoder
abbrev port := PortPoly.port
theorem port_poly : Groundwork.PolyT port := PortPoly.port_poly
private abbrev tree := PortPoly.tree
private def net (p T a0 b0 a1 b1 : ℕ) (c : Coeff) (η : W) := joinB (PointGraph.zeroLast (Routes.bank (d p) (e p)).size) (Routes.network (hd p) p T a0 b0 a1 b1 c η)
private theorem fits (p T a0 b0 a1 b1 : ℕ) (c : Coeff) (η : W) :
    FitsG (tree (CoreCheck.pad p) (bitLen p) p T a0 b0 a1 b1 c η) (AnchoredLayout.block (net p T a0 b0 a1 b1 c η).core ((Routes.bank (d p) (e p)).size+1)) := by
  have hs : (Routes.bank (d p) (e p)).size+1 = regs (d p)+4*d p+2 := by
    change (GateRoutes.S (d p) (e p)).size + (d p + (d p + (d p + (d p+1)))) + 1 = _; rw [GraphBudget.anchorSize]; omega
  unfold tree; rw [pad_eq]; refine catG_spec (A:=⟨AnchoredLayout.anchors _,fun _ _ => true⟩) (B:=(net ..).core) ⟨hs.symm,fun _ _ => rfl⟩ ?_
  refine catB ⟨rfl,fun g w => (zeroLast_local _ g w).symm⟩ ?_
  unfold Routes.network; apply catB
  · change FitsG _ (joinB (RangeRows.block ..) (joinB _ _)).core
    refine catB (catB (catB (range_spec ..) (range_spec ..)) (many_spec fun _ => catB (range_spec ..) (range_spec ..))) (catB (many_spec fun i => hash_spec _ _ _ i.castSucc) ?_)
    refine ⟨rfl,fun i w => ?_⟩; unfold CurveRows.block; rw [rows_local]; rfl
  refine catB ?_ (catB ?_ (catB ?_ (catB ?_ ?_)))
  · unfold genHashG HashRows.block; refine catB (catB ?_ ?_) (catB ?_ (catB ?_ ?_))
    all_goals first | apply prod_spec | apply add_spec
    all_goals intros; simp only [Routes.network.six,wires,Routes.network.coord,rword,GateRoutes.quot,GateRoutes.word,HashRows.padded,HashRows.pub,regR,pinR,Ref.read,Function.comp_apply] <;> split_ifs <;> rfl
  · refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; simp [rowsG,Routes.network.coord,GateRoutes.word,HashRows.padded,Ref.read,Routes.network.a6Reg,Routes.network.b6Reg]
  · refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; simp [zeroLastG,Ref.read]
  · apply add_spec <;> intros <;> simp only [RangeRows.pad,regR,pinR,Ref.read] <;> split_ifs <;> rfl
  · refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; simp only [rowsG,List.getD_eq_getElem _ _ i.isLt]
    let refs := Routes.network.digits (d:=d p) (e:=e p) (bitLen p)
    have len : refs.length = 1+(bitLen p+bitLen p) := by simp [refs,Routes.network.digits]; omega
    by_cases h : i.val < refs.length
    · have mem := List.getElem_mem h; change refs[i.val] ∈ refs at mem
      simp only [refs,Routes.network.digits,List.mem_cons,List.mem_append,List.mem_ofFn] at mem
      have read : ∀ x, refs[i.val].read x = x := by
        intro x; simp only [refs,Routes.network.digits]; rcases mem with hm | ⟨j,hm⟩ | ⟨j,hm⟩
        · rw [hm]; rfl
        all_goals rw [←hm]; simp [Routes.network.coord,GateRoutes.word,HashRows.padded,Ref.read]
      change decide _ = decide (i.val < refs.length ∧ (refs[i.val]?.getD _).read _ = _)
      simp [List.getElem?_eq_getElem h,read,len]; rfl
    · change decide _ = decide (i.val < refs.length ∧ _); simp [←len,h]
open w4_M5Network in
/-- Every local port assignment yields the encoded bit of the subdivision tensor. -/
theorem port_eval {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (T : ℕ) (S : ECSeed p m) (i : Fin m) (η : W) :
    let a0 := (S i false).1.val+1; let b0 := (S i false).2.val
    let a1 := (S i true).1.val+1; let b1 := (S i true).2.val
    let A := Semantics.layout p T a0 b0 a1 b1 (GateSemantics.coeff E) η
    let t := Semantics.tests p T a0 b0 a1 b1 (GateSemantics.coeff E) η
    ∀ (v : Fin (w3_factorGraph A).subdivision.nV) (a : Fin ((w3_factorGraph A).subdivision.deg v) → Bool),
      port (encodePortQuery (word E T S i η) v.val (List.ofFn a)) = encodeNatListBin
        [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A t) v a then 1 else 0] := by
  dsimp only; intro v a; apply fullPort_eval (F:=PortPoly.decoded) (AnchoredLayout.block (net ..).core _) (AnchoredLayout.wiring (net ..).core (net ..).name)
  obtain ⟨hp,hT,_,_,hη,hc⟩ := fields E T S i η
  have H (k : Fin 4) := seedEntry_eq E T S i η k
  unfold PortPoly.decoded; simp only [width,hp,S8G.FpMoment.Code.width_eq,hT,hη,ElemDecoder.coeff,hc]
  have H0 := H 0; have H1 := H 1; have H2 := H 2; have H3 := H 3
  norm_num [Fin.isValue] at H0 H1 H2 H3
  rw [H0,H1,H2,H3]; exact fits ..
end DetDLP.S8H4.PortEval


