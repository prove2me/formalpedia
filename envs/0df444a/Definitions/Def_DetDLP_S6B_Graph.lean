-- Prove2me | Definitions.Def_DetDLP_S6B_Graph
-- name    : DetDLP_S6B_Graph
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:34:32.621223+00:00
-- url     : https://prove2.me/theorems/195bb1af-c962-4c98-a824-51f915e72c0c
-- title:
--   Polynomial-time printer for the numbered multiplication graph
-- statement:
--   From a unary width $d\ge1$, emit the canonical graph encoding of the multiplication network. The printer lists the bipartition colors in vertex order and both endpoints in edge order. Its output agrees exactly with the graph field required by the contraction machine, and the printing function has polynomial running time.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proposition 2.6 (pp. 10–11)

import Definitions.Def_DetDLP_W4_M5GateOps
import Definitions.Def_DetDLP_W5_M6Sort

set_option autoImplicit false
namespace DetDLP.S6BGraph
open Groundwork Groundwork.PolyT w4_MulParams w4_M5GraphBounds w4_M5EdgeNat w4_M5GateOps w4_M5Evaluator
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] Groundwork.PolyT.const Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.comp Groundwork.PolyT.prodMk Groundwork.PolyT.mul Groundwork.PolyT.length Groundwork.PolyT.flatMap Groundwork.PolyT.map P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_ite__226169acf219 P2M_Groundwork_PolyT_id__1c5d0f44cc8f J_poly L1_poly L2_poly n0_poly vertexCount_poly w5_M6Sort.cw_poly w5_M6Sort.encode_poly srcNat_poly dstNat_poly

private def sel (s : ℕ) (l : Bool) (r : ℕ → Bool) (y : ℕ) := if y < s then l else r (y-s)
private theorem leftS {s y : ℕ} {l : Bool} {r : ℕ → Bool} (h : y < s) : sel s l r y = l := if_pos h
private theorem rightS (s y : ℕ) (l : Bool) (r : ℕ → Bool) : sel s l r (s+y) = r y := by simp [sel]

def color (d : ℕ) : ℕ → Bool := sel (2*d) true $ sel (2*n0 d) false $ sel (2*L2 d) true $
  sel (2*L1 d) false $ sel (L2 d*L1 d) true $ sel (L1 d) false $ sel (L2 d) true $ sel (2*n0 d) false (fun _ => true)

theorem color_vertex {d : ℕ} (v : Vertex d) : color d (vertexIndex d v).val = side v := by
  cases v with
  | inputBit x y => let p := finProdFinEquiv (x,y); change color d (vNum d 0 p.val) = _; simp only [color,vNum,leftS p.isLt,side]
  | pack x y => let p := finProdFinEquiv (x,y); change color d (vNum d 1 p.val) = _; simp only [color,vNum,rightS,leftS p.isLt,side]
  | forward1 x y => let p := finProdFinEquiv (x,y); change color d (vNum d 2 p.val) = _; simp only [color,vNum,rightS,leftS p.isLt,side]
  | forward2 x y => let p := finProdFinEquiv (x,y); change color d (vNum d 3 p.val) = _; simp only [color,vNum,rightS,leftS p.isLt,side]
  | pointwise x y => let p := finProdFinEquiv (x,y); change color d (vNum d 4 p.val) = _; simp only [color,vNum,rightS,leftS p.isLt,side]
  | inverse1 y => change color d (vNum d 5 y.val) = _; simp only [color,vNum,rightS,leftS y.isLt,side]
  | inverse2 y => change color d (vNum d 6 y.val) = _; simp only [color,vNum,rightS,leftS y.isLt,side]
  | carry y => change color d (vNum d 7 y.val) = _; simp only [color,vNum,rightS,leftS y.isLt,side]
  | carrySpacer y => change color d (vNum d 8 y.val) = _; simp only [color,vNum,rightS,side]
  | outputBit y => change color d (vNum d 9 y.val) = _; simp only [color,vNum,rightS,side]

@[local fun_prop] theorem color_poly {α} [Enc α] {d v : α → ℕ} (hd : PolyT d) (hv : PolyT v) : PolyT (fun x => color (d x) (v x)) := by simp only [color,sel]; fun_prop

def colors (q : Pad) := (List.range (cap q (vertexCount q.length))).map (color q.length)
def ids (q : Pad) := (List.range (cap q (edgeCount q.length (W q.length)))).flatMap (fun i => [srcNat q.length i,dstNat q.length i])

def image (q : Pad) := Encoding.encodeList id [countWord (vertexCount q.length),countWord (edgeCount q.length (W q.length)),colors q,encodeNatListBin (ids q)]

private theorem range_as_fin (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem
  · simp
  · intro i hi hj; simp

theorem image_graph (q : Pad) (hd : 1 ≤ q.length) : image q = (graph q.length hd).encode := by
  let G := graph q.length hd
  have hv : vertexCount q.length ≤ 1100*(q.length+1) := (w4_M5QueryBridge.vertices_le hd).trans (by omega)
  have he : edgeCount q.length (W q.length) ≤ 1100*(q.length+1) := (graph_edge_bound hd).le
  have h1 : colors q = List.ofFn G.side := by
    rw [colors,cap,min_eq_left hv,range_as_fin,List.map_map,List.ofFn_eq_map]
    apply List.map_congr_left; intro i _
    simpa [G,graph] using color_vertex ((vertexIndex q.length).symm i)
  have h2 : ids q = (List.finRange G.nE).flatMap (fun i => [(G.endpoints i).1.val,(G.endpoints i).2.val]) := by
    rw [ids,cap,min_eq_left he,range_as_fin,List.flatMap_map]
    exact List.flatMap_congr fun i _ => by simp [srcNat,dstNat,endpointsNat_eq hd i,G]
  rw [image,h1,h2]; rfl

@[local fun_prop] theorem colors_poly {α} [Enc α] {q : α → Pad} (hq : PolyT q) : PolyT (fun x => colors (q x)) := by
  let hq' : PolyT (fun p : α × ℕ => q p.1) := Groundwork.PolyT.comp hq (Groundwork.PolyT.fst (f:=fun p : α × ℕ => p) Groundwork.PolyT.id')
  apply Groundwork.PolyT.map (l := fun x => List.range (cap (q x) (vertexCount (q x).length))) (f := fun x i => color (q x).length i) (color_poly (Groundwork.PolyT.length hq') (Groundwork.PolyT.snd (f:=fun p : α × ℕ => p) Groundwork.PolyT.id'))
  exact Groundwork.PolyT.range (cap_unary hq (by fun_prop))

@[local fun_prop] theorem ids_poly {α} [Enc α] {q : α → Pad} (hq : PolyT q) : PolyT (fun x => ids (q x)) := by
  have hq' : PolyT (fun p : α × ℕ => (q p.1).length) := Groundwork.PolyT.length (Groundwork.PolyT.comp hq (Groundwork.PolyT.fst (f:=fun p : α × ℕ => p) Groundwork.PolyT.id'))
  have hi : PolyT (fun p : α × ℕ => p.2) := Groundwork.PolyT.snd (f:=fun p : α × ℕ => p) Groundwork.PolyT.id'
  apply Groundwork.PolyT.flatMap (f := fun x i => [srcNat (q x).length i,dstNat (q x).length i]) (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (srcNat_poly hq' hi) (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (dstNat_poly hq' hi) (Groundwork.PolyT.const [])))
  exact Groundwork.PolyT.range (cap_unary hq (by simp only [edgeCount,W]; fun_prop))

private theorem frame_flat (w : List Bool) : Encoding.frame w = w.flatMap (fun b => [true,b]) ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [Encoding.frame, List.flatMap] using congrArg (fun u => true::b::u) ih

set_option maxHeartbeats 1000000 in
@[local fun_prop] theorem image_poly {α} [Enc α] {q : α → Pad} (hq : PolyT q) : PolyT (fun x => image (q x)) := by
  simp only [image,Encoding.encodeList,id_eq,frame_flat,edgeCount,W]; fun_prop
end DetDLP.S6BGraph


