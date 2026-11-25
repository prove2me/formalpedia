-- Prove2me | Definitions.Def_DetDLP_W4_M5Dispatch
-- name    : DetDLP_W4_M5Dispatch
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T02:54:44.585007+00:00
-- url     : https://prove2.me/theorems/50922846-af77-4c3e-9eb4-e4fc9bdfc5b3
-- title:
--   Polynomial-time dispatch on the numbered multiplication-network vertices

import Definitions.Def_DetDLP_W4_M5GateNat
set_option autoImplicit false
namespace DetDLP.w4_M5Dispatch
open Groundwork Groundwork.PolyT w4_MulParams w4_M5GraphBounds w4_M5GateOps w4_M5GateNat w4_M5Evaluator w4_M5EdgeNat
attribute [local fun_prop] Groundwork.PolyT.const Groundwork.PolyT.div Groundwork.PolyT.mod Groundwork.PolyT.mul Groundwork.PolyT.prodMk Groundwork.PolyT.length P2M_Groundwork_PolyT_ite__226169acf219 n0_poly L1_poly L2_poly vertexCount_poly pack_poly forward1_poly forward2_poly pointwise_poly inverse1_poly inverse2_poly carry_poly carrySpacer_poly
attribute [local irreducible] vertexCount n0 L1 L2 pack forward1 forward2 pointwise inverse1 inverse2 carry carrySpacer
private def sel (s : ℕ) (l r : ℕ → Bool) (y : ℕ) := if y < s then l y else r (y-s)
private theorem leftS {s y} {l r : ℕ → Bool} (h : y < s) : sel s l r y = l y := if_pos h
private theorem rightS (s y) (l r : ℕ → Bool) : sel s l r (s+y) = r y := by simp [sel]
private def run (c : Ctx) (d : ℕ) : ℕ → Bool :=
  sel (2*d) (fun _ => true) $
  sel (2*n0 d) (fun y => pack c (y / (n0 d)) (y % (n0 d))) $
  sel (2*L2 d) (fun y => forward1 c (y / (L2 d)) (y % (L2 d))) $
  sel (2*L1 d) (fun y => forward2 c (y / (L1 d)) (y % (L1 d))) $
  sel (L2 d*L1 d) (fun y => pointwise c (y / (L1 d)) (y % (L1 d))) $
  sel (L1 d) (fun y => inverse1 c y) $
  sel (L2 d) (fun y => inverse2 c y) $
  sel (2*n0 d) (fun y => carry c y) $
  sel (2*n0 d-1) (fun y => carrySpacer c y) (fun _ => true)
def evalNat (q : Pad) (v : ℕ) (a : List Bool) := if 1 ≤ q.length then if v < vertexCount q.length then run (q,v,a) q.length v else false else false
set_option maxHeartbeats 1000000 in
theorem evalNat_poly {α} [Enc α] {q : α → Pad} {v : α → ℕ} {a : α → List Bool} (hq : PolyT q) (hv : PolyT v) (ha : PolyT a) : PolyT (fun x => evalNat (q x) (v x) (a x)) := by simp only [evalNat,run,sel]; fun_prop

def gate (c : Ctx) {d : ℕ} : Vertex d → Bool
  | .inputBit x y => true
  | .pack x y => pack c x y
  | .forward1 x y => forward1 c x y
  | .forward2 x y => forward2 c x y
  | .pointwise x y => pointwise c x y
  | .inverse1 y => inverse1 c y
  | .inverse2 y => inverse2 c y
  | .carry y => carry c y
  | .carrySpacer y => carrySpacer c y
  | .outputBit y => true
private theorem dv {n m} (x : Fin n) (y : Fin m) : (finProdFinEquiv (x,y)).val / m = x.val := by change (y.val+m*x.val)/m = _; rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt y.isLt),Nat.div_eq_of_lt y.isLt,Nat.zero_add]
private theorem md {n m} (x : Fin n) (y : Fin m) : (finProdFinEquiv (x,y)).val % m = y.val := by change (y.val+m*x.val)%m = _; simp [Nat.mod_eq_of_lt y.isLt]
private theorem run_gate (c : Ctx) (d : ℕ) (u : Vertex d) : run c d (vertexIndex d u).val = gate c u := by
  cases u with
  | inputBit x y =>
    let p := finProdFinEquiv (x,y)
    change run c d (vNum d 0 p.val) = _
    simp only [run,vNum,rightS,leftS p.isLt,p,dv,md,gate]
  | pack x y =>
    let p := finProdFinEquiv (x,y)
    change run c d (vNum d 1 p.val) = _
    simp only [run,vNum,rightS,leftS p.isLt,p,dv,md,gate]
  | forward1 x y =>
    let p := finProdFinEquiv (x,y)
    change run c d (vNum d 2 p.val) = _
    simp only [run,vNum,rightS,leftS p.isLt,p,dv,md,gate]
  | forward2 x y =>
    let p := finProdFinEquiv (x,y)
    change run c d (vNum d 3 p.val) = _
    simp only [run,vNum,rightS,leftS p.isLt,p,dv,md,gate]
  | pointwise x y =>
    let p := finProdFinEquiv (x,y)
    change run c d (vNum d 4 p.val) = _
    simp only [run,vNum,rightS,leftS p.isLt,p,dv,md,gate]
  | inverse1 y =>
    let p := y
    change run c d (vNum d 5 p.val) = _
    simp only [run,vNum,rightS,leftS p.isLt,p,dv,md,gate]
  | inverse2 y =>
    let p := y
    change run c d (vNum d 6 p.val) = _
    simp only [run,vNum,rightS,leftS p.isLt,p,dv,md,gate]
  | carry y =>
    let p := y
    change run c d (vNum d 7 p.val) = _
    simp only [run,vNum,rightS,leftS p.isLt,p,dv,md,gate]
  | carrySpacer y =>
    let p := y
    change run c d (vNum d 8 p.val) = _
    simp only [run,vNum,rightS,leftS p.isLt,p,dv,md,gate]
  | outputBit y =>
    let p := y
    change run c d (vNum d 9 p.val) = _
    simp only [run,vNum,rightS,leftS p.isLt,p,dv,md,gate]
theorem evalNat_at (q : Pad) (hd : 1 ≤ q.length) (u : Vertex q.length) (a : List Bool) : evalNat q (vertexIndex q.length u).val a = gate (q,(vertexIndex q.length u).val,a) u := by rw [evalNat,if_pos hd,if_pos (vertexIndex q.length u).isLt,run_gate]
end DetDLP.w4_M5Dispatch


