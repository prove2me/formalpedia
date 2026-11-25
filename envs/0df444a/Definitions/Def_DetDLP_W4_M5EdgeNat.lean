-- Prove2me | Definitions.Def_DetDLP_W4_M5EdgeNat
-- name    : DetDLP_W4_M5EdgeNat
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T02:12:15.112217+00:00
-- url     : https://prove2.me/theorems/1b9480fd-643e-42c4-9bbd-9d3ffec3d8cf
-- title:
--   Natural-number endpoints for the multiplication graph
-- statement:
--   Both endpoint projections are polynomial-time computable and agree with the graph incidence map on every valid edge index.

import Definitions.Def_DetDLP_W4_M5PortEval

set_option autoImplicit false
namespace DetDLP.w4_M5EdgeNat
open Groundwork Groundwork.PolyT w4_MulParams w4_M5GraphBounds w4_M5Evaluator
attribute [local fun_prop] Groundwork.PolyT.comp P2M_Groundwork_PolyT_id__1c5d0f44cc8f Groundwork.PolyT.mul Groundwork.PolyT.div Groundwork.PolyT.mod Groundwork.PolyT.const Groundwork.PolyT.prodMk Groundwork.PolyT.fst Groundwork.PolyT.snd P2M_Groundwork_PolyT_ite__226169acf219 J_poly L1_poly L2_poly n0_poly
set_option maxHeartbeats 2000000

def vNum (d : ℕ) : ℕ → ℕ → ℕ
  | 0, y => y
  | 1, y => ((2*d) + y)
  | 2, y => ((2*d) + ((2*n0 d) + y))
  | 3, y => ((2*d) + ((2*n0 d) + ((2*L2 d) + y)))
  | 4, y => ((2*d) + ((2*n0 d) + ((2*L2 d) + ((2*L1 d) + y))))
  | 5, y => ((2*d) + ((2*n0 d) + ((2*L2 d) + ((2*L1 d) + ((L2 d*L1 d) + y)))))
  | 6, y => ((2*d) + ((2*n0 d) + ((2*L2 d) + ((2*L1 d) + ((L2 d*L1 d) + ((L1 d) + y))))))
  | 7, y => ((2*d) + ((2*n0 d) + ((2*L2 d) + ((2*L1 d) + ((L2 d*L1 d) + ((L1 d) + ((L2 d) + y)))))))
  | 8, y => ((2*d) + ((2*n0 d) + ((2*L2 d) + ((2*L1 d) + ((L2 d*L1 d) + ((L1 d) + ((L2 d) + ((2*n0 d) + y))))))))
  | _, y => ((2*d) + ((2*n0 d) + ((2*L2 d) + ((2*L1 d) + ((L2 d*L1 d) + ((L1 d) + ((L2 d) + ((2*n0 d) + ((2*n0 d-1) + y)))))))))

def edgeBase (d : ℕ) : ℕ → ℕ → ℕ
  | 0, y => y
  | 1, y => (((2)*(d)) + y)
  | 2, y => (((2)*(d)) + (((2)*((n0 d)*(W d))) + y))
  | 3, y => (((2)*(d)) + (((2)*((n0 d)*(W d))) + (((2)*((L2 d)*((L1 d)*(W d)))) + y)))
  | 4, y => (((2)*(d)) + (((2)*((n0 d)*(W d))) + (((2)*((L2 d)*((L1 d)*(W d)))) + (((2)*((L2 d)*((L1 d)*(W d)))) + y))))
  | 5, y => (((2)*(d)) + (((2)*((n0 d)*(W d))) + (((2)*((L2 d)*((L1 d)*(W d)))) + (((2)*((L2 d)*((L1 d)*(W d)))) + (((L2 d)*((L1 d)*(W d))) + y)))))
  | 6, y => (((2)*(d)) + (((2)*((n0 d)*(W d))) + (((2)*((L2 d)*((L1 d)*(W d)))) + (((2)*((L2 d)*((L1 d)*(W d)))) + (((L2 d)*((L1 d)*(W d))) + (((L2 d)*((L1 d)*(W d))) + y))))))
  | 7, y => (((2)*(d)) + (((2)*((n0 d)*(W d))) + (((2)*((L2 d)*((L1 d)*(W d)))) + (((2)*((L2 d)*((L1 d)*(W d)))) + (((L2 d)*((L1 d)*(W d))) + (((L2 d)*((L1 d)*(W d))) + (((2*n0 d)*(W d)) + y)))))))
  | 8, y => (((2)*(d)) + (((2)*((n0 d)*(W d))) + (((2)*((L2 d)*((L1 d)*(W d)))) + (((2)*((L2 d)*((L1 d)*(W d)))) + (((L2 d)*((L1 d)*(W d))) + (((L2 d)*((L1 d)*(W d))) + (((2*n0 d)*(W d)) + (((2*n0 d-1)*(W d)) + y))))))))
  | _, y => (((2)*(d)) + (((2)*((n0 d)*(W d))) + (((2)*((L2 d)*((L1 d)*(W d)))) + (((2)*((L2 d)*((L1 d)*(W d)))) + (((L2 d)*((L1 d)*(W d))) + (((L2 d)*((L1 d)*(W d))) + (((2*n0 d)*(W d)) + (((2*n0 d-1)*(W d)) + (((2*n0 d-1)*(W d)) + y)))))))))

def edgePair (d : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, y => (vNum d 0 ((y % (d)) + (d) * (y / (d))), vNum d 1 ((y % (d)) / k d + (n0 d) * (y / (d))))
  | 1, y => (vNum d 1 (((y % ((n0 d)*(W d))) / (W d)) + (n0 d) * (y / ((n0 d)*(W d)))), vNum d 2 ((((y % ((n0 d)*(W d))) / (W d)) % L2 d) + (L2 d) * (y / ((n0 d)*(W d)))))
  | 2, y => (vNum d 2 (((y % ((L2 d)*((L1 d)*(W d)))) / ((L1 d)*(W d))) + (L2 d) * (y / ((L2 d)*((L1 d)*(W d))))), vNum d 3 ((((y % ((L2 d)*((L1 d)*(W d)))) % ((L1 d)*(W d))) / (W d)) + (L1 d) * (y / ((L2 d)*((L1 d)*(W d))))))
  | 3, y => (vNum d 3 ((((y % ((L2 d)*((L1 d)*(W d)))) % ((L1 d)*(W d))) / (W d)) + (L1 d) * (y / ((L2 d)*((L1 d)*(W d))))), vNum d 4 ((((y % ((L2 d)*((L1 d)*(W d)))) % ((L1 d)*(W d))) / (W d)) + (L1 d) * ((y % ((L2 d)*((L1 d)*(W d)))) / ((L1 d)*(W d)))))
  | 4, y => (vNum d 4 (((y % ((L1 d)*(W d))) / (W d)) + (L1 d) * (y / ((L1 d)*(W d)))), vNum d 5 (((y % ((L1 d)*(W d))) / (W d))))
  | 5, y => (vNum d 5 (((y % ((L1 d)*(W d))) / (W d))), vNum d 6 ((y / ((L1 d)*(W d)))))
  | 6, y => (vNum d 6 ((y / (W d)) % L2 d), vNum d 7 ((y / (W d))))
  | 7, y => (vNum d 7 ((y / (W d))), vNum d 8 ((y / (W d))))
  | 8, y => (vNum d 8 ((y / (W d))), vNum d 7 ((y / (W d))+1))
  | _, y => (vNum d 7 (y/k d), vNum d 9 (y))

private def selectBlock {β} (s : ℕ) (l r : ℕ → β) (i : ℕ) := if i < s then l i else r (i-s)
private theorem select_left {β} (s : ℕ) (l r : ℕ → β) {i : ℕ} (h : i < s) : selectBlock s l r i = l i := if_pos h
private theorem select_right {β} (s : ℕ) (l r : ℕ → β) (i : ℕ) : selectBlock s l r (s+i) = r i := by simp [selectBlock]

private def ep9 (d : ℕ) := edgePair d 9
private def ep8 (d : ℕ) := selectBlock ((2*n0 d-1)*(W d)) (edgePair d 8) (ep9 d)
private def ep7 (d : ℕ) := selectBlock ((2*n0 d-1)*(W d)) (edgePair d 7) (ep8 d)
private def ep6 (d : ℕ) := selectBlock ((2*n0 d)*(W d)) (edgePair d 6) (ep7 d)
private def ep5 (d : ℕ) := selectBlock ((L2 d)*((L1 d)*(W d))) (edgePair d 5) (ep6 d)
private def ep4 (d : ℕ) := selectBlock ((L2 d)*((L1 d)*(W d))) (edgePair d 4) (ep5 d)
private def ep3 (d : ℕ) := selectBlock ((2)*((L2 d)*((L1 d)*(W d)))) (edgePair d 3) (ep4 d)
private def ep2 (d : ℕ) := selectBlock ((2)*((L2 d)*((L1 d)*(W d)))) (edgePair d 2) (ep3 d)
private def ep1 (d : ℕ) := selectBlock ((2)*((n0 d)*(W d))) (edgePair d 1) (ep2 d)
def endpointsNat (d : ℕ) := selectBlock ((2)*(d)) (edgePair d 0) (ep1 d)
abbrev srcNat (d e : ℕ) := (endpointsNat d e).1
abbrev dstNat (d e : ℕ) := (endpointsNat d e).2

section
variable {α} [Enc α] {d e : α → ℕ} (hd : PolyT d) (he : PolyT e)
include hd he
@[local fun_prop] private theorem pair0_poly : PolyT (fun x => edgePair (d x) 0 (e x)) := by simp only [edgePair,vNum,k,W]; fun_prop
@[local fun_prop] private theorem pair1_poly : PolyT (fun x => edgePair (d x) 1 (e x)) := by simp only [edgePair,vNum,k,W]; fun_prop
@[local fun_prop] private theorem pair2_poly : PolyT (fun x => edgePair (d x) 2 (e x)) := by simp only [edgePair,vNum,k,W]; fun_prop
@[local fun_prop] private theorem pair3_poly : PolyT (fun x => edgePair (d x) 3 (e x)) := by simp only [edgePair,vNum,k,W]; fun_prop
@[local fun_prop] private theorem pair4_poly : PolyT (fun x => edgePair (d x) 4 (e x)) := by simp only [edgePair,vNum,k,W]; fun_prop
@[local fun_prop] private theorem pair5_poly : PolyT (fun x => edgePair (d x) 5 (e x)) := by simp only [edgePair,vNum,k,W]; fun_prop
@[local fun_prop] private theorem pair6_poly : PolyT (fun x => edgePair (d x) 6 (e x)) := by simp only [edgePair,vNum,k,W]; fun_prop
@[local fun_prop] private theorem pair7_poly : PolyT (fun x => edgePair (d x) 7 (e x)) := by simp only [edgePair,vNum,k,W]; fun_prop
@[local fun_prop] private theorem pair8_poly : PolyT (fun x => edgePair (d x) 8 (e x)) := by simp only [edgePair,vNum,k,W]; fun_prop
@[local fun_prop] private theorem pair9_poly : PolyT (fun x => edgePair (d x) 9 (e x)) := by simp only [edgePair,vNum,k,W]; fun_prop
omit hd he in
private theorem select_poly {β} [Enc β] {s i : α → ℕ} {l r : α → ℕ → β} (hs : PolyT s) (hi : PolyT i)
    (hl : PolyT fun x => l x (i x)) (hr : PolyT fun x => r x (i x-s x)) : PolyT (fun x => selectBlock (s x) (l x) (r x) (i x)) := by
  exact Groundwork.PolyT.ite' (c := fun x => i x < s x) (by fun_prop) hl hr

private theorem ep9_poly : PolyT (fun x => ep9 (d x) (e x)) := pair9_poly hd he
private theorem ep8_poly : PolyT (fun x => ep8 (d x) (e x)) := by
  exact select_poly (s := fun x => (2*n0 (d x)-1)*(W (d x))) (i := e) (l := fun x => edgePair (d x) 8) (r := fun x => ep9 (d x)) (by simp only [W]; fun_prop) he (pair8_poly hd he) (ep9_poly hd (by simp only [W]; fun_prop))
private theorem ep7_poly : PolyT (fun x => ep7 (d x) (e x)) := by
  exact select_poly (s := fun x => (2*n0 (d x)-1)*(W (d x))) (i := e) (l := fun x => edgePair (d x) 7) (r := fun x => ep8 (d x)) (by simp only [W]; fun_prop) he (pair7_poly hd he) (ep8_poly hd (by simp only [W]; fun_prop))
private theorem ep6_poly : PolyT (fun x => ep6 (d x) (e x)) := by
  exact select_poly (s := fun x => (2*n0 (d x))*(W (d x))) (i := e) (l := fun x => edgePair (d x) 6) (r := fun x => ep7 (d x)) (by simp only [W]; fun_prop) he (pair6_poly hd he) (ep7_poly hd (by simp only [W]; fun_prop))
private theorem ep5_poly : PolyT (fun x => ep5 (d x) (e x)) := by
  exact select_poly (s := fun x => (L2 (d x))*((L1 (d x))*(W (d x)))) (i := e) (l := fun x => edgePair (d x) 5) (r := fun x => ep6 (d x)) (by simp only [W]; fun_prop) he (pair5_poly hd he) (ep6_poly hd (by simp only [W]; fun_prop))
private theorem ep4_poly : PolyT (fun x => ep4 (d x) (e x)) := by
  exact select_poly (s := fun x => (L2 (d x))*((L1 (d x))*(W (d x)))) (i := e) (l := fun x => edgePair (d x) 4) (r := fun x => ep5 (d x)) (by simp only [W]; fun_prop) he (pair4_poly hd he) (ep5_poly hd (by simp only [W]; fun_prop))
private theorem ep3_poly : PolyT (fun x => ep3 (d x) (e x)) := by
  exact select_poly (s := fun x => (2)*((L2 (d x))*((L1 (d x))*(W (d x))))) (i := e) (l := fun x => edgePair (d x) 3) (r := fun x => ep4 (d x)) (by simp only [W]; fun_prop) he (pair3_poly hd he) (ep4_poly hd (by simp only [W]; fun_prop))
private theorem ep2_poly : PolyT (fun x => ep2 (d x) (e x)) := by
  exact select_poly (s := fun x => (2)*((L2 (d x))*((L1 (d x))*(W (d x))))) (i := e) (l := fun x => edgePair (d x) 2) (r := fun x => ep3 (d x)) (by simp only [W]; fun_prop) he (pair2_poly hd he) (ep3_poly hd (by simp only [W]; fun_prop))
private theorem ep1_poly : PolyT (fun x => ep1 (d x) (e x)) := by
  exact select_poly (s := fun x => (2)*((n0 (d x))*(W (d x)))) (i := e) (l := fun x => edgePair (d x) 1) (r := fun x => ep2 (d x)) (by simp only [W]; fun_prop) he (pair1_poly hd he) (ep2_poly hd (by simp only [W]; fun_prop))
theorem endpointsNat_poly : PolyT (fun x => endpointsNat (d x) (e x)) := by
  exact select_poly (s := fun x => (2)*((d x))) (i := e) (l := fun x => edgePair (d x) 0) (r := fun x => ep1 (d x)) (by fun_prop) he (pair0_poly hd he) (ep1_poly hd (by fun_prop))

theorem srcNat_poly : PolyT (fun x => srcNat (d x) (e x)) := Groundwork.PolyT.fst (f := fun x => endpointsNat (d x) (e x)) (endpointsNat_poly hd he)
theorem dstNat_poly : PolyT (fun x => dstNat (d x) (e x)) := Groundwork.PolyT.snd (f := fun x => endpointsNat (d x) (e x)) (endpointsNat_poly hd he)
end

private theorem unpack_div {n m} (x : Fin n) (y : Fin m) : (y.val + m * x.val) / m = x.val := by rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt y.isLt),Nat.div_eq_of_lt y.isLt,Nat.zero_add]
private theorem unpack_mod {n m} (x : Fin n) (y : Fin m) : (y.val + m * x.val) % m = y.val := by simp [Nat.mod_eq_of_lt y.isLt]
private theorem fdiv {n m} (x : Fin n) (y : Fin m) : (finProdFinEquiv (x,y)).val / m = x.val := unpack_div x y
private theorem fmod {n m} (x : Fin n) (y : Fin m) : (finProdFinEquiv (x,y)).val % m = y.val := unpack_mod x y

theorem endpointsNat_eq {d} (hd : 1 ≤ d) (i : Fin (graph d hd).nE) : endpointsNat d i.val = (((graph d hd).endpoints i).1.val, ((graph d hd).endpoints i).2.val) := by
  obtain ⟨e,rfl⟩ := (edgeIndex d (W d)).surjective i
  simp only [graph,Equiv.symm_apply_apply]
  cases e with
  | input x0 x1 =>
    let p := finProdFinEquiv (x0, x1)
    change endpointsNat d (edgeBase d 0 p.val) = _
    simp only [endpointsNat,ep1,ep2,ep3,ep4,ep5,ep6,ep7,ep8,ep9,edgeBase,select_right,select_left _ _ _ p.isLt,edgePair,p,fdiv,fmod,vNum]
    rfl
  | packForward x0 x1 x2 =>
    let p := finProdFinEquiv (x0, finProdFinEquiv (x1, x2))
    change endpointsNat d (edgeBase d 1 p.val) = _
    simp only [endpointsNat,ep1,ep2,ep3,ep4,ep5,ep6,ep7,ep8,ep9,edgeBase,select_right,select_left _ _ _ p.isLt,edgePair,p,fdiv,fmod,vNum]
    rfl
  | forwardMiddle x0 x1 x2 x3 =>
    let p := finProdFinEquiv (x0, finProdFinEquiv (x1, finProdFinEquiv (x2, x3)))
    change endpointsNat d (edgeBase d 2 p.val) = _
    simp only [endpointsNat,ep1,ep2,ep3,ep4,ep5,ep6,ep7,ep8,ep9,edgeBase,select_right,select_left _ _ _ p.isLt,edgePair,p,fdiv,fmod,vNum]
    rfl
  | forwardPoint x0 x1 x2 x3 =>
    let p := finProdFinEquiv (x0, finProdFinEquiv (x1, finProdFinEquiv (x2, x3)))
    change endpointsNat d (edgeBase d 3 p.val) = _
    simp only [endpointsNat,ep1,ep2,ep3,ep4,ep5,ep6,ep7,ep8,ep9,edgeBase,select_right,select_left _ _ _ p.isLt,edgePair,p,fdiv,fmod,vNum]
    rfl
  | pointInverse x0 x1 x2 =>
    let p := finProdFinEquiv (x0, finProdFinEquiv (x1, x2))
    change endpointsNat d (edgeBase d 4 p.val) = _
    simp only [endpointsNat,ep1,ep2,ep3,ep4,ep5,ep6,ep7,ep8,ep9,edgeBase,select_right,select_left _ _ _ p.isLt,edgePair,p,fdiv,fmod,vNum]
    rfl
  | inverseMiddle x0 x1 x2 =>
    let p := finProdFinEquiv (x0, finProdFinEquiv (x1, x2))
    change endpointsNat d (edgeBase d 5 p.val) = _
    simp only [endpointsNat,ep1,ep2,ep3,ep4,ep5,ep6,ep7,ep8,ep9,edgeBase,select_right,select_left _ _ _ p.isLt,edgePair,p,fdiv,fmod,vNum]
    rfl
  | coefficient x0 x1 =>
    let p := finProdFinEquiv (x0, x1)
    change endpointsNat d (edgeBase d 6 p.val) = _
    simp only [endpointsNat,ep1,ep2,ep3,ep4,ep5,ep6,ep7,ep8,ep9,edgeBase,select_right,select_left _ _ _ p.isLt,edgePair,p,fdiv,fmod,vNum]
    rfl
  | carryLeft x0 x1 =>
    let p := finProdFinEquiv (x0, x1)
    change endpointsNat d (edgeBase d 7 p.val) = _
    simp only [endpointsNat,ep1,ep2,ep3,ep4,ep5,ep6,ep7,ep8,ep9,edgeBase,select_right,select_left _ _ _ p.isLt,edgePair,p,fdiv,fmod,vNum]
    rfl
  | carryRight x0 x1 =>
    let p := finProdFinEquiv (x0, x1)
    change endpointsNat d (edgeBase d 8 p.val) = _
    simp only [endpointsNat,ep1,ep2,ep3,ep4,ep5,ep6,ep7,ep8,ep9,edgeBase,select_right,select_left _ _ _ p.isLt,edgePair,p,fdiv,fmod,vNum]
    rfl
  | output x0 =>
    let p := x0
    change endpointsNat d (edgeBase d 9 p.val) = _
    simp only [endpointsNat,ep1,ep2,ep3,ep4,ep5,ep6,ep7,ep8,ep9,edgeBase,select_right,edgePair,p,fdiv,fmod,vNum]
    rfl

end DetDLP.w4_M5EdgeNat


