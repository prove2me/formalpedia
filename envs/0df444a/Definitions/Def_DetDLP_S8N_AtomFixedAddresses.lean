-- Prove2me | Definitions.Def_DetDLP_S8N_AtomFixedAddresses
-- name    : DetDLP_S8N_AtomFixedAddresses
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T11:53:46.412626+00:00
-- url     : https://prove2.me/theorems/80df20af-1602-5e80-a76c-64d18095ce2a
-- title:
--   Physical register addresses for fixed elliptic-curve atom rows
-- statement:
--   The fixed rows in a moment atom read the same registers as the corresponding rows of the established point circuit after its selector is skipped. Contiguous routing preserves each source index and maps the constant pin to the global pin.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, elliptic-curve moment-query compiler.

import Definitions.Def_DetDLP_S8H4_TracksSpec
import Definitions.Def_DetDLP_S8M_ECAtomSlot

set_option autoImplicit false
namespace DetDLP.S8N.AtomFixedGeometry
open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes ResidueWires RangeRows HashRows
open S8H4.TracksPoly S8H4.TracksRowsSpec S8H4.TracksHashSpec
open private fixed from Definitions.Def_DetDLP_S8M_ECAtomSlot
open private base_ok remap_ok body_ok from Definitions.Def_DetDLP_S8H4_TracksSpec

private theorem right {k : ℕ} {a b : R} {u v : B k}
    (h : Tracks (cat a b) (joinB u v)) (hl : a.1 = u.core.A.ne) : Tracks b v := by
  refine ⟨?_, fun i => ?_⟩
  · have eq : a.1 + b.1 = u.core.A.ne + v.core.A.ne := h.1
    rw [hl] at eq
    exact Nat.add_left_cancel eq
  · simpa [cat, joinB, hl] using h.2 (Fin.natAdd u.core.A.ne i)

private theorem left {k : ℕ} {a b : R} {u v : B k}
    (h : Tracks (cat a b) (joinB u v)) (hl : a.1 = u.core.A.ne) : Tracks a u := by
  exact ⟨hl,fun i => by simpa [cat,joinB,hl,i.isLt] using h.2 (Fin.castAdd v.core.A.ne i)⟩

def table (d e : ℕ) : R :=
  cat (remap (baseR d e) (top d e) (newTop d e))
    (cat (hash6R d e) (cat (flagR d e) (ltR d e)))

/-- Recover the identical flag and comparator from the existing checked point network. -/
theorem tracks {d : ℕ} (hd : 1 ≤ d) (p T : ℕ) (c : Coeff) :
    Tracks (table d (w4_M5GraphBounds.graph d hd).nE) (fixed hd p T c) := by
  have net := body_ok hd 0 T 0 0 0 0 (show 0 ≤ d from Nat.zero_le _) c []
  have pbase := remap_ok (base_ok hd 0 c)
  have afterBase := right net pbase.1
  have afterHash := right afterBase (hash6_ok hd 0 c).1
  have afterMux := right afterHash rfl
  have flag := left afterMux rfl
  have threshold := left (right afterMux rfl) rfl
  exact cat_ok (remap_ok (base_ok hd p c)) (cat_ok (hash6_ok hd p c) (cat_ok flag threshold))

end DetDLP.S8N.AtomFixedGeometry

set_option autoImplicit false
namespace DetDLP.S8N.AtomFixedGeometry
open S8H4.TracksPoly
open private top_eq from Definitions.Def_DetDLP_S8H4_TracksPoly

theorem seedReg_eq (d e : ℕ) : 118*d+14*e+45 = top d e := (top_eq d e).symm

theorem slotWidth_eq (d e : ℕ) : (122*d+14*e+46) = newTop d e := by
  simp only [newTop,top_eq]
  omega

private theorem before_eq (d e : ℕ) :
    (remap (baseR d e) (top d e) (newTop d e)).1+(hash6R d e).1 = (337*d+28*e+150) := by
  have h (g : Fin 7) : (hashR d e g).1 = 4*e+36*d+10 := by
    change ((e+e+4*d*2)+(e+e+4*d*2))+(2*d*5+((d+1)*5+(d+1)*5)) = _
    omega
  have h6 : (hash6R d e).1 = 4*e+36*d+10 := by
    change ((e+e+4*d*2)+(e+e+4*d*2))+(2*d*5+((d+1)*5+(d+1)*5)) = _
    omega
  simp only [remap,baseR,rangesR,manyR,checkR,h,h6,cat,plusRows,curveR]
  omega

theorem width_eq (d e : ℕ) : (table d e).1 = (342*d+28*e+156) := by
  have hb := before_eq d e
  change (baseR d e).1+(hash6R d e).1=337*d+28*e+150 at hb
  change (baseR d e).1+((hash6R d e).1+(1+(d+1)*5))=342*d+28*e+156
  omega

private theorem past (a b c : R) (i : ℕ) (h : a.1+b.1 ≤ i) :
    (cat a (cat b c)).2 i = c.2 (i-(a.1+b.1)) := by
  have ha : ¬i<a.1 := by omega
  have hb : ¬i-a.1<b.1 := by omega
  simp [cat,ha,hb,Nat.sub_add_eq]

private theorem after (a b : R) (i : ℕ) : (cat a b).2 (a.1+i) = b.2 i := by simp [cat]

private theorem skip (a b m f t z : R) (i : ℕ) (hi : i < a.1+(b.1+(f.1+t.1))) :
    (cat a (cat b (cat f t))).2 i =
      (cat a (cat b (cat m (cat f (cat t z))))).2
        (if i<a.1+b.1 then i else m.1+i) := by
  split
  · rename_i h
    by_cases ha : i<a.1
    · simp [cat,ha]
    · have hb : i-a.1<b.1 := by omega
      simp [cat,ha,hb]
  · rename_i h
    rw [past _ _ _ i (by omega),past _ _ _ (m.1+i) (by omega)]
    rw [show m.1+i-(a.1+b.1) = m.1+(i-(a.1+b.1)) by omega,after]
    by_cases hf : i-(a.1+b.1)<f.1
    · simp [cat,hf]
    · have ht : i-(a.1+b.1)-f.1<t.1 := by omega
      simp [cat,hf,ht]

theorem localSource_eq (d e i : ℕ) (hi : i < (table d e).1) :
    sigNat d e 0 0 ((122*d+14*e+46)+2+(if i<337*d+28*e+150 then i else 3*d+i)) =
      (table d e).2 i := by
  let j := if i < (337*d+28*e+150) then i else 3*d+i
  change sigNat d e 0 0 ((122*d+14*e+46)+2+j) = _
  rw [slotWidth_eq,show newTop d e+2+j = (newTop d e+1)+(1+j) by omega]
  unfold sigNat route
  rw [after (newTop d e+1,id) _ (1+j),after (1,fun _ => newTop d e) _ j]
  have h := skip (remap (baseR d e) (top d e) (newTop d e)) (hash6R d e)
    (muxR d e) (flagR d e) (ltR d e) (preR d e 0 0) i hi
  simpa only [j,before_eq,muxR,Nat.mul_comm d 3,table] using h.symm

end DetDLP.S8N.AtomFixedGeometry

namespace DetDLP.S8N.AtomFixedGeometry
open S8H0 RegisterMap GateRoutes

private theorem indexAddress (t : Shape) (j : Fin t.size) :
    (S8M.ECAtomSlot.address t j).index = j := by
  induction t with
  | bit => exact Fin.ext (by have := j.isLt; change j.val < 1 at this; change 0 = j.val; omega)
  | word => rfl
  | pair l r il ir =>
    simp only [S8M.ECAtomSlot.address]
    split <;> simp only [Addr.index,il,ir] <;> apply Fin.ext
    · rfl
    · change l.size+(j.val-l.size)=j.val; omega
  | vec n t ih =>
    simp only [S8M.ECAtomSlot.address,Addr.index,ih,Prod.mk.eta]
    exact finProdFinEquiv.apply_symm_apply j

theorem routeIndex {l s : Shape} (q : Path l s) (off : ℕ)
    (hq : ∀ a, (q a).index.val = off+a.index.val) (v : Fin (l.size+1)) :
    (S8M.ECAtomSlot.route q v).val = if v.val=l.size then s.size else off+v.val := by
  induction v using Fin.lastCases with
  | last => simp [S8M.ECAtomSlot.route]
  | cast j =>
    simp only [Fin.val_castSucc,if_neg (Nat.ne_of_lt j.isLt),S8M.ECAtomSlot.route,
      Fin.lastCases_castSucc,hq,indexAddress]

end DetDLP.S8N.AtomFixedGeometry


