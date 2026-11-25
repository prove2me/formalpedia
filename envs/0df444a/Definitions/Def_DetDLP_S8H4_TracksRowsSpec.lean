-- Prove2me | Definitions.Def_DetDLP_S8H4_TracksRowsSpec
-- name    : DetDLP_S8H4_TracksRowsSpec
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T01:57:19.621842+00:00
-- url     : https://prove2.me/theorems/69cdc310-646c-5754-a271-26838e1b1e23
-- title:
--   Tracking names through primitive EC rows
-- statement:
--   Concatenation, addition and product rows track their semantic signal addresses.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H4_TracksPoly
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
namespace DetDLP.S8H4.TracksRowsSpec
open Groundwork S8H0 S8H.PointAddresses GateRoutes GateSemantics PointGraph RegisterMap NamedBlocks TracksPoly

set_option maxHeartbeats 3000000
def Tracks {k : ℕ} (a : R) (b : B k) := a.1=b.core.A.ne ∧ ∀ i, a.2 i.val=(b.name i).val
theorem cat_ok {k} {a b : R} {u v : B k} (h : Tracks a u) (j : Tracks b v) : Tracks (cat a b) (joinB u v) := by
  refine ⟨congrArg₂ Nat.add h.1 j.1,?_⟩; intro i; induction i using Fin.addCases with
  | left i => simpa [cat,joinB,h.1,i.isLt] using h.2 i | right i => simpa [cat,joinB,h.1] using j.2 i
theorem many_ok {k} (n) (f : Fin (n+1) → R) (b : Fin (n+1) → B k) (h : ∀ g, Tracks (f g) (b g)) : Tracks (manyR n f) (RangeRows.many n b) := by induction n with | zero => exact h 0 | succ n ih => exact cat_ok (h 0) (ih _ _ fun _ => h _)
theorem plus_ok {s n} {a b z c : ℕ → ℕ} {A B Z C : Fin n → Ref s} (v : Bool) (h : ∀ j : Fin n, a j=(A j).source.val ∧ b j=(B j).source.val ∧ z j=(Z j).source.val ∧ c j=(C j).source.val) : Tracks (plusRows n a b z c) (NamedBlocks.add v A B Z C) := by
  refine ⟨rfl,?_⟩; intro i; simp only [plusRows,(add_spec n).bit i,NamedBlocks.add,mapped,colRef]; generalize (S8C.AddLayout.layout n).bit i=k; generalize hj : k.val%4=l; have hl : l<4 := hj ▸ Nat.mod_lt _ (by decide); have H := h (⟨k.val/4,by have := k.isLt; change _<n*4 at this; omega⟩ : Fin n); interval_cases l <;> norm_num <;> tauto
theorem ext_val {d} (hd : 1≤d) (i : Fin (4*d)) : (w4_M5PortTensor.ext hd i).val = if i.val<2*d then i.val else (w4_M5GraphBounds.graph d hd).nE-2*d+(i.val-2*d) := by
  unfold w4_M5PortTensor.ext w4_M5PortTensor.extEdge; split
  · rw [if_pos (by omega)]; change i.val+d*0=i.val; omega
  · split
    · change i.val-d+d*1=i.val; omega
    · change _ = w4_M5GraphBounds.edgeCount d _-2*d+_; unfold w4_M5GraphBounds.edgeCount; change 2*d+(_+(_+(_+(_+(_+(_+(_+(_+(i.val-2*d))))))))) = _; omega
theorem prod_ok {s d} {hd : 1≤d} {off} {a b z : ℕ → ℕ} {A B Z : HashRows.Word s} {W : Fin (w3_fpMulLayout d hd).nb → Ref s} (h : ∀ j, a j=(A j).source.val ∧ b j=(B j).source.val ∧ z j=(Z j).source.val) (hw : ∀ j, off+j.val=(W j).source.val) : Tracks (prodR d (w4_M5GraphBounds.graph d hd).nE off a b z) (HashRows.product hd A B Z W) := by
  apply cat_ok <;> refine ⟨rfl,?_⟩
  · intro i; have H := hw ((w3_fpMulLayout d hd).bit i); rw [← (mul_spec hd).bit i] at H; simpa only [S8H.PointAddresses.mul,wires_eq hd,mapped] using H
  · intro i; obtain ⟨⟨j,k⟩,rfl⟩ := finProdFinEquiv.surjective i; fin_cases k <;> simp [eqs,rows,mapped,HashRows.busRef,finProdFinEquiv_apply_val,show (1+2*j.val)/2=j.val by omega]
    · simpa only [ext_val] using hw (w4_M5PortTensor.ext hd j)
    · split <;> first | exact (h _).1 | split <;> first | exact (h _).2.1 | exact (h _).2.2
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
theorem padded_val {s n} (f : Fin n → Ref s) (j) : (HashRows.padded f j).source.val = if h:j<n then (f ⟨j,h⟩).source.val else s.size := by unfold HashRows.padded; split <;> rfl
theorem rpad_val {s n m} (f : Fin n → Ref s) (j : Fin m) : (RangeRows.pad f j).source.val = if h:j.val<n then (f ⟨j,h⟩).source.val else s.size := by unfold RangeRows.pad; split <;> rfl
end DetDLP.S8H4.TracksRowsSpec


