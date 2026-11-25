-- Prove2me | Definitions.Def_DetDLP_W3_GatedWireWeights
-- name    : DetDLP_W3_GatedWireWeights
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:16:52.620555+00:00
-- url     : https://prove2.me/theorems/efe5124b-6ab5-47af-bf34-8bb228524ba4
-- title:
--   Weighted local checks on a native wire graph
-- statement:
--   For a graph with one designated vertex per lookup slot, assign zero to a failed local check, one to an ordinary successful check, and the signed lookup factor to a successful lookup check. A failed global assignment then has zero weight, while an assignment that reads the addresses of a pair of tuples has precisely its prescribed product weight.

import Definitions.Def_DetDLP_W3_NativeLookupWeight
import Definitions.Def_DetDLP_W3_WireCore

set_option autoImplicit false
namespace DetDLP
open w4_M5Network

abbrev w3_lookupSlot (q : w3_Query) := Fin q.m × Fin 2 × Bool

def w3_wireLocal (G : WireGraph) (v : Fin G.nV) (a : Fin G.nE → Bool) (j : Fin (G.deg v)) : Bool :=
  a ((G.ports v).get j)

/-- Ordinary gates contribute only an indicator; lookup gates contribute a selected label word. -/
noncomputable def w3_gateWeight {q : w3_Query} {G : WireGraph} {n : ℕ}
    (slot : Fin G.nV ≃ (w3_lookupSlot q ⊕ Fin n))
    (address : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → ℕ)
    (check : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (v : Fin G.nV) (a : Fin (G.deg v) → Bool) : TruncPoly (w3_precision q) (w3_len q) :=
  if check v a then match slot v with
    | .inl (i,_,pos) => w3_addressWeight q i pos (address v a)
    | .inr _ => 1
  else 0

theorem w3_gateWeight_dead {q : w3_Query} {G : WireGraph} {n : ℕ}
    (slot : Fin G.nV ≃ (w3_lookupSlot q ⊕ Fin n))
    (address : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → ℕ)
    (check : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (a : Fin G.nE → Bool) (ha : ¬ G.Satisfies check a) :
    (∏ v, w3_gateWeight slot address check v (w3_wireLocal G v a)) = 0 := by
  classical
  change ¬ ∀ v, check v (w3_wireLocal G v a) = true at ha
  obtain ⟨v,hv⟩ := not_forall.mp ha
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [w3_gateWeight,hv])

theorem w3_gateWeight_live {q : w3_Query} {G : WireGraph} {n : ℕ}
    (slot : Fin G.nV ≃ (w3_lookupSlot q ⊕ Fin n))
    (address : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → ℕ)
    (check : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (a : Fin G.nE → Bool) (ha : G.Satisfies check a) (X Y : q.FB.BlockTuple)
    (inj : ∀ i, Function.Injective (q.addr i))
    (haddr : ∀ (i : Fin q.m) (s : Fin 2) (b : Bool),
      let v := slot.symm (.inl (i,s,b))
      address v (w3_wireLocal G v a) = q.addr i (if b then Y i s else X i s)) :
    (∏ v, w3_gateWeight slot address check v (w3_wireLocal G v a)) = w3_pairWeight q (X,Y) := by
  classical
  let f := fun v => w3_gateWeight slot address check v (w3_wireLocal G v a)
  change (∏ v, f v) = _
  have steps : (∏ v, f v) = ∏ t, f (slot.symm t) := (slot.symm.prod_comp f).symm
  rw [steps, Fintype.prod_sum_type]
  have hh (v) : check v (w3_wireLocal G v a) = true := ha v
  simp only [w3_lookupSlot, Fintype.prod_prod_type, Fintype.prod_bool, f, w3_gateWeight,
    hh, if_true, Equiv.apply_symm_apply, haddr, Bool.false_eq_true, if_false, Finset.prod_const_one,
    mul_one]
  simpa only [mul_comm] using w3_addressWeight_product q inj X Y

end DetDLP


