-- Prove2me | Definitions.Def_DetDLP_S8L_FpPairAddresses
-- name    : DetDLP_S8L_FpPairAddresses
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:50:40.83287+00:00
-- url     : https://prove2.me/theorems/7e85958b-4ece-4667-9cd4-78e2a7992cce
-- title:
--   Numeric addresses for the pair-query arithmetic bank
-- statement:
--   The gate and bit endpoints of every arithmetic edge are computed by dividing by the size of one tile and applying its local address map. The address map agrees with the rectangular layout and is polynomial time for a polynomial-time tile count.

import Definitions.Def_DetDLP_S8L_FpPairTiles
import Definitions.Def_DetDLP_S8H_PointAddresses

set_option autoImplicit false
namespace DetDLP.S8L.FpPair.Address
open S8H.PointAddresses S8G.FpMoment S8J Groundwork

/-- The local edge number is the remainder, and the tile number is the quotient. -/
def repeatCode (m : ℕ) (a : Code) : Code := ⟨m*a.ng,m*a.nb,m*a.ne,
  fun e => a.gate (e%a.ne) + a.ng*(e/a.ne),
  fun e => a.bit (e%a.ne) + a.nb*(e/a.ne)⟩

theorem repeat_spec {a : Code} {A : w3_FactorLayout} (h : Models a A) (m : ℕ) :
    Models (repeatCode m a) (tiles m A) := by
  refine ⟨congrArg (m*·) h.ng,congrArg (m*·) h.nb,congrArg (m*·) h.ne,?_,?_⟩
  · intro e; change a.gate (e.val%a.ne) + a.ng*(e.val/a.ne) = _
    rw [h.ne,h.ng]; exact congrArg (· + A.ng*(e.val/A.ne)) (h.gate e.modNat)
  · intro e; change a.bit (e.val%a.ne) + a.nb*(e.val/a.ne) = _
    rw [h.ne,h.nb]; exact congrArg (· + A.nb*(e.val/A.ne)) (h.bit e.modNat)

def stageCode (d : ℕ) := sum (sum (mul d) (mul d)) (add (2*d))
def bankCode (m d : ℕ) := sum (repeatCode (2*m) (hash d)) (repeatCode (2*m-1) (stageCode d))

theorem stage_spec {d : ℕ} (hd : 1 ≤ d) : Models (stageCode d) (stage d hd) :=
  sum_spec (sum_spec (mul_spec hd) (mul_spec hd)) (add_spec _)

theorem bank_spec {d : ℕ} (hd : 1 ≤ d) (m : ℕ) :
    Models (bankCode m d) (bank m (HashGateLayout.layout d hd) (stage d hd)) :=
  sum_spec (repeat_spec (hash_spec hd) _) (repeat_spec (stage_spec hd) _)

attribute [local fun_prop] PolyT.mul PolyT.sub PolyT.div PolyT.mod PolyT.const

theorem repeat_poly {c : ℕ → Code} (h : Uniform c) {n : ℕ → ℕ}
    (hn : ∀ {α : Type} [Enc α] {d : α → ℕ}, PolyT d → PolyT fun x => n (d x)) :
    Uniform (fun d => repeatCode (n d) (c d)) := by
  constructor
  · intros; exact PolyT.mul (hn ‹_›) (h.ng ‹_›)
  · intros; exact PolyT.mul (hn ‹_›) (h.nb ‹_›)
  · intros; exact PolyT.mul (hn ‹_›) (h.ne ‹_›)
  · intro α _ d e hd he; exact PolyT.add (h.gate hd (PolyT.mod he (h.ne hd))) (PolyT.mul (h.ng hd) (PolyT.div he (h.ne hd)))
  · intro α _ d e hd he; exact PolyT.add (h.bit hd (PolyT.mod he (h.ne hd))) (PolyT.mul (h.nb hd) (PolyT.div he (h.ne hd)))

theorem stage_poly : Uniform stageCode := sum_poly (sum_poly mul_poly mul_poly) (add_poly _ (by intros; fun_prop))
theorem bank_poly {n : ℕ → ℕ} (hn : ∀ {α : Type} [Enc α] {d : α → ℕ}, PolyT d → PolyT fun x => n (d x)) :
    Uniform (fun d => bankCode (n d) d) := by
  apply sum_poly
  · exact repeat_poly hash_poly (fun h => PolyT.mul (PolyT.const 2) (hn h))
  · exact repeat_poly stage_poly (fun h => PolyT.sub (PolyT.mul (PolyT.const 2) (hn h)) (PolyT.const 1))

end DetDLP.S8L.FpPair.Address


