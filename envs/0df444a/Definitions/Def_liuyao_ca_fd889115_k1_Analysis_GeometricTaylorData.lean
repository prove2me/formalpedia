-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricTaylorData
-- name    : liuyao_ca_fd889115_k1_Analysis_GeometricTaylorData
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:45:37.139098+00:00
-- url     : https://prove2.me/theorems/20e907d8-ec3d-4c9a-8ff7-ff321e4dc51c
-- title:
--   Computable analysis · GeometricTaylorData · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/GeometricTaylorData.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricDerivative
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealDerivativeAlgebra

set_option autoImplicit true

/-! Successive geometric derivatives and quantitative data for Taylor.
This file does not assert a factorial remainder from a coefficient recurrence.
All real-input values are derived from the primary rational samplers. -/
namespace ComputableAnalysis.GeometricTrig
open RawLimit ComputableCoefficient RealApproximationOrder
set_option maxHeartbeats 300000

def evaluate (cosine : Bool) (x : RealCompute) : RealCompute := if cosine then cosAt x else sinAt x

theorem at_valid (cosine : Bool) {x : RealCompute} (hx : x.Valid) : (evaluate cosine x).Valid := by
  cases cosine
  · exact sinAt_valid hx
  · exact cosAt_valid hx

theorem at_rational (cosine : Bool) (q : Rat) : (evaluate cosine (RealCompute.ofRat q)).Equiv (sample cosine q) := by
  cases cosine
  · exact sinAt_rational q
  · exact cosAt_rational q

theorem at_congr (cosine : Bool) {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (he : x.Equiv y) :
    (evaluate cosine x).Equiv (evaluate cosine y) := by
  cases cosine
  · exact sinAt_congr hx hy he
  · exact cosAt_congr hx hy he

theorem at_small (cosine : Bool) {x : RealCompute} (hx : x.Valid) :
    Small (parameter (evaluate cosine x) (at_valid cosine hx)) 1 := by
  have bound (q : Rat) : InInterval (sample cosine q) {lo := -1,hi := 1} := by
    constructor
    · intro i j
      exact Rat.le_trans (sample_bounds cosine q j).1 (RealCompute.interval_order_of_valid _ (sample_valid _ _) j)
    · intro i j
      exact Rat.le_trans (RealCompute.interval_order_of_valid _ (sample_valid _ _) i) (sample_bounds cosine q i).2
  have cover (n : Nat) : InInterval (sample cosine (x.compute n).lo) ((evaluate cosine x).compute n) := by
    have h := LipschitzRealExtension.covers (sample_valid cosine) (L := 32) (by decide +kernel)
      (sample_lipschitz cosine) hx n ⟨Rat.le_refl,RealCompute.interval_order_of_valid _ hx n⟩
    cases cosine <;> exact h
  constructor
  · intro i j
    exact RealCompute.le_trans (sample_valid _ _) (bound (x.compute j).lo).1 (cover j).2 0 0
  · intro i j
    exact RealCompute.le_trans (sample_valid _ _) (cover i).1 (bound (x.compute i).lo).2 0 0

/-- The rational sampler for the successive derivative. -/
def jet : Nat → Bool → Rat → RealCompute
  | 0,cosine,q => sample cosine q
  | n+1,cosine,q => RealCompute.mul pi (if cosine then -(jet n false q) else jet n true q)

/-- Its represented-input value, derived from geometric sine/cosine. -/
def jetAt : Nat → Bool → RealCompute → RealCompute
  | 0,cosine,x => evaluate cosine x
  | n+1,cosine,x => RealCompute.mul pi (if cosine then -(jetAt n false x) else jetAt n true x)

theorem jet_valid (n : Nat) (cosine : Bool) (q : Rat) : (jet n cosine q).Valid := by
  induction n generalizing cosine with
  | zero => exact sample_valid cosine q
  | succ n ih =>
    cases cosine
    · exact RealCompute.mul_valid pi_valid (ih true)
    · exact RealCompute.mul_valid pi_valid (RealCompute.neg_valid (ih false))

theorem jetAt_valid (n : Nat) (cosine : Bool) {x : RealCompute} (hx : x.Valid) : (jetAt n cosine x).Valid := by
  induction n generalizing cosine with
  | zero => exact at_valid cosine hx
  | succ n ih =>
    cases cosine
    · exact RealCompute.mul_valid pi_valid (ih true)
    · exact RealCompute.mul_valid pi_valid (RealCompute.neg_valid (ih false))

theorem jetAt_rational (n : Nat) (cosine : Bool) (q : Rat) :
    (jetAt n cosine (RealCompute.ofRat q)).Equiv (jet n cosine q) := by
  induction n generalizing cosine with
  | zero => exact at_rational cosine q
  | succ n ih =>
    cases cosine
    · exact RealCompute.mul_equiv pi_valid pi_valid (jetAt_valid n true (RealCompute.ofRat_valid q))
        (jet_valid n true q) (RealCompute.equiv_refl _ pi_valid) (ih true)
    · exact RealCompute.mul_equiv pi_valid pi_valid (RealCompute.neg_valid (jetAt_valid n false (RealCompute.ofRat_valid q)))
        (RealCompute.neg_valid (jet_valid n false q)) (RealCompute.equiv_refl _ pi_valid) (RealCompute.neg_equiv (ih false))

theorem jetAt_congr (n : Nat) (cosine : Bool) {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (he : x.Equiv y) : (jetAt n cosine x).Equiv (jetAt n cosine y) := by
  induction n generalizing cosine with
  | zero => exact at_congr cosine hx hy he
  | succ n ih =>
    cases cosine
    · exact RealCompute.mul_equiv pi_valid pi_valid (jetAt_valid n true hx) (jetAt_valid n true hy)
        (RealCompute.equiv_refl _ pi_valid) (ih true)
    · exact RealCompute.mul_equiv pi_valid pi_valid (RealCompute.neg_valid (jetAt_valid n false hx))
        (RealCompute.neg_valid (jetAt_valid n false hy)) (RealCompute.equiv_refl _ pi_valid) (RealCompute.neg_equiv (ih false))

/-- Every member of the cycle is the actual derivative of its predecessor,
at every valid represented real. The sign and pi factors are retained. -/
theorem jet_derivative (n : Nat) (cosine : Bool) {x : RealCompute} (hx : x.Valid) :
    RealSecantDerivative.HasDerivativeAt (fun _ => True) (jet n cosine) x (jetAt (n+1) cosine x) := by
  induction n generalizing cosine with
  | zero =>
    cases cosine
    · exact sin_derivative hx
    · apply RealSecantDerivative.congr_value (cos_derivative hx) (jetAt_valid 1 true hx)
      let S := parameter (sinAt x) (sinAt_valid hx)
      exact arithmetic_identity (Value.neg (Value.mul piValue S)) (Value.mul piValue (Value.neg S)) (by
        intro s
        simp only [Value.mul,Value.neg]
        grind only)
  | succ n ih =>
    cases cosine
    · exact (ih true).constant_mul pi pi_valid
    · exact (ih false).negate.constant_mul pi pi_valid

/-- A uniform rational bound for every successive derivative. This is
analytic input to a later finite Taylor remainder, not that remainder itself. -/
theorem jetAt_small (n : Nat) (cosine : Bool) {x : RealCompute} (hx : x.Valid) :
    Small (parameter (jetAt n cosine x) (jetAt_valid n cosine hx)) ((8:Rat)^n) := by
  induction n generalizing cosine with
  | zero => exact at_small cosine hx
  | succ n ih =>
    have h (c : Bool) := pi_small.mul (ih c)
    have hn := pi_small.mul ((ih false).neg)
    rw [Rat.pow_succ]
    have hc : (8:Rat)^n*8=8*8^n := Rat.mul_comm _ _
    rw [hc]
    cases cosine
    · exact h true
    · exact hn

/-- Geometric initial values, independent of any series definition. -/
theorem sample_zero (cosine : Bool) :
    (sample cosine 0).Equiv (RealCompute.ofRat (if cosine then 1 else 0)) := by
  have h := sample_on_closed_quarter 0 cosine (q := 0) (by decide +kernel) (by decide +kernel)
  have he : (turn 0 cosine ((0:Rat)-(0:Int)/2))=quarter cosine 0 := by
    rw [show (0:Rat)-(0:Int)/2=0 by decide +kernel]
    simp only [turn,show (0:Int)%4=0 by decide,↓reduceIte]
  rw [he] at h
  exact RealCompute.equiv_trans (sample_valid _ _) (quarter_valid _ _) (RealCompute.ofRat_valid _)
    h (quarter_zero cosine)

def initial : Nat → Bool → RealCompute
  | 0,cosine => RealCompute.ofRat (if cosine then 1 else 0)
  | n+1,cosine => RealCompute.mul pi (if cosine then -(initial n false) else initial n true)

theorem initial_valid (n : Nat) (cosine : Bool) : (initial n cosine).Valid := by
  induction n generalizing cosine with
  | zero => exact RealCompute.ofRat_valid _
  | succ n ih =>
    cases cosine
    · exact RealCompute.mul_valid pi_valid (ih true)
    · exact RealCompute.mul_valid pi_valid (RealCompute.neg_valid (ih false))

theorem jet_zero (n : Nat) (cosine : Bool) : (jet n cosine 0).Equiv (initial n cosine) := by
  induction n generalizing cosine with
  | zero => exact sample_zero cosine
  | succ n ih =>
    cases cosine
    · exact RealCompute.mul_equiv pi_valid pi_valid (jet_valid n true 0) (initial_valid n true)
        (RealCompute.equiv_refl _ pi_valid) (ih true)
    · exact RealCompute.mul_equiv pi_valid pi_valid (RealCompute.neg_valid (jet_valid n false 0))
        (RealCompute.neg_valid (initial_valid n false)) (RealCompute.equiv_refl _ pi_valid) (RealCompute.neg_equiv (ih false))

end ComputableAnalysis.GeometricTrig


