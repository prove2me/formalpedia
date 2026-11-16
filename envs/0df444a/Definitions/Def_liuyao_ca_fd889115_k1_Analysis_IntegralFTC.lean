-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralFTC
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralFTC
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:35.173198+00:00
-- url     : https://prove2.me/theorems/6a96ef96-8af9-45c0-81db-9f0df6b7ce1f
-- title:
--   Computable analysis · IntegralFTC · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/IntegralFTC.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralSpecification
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Differential

set_option autoImplicit true

/-!
# FTC for any supplied integral

The endpoint function and integral are independently supplied represented
computations. Finite local derivative-order evidence gives the endpoint law
by telescoping and the integral specification. No integral construction is a
hypothesis of the uniqueness proof, and no endpoint identity is assumed.
-/
namespace ComputableAnalysis
namespace Integral

/-- The local mean-value inequalities needed by FTC. These compare a
derivative's constant bounds with finite endpoint increments on a rational
cell; they say nothing about an integral or a quadrature algorithm. -/
structure CellDerivativeBounds (f : FunctionOnInterval) (P : Rat → RealCompute) : Prop where
  valid : ∀ x, inDomainInterval f.lower f.upper x → (P x).Valid
  lower : ∀ (u v l : Rat), f.lower ≤ u → u ≤ v → v ≤ f.upper →
    (∀ x (hx : inDomainInterval f.lower f.upper x), u ≤ x → x ≤ v →
      ∀ n, l ≤ (f.compute x hx n).hi) →
    (RealCompute.ofRat ((v-u)*l)).Le (P v-P u)
  upper : ∀ (u v r : Rat), f.lower ≤ u → u ≤ v → v ≤ f.upper →
    (∀ x (hx : inDomainInterval f.lower f.upper x), u ≤ x → x ≤ v →
      ∀ n, (f.compute x hx n).lo ≤ r) →
    (P v-P u).Le (RealCompute.ofRat ((v-u)*r))

private theorem telescope_bounds (v : Nat → RealCompute) (l u : Nat → Rat)
    (N : Nat) (hv : ∀ k, k ≤ N → (v k).Valid)
    (hl : ∀ k, k < N → (RealCompute.ofRat (l k)).Le (v (k+1)-v k))
    (hu : ∀ k, k < N → (v (k+1)-v k).Le (RealCompute.ofRat (u k))) :
    (RealCompute.ofRat (rectangleSum l N)).Le (v N-v 0) ∧
      (v N-v 0).Le (RealCompute.ofRat (rectangleSum u N)) := by
  induction N with
  | zero =>
    have h := RealCompute.sub_self_equiv_zero (hv 0 (by omega))
    have hvalid := RealCompute.sub_valid (hv 0 (by omega)) (hv 0 (by omega))
    exact ⟨RealCompute.le_of_equiv (RealCompute.ofRat_valid 0) hvalid
      (RealCompute.equiv_symm h), RealCompute.le_of_equiv hvalid (RealCompute.ofRat_valid 0) h⟩
  | succ N ih =>
    have hprev := ih (fun k hk => hv k (by omega))
      (fun k hk => hl k (by omega)) (fun k hk => hu k (by omega))
    have haddl := RealCompute.le_add_le_add hprev.1 (hl N (by omega))
    have haddu := RealCompute.le_add_le_add hprev.2 (hu N (by omega))
    have ht := RealCompute.sub_add_sub_cancel_middle_equiv
      (hv 0 (by omega)) (hv N (by omega)) (hv (N+1) (by omega))
    have hsum := RealCompute.add_valid
      (RealCompute.sub_valid (hv N (by omega)) (hv 0 (by omega)))
      (RealCompute.sub_valid (hv (N+1) (by omega)) (hv N (by omega)))
    have hend := RealCompute.sub_valid (hv (N+1) (by omega)) (hv 0 (by omega))
    constructor
    · exact RealCompute.le_trans hsum haddl (RealCompute.le_of_equiv hsum hend ht)
    · exact RealCompute.le_trans hsum
        (RealCompute.le_of_equiv hend hsum (RealCompute.equiv_symm ht)) haddu

/-- Every finite rectangle test bounds the endpoint difference. -/
theorem CellDerivativeBounds.encloses {f : FunctionOnInterval} {P : Rat → RealCompute}
    (hP : CellDerivativeBounds f P) (B : Bounds f) :
    B.Encloses (P f.upper-P f.lower) := by
  have h := telescope_bounds (fun k => P (B.partition.point k))
    (fun k => (B.partition.point (k+1)-B.partition.point k)*B.lower k)
    (fun k => (B.partition.point (k+1)-B.partition.point k)*B.upper k)
    B.partition.pieces
    (fun k hk => hP.valid _ (B.partition.point_in_bounds hk))
    (by
      intro k hk
      let C := B.partition.cell k hk
      exact hP.lower C.lower C.upper (B.lower k) C.lower_mem C.ordered C.upper_mem
        (fun x hx hxl hxu n => B.lower_le k hk x ⟨hxl, hxu⟩ n))
    (by
      intro k hk
      let C := B.partition.cell k hk
      exact hP.upper C.lower C.upper (B.upper k) C.lower_mem C.ordered C.upper_mem
        (fun x hx hxl hxu n => B.upper_ge k hk x ⟨hxl, hxu⟩ n))
  rw [B.partition.left_endpoint, B.partition.right_endpoint] at h
  intro n
  exact ⟨h.1 0 n, h.2 n 0⟩

/-- FTC is a law about any witness of the integral definition. There is no
chosen quadrature, monotonicity decomposition, or integral-existence premise. -/
theorem HasIntegral.ftc {f : FunctionOnInterval} {P : Rat → RealCompute} {I : RealCompute}
    (hI : HasIntegral f I) (hP : CellDerivativeBounds f P) :
    I.Equiv (P f.upper-P f.lower) :=
  equiv_of_bounds hI.tight hI.bounds hP.encloses

/-- Existence is a separate corollary: local derivative order plus tight
integrand bounds certifies the actual endpoint computation as an integral. -/
theorem CellDerivativeBounds.hasIntegral {f : FunctionOnInterval} {P : Rat → RealCompute}
    (hP : CellDerivativeBounds f P) (hab : f.lower ≤ f.upper)
    (htight : HasTightBounds f) : HasIntegral f (P f.upper-P f.lower) :=
  ⟨RealCompute.sub_valid (hP.valid _ ⟨hab, Rat.le_refl⟩)
    (hP.valid _ ⟨Rat.le_refl, hab⟩), hP.encloses, htight⟩

end Integral
end ComputableAnalysis


