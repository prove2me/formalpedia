-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealDerivativeAlgebra
-- name    : liuyao_ca_fd889115_k1_Analysis_RealDerivativeAlgebra
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:00:27.301084+00:00
-- url     : https://prove2.me/theorems/83791370-c652-40ab-9e91-b256c9ad3a8b
-- title:
--   Computable analysis · RealDerivativeAlgebra · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RealDerivativeAlgebra.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueBounds
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealSecantDerivative

set_option autoImplicit true

/-! Multiplication by a supplied represented constant preserves the full
covered real derivative. No derivative-existence class is introduced. -/
namespace ComputableAnalysis.RealSecantDerivative
open RawLimit BracketDerivative ComputableCoefficient RealApproximationOrder
set_option maxHeartbeats 200000

theorem secant_constant_mul {f : Rat → RealCompute} {a b : Rat}
    (C : RealCompute) (hC : C.Valid) (ha : (f a).Valid) (hb : (f b).Valid) :
    (RealCompute.mul C (secant f a b)).Equiv
      (secant (fun q => RealCompute.mul C (f q)) a b) := by
  let c := parameter C hC
  let A := parameter (f a) ha
  let B := parameter (f b) hb
  exact arithmetic_identity (Value.mul c (scale (1/(b-a)) (RealApproximationOrder.sub B A)))
    (scale (1/(b-a)) (RealApproximationOrder.sub (Value.mul c B) (Value.mul c A))) (by
      intro s
      simp only [Value.mul,scale,RealApproximationOrder.sub]
      grind only)

/-- The constant can be irrational; its actual interval computation is used. -/
theorem HasDerivativeAt.constant_mul {domain : Rat → Prop} {f : Rat → RealCompute}
    {x d : RealCompute} (h : HasDerivativeAt domain f x d) (C : RealCompute) (hC : C.Valid) :
    HasDerivativeAt domain (fun q => RealCompute.mul C (f q)) x (RealCompute.mul C d) := by
  refine ⟨h.1,RealCompute.mul_valid hC h.2.1,fun q hq => RealCompute.mul_valid hC (h.2.2.1 q hq),
    h.2.2.2.1,fun A hA => ?_⟩
  obtain ⟨hd,Q,n,m,hn,hm,hdiag,he,cover⟩ := h.2.2.2.2 A hA
  let P : Nat → Nat → QInterval := fun i j =>
    RealIntervalImage.product (C.compute j) (Q i (m j))
  have hv : (diagonal P n (fun j => j)).Valid := by
    change (RealCompute.mul C (diagonal Q n m)).Valid
    exact RealCompute.mul_valid hC hdiag
  have hp : (diagonal P n (fun j => j)).Equiv (RealCompute.mul C d) := by
    change (RealCompute.mul C (diagonal Q n m)).Equiv (RealCompute.mul C d)
    exact RealCompute.mul_equiv hC hC hdiag hd (RealCompute.equiv_refl _ hC) he
  refine ⟨RealCompute.mul_valid hC hd,P,n,(fun j => j),hn,cofinal_id,hv,hp,?_⟩
  rintro k y ⟨a,b,ha,hab,hb,rfl⟩
  have mem := (hA.2.2.2 (n k)).2
  have da := mem a ha (Rat.le_trans (Rat.le_of_lt hab) hb)
  have db := mem b (Rat.le_trans ha (Rat.le_of_lt hab)) hb
  have va := h.2.2.1 a da
  have vb := h.2.2.1 b db
  have old := cover k (secant f a b) ⟨a,b,ha,hab,hb,rfl⟩
  have image := RealIntervalImage.mul hC (secant_valid va vb) (RealIntervalImage.current hC k) old
  exact inInterval_congr (RealCompute.mul_valid hC (secant_valid va vb))
    (secant_valid (RealCompute.mul_valid hC va) (RealCompute.mul_valid hC vb))
    (secant_constant_mul (f := f) (a := a) (b := b) C hC va vb) image

end ComputableAnalysis.RealSecantDerivative


