-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCRealProduct
-- name    : liuyao_ca_fd889115_k1_Analysis_FTCRealProduct
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:11:49.259272+00:00
-- url     : https://prove2.me/theorems/9050b861-15a9-4826-8a70-52100503c8c0
-- title:
--   Computable analysis · FTCRealProduct · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FTCRealProduct.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCRealCalculus
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralLinearity

set_option autoImplicit true

/-! Product FTC data from actual first-order and value bounds. The quadratic
cross increment is retained; no product integral identity is assumed. -/
namespace ComputableAnalysis.FTCRealCalculus
open ComputableCoefficient RealApproximationOrder FTCRealOrder
set_option maxHeartbeats 800000

theorem product_lipschitz (f g : Rat → Value) (a b L M B C : Rat)
    (lf : LipschitzIntegralBounds.Lipschitz f a b L)
    (lg : LipschitzIntegralBounds.Lipschitz g a b M)
    (bf : ∀ t,a≤t → t≤b → Small (f t) B)
    (bg : ∀ t,a≤t → t≤b → Small (g t) C) :
    LipschitzIntegralBounds.Lipschitz (fun t => Value.mul (f t) (g t)) a b (L*C+B*M) := by
  intro u v hu huv hv
  have H := ((lf u v hu huv hv).mul (bg v (Rat.le_trans hu huv) hv)).add
    ((bf u hu (Rat.le_trans huv hv)).mul (lg u v hu huv hv))
  have he : (L*(v-u))*C+B*(M*(v-u))=(L*C+B*M)*(v-u) := by grind only
  rw [he] at H
  apply H.congr
  apply arithmetic_identity; intro s
  simp only [Value.add,Value.mul,sub]
  grind only

/-- A product rule carrying enough quantitative evidence to apply FTC. -/
def Step.mul {f df g dg : Rat → Value} {a b : Rat}
    (S : Step f df a b) (T : Step g dg a b)
    (B C D E : Rat) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E)
    (bf : ∀ t,a≤t → t≤b → Small (f t) B)
    (bg : ∀ t,a≤t → t≤b → Small (g t) C)
    (bd : ∀ t,a≤t → t≤b → Small (df t) D)
    (be : ∀ t,a≤t → t≤b → Small (dg t) E) :
    Step (fun t => Value.mul (f t) (g t))
      (fun t => Value.add (Value.mul (df t) (g t)) (Value.mul (f t) (dg t))) a b where
  error := S.error*C+B*T.error+D*E
  error_nonnegative := Rat.add_nonneg (Rat.add_nonneg (Rat.mul_nonneg S.error_nonnegative hC)
    (Rat.mul_nonneg hB T.error_nonnegative)) (Rat.mul_nonneg hD hE)
  radius := ⟨min S.radius.val T.radius.val,by
    rw [Rat.min_def]; split
    · exact S.radius.property
    · exact T.radius.property⟩
  firstOrder := by
    intro u v hu huv hv hs
    have hsS : v-u≤S.radius.val := by
      change v-u≤min S.radius.val T.radius.val at hs
      rw [Rat.min_def] at hs; split at hs <;> grind only
    have hsT : v-u≤T.radius.val := by
      change v-u≤min S.radius.val T.radius.val at hs
      rw [Rat.min_def] at hs; split at hs <;> grind only
    have lf := lipschitz_of_firstOrder S.firstOrder S.error_nonnegative S.radius.property bd
    have lg := lipschitz_of_firstOrder T.firstOrder T.error_nonnegative T.radius.property be
    have H := (((S.firstOrder u v hu huv hv hsS).mul (bg u hu (Rat.le_trans (Rat.le_of_lt huv) hv))).add
      ((bf u hu (Rat.le_trans (Rat.le_of_lt huv) hv)).mul (T.firstOrder u v hu huv hv hsT))).add
        ((lf u v hu (Rat.le_of_lt huv) hv).mul (lg u v hu (Rat.le_of_lt huv) hv))
    have he : (S.error*(v-u)*(v-u))*C+B*(T.error*(v-u)*(v-u))+
        (D*(v-u))*(E*(v-u))=(S.error*C+B*T.error+D*E)*(v-u)*(v-u) := by grind only
    rw [he] at H
    apply H.congr
    apply arithmetic_identity; intro s
    simp only [Value.add,Value.mul,sub,RealApproximationOrder.scale]
    grind only
  variation := S.variation*C+D*E+(D*E+B*T.variation)
  variation_nonnegative := Rat.add_nonneg
    (Rat.add_nonneg (Rat.mul_nonneg S.variation_nonnegative hC) (Rat.mul_nonneg hD hE))
    (Rat.add_nonneg (Rat.mul_nonneg hD hE) (Rat.mul_nonneg hB T.variation_nonnegative))
  lipschitz := by
    have lf := lipschitz_of_firstOrder S.firstOrder S.error_nonnegative S.radius.property bd
    have lg := lipschitz_of_firstOrder T.firstOrder T.error_nonnegative T.radius.property be
    have H := product_lipschitz df g a b S.variation E D C S.lipschitz lg bd bg
    have K := product_lipschitz f dg a b D T.variation B E lf T.lipschitz bf be
    intro u v hu huv hv
    have H' := (H u v hu huv hv).add (K u v hu huv hv)
    have he : (S.variation*C+D*E)*(v-u)+(D*E+B*T.variation)*(v-u)=
      (S.variation*C+D*E+(D*E+B*T.variation))*(v-u) := by grind only
    rw [he] at H'
    apply H'.congr
    apply arithmetic_identity; intro s; simp only [Value.add,sub]; grind only

theorem Step.integrationByParts {f df g dg : Rat → Value} {a b : Rat}
    (S : Step f df a b) (T : Step g dg a b) (hab : a≤b)
    (B C D E : Rat) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E)
    (bf : ∀ t,a≤t → t≤b → Small (f t) B)
    (bg : ∀ t,a≤t → t≤b → Small (g t) C)
    (bd : ∀ t,a≤t → t≤b → Small (df t) D)
    (be : ∀ t,a≤t → t≤b → Small (dg t) E)
    {I J : RealCompute}
    (hI : Integral.HasIntegral (LipschitzIntegralBounds.onInterval (fun t => Value.mul (df t) (g t)) a b) I)
    (hJ : Integral.HasIntegral (LipschitzIntegralBounds.onInterval (fun t => Value.mul (f t) (dg t)) a b) J) :
    I.Equiv (((Value.mul (f b) (g b)).real.preferred-(Value.mul (f a) (g a)).real.preferred)-J) := by
  let U := S.mul T B C D E hB hC hD hE bf bg bd be
  have hK := U.hasIntegral hab
  have hs := hI.add_identity hJ hK rfl rfl rfl rfl
    (by intro t _ _ _; exact RealCompute.equiv_refl _ (Value.add (Value.mul (df t) (g t)) (Value.mul (f t) (dg t))).real.valid)
  apply RealCompute.equiv_symm
  apply RealCompute.equiv_trans (x := _-J) (y := (I+J)-J) (z := I)
    (RealCompute.sub_valid hK.valid hJ.valid) (RealCompute.sub_valid (RealCompute.add_valid hI.valid hJ.valid) hJ.valid) hI.valid
  · exact RealCompute.sub_equiv hK.valid (RealCompute.add_valid hI.valid hJ.valid) hJ.valid hJ.valid hs
      (RealCompute.equiv_refl J hJ.valid)
  · exact RealCompute.add_sub_cancel_right_equiv hI.valid hJ.valid

end ComputableAnalysis.FTCRealCalculus


