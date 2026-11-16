-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_CubeAverage
-- name    : liuyao_ca_fd889115_k1_Analysis_CubeAverage
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:13:33.357425+00:00
-- url     : https://prove2.me/theorems/7ac7fc1a-d184-4d31-a009-e15c24ff90c3
-- title:
--   Computable analysis · CubeAverage · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/CubeAverage.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RationalBoxes
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueBounds
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealIntervalImage

set_option autoImplicit true

/-! Normalized iterated integration over a cube. Only joint Lipschitz
control is needed here; differentiability is not used by these estimates. -/

open ComputableAnalysis.ComputableCoefficient
open ComputableAnalysis.RealApproximationOrder

namespace ComputableAnalysis

structure JointLipschitzSampler (dimension : Nat) where
  value : QPoint dimension → Value
  bound : Rat
  nonnegative : 0 ≤ bound
  control : ∀ x y (δ : Rat), 0 ≤ δ →
    (∀ i, x i ≤ y i + δ ∧ y i ≤ x i + δ) →
    Small (sub (value x) (value y)) (bound * δ)

namespace JointLipschitzSampler

/-- The Dirac action at a rational point is evaluation at that point. -/
def diracValue {n : Nat} (f : JointLipschitzSampler n) (a : QPoint n) : Value :=
  f.value a

private def sliceData {n : Nat} (f : JointLipschitzSampler (n + 1))
    (x : QPoint n) : LipschitzQuadrature.Data (fun t => f.value (appendLast x t)) (-1) 1 where
  ordered := by decide +kernel
  constant := f.bound
  nonnegative := f.nonnegative
  lipschitz := by
    intro u v _ huv _
    apply f.control _ _ (v - u) (by grind only)
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [appendLast, Fin.lastCases_last]
      constructor <;> grind only
    · simp only [appendLast, Fin.lastCases_castSucc]
      constructor <;> grind only

private def sliceAverage {n : Nat} (f : JointLipschitzSampler (n + 1))
    (x : QPoint n) : Value :=
  scale (1 / 2) (f.sliceData x).value

private theorem normalized_difference_small {f g : Rat → Value}
    (F : LipschitzQuadrature.Data f (-1) 1) (G : LipschitzQuadrature.Data g (-1) 1)
    (B : Rat) (h : ∀ t, -1 ≤ t → t ≤ 1 → Small (sub (f t) (g t)) B) :
    Small (sub (scale (1 / 2) F.value) (scale (1 / 2) G.value)) B := by
  have hb := (F.difference_small G B h).scale_nonnegative (c := 1 / 2)
    (by decide +kernel)
  have he : (1 / 2 : Rat) * ((1 - (-1)) * B) = B := by grind
  rw [he] at hb
  exact hb.congr (arithmetic_identity _ _ (by
    intro s
    simp only [scale, sub]
    grind only))

/-- Integrate one coordinate against the uniform probability measure on
the unit interval. The joint Lipschitz bound persists in the remaining
coordinates. -/
def averageLast {n : Nat} (f : JointLipschitzSampler (n + 1)) :
    JointLipschitzSampler n where
  value := f.sliceAverage
  bound := f.bound
  nonnegative := f.nonnegative
  control := by
    intro x y δ hδ hxy
    apply normalized_difference_small (f.sliceData x) (f.sliceData y)
    intro t _ _
    apply f.control _ _ δ hδ
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [appendLast, Fin.lastCases_last]
      constructor <;> grind only
    · simpa [appendLast] using hxy j

/-- Normalized integral over the rational unit cube, one coordinate at a
time. In dimension zero there is just one sample. -/
def cubeAverage : {n : Nat} → JointLipschitzSampler n → Value
  | 0, f => f.value (origin 0)
  | _ + 1, f => cubeAverage f.averageLast

theorem cubeAverage_line (f : JointLipschitzSampler 1)
    (D : LipschitzQuadrature.Data (fun t => f.value (fun _ => t)) (-1) 1) :
    f.cubeAverage.real.preferred.Equiv (scale (1 / 2) D.value).real.preferred := by
  change (scale (1 / 2) (f.sliceData (origin 0)).value).real.preferred.Equiv _
  apply RealCompute.scaleRat_equiv
  apply (f.sliceData (origin 0)).congr D
  intro t _ _
  have he : appendLast (origin 0) t = fun _ => t := by
    funext i
    refine Fin.lastCases ?_ (fun j => Fin.elim0 j) i
    simp only [appendLast, Fin.lastCases_last]
  rw [he]
  exact RealCompute.equiv_refl _ (f.value (fun _ => t)).real.valid

/-- The iterated integral depends only on the values on the cube. -/
theorem cubeAverage_congr {n : Nat} (f g : JointLipschitzSampler n)
    (h : ∀ x, (∀ i, -1 ≤ x i ∧ x i ≤ 1) →
      (f.value x).real.preferred.Equiv (g.value x).real.preferred) :
    f.cubeAverage.real.preferred.Equiv g.cubeAverage.real.preferred := by
  induction n with
  | zero => exact h (origin 0) (fun i => Fin.elim0 i)
  | succ n ih =>
    apply ih f.averageLast g.averageLast
    intro x hx
    apply RealCompute.scaleRat_equiv
    exact (f.sliceData x).congr (g.sliceData x) (fun t ht ht' =>
      h (appendLast x t) (fun i => by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [appendLast] using And.intro ht ht'
        · simpa [appendLast] using hx j))

/-- A uniform bound for the difference of two samplers also bounds the
difference of their normalized integrals. -/
theorem cubeAverage_difference_small {n : Nat} (f g : JointLipschitzSampler n)
    (B : Rat) (h : ∀ x, (∀ i, -1 ≤ x i ∧ x i ≤ 1) →
      Small (sub (f.value x) (g.value x)) B) :
    Small (sub f.cubeAverage g.cubeAverage) B := by
  induction n with
  | zero => exact h (origin 0) (fun i => Fin.elim0 i)
  | succ n ih =>
    apply ih f.averageLast g.averageLast
    intro x hx
    apply normalized_difference_small (f.sliceData x) (g.sliceData x)
    intro t ht ht'
    apply h (appendLast x t)
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [appendLast] using And.intro ht ht'
    · simpa [appendLast] using hx j

private def constantSlice (c : Value) : LipschitzQuadrature.Data (fun _ => c) (-1) 1 where
  ordered := by decide +kernel
  constant := 0
  nonnegative := Rat.le_refl
  lipschitz := by
    intro u v _ _ _
    rw [Rat.zero_mul]
    have h : Small (Value.rational 0) 0 :=
      ⟨fun _ _ => Rat.le_refl, fun _ _ => Rat.le_refl⟩
    exact h.congr (RealCompute.equiv_symm (RealCompute.sub_self_equiv_zero c.real.valid))

private theorem constantSlice_average (c : Value) :
    (scale (1 / 2) (constantSlice c).value).real.preferred.Equiv c.real.preferred := by
  have hc := Integral.constant_hasIntegral c.real.preferred c.real.valid (-1) 1
    (by decide +kernel)
  have he := (constantSlice c).identify (hc.congrFunction
    ⟨rfl, rfl, fun _ _ _ => RealCompute.equiv_refl _ c.real.valid⟩)
  exact RealCompute.equiv_trans (RealCompute.scaleRat_valid (constantSlice c).value.real.valid)
    (RealCompute.scaleRat_valid (RealCompute.scaleRat_valid c.real.valid)) c.real.valid
    (RealCompute.scaleRat_equiv he)
    (arithmetic_identity (scale (1 / 2) (scale (1 - (-1)) c)) c (by
      intro s
      simp only [scale]
      grind))

/-- A whole-cube bound from a fixed reference value also bounds the
normalized iterated integral from that value. -/
theorem cubeAverage_near {n : Nat} (f : JointLipschitzSampler n) (c : Value) (B : Rat)
    (h : ∀ x, (∀ i, -1 ≤ x i ∧ x i ≤ 1) → Small (sub (f.value x) c) B) :
    Small (sub f.cubeAverage c) B := by
  induction n with
  | zero => exact h (origin 0) (fun i => Fin.elim0 i)
  | succ n ih =>
    apply ih f.averageLast
    intro x hx
    have hb := normalized_difference_small (f.sliceData x) (constantSlice c) B
      (fun t ht ht' => h (appendLast x t) (fun i => by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [appendLast] using And.intro ht ht'
        · simpa [appendLast] using hx j))
    apply hb.congr
    exact RealCompute.sub_equiv (f.averageLast.value x).real.valid (f.averageLast.value x).real.valid
      (scale (1 / 2) (constantSlice c).value).real.valid c.real.valid
      (RealCompute.equiv_refl _ (f.averageLast.value x).real.valid) (constantSlice_average c)

/-- The normalized average over a cube of radius `r` centered at `a`.
At radius zero this evaluates the sampler at the center. -/
def centeredAverage {n : Nat} (f : JointLipschitzSampler n)
    (a : QPoint n) (r : Rat) (hr : 0 ≤ r) : Value :=
  let scaled : JointLipschitzSampler n :=
    { value := fun x => f.value (fun i => a i + r * x i)
      bound := f.bound * r
      nonnegative := Rat.mul_nonneg f.nonnegative hr
      control := by
        intro x y δ hδ hxy
        rw [Rat.mul_assoc]
        apply f.control _ _ _ (Rat.mul_nonneg hr hδ)
        intro i
        have h₁ := Rat.mul_le_mul_of_nonneg_left (hxy i).1 hr
        have h₂ := Rat.mul_le_mul_of_nonneg_left (hxy i).2 hr
        simp only [Rat.mul_add] at h₁ h₂
        constructor <;> grind only }
  scaled.cubeAverage

/-- Quantitative convergence of normalized cube averages to the Dirac
evaluation. At radius `r` the error is at most the Lipschitz bound times
`r`, in every finite dimension. -/
theorem centeredAverage_near {n : Nat} (f : JointLipschitzSampler n)
    (a : QPoint n) (r : Rat) (hr : 0 ≤ r) :
    Small (sub (f.centeredAverage a r hr) (f.diracValue a)) (f.bound * r) := by
  unfold centeredAverage
  apply cubeAverage_near
  intro x hx
  apply f.control _ _ _ hr
  intro i
  have h₁ := Rat.mul_le_mul_of_nonneg_left (hx i).1 hr
  have h₂ := Rat.mul_le_mul_of_nonneg_left (hx i).2 hr
  simp only [Rat.mul_neg, Rat.mul_one] at h₁ h₂
  constructor <;> grind only

/-- Shrinking dyadic cube averages converge to evaluation at their center. -/
theorem centeredAverage_tendsTo {n : Nat} (f : JointLipschitzSampler n) (a : QPoint n) :
    RawLimit.TendsTo
      (fun k => (f.centeredAverage a (RawLimit.allowance k)
        (Rat.le_of_lt (RawLimit.allowance_pos k))).real.preferred)
      (f.diracValue a).real.preferred := by
  refine ⟨(f.value a).real.valid, fun _ => (centeredAverage ..).real.valid, ?_⟩
  intro m eps
  let δ : QPos := ⟨eps.val / (1 + f.bound), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by have := f.nonnegative; grind only))⟩
  obtain ⟨N, hN⟩ := RawLimit.allowance_shrinks δ
  refine ⟨N, fun k hk => ?_⟩
  have hε : f.bound * RawLimit.allowance k ≤ eps.val := by
    calc
      f.bound * RawLimit.allowance k ≤ f.bound * δ.val :=
        Rat.mul_le_mul_of_nonneg_left (hN k hk) f.nonnegative
      _ ≤ δ.val * (1 + f.bound) := by
        rw [Rat.mul_comm f.bound δ.val]
        exact Rat.mul_le_mul_of_nonneg_left (by grind only) (Rat.le_of_lt δ.property)
      _ = eps.val := Rat.div_mul_cancel (Rat.ne_of_gt (by have := f.nonnegative; grind only))
  have hcenter := RawLimit.inInterval_of_contains_compute (f.value a).real.valid m
    (I := (f.value a).real.compute m) ⟨Rat.le_refl, Rat.le_refl⟩
  exact RealIntervalImage.error_translate (centeredAverage ..).real.valid
    (f.value a).real.valid eps.val ((centeredAverage_near f a _ _).mono hε) hcenter

end JointLipschitzSampler
end ComputableAnalysis


