-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FourierQuadratureRationalProof
-- name    : liuyao_ca_fd889115_k1_Analysis_FourierQuadratureRationalProof
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T19:13:49.373175+00:00
-- url     : https://prove2.me/theorems/2cfaf2c9-78d5-4f8f-9239-d81fb04b91a8
-- title:
--   Fourier quadrature · rational arithmetic proof
-- statement:
--   Private portability check of the Fourier quadrature module. One rational arithmetic step uses explicit rewrites to shorten checker runtime.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_CubeAverage
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricPeriodic
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricTaylorData
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueCongruence
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EffectiveImproperIntegral
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricIntegralData
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzTaggedQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCMonomials
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GaussianDifferential
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerNegativeRate
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerLegacySeries
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanPositiveFTC
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RepresentedPositiveSquareRoot

set_option autoImplicit true

/-! Finite-box Fourier quadrature using rational-angle geometric trigonometry. -/

namespace ComputableAnalysis.FourierQuadrature

open ComputableCoefficient RealApproximationOrder

set_option maxRecDepth 4096

private theorem sum_le : ∀ (d : Nat) (f g : QPoint d),
    (∀ i, f i ≤ g i) → sumRat d f ≤ sumRat d g
  | 0, _, _, _ => Rat.le_refl
  | d + 1, f, g, h => by
    have hs := sum_le d _ _ (fun i => h i.castSucc)
    have hl := h (Fin.last d)
    simp only [sumRat]
    grind only

private theorem sum_scale (a : Rat) : ∀ (d : Nat) (f : QPoint d),
    sumRat d (fun i => f i * a) = sumRat d f * a
  | 0, _ => (Rat.zero_mul a).symm
  | d + 1, f => by
    simp only [sumRat, sum_scale a d]
    exact (Rat.add_mul _ _ _).symm

private theorem sum_sub : ∀ (d : Nat) (f g : QPoint d),
    sumRat d f - sumRat d g = sumRat d (fun i => f i - g i)
  | 0, _, _ => Rat.sub_self
  | d + 1, f, g => by
    simp only [sumRat, ← sum_sub d]
    grind only

private theorem sum_zero (d : Nat) : sumRat d (fun _ => 0) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [sumRat, ih, Rat.add_zero]

private theorem entry_le_sum : ∀ (d : Nat) (f : QPoint d),
    (∀ i, 0 ≤ f i) → ∀ i, f i ≤ sumRat d f
  | 0, _, _, i => Fin.elim0 i
  | d + 1, f, hf, i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hs : 0 ≤ sumRat d (fun j => f j.castSucc) :=
        by rw [← sum_zero d]; exact sum_le d _ _ (fun j => hf j.castSucc)
      simp only [sumRat]
      grind only
    · have h := entry_le_sum d (fun j => f j.castSucc) (fun j => hf j.castSucc) j
      have hl := hf (Fin.last d)
      simp only [sumRat]
      grind only

private def clamp (x : Rat) : Rat := max (-1) (min x 1)

private theorem clamp_range (x : Rat) : -1 ≤ clamp x ∧ clamp x ≤ 1 := by
  unfold clamp
  grind

private theorem clamp_close {x y δ : Rat} (h : x ≤ y + δ ∧ y ≤ x + δ) :
    clamp x ≤ clamp y + δ ∧ clamp y ≤ clamp x + δ := by
  have hδ : 0 ≤ δ := by grind only
  unfold clamp
  simp only [Rat.max_def, Rat.min_def]
  split <;> split <;> split <;> (try split) <;> grind only

private def halfWidth {d : Nat} (B : RationalBox d) (i : Fin d) : Rat :=
  (B.upper i - B.lower i) / 2

private theorem halfWidth_nonneg {d : Nat} (B : RationalBox d) (i : Fin d) :
    0 ≤ halfWidth B i := by
  have := B.ordered i
  unfold halfWidth
  grind

/-- Map the unit cube affinely to the support box. Clipping outside the
cube gives a sampler with the same joint bound on all rational inputs. -/
def boxPoint {d : Nat} (B : RationalBox d) (x : QPoint d) : QPoint d :=
  fun i => B.lower i + halfWidth B i * (1 + clamp (x i))

theorem boxPoint_on_unitCube {d : Nat} (B : RationalBox d) (x : QPoint d)
    (hx : ∀ i, -1 ≤ x i ∧ x i ≤ 1) (i : Fin d) :
    boxPoint B x i = B.lower i + ((B.upper i - B.lower i) / 2) * (1 + x i) := by
  simp only [boxPoint, halfWidth, clamp, Rat.max_def, Rat.min_def,
    if_pos (hx i).1, if_pos (hx i).2]

private theorem boxPoint_range {d : Nat} (B : RationalBox d) (x : QPoint d) :
    B.Contains (boxPoint B x) := by
  intro i
  have h := clamp_range (x i)
  have hp := halfWidth_nonneg B i
  have hl := Rat.mul_nonneg hp (show 0 ≤ 1 + clamp (x i) by grind only)
  have hu := Rat.mul_le_mul_of_nonneg_left (show 1 + clamp (x i) ≤ 2 by grind only) hp
  have hw : halfWidth B i * 2 = B.upper i - B.lower i := by
    unfold halfWidth
    grind
  constructor <;> grind only [boxPoint]

private def widths {d : Nat} (B : RationalBox d) : Rat :=
  sumRat d (halfWidth B)

private theorem widths_nonneg {d : Nat} (B : RationalBox d) : 0 ≤ widths B := by
  rw [widths, ← sum_zero d]
  exact sum_le d _ _ (halfWidth_nonneg B)

private theorem boxPoint_close {d : Nat} (B : RationalBox d)
    {x y : QPoint d} {δ : Rat} (hδ : 0 ≤ δ)
    (hxy : ∀ i, x i ≤ y i + δ ∧ y i ≤ x i + δ) (i : Fin d) :
    boxPoint B x i ≤ boxPoint B y i + widths B * δ ∧
    boxPoint B y i ≤ boxPoint B x i + widths B * δ := by
  have h := clamp_close (hxy i)
  have hp := halfWidth_nonneg B i
  have hs := Rat.mul_le_mul_of_nonneg_right (entry_le_sum d _ (halfWidth_nonneg B) i) hδ
  have hu := Rat.mul_le_mul_of_nonneg_left (show 1 + clamp (x i) ≤ 1 + clamp (y i) + δ by grind only) hp
  have hl := Rat.mul_le_mul_of_nonneg_left (show 1 + clamp (y i) ≤ 1 + clamp (x i) + δ by grind only) hp
  change halfWidth B i * δ ≤ widths B * δ at hs
  constructor <;> grind only [boxPoint, Rat.mul_add]

private def boxSampler {d : Nat} (f : JointLipschitzSampler d) (B : RationalBox d) :
    JointLipschitzSampler d where
  value x := f.value (boxPoint B x)
  bound := f.bound * widths B
  nonnegative := Rat.mul_nonneg f.nonnegative (widths_nonneg B)
  control := by
    intro x y δ hδ hxy
    rw [Rat.mul_assoc]
    exact f.control _ _ _ (Rat.mul_nonneg (widths_nonneg B) hδ)
      (boxPoint_close B hδ hxy)

private def initialBound (a : Value) : Rat :=
  qabs (a.real.compute 0).lo + qabs (a.real.compute 0).hi

private theorem initialBound_nonneg (a : Value) : 0 ≤ initialBound a :=
  Rat.add_nonneg (qabs_nonneg _) (qabs_nonneg _)

private theorem small_initialBound (a : Value) : Small a (initialBound a) := by
  exact RawLimit.inInterval_of_contains_compute (I := ⟨-initialBound a, initialBound a⟩) a.real.valid 0 (by
    have hlo := neg_qabs_le_self (a.real.compute 0).lo
    have hhi := self_le_qabs (a.real.compute 0).hi
    have h₁ := qabs_nonneg (a.real.compute 0).lo
    have h₂ := qabs_nonneg (a.real.compute 0).hi
    change -(initialBound a) ≤ (a.real.compute 0).lo ∧ (a.real.compute 0).hi ≤ initialBound a
    unfold initialBound
    constructor <;> grind only)

private def boxBound {d : Nat} (f : JointLipschitzSampler d) (B : RationalBox d) : Rat :=
  initialBound (f.value B.lower) + f.bound * (2 * widths B)

private theorem boxBound_nonneg {d : Nat} (f : JointLipschitzSampler d) (B : RationalBox d) :
    0 ≤ boxBound f B :=
  Rat.add_nonneg (initialBound_nonneg _) (Rat.mul_nonneg f.nonnegative
    (Rat.mul_nonneg (by decide) (widths_nonneg B)))

private theorem small_boxSampler {d : Nat} (f : JointLipschitzSampler d) (B : RationalBox d)
    (x : QPoint d) : Small ((boxSampler f B).value x) (boxBound f B) := by
  have hd := f.control (boxPoint B x) B.lower (2 * widths B)
    (Rat.mul_nonneg (by decide) (widths_nonneg B)) (fun i => by
      have hp := boxPoint_range B x i
      have hw := entry_le_sum d _ (halfWidth_nonneg B) i
      have he : halfWidth B i * 2 = B.upper i - B.lower i := by unfold halfWidth; grind
      change halfWidth B i ≤ widths B at hw
      have hm := Rat.mul_le_mul_of_nonneg_right hw (show (0 : Rat) ≤ 2 by decide)
      have hz := widths_nonneg B
      constructor <;> grind only)
  change Small (sub (f.value (boxPoint B x)) (f.value B.lower)) _ at hd
  exact ((small_initialBound (f.value B.lower)).add hd).congr
    (arithmetic_identity _ _ (by intro s; simp only [Value.add, sub, boxSampler]; grind only))

def phase {d : Nat} (ξ x : QPoint d) : Rat :=
  sumRat d (fun i => (-2 * ξ i) * x i)

private def phaseWeight {d : Nat} (ξ : QPoint d) : Rat :=
  sumRat d (fun i => qabs (-2 * ξ i))

private theorem phaseWeight_nonneg {d : Nat} (ξ : QPoint d) : 0 ≤ phaseWeight ξ := by
  rw [phaseWeight, ← sum_zero d]
  exact sum_le d _ _ (fun _ => qabs_nonneg _)

private theorem phase_close {d : Nat} (ξ x y : QPoint d) (δ : Rat)
    (hxy : ∀ i, x i ≤ y i + δ ∧ y i ≤ x i + δ) :
    qabs (phase ξ x - phase ξ y) ≤ phaseWeight ξ * δ := by
  have h i : qabs ((-2 * ξ i) * x i - (-2 * ξ i) * y i) ≤ qabs (-2 * ξ i) * δ := by
    rw [show (-2 * ξ i) * x i - (-2 * ξ i) * y i = (-2 * ξ i) * (x i - y i) by grind only,
      qabs_mul]
    exact Rat.mul_le_mul_of_nonneg_left (qabs_le_of_neg_le_le
      (show -δ ≤ x i - y i by have := (hxy i).2; grind only)
      (show x i - y i ≤ δ by have := (hxy i).1; grind only)) (qabs_nonneg _)
  unfold phase phaseWeight
  rw [sum_sub, ← sum_scale]
  apply qabs_le_of_neg_le_le
  · have hn := sum_le d (fun i => qabs (-2 * ξ i) * (-δ))
        (fun i => (-2 * ξ i) * x i - (-2 * ξ i) * y i) (fun i => by
          have hl := neg_qabs_le_self ((-2 * ξ i) * x i - (-2 * ξ i) * y i)
          have hh := h i
          grind only)
    rw [sum_scale, Rat.mul_neg, ← sum_scale] at hn
    exact hn
  · exact sum_le d _ _ (fun i => Rat.le_trans (self_le_qabs _) (h i))

private def trigValue (cosine : Bool) (q : Rat) : Value :=
  parameter (GeometricTrig.sample cosine q) (GeometricTrig.sample_valid cosine q)

private theorem trig_small (cosine : Bool) (q : Rat) : Small (trigValue cosine q) 1 :=
  RawLimit.inInterval_of_contains_compute (I := ⟨-1, 1⟩) (GeometricTrig.sample_valid cosine q) 0
    (GeometricTrig.sample_bounds cosine q 0)

private def trigSampler {d : Nat} (B : RationalBox d) (ξ : QPoint d) (cosine : Bool) :
    JointLipschitzSampler d where
  value x := trigValue cosine (phase ξ (boxPoint B x))
  bound := 32 * (phaseWeight ξ * widths B)
  nonnegative := Rat.mul_nonneg (by decide) (Rat.mul_nonneg (phaseWeight_nonneg ξ) (widths_nonneg B))
  control := by
    intro x y δ hδ hxy
    have h : Small (sub (trigValue cosine (phase ξ (boxPoint B x)))
      (trigValue cosine (phase ξ (boxPoint B y))))
      (32 * qabs (phase ξ (boxPoint B x) - phase ξ (boxPoint B y))) := by
      simpa only [Small, sub, trigValue, parameter, Value.parameter, RealCompute.Certified.ofRaw, Rat.neg_mul] using
        GeometricTrig.sample_lipschitz cosine (phase ξ (boxPoint B y)) (phase ξ (boxPoint B x))
    apply h.mono
    have hb := Rat.mul_le_mul_of_nonneg_left
      (phase_close ξ _ _ _ (boxPoint_close B hδ hxy)) (show (0 : Rat) ≤ 32 by decide)
    simpa only [Rat.mul_assoc] using hb

private def productSampler {d : Nat} (f g : JointLipschitzSampler d) (M N : Rat)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hf : ∀ x, Small (f.value x) M)
    (hg : ∀ x, Small (g.value x) N) : JointLipschitzSampler d where
  value x := Value.mul (f.value x) (g.value x)
  bound := f.bound * N + M * g.bound
  nonnegative := Rat.add_nonneg (Rat.mul_nonneg f.nonnegative hN) (Rat.mul_nonneg hM g.nonnegative)
  control := by
    intro x y δ hδ hxy
    have h := ((f.control x y δ hδ hxy).mul (hg x)).add ((hf y).mul (g.control x y δ hδ hxy))
    have hbudget : f.bound * δ * N + M * (g.bound * δ) =
        (f.bound * N + M * g.bound) * δ := by grind only
    rw [hbudget] at h
    exact h.congr (arithmetic_identity _ _ (by intro s; simp only [Value.add, Value.mul, sub]; grind only))

private def boxIntegral {d : Nat} (B : RationalBox d) (f : JointLipschitzSampler d) : Value :=
  scale (B.dyadicCellVolume 0) f.cubeAverage

/-- Fourier phase times the input, pulled back to the normalized cube. -/
private def componentSampler {d : Nat} (B : RationalBox d) (f : JointLipschitzSampler d)
    (ξ : QPoint d) (cosine : Bool) : JointLipschitzSampler d :=
  productSampler (boxSampler f B) (trigSampler B ξ cosine)
    (boxBound f B) 1 (boxBound_nonneg f B) (by decide)
    (small_boxSampler f B) (fun _ => trig_small _ _)

/-- One real component of the finite-box Fourier transform at a rational
frequency, with phase `exp(-2π i x⋅ξ)`. Input values are represented reals. -/
def component {d : Nat} (B : RationalBox d) (f : JointLipschitzSampler d)
    (ξ : QPoint d) (cosine : Bool) : Value :=
  boxIntegral B (componentSampler B f ξ cosine)

/-- Real and imaginary components of the finite-box transform of a real
sampler at a rational frequency. -/
def transform {d : Nat} (B : RationalBox d) (f : JointLipschitzSampler d)
    (ξ : QPoint d) : Value × Value :=
  (component B f ξ true, component B f ξ false)

/-- Integrate a spatial sampler over a rational box by iterated quadrature. -/
def integral {d : Nat} (B : RationalBox d) (f : JointLipschitzSampler d) : Value :=
  boxIntegral B (boxSampler f B)

private theorem phase_origin {d : Nat} (x : QPoint d) : phase (origin d) x = 0 := by
  simp only [phase, origin, Rat.mul_zero, Rat.zero_mul, sum_zero]

/-- At zero frequency the real component is the box integral and the
imaginary component vanishes. -/
theorem component_at_zero {d : Nat} (B : RationalBox d) (f : JointLipschitzSampler d) :
    (component B f (origin d) true).real.preferred.Equiv (integral B f).real.preferred ∧
      (component B f (origin d) false).real.preferred.Equiv (RealCompute.ofRat 0) := by
  have hcos : ∀ x, Same ((componentSampler B f (origin d) true).value x)
      ((boxSampler f B).value x) := by
    intro x
    let a := (boxSampler f B).value x
    have ht : Same ((trigSampler B (origin d) true).value x) (Value.rational 1) := by
      change (GeometricTrig.sample true (phase (origin d) (boxPoint B x))).Equiv (RealCompute.ofRat 1)
      rw [phase_origin]
      exact GeometricTrig.sample_zero true
    exact ((Same.refl a).mul ht).trans (arithmetic_identity _ _ (by
      intro s
      simp [a, Value.mul, Value.rational, Rat.mul_one]))
  let z : JointLipschitzSampler d :=
    { value := fun _ => Value.rational 0
      bound := 0
      nonnegative := Rat.le_refl
      control := by
        intro _ _ δ _ _
        rw [Rat.zero_mul]
        have h : Small (Value.rational 0) 0 := ⟨fun _ _ => Rat.le_refl, fun _ _ => Rat.le_refl⟩
        exact h.congr (arithmetic_identity _ _ (by intro s; simp [sub, Value.rational, Rat.sub_self])) }
  have hsin : ∀ x, Same ((componentSampler B f (origin d) false).value x) (z.value x) := by
    intro x
    let a := (boxSampler f B).value x
    have ht : Same ((trigSampler B (origin d) false).value x) (Value.rational 0) := by
      change (GeometricTrig.sample false (phase (origin d) (boxPoint B x))).Equiv (RealCompute.ofRat 0)
      rw [phase_origin]
      exact GeometricTrig.sample_zero false
    exact ((Same.refl a).mul ht).trans (arithmetic_identity _ _ (by
      intro s
      simp [z, Value.mul, Value.rational, Rat.mul_zero]))
  have hzero : Same z.cubeAverage (Value.rational 0) := by
    have hbound : Small (sub z.cubeAverage (Value.rational 0)) 0 := by
      apply z.cubeAverage_near (Value.rational 0) 0
      intro _ _
      have h : Small (Value.rational 0) 0 := ⟨fun _ _ => Rat.le_refl, fun _ _ => Rat.le_refl⟩
      exact h.congr (arithmetic_identity _ _ (by intro s; simp [z, sub, Value.rational, Rat.sub_self]))
    have hz : Small z.cubeAverage 0 := hbound.congr (arithmetic_identity _ _ (by
      intro s
      simp [sub, Value.rational, show ∀ q : Rat, q - 0 = q by intro; grind only]))
    change z.cubeAverage.real.preferred.Equiv (RealCompute.ofRat 0)
    exact RealCompute.equiv_of_le_of_ge hz.2 (by simpa only [Rat.neg_zero] using hz.1)
  constructor
  · exact RealCompute.scaleRat_equiv ((componentSampler B f (origin d) true).cubeAverage_congr
      (boxSampler f B) (fun x _ => hcos x))
  · have h := (componentSampler B f (origin d) false).cubeAverage_congr z (fun x _ => hsin x)
    exact ((Same.trans (X := (componentSampler B f (origin d) false).cubeAverage)
      (Y := z.cubeAverage) h hzero).scale (B.dyadicCellVolume 0)).trans
      (arithmetic_identity _ (Value.rational 0) (by
        intro s
        simp [scale, Value.rational, Rat.mul_zero]))

/-- The Fourier value on a fixed box depends only on the represented
values of the input inside that box. -/
theorem component_congr {d : Nat} (B : RationalBox d) (ξ : QPoint d) (cosine : Bool)
    (f g : JointLipschitzSampler d)
    (h : ∀ x, B.Contains x → Same (f.value x) (g.value x)) :
    Same (component B f ξ cosine) (component B g ξ cosine) := by
  apply RealCompute.scaleRat_equiv
  apply JointLipschitzSampler.cubeAverage_congr
  intro x _
  exact Same.mul (h (boxPoint B x) (boxPoint_range B x))
    (Same.refl ((trigSampler B ξ cosine).value x))

private theorem normalized_component_frequency_bound {d : Nat} (B : RationalBox d)
    (f : JointLipschitzSampler d) (ξ η : QPoint d) (cosine : Bool) (R δ : Rat)
    (hδ : 0 ≤ δ)
    (hR : ∀ x, B.Contains x → ∀ i, qabs (x i) ≤ R)
    (hξη : ∀ i, ξ i ≤ η i + δ ∧ η i ≤ ξ i + δ) :
    Small (sub (componentSampler B f ξ cosine).cubeAverage
      (componentSampler B f η cosine).cubeAverage)
      (boxBound f B * (32 * (sumRat d (fun _ => 2 * R) * δ))) := by
  apply JointLipschitzSampler.cubeAverage_difference_small
  intro x _
  let y := boxPoint B x
  have symmetric (u v : QPoint d) : phase u v = phase v u := by
    unfold phase
    congr 1
    funext i
    rw [Rat.mul_assoc, Rat.mul_comm (u i) (v i), ← Rat.mul_assoc]
  have hweight : phaseWeight y ≤ sumRat d (fun _ => 2 * R) := by
    apply sum_le
    intro i
    rw [qabs_mul]
    exact Rat.mul_le_mul_of_nonneg_left (hR y (boxPoint_range B x) i) (by decide)
  have hp : qabs (phase ξ y - phase η y) ≤ sumRat d (fun _ => 2 * R) * δ := by
    rw [symmetric ξ y, symmetric η y]
    exact Rat.le_trans (phase_close y ξ η δ hξη)
      (Rat.mul_le_mul_of_nonneg_right hweight hδ)
  have ht : Small (sub (trigValue cosine (phase ξ y)) (trigValue cosine (phase η y)))
      (32 * (sumRat d (fun _ => 2 * R) * δ)) := by
    have hl : Small (sub (trigValue cosine (phase ξ y)) (trigValue cosine (phase η y)))
        (32 * qabs (phase ξ y - phase η y)) := by
      simpa only [Small, sub, trigValue, parameter, Value.parameter, RealCompute.Certified.ofRaw, Rat.neg_mul] using
        GeometricTrig.sample_lipschitz cosine (phase η y) (phase ξ y)
    exact hl.mono (Rat.mul_le_mul_of_nonneg_left hp (by decide))
  exact ((small_boxSampler f B x).mul ht).congr
    (arithmetic_identity _ _ (by
      intro s
      simp only [componentSampler, productSampler, trigSampler, Value.mul, sub, y]
      grind only))

/-- Frequency perturbations of at most `δ` in each coordinate have an
explicit error bound for each component of the finite-box transform. -/
theorem component_frequency_bound {d : Nat} (B : RationalBox d)
    (f : JointLipschitzSampler d) (ξ η : QPoint d) (cosine : Bool) (δ : Rat)
    (hδ : 0 ≤ δ)
    (hξη : ∀ i, ξ i ≤ η i + δ ∧ η i ≤ ξ i + δ) :
    let radius := sumRat d (fun i => qabs (B.lower i) + qabs (B.upper i))
    Small (sub (component B f ξ cosine) (component B f η cosine))
      (B.dyadicCellVolume 0 *
        (boxBound f B * (32 * (sumRat d (fun _ => 2 * radius) * δ)))) := by
  intro radius
  have hR : ∀ x, B.Contains x → ∀ i, qabs (x i) ≤ radius := by
    intro x hx i
    have h := entry_le_sum d (fun j => qabs (B.lower j) + qabs (B.upper j))
      (fun j => Rat.add_nonneg (qabs_nonneg _) (qabs_nonneg _)) i
    have hl := neg_qabs_le_self (B.lower i)
    have hu := self_le_qabs (B.upper i)
    have hlo := qabs_nonneg (B.lower i)
    have hhi := qabs_nonneg (B.upper i)
    change qabs (B.lower i) + qabs (B.upper i) ≤ radius at h
    exact qabs_le_of_neg_le_le (by have := (hx i).1; grind only)
      (by have := (hx i).2; grind only)
  have h := Small.scale_nonnegative B.volume_nonneg
    (normalized_component_frequency_bound B f ξ η cosine radius δ hδ hR hξη)
  exact h.congr (arithmetic_identity _ _ (by
    intro s
    simp only [component, boxIntegral, scale, sub]
    grind only))

private def expandingBox (d n : Nat) : RationalBox d :=
  let r : Rat := ((n + 1 : Nat) : Rat)
  ⟨fun _ => -r, fun _ => r, fun _ => by
    have hr : 0 ≤ r := Rat.natCast_nonneg
    grind only⟩

/-- The compact stages for the full-space transform use cubes of radius
`n + 1`, with the same spatial sampler and frequency at every stage. -/
def expandingComponent {d : Nat} (f : JointLipschitzSampler d)
    (ξ : QPoint d) (cosine : Bool) (n : Nat) : Value :=
  component (expandingBox d n) f ξ cosine

/-- Full-space Fourier quadrature refines the compact quadrature at each
stage and intersects finitely many intervals widened by the tail budget. -/
def wholeSpaceComponent {d : Nat} (f : JointLipschitzSampler d)
    (ξ : QPoint d) (cosine : Bool) (tail : Nat → Rat) : RealCompute :=
  RepresentedSeries.sum (expandingComponent f ξ cosine) tail

/-- A shrinking annular bound certifies the full-space evaluator and
identifies it as the limit of the actual compact Fourier quadratures. -/
theorem wholeSpaceComponent_tendsTo {d : Nat} (f : JointLipschitzSampler d)
    (ξ : QPoint d) (cosine : Bool) (tail : Nat → Rat)
    (shrinks : ShrinksToZero tail)
    (annuli : ∀ k n, k ≤ n →
      Small (sub (expandingComponent f ξ cosine n) (expandingComponent f ξ cosine k)) (tail k)) :
    RawLimit.TendsTo (fun n => (expandingComponent f ξ cosine n).real.preferred)
      (wholeSpaceComponent f ξ cosine tail) := by
  let P := expandingComponent f ξ cosine
  let D : EffectiveImproperIntegral.Data :=
    { compact := P
      error := tail
      nonnegative := by
        intro n
        have h := annuli n n (Nat.le_refl _)
        have hzero : Small (Value.rational 0) (tail n) :=
          h.congr (RealCompute.sub_self_equiv_zero (P n).real.valid)
        exact hzero.2 0 0
      shrinks := shrinks
      tail := annuli }
  exact D.tendsTo

/-- The whole-space value is independent of the certified tail budget. -/
theorem wholeSpaceComponent_tail_congr {d : Nat} (f : JointLipschitzSampler d)
    (ξ : QPoint d) (cosine : Bool) (tail₁ tail₂ : Nat → Rat)
    (shrinks₁ : ShrinksToZero tail₁) (shrinks₂ : ShrinksToZero tail₂)
    (annuli₁ : ∀ k n, k ≤ n →
      Small (sub (expandingComponent f ξ cosine n) (expandingComponent f ξ cosine k)) (tail₁ k))
    (annuli₂ : ∀ k n, k ≤ n →
      Small (sub (expandingComponent f ξ cosine n) (expandingComponent f ξ cosine k)) (tail₂ k)) :
    (wholeSpaceComponent f ξ cosine tail₁).Equiv (wholeSpaceComponent f ξ cosine tail₂) :=
  RawLimit.unique
    (wholeSpaceComponent_tendsTo f ξ cosine tail₁ shrinks₁ annuli₁)
    (wholeSpaceComponent_tendsTo f ξ cosine tail₂ shrinks₂ annuli₂)

private def lineData (f : JointLipschitzSampler 1) {a b : Rat} (hab : a ≤ b) :
    LipschitzQuadrature.Data (fun t => f.value (fun _ => t)) a b where
  ordered := hab
  constant := f.bound
  nonnegative := f.nonnegative
  lipschitz u v _ huv _ :=
    f.control (fun _ => v) (fun _ => u) (v - u) (by grind only) (fun _ => by
      constructor <;> grind only)

private theorem boxIntegral_line (B : RationalBox 1) (f g : JointLipschitzSampler 1)
    (h : ∀ t, -1 ≤ t → t ≤ 1 →
      Same (g.value (fun _ => t)) (f.value (boxPoint B (fun _ => t)))) :
    Same (boxIntegral B g) (lineData f (B.ordered (Fin.last 0))).value := by
  let a := B.lower (Fin.last 0)
  let b := B.upper (Fin.last 0)
  let L := lineData f (B.ordered (Fin.last 0))
  let G := lineData g (a := -1) (b := 1) (by decide +kernel)
  have hc : B.dyadicCellVolume 0 = b - a := by
    change (1 : Rat) * ((b - a) / 1) = b - a
    grind only
  have hsample : Same g.cubeAverage (scale (1 / 2) G.value) := g.cubeAverage_line G
  have hbox := hsample.scale (B.dyadicCellVolume 0)
  change Same (boxIntegral B g) (scale (B.dyadicCellVolume 0) (scale (1 / 2) G.value)) at hbox
  by_cases he : a = b
  · have hzero : Same L.value (Value.rational 0) := by
      change L.integral.Equiv (RealCompute.ofRat 0)
      change (if a = b then RealCompute.ofRat 0 else _) |>.Equiv (RealCompute.ofRat 0)
      rw [if_pos he]
      exact RealCompute.equiv_refl (RealCompute.ofRat 0) (RealCompute.ofRat_valid 0)
    apply hbox.trans (Same.trans (Y := Value.rational 0) ?_ hzero.symm)
    rw [hc, show b - a = 0 by grind only]
    exact arithmetic_identity _ _ (fun _ => Rat.zero_mul _)
  · have hs : 0 < (b - a) / 2 := by have := L.ordered; grind only
    have heq : Same L.value (scale ((b - a) / 2) G.value) := by
      apply G.affine_identity L (c := a + (b - a) / 2) hs
        (by grind only) (by grind only)
      intro t ht ht'
      refine (h t ht ht').trans ?_
      have hp : boxPoint B (fun _ => t) = fun _ => a + (b - a) / 2 + (b - a) / 2 * t := by
        funext i
        refine Fin.lastCases ?_ (fun j => Fin.elim0 j) i
        rw [boxPoint_on_unitCube B _ (fun _ => ⟨ht, ht'⟩)]
        change a + (b - a) / 2 * (1 + t) = _
        grind only
      rw [hp]
      exact Same.refl _
    refine hbox.trans (Same.trans (Y := scale ((b - a) / 2) G.value) ?_ heq.symm)
    rw [hc]
    apply arithmetic_identity
    intro s
    simp only [scale]
    grind only [Rat.div_def]

/-- Fourier integrand on the ambient line, prior to the change to cube coordinates. -/
private def linePhaseSampler (f : JointLipschitzSampler 1) (ξ : QPoint 1) (cosine : Bool)
    (M : Rat) (hM : 0 ≤ M) (hf : ∀ x, Small (f.value x) M) : JointLipschitzSampler 1 :=
  productSampler f
    { value := fun x => trigValue cosine (phase ξ x)
      bound := 32 * phaseWeight ξ
      nonnegative := Rat.mul_nonneg (by decide) (phaseWeight_nonneg ξ)
      control := by
        intro x y δ _ hxy
        have h : Small (sub (trigValue cosine (phase ξ x)) (trigValue cosine (phase ξ y)))
            (32 * qabs (phase ξ x - phase ξ y)) := by
          simpa only [Small, sub, trigValue, parameter, Value.parameter, RealCompute.Certified.ofRaw, Rat.neg_mul] using
            GeometricTrig.sample_lipschitz cosine (phase ξ y) (phase ξ x)
        exact h.mono (by
          rw [Rat.mul_assoc]
          exact Rat.mul_le_mul_of_nonneg_left (phase_close ξ x y δ hxy) (by decide)) }
    M 1 hM (by decide) hf (fun _ => trig_small _ _)

private theorem expandingComponent_line (f : JointLipschitzSampler 1) (ξ : QPoint 1) (cosine : Bool)
    (M : Rat) (hM : 0 ≤ M) (hf : ∀ x, Small (f.value x) M) (n : Nat) :
    Same (expandingComponent f ξ cosine n)
      (lineData (linePhaseSampler f ξ cosine M hM hf)
        (a := -((n + 1 : Nat) : Rat)) (b := ((n + 1 : Nat) : Rat)) (by
          have _h : (0 : Rat) ≤ ((n + 1 : Nat) : Rat) := Rat.natCast_nonneg
          grind only)).value := by
  apply boxIntegral_line
  intro t _ _
  exact Same.refl _

private def radius (n : Nat) : Rat := ((n + 1 : Nat) : Rat)

private theorem radius_pos (n : Nat) : 0 < radius n :=
  Rat.natCast_pos.mpr (Nat.succ_pos n)

private theorem radius_succ (n : Nat) : radius (n+1) = radius n + 1 := by
  unfold radius
  rw [Rat.natCast_add]
  rfl

private theorem reciprocalDifference (n : Nat) :
    1 / radius n - 1 / radius (n+1) = 1 / (radius n * radius (n+1)) := by
  have h₁ := Rat.mul_inv_cancel (radius n) (Rat.ne_of_gt (radius_pos n))
  have h₂ := Rat.mul_inv_cancel (radius (n+1)) (Rat.ne_of_gt (radius_pos (n+1)))
  have h₃ := radius_succ n
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  have he : (radius n + 1) * (radius (n+1))⁻¹ = 1 := by rwa [← h₃]
  calc
    _ = (radius n)⁻¹ * ((radius n + 1) * (radius (n+1))⁻¹) -
        ((radius n)⁻¹ * radius n) * (radius (n+1))⁻¹ := by rw [he]; grind only
    _ = _ := by grind only

private theorem reciprocal_mul_mono {a b : Rat} (ha : 0 < a) (hab : a ≤ b) :
    1 / b ≤ 1 / a := by
  have hb : 0 < b := by grind only
  have hp := Rat.mul_pos ha hb
  apply Rat.le_of_mul_le_mul_right (c := a * b) _ hp
  have ha₁ := Rat.mul_inv_cancel a (Rat.ne_of_gt ha)
  have hb₁ := Rat.mul_inv_cancel b (Rat.ne_of_gt hb)
  have hleft : (1 / b) * (a * b) = a := by grind only [Rat.div_def]
  have hright : (1 / a) * (a * b) = b := by grind only [Rat.div_def]
  rwa [hleft, hright]

/-- A uniform bound and quadratic spatial decay on the line. Both are bounds
on the original sampler, before multiplication by a Fourier mode. -/
structure LineDecay (f : JointLipschitzSampler 1) where
  bound : Rat
  nonnegative : 0 ≤ bound
  bounded : ∀ t : Rat, Small (f.value (fun _ => t)) bound
  outside : ∀ t : Rat, 1 ≤ qabs t →
    Small (f.value (fun _ => t)) (bound / (qabs t * qabs t))

private theorem lineDecay_all {f : JointLipschitzSampler 1} (D : LineDecay f) (x : QPoint 1) :
    Small (f.value x) D.bound := by
  have he : (fun _ : Fin 1 => x (Fin.last 0)) = x := by
    funext i
    refine Fin.lastCases rfl (fun j => Fin.elim0 j) i
  simpa only [he] using D.bounded (x (Fin.last 0))

/-- Every bounded sampler supported in a rational interval has a decay
certificate. The same constructor applies to compactly supported tests. -/
def LineDecay.of_support {f : JointLipschitzSampler 1} (M R : Rat)
    (hM : 0 ≤ M) (hR : 1 ≤ R)
    (bounded : ∀ t : Rat, Small (f.value (fun _ => t)) M)
    (vanishes : ∀ t : Rat, R < qabs t → Same (f.value (fun _ => t)) (Value.rational 0)) :
    LineDecay f where
  bound := M * (R * R)
  nonnegative := Rat.mul_nonneg hM (rat_square_nonneg_basic R)
  bounded t := (bounded t).mono (by
    have hr : 0 ≤ R := by grind only
    have h := Rat.mul_le_mul_of_nonneg_right hR hr
    have h₁ : 1 ≤ R * R := by grind only
    simpa only [Rat.mul_one] using Rat.mul_le_mul_of_nonneg_left h₁ hM)
  outside t ht := by
    have hq : 0 < qabs t := by grind only
    have hq₂ := Rat.mul_pos hq hq
    by_cases h : R < qabs t
    · have hz : Small (Value.rational 0) 0 :=
        ⟨fun _ _ => (by decide +kernel : (-0 : Rat) ≤ 0), fun _ _ => Rat.le_refl⟩
      exact (hz.congr (vanishes t h).symm).mono (Rat.mul_nonneg
        (Rat.mul_nonneg hM (rat_square_nonneg_basic R)) (Rat.le_of_lt (Rat.inv_pos.mpr hq₂)))
    · have htR : qabs t ≤ R := by grind only
      have hsq : qabs t * qabs t ≤ R * R :=
        Rat.le_trans (Rat.mul_le_mul_of_nonneg_right htR (Rat.le_of_lt hq))
          (Rat.mul_le_mul_of_nonneg_left htR (show 0 ≤ R by grind only))
      apply (bounded t).mono
      apply Rat.le_of_mul_le_mul_right (c := qabs t * qabs t) _ hq₂
      rw [Rat.div_mul_cancel (Rat.ne_of_gt hq₂)]
      exact Rat.mul_le_mul_of_nonneg_left hsq hM

private theorem intervalTail_step (g : JointLipschitzSampler 1) (M : Rat) (hM : 0 ≤ M)
    (hout : ∀ t : Rat, 1 ≤ qabs t → Small (g.value (fun _ => t)) (M / (qabs t * qabs t)))
    (n : Nat) :
    Small (sub (lineData g ((expandingBox 1 (n+1)).ordered (Fin.last 0))).value
      (lineData g ((expandingBox 1 n).ordered (Fin.last 0))).value)
      (4 * M * (1 / radius n - 1 / radius (n + 1))) := by
  let a := radius n
  let b := radius (n + 1)
  have ha : 0 < a := radius_pos n
  have hb : b = a + 1 := radius_succ n
  have ha1 : 1 ≤ a := by
    change (1 : Rat) ≤ ((n + 1 : Nat) : Rat)
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  let L := lineData g (a := -b) (b := -a) (by grind only)
  let I := lineData g (a := -a) (b := a) (by grind only)
  let R := lineData g (a := a) (b := b) (by grind only)
  let LI := lineData g (a := -b) (b := a) (by grind only)
  let O := lineData g (a := -b) (b := b) (by grind only)
  have hL : Same LI.value (Value.add L.value I.value) := L.append I LI
  have hR : Same O.value (Value.add LI.value R.value) := LI.append R O
  have ho : Same (sub O.value I.value) (Value.add L.value R.value) := by
    refine ((hR.trans (hL.add (Same.refl R.value))).sub (Same.refl I.value)).trans ?_
    apply arithmetic_identity
    intro s
    simp only [Value.add, sub]
    grind only
  have outer (t : Rat) (ht : a ≤ qabs t) :
      Small (g.value (fun _ => t)) (M / (a * a)) := by
    have h := hout t (Rat.le_trans ha1 ht)
    have hp := Rat.le_of_lt ha
    have hsq : a * a ≤ qabs t * qabs t :=
      Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ht hp)
        (Rat.mul_le_mul_of_nonneg_left ht (qabs_nonneg t))
    have hinv := reciprocal_mul_mono (Rat.mul_pos ha ha) hsq
    have hscaled := Rat.mul_le_mul_of_nonneg_left hinv hM
    exact h.mono (by simpa only [Rat.div_def, Rat.one_mul] using hscaled)
  have hl := L.small (M / (a * a)) (fun t _ ht => outer t (by
    rw [qabs_eq_neg_of_nonpos (by grind only)]
    grind only))
  have hr := R.small (M / (a * a)) (fun t ht _ => outer t
    (Rat.le_trans ht (self_le_qabs t)))
  have hbudget : ((-a) - (-b)) * (M / (a * a)) +
      (b - a) * (M / (a * a)) ≤ 4 * M * (1 / a - 1 / b) := by
    simp only [show -a - -b = 1 by grind only, show b - a = 1 by grind only, Rat.one_mul]
    change _ ≤ 4 * M * (1 / radius n - 1 / radius (n + 1))
    rw [reciprocalDifference]
    change _ ≤ 4 * M * (1 / (a * b))
    have hab : a * b ≤ 2 * (a * a) := by
      have h := Rat.mul_le_mul_of_nonneg_left (show b ≤ 2 * a by grind only) (Rat.le_of_lt ha)
      grind only
    have hp : 0 < a * b := Rat.mul_pos ha (by grind only)
    have hi := reciprocal_mul_mono hp hab
    have hm := Rat.mul_le_mul_of_nonneg_left hi
      (show 0 ≤ 4 * M from Rat.mul_nonneg (by decide) hM)
    have he : 4 * M * (1 / (2 * (a * a))) =
        M / (a * a) + M / (a * a) := by
      simp only [Rat.div_def, Rat.inv_mul_rev, Rat.one_mul]
      have htwo := Rat.mul_inv_cancel 2 (by decide : (2 : Rat) ≠ 0)
      grind only
    rwa [he] at hm
  exact ((hl.add hr).mono hbudget).congr ho.symm

private theorem lineTail_step {f : JointLipschitzSampler 1} (D : LineDecay f)
    (ξ : QPoint 1) (cosine : Bool) (n : Nat) :
    Small (sub (expandingComponent f ξ cosine (n + 1)) (expandingComponent f ξ cosine n))
      (4 * D.bound * (1 / radius n - 1 / radius (n + 1))) := by
  let g := linePhaseSampler f ξ cosine D.bound D.nonnegative (lineDecay_all D)
  have H := intervalTail_step g D.bound D.nonnegative (fun t ht => by
    change Small (Value.mul (f.value (fun _ => t)) (trigValue cosine (phase ξ (fun _ => t)))) _
    simpa only [Rat.mul_one] using (D.outside t ht).mul (trig_small cosine (phase ξ (fun _ => t)))) n
  exact H.congr ((expandingComponent_line f ξ cosine D.bound D.nonnegative (lineDecay_all D) (n+1)).symm.sub
    (expandingComponent_line f ξ cosine D.bound D.nonnegative (lineDecay_all D) n).symm)

private theorem annuli_of_step (P : Nat → Value) (M : Rat) (hM : 0 ≤ M)
    (step : ∀ n, Small (sub (P (n+1)) (P n)) (4*M*(1/radius n - 1/radius (n+1))))
    (k n : Nat) (hkn : k ≤ n) :
    Small (sub (P n) (P k)) (4*M/radius k) := by
  have H : Small (sub (P n) (P k)) (4 * M * (1 / radius k - 1 / radius n)) := by
    induction hkn with
    | refl =>
      rw [Rat.sub_self, Rat.mul_zero]
      exact (show Small (Value.rational 0) 0 from
        ⟨fun _ _ => (by decide +kernel : (-0 : Rat) ≤ 0), fun _ _ => Rat.le_refl⟩).congr
        (RealCompute.equiv_symm (RealCompute.sub_self_equiv_zero (P k).real.valid))
    | @step n _ ih =>
      have h := ih.add (step n)
      rw [show 4 * M * (1 / radius k - 1 / radius n) +
        4 * M * (1 / radius n - 1 / radius (n + 1)) =
        4 * M * (1 / radius k - 1 / radius (n + 1)) by grind only] at h
      exact h.congr (arithmetic_identity _ _ (by
        intro s
        simp only [Value.add, sub]
        grind only))
  apply H.mono
  have h := Rat.mul_le_mul_of_nonneg_left
    (show 1 / radius k - 1 / radius n ≤ 1 / radius k by
      have hp : 0 ≤ 1 / radius n := Rat.mul_nonneg (by decide : (0 : Rat) ≤ 1)
        (Rat.le_of_lt (Rat.inv_pos.mpr (radius_pos n)))
      grind only) (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 4) hM)
  simpa only [radius, Rat.div_def, Rat.one_mul] using h

/-- The two outer intervals telescope to a shrinking error independent
of frequency. This certifies the actual expanding box quadratures. -/
theorem line_annuli {f : JointLipschitzSampler 1} (D : LineDecay f)
    (ξ : QPoint 1) (cosine : Bool) (k n : Nat) (hkn : k ≤ n) :
    Small (sub (expandingComponent f ξ cosine n) (expandingComponent f ξ cosine k))
      (4 * D.bound / ((k + 1 : Nat) : Rat)) :=
  annuli_of_step _ D.bound D.nonnegative (lineTail_step D ξ cosine) k n hkn

/-- Each truncation uses the absolute dyadic grid in the spatial
coordinate. The decay certificate supplies bounds for the product
with the Fourier phase. -/
def lineCompactComponent {f : JointLipschitzSampler 1} (D : LineDecay f)
    (ξ : QPoint 1) (cosine : Bool) (n : Nat) : Value :=
  (lineData (linePhaseSampler f ξ cosine D.bound D.nonnegative (lineDecay_all D))
    ((expandingBox 1 n).ordered (Fin.last 0))).value

theorem lineCompactComponent_agrees {f : JointLipschitzSampler 1} (D : LineDecay f)
    (ξ : QPoint 1) (cosine : Bool) (n : Nat) :
    Same (expandingComponent f ξ cosine n) (lineCompactComponent D ξ cosine n) :=
  expandingComponent_line f ξ cosine D.bound D.nonnegative (lineDecay_all D) n

private def lineTransformData {f : JointLipschitzSampler 1} (D : LineDecay f)
    (ξ : QPoint 1) (cosine : Bool) : EffectiveImproperIntegral.Data where
  compact := lineCompactComponent D ξ cosine
  error k := 4 * D.bound / ((k + 1 : Nat) : Rat)
  nonnegative k := Rat.mul_nonneg (Rat.mul_nonneg (by decide) D.nonnegative)
    (Rat.le_of_lt (Rat.inv_pos.mpr (radius_pos k)))
  shrinks := shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl)
  tail k n hkn := (line_annuli D ξ cosine k n hkn).congr
    ((lineCompactComponent_agrees D ξ cosine n).sub (lineCompactComponent_agrees D ξ cosine k))

/-- Computed whole-line Fourier component with the explicit decay budget. -/
def lineTransform {f : JointLipschitzSampler 1} (D : LineDecay f)
    (ξ : QPoint 1) (cosine : Bool) : RealCompute :=
  (lineTransformData D ξ cosine).raw

theorem lineTransform_valid {f : JointLipschitzSampler 1} (D : LineDecay f)
    (ξ : QPoint 1) (cosine : Bool) : (lineTransform D ξ cosine).Valid :=
  (lineTransformData D ξ cosine).valid

theorem lineTransform_error {f : JointLipschitzSampler 1} (D : LineDecay f)
    (ξ : QPoint 1) (cosine : Bool) (k : Nat) :
    Small (sub (parameter (lineTransform D ξ cosine) (lineTransform_valid D ξ cosine))
      (expandingComponent f ξ cosine k)) (4 * D.bound / ((k + 1 : Nat) : Rat)) :=
  ((lineTransformData D ξ cosine).distance k).congr
    ((Same.refl _).sub (lineCompactComponent_agrees D ξ cosine k).symm)

theorem lineTransform_tendsTo {f : JointLipschitzSampler 1} (D : LineDecay f)
    (ξ : QPoint 1) (cosine : Bool) :
    RawLimit.TendsTo (fun n => (expandingComponent f ξ cosine n).real.preferred)
      (lineTransform D ξ cosine) :=
  RawLimit.congr_sequence (lineTransformData D ξ cosine).tendsTo
    (fun n => (expandingComponent f ξ cosine n).real.valid)
    (fun n => (lineCompactComponent_agrees D ξ cosine n).symm)

/-- A uniform magnitude bound for each component of the whole-line
transform, obtained by integrating the central interval and adding its tail. -/
theorem lineTransform_small {f : JointLipschitzSampler 1} (D : LineDecay f)
    (ξ : QPoint 1) (cosine : Bool) :
    Small (parameter (lineTransform D ξ cosine) (lineTransform_valid D ξ cosine)) (6 * D.bound) := by
  let g := linePhaseSampler f ξ cosine D.bound D.nonnegative (lineDecay_all D)
  let I := lineData g (a := -1) (b := 1) (by decide +kernel)
  have hi : Small I.value (2 * D.bound) := by
    have h := I.small D.bound (fun t _ _ => by
      have h := (D.bounded t).mul (trig_small cosine (phase ξ (fun _ => t)))
      change Small (Value.mul (f.value (fun _ => t)) (trigValue cosine (phase ξ (fun _ => t))))
        D.bound
      simpa only [Rat.mul_one] using h)
    simpa only [show (1 : Rat) - -1 = 2 by decide +kernel] using h
  have hc : Same (expandingComponent f ξ cosine 0) I.value :=
    expandingComponent_line f ξ cosine D.bound D.nonnegative (lineDecay_all D) 0
  have ht := lineTransform_error D ξ cosine 0
  have h := ht.add (hi.congr hc.symm)
  have he : 4 * D.bound / (((0 + 1 : Nat) : Rat)) + 2 * D.bound = 6 * D.bound := by
    change 4 * D.bound / 1 + 2 * D.bound = 6 * D.bound
    grind only
  rw [he] at h
  exact h.congr (arithmetic_identity _ _ (by
    intro s
    simp only [Value.add, sub]
    grind only))

/-- The limit is independent of the supplied decay bounds. -/
theorem lineTransform_congr_bounds {f : JointLipschitzSampler 1} (D E : LineDecay f)
    (ξ : QPoint 1) (cosine : Bool) :
    (lineTransform D ξ cosine).Equiv (lineTransform E ξ cosine) :=
  RawLimit.unique (lineTransform_tendsTo D ξ cosine) (lineTransform_tendsTo E ξ cosine)

/-- Equivalent samplers give the same transform, even if their interval
computations and decay certificates differ. -/
theorem lineTransform_congr {f g : JointLipschitzSampler 1} (D : LineDecay f) (E : LineDecay g)
    (h : ∀ x, Same (f.value x) (g.value x)) (ξ : QPoint 1) (cosine : Bool) :
    (lineTransform D ξ cosine).Equiv (lineTransform E ξ cosine) := by
  apply RawLimit.unique (lineTransform_tendsTo D ξ cosine)
  apply RawLimit.congr_sequence (lineTransform_tendsTo E ξ cosine)
    (fun n => (expandingComponent f ξ cosine n).real.valid)
  intro n
  exact component_congr (expandingBox 1 n) ξ cosine g f (fun x _ => (h x).symm)

/-- After the expanding interval covers the support, each later stage
has the same value as the whole-line transform. -/
theorem lineTransform_of_support {f : JointLipschitzSampler 1} (D : LineDecay f)
    (ξ : QPoint 1) (cosine : Bool) (R : Rat) (k : Nat) (hR : R ≤ ((k + 1 : Nat) : Rat))
    (vanishes : ∀ t : Rat, R ≤ qabs t → Same (f.value (fun _ => t)) (Value.rational 0)) :
    (lineTransform D ξ cosine).Equiv (expandingComponent f ξ cosine k).real.preferred := by
  let g := linePhaseSampler f ξ cosine D.bound D.nonnegative (lineDecay_all D)
  let a := radius k
  have ha := radius_pos k
  have stages (n : Nat) (hkn : k ≤ n) :
      Same (expandingComponent f ξ cosine n) (expandingComponent f ξ cosine k) := by
    let b := radius n
    have hab : a ≤ b := by
      change ((k + 1 : Nat) : Rat) ≤ ((n + 1 : Nat) : Rat)
      exact_mod_cast (show k + 1 ≤ n + 1 by omega)
    let L := lineData g (a := -b) (b := -a) (by grind only)
    let I := lineData g (a := -a) (b := a) (by grind only)
    let P := lineData g (a := -b) (b := a) (by grind only)
    let Q := lineData g (a := a) (b := b) hab
    let O := lineData g (a := -b) (b := b) (by grind only)
    have outside (t : Rat) (ht : a ≤ qabs t) :
        Same (g.value (fun _ => t)) (Value.rational 0) := by
      have h := (vanishes t (Rat.le_trans hR ht)).mul (Same.refl (trigValue cosine
        (phase ξ (fun _ => t))))
      refine h.trans (arithmetic_identity _ _ ?_)
      intro s
      simp only [Value.mul, Value.rational, Rat.zero_mul]
    have zeroIntegral {u v : Rat}
        (T : LipschitzQuadrature.Data (fun t => g.value (fun _ => t)) u v)
        (ht : ∀ t, u ≤ t → t ≤ v → a ≤ qabs t) : Same T.value (Value.rational 0) := by
      have hc := Integral.constant_hasIntegral (RealCompute.ofRat 0) (RealCompute.ofRat_valid 0) u v T.ordered
      have h := T.identify (hc.congrFunction
        (G := LipschitzIntegralBounds.onInterval (fun t => g.value (fun _ => t)) u v)
        ⟨rfl, rfl, fun t hdom _ => (outside t (ht t hdom.1 hdom.2)).symm⟩)
      exact Same.trans (Y := scale (v - u) (Value.rational 0)) h
        (arithmetic_identity _ _ (fun _ => Rat.mul_zero _))
    have hl := zeroIntegral L (fun t _ ht => by
      rw [qabs_eq_neg_of_nonpos (by grind only)]
      grind only)
    have hq := zeroIntegral Q (fun t ht _ => Rat.le_trans ht (self_le_qabs t))
    have hP : Same P.value (Value.add L.value I.value) := L.append I P
    have hO : Same O.value (Value.add P.value Q.value) := P.append Q O
    have hinner := expandingComponent_line f ξ cosine D.bound D.nonnegative (lineDecay_all D) k
    have houter := expandingComponent_line f ξ cosine D.bound D.nonnegative (lineDecay_all D) n
    have he : Same (Value.add (Value.add (Value.rational 0) I.value) (Value.rational 0)) I.value := by
      apply arithmetic_identity
      intro s
      simp only [Value.add, Value.rational, Rat.add_zero, Rat.zero_add]
    exact houter.trans (hO.trans (((hP.trans (hl.add (Same.refl I.value))).add hq).trans
      (he.trans hinner.symm)))
  apply RawLimit.unique (lineTransform_tendsTo D ξ cosine)
  refine ⟨(expandingComponent f ξ cosine k).real.valid,
    fun n => (expandingComponent f ξ cosine n).real.valid, ?_⟩
  intro m eps
  refine ⟨k, fun n hkn => ?_⟩
  have h := stages n hkn
  have hv := (expandingComponent f ξ cosine k).real.valid
  have hn := (expandingComponent f ξ cosine n).real.valid
  let x := (expandingComponent f ξ cosine k).real.preferred
  have hc : RawLimit.InInterval x (QInterval.expand (x.compute m) eps.val) := by
    apply RawLimit.inInterval_of_contains_compute hv m
    have := eps.property
    change (x.compute m).lo - eps.val ≤ (x.compute m).lo ∧
      (x.compute m).hi ≤ (x.compute m).hi + eps.val
    constructor <;> grind only
  exact RawLimit.inInterval_congr hv hn h.symm hc

private def frequencyRate (f : JointLipschitzSampler 1) (n : Nat) : Rat :=
  let B := expandingBox 1 n
  let R := sumRat 1 (fun i => qabs (B.lower i) + qabs (B.upper i))
  B.dyadicCellVolume 0 * (boxBound f B * (32 * sumRat 1 (fun _ => 2 * R)))

private theorem frequencyRate_nonneg (f : JointLipschitzSampler 1) (n : Nat) :
    0 ≤ frequencyRate f n := by
  let B := expandingBox 1 n
  let R := sumRat 1 (fun i => qabs (B.lower i) + qabs (B.upper i))
  have hR : 0 ≤ R := by
    rw [← sum_zero 1]
    exact sum_le 1 _ _ (fun _ => Rat.add_nonneg (qabs_nonneg _) (qabs_nonneg _))
  have hS : 0 ≤ sumRat 1 (fun _ => 2 * R) := by
    rw [← sum_zero 1]
    exact sum_le 1 _ _ (fun _ => Rat.mul_nonneg (by decide) hR)
  exact Rat.mul_nonneg B.volume_nonneg (Rat.mul_nonneg (boxBound_nonneg f B)
    (Rat.mul_nonneg (by decide) hS))

private def third (eps : QPos) : QPos :=
  ⟨eps.val / 3, Rat.mul_pos eps.property (by decide +kernel)⟩

private def lineTailStage (M : Rat) (eps : QPos) : Nat :=
  ((4 * M).num.natAbs + 1) * (eps.val.den + 1)

private theorem lineTailStage_spec (M : Rat) (eps : QPos) :
    4 * M / ((lineTailStage M eps + 1 : Nat) : Rat) ≤ eps.val := by
  let C : Rat := 4 * M
  let N := C.num.natAbs + 1
  let B := eps.val.den + 1
  let T : Rat := ((N * B + 1 : Nat) : Rat)
  have hC : C ≤ (N : Rat) := Rat.le_trans (self_le_qabs C) (qabs_le_numNatAbs_succ C)
  have hB : (0 : Rat) < (B : Rat) := Rat.natCast_pos.mpr (Nat.succ_pos _)
  have hT : 0 < T := Rat.natCast_pos.mpr (Nat.succ_pos _)
  have hmul : (N : Rat) * (B : Rat) ≤ T := by
    change (N : Rat) * (B : Rat) ≤ ((N * B + 1 : Nat) : Rat)
    exact_mod_cast (Nat.le_succ (N * B))
  have hbound : C / T ≤ 1 / (B : Rat) := by
    apply Rat.le_of_mul_le_mul_right (c := T * (B : Rat)) _ (Rat.mul_pos hT hB)
    have hl : (C / T) * (T * (B : Rat)) = C * (B : Rat) := by
      rw [← Rat.mul_assoc, Rat.div_mul_cancel (Rat.ne_of_gt hT)]
    have hr : (1 / (B : Rat)) * (T * (B : Rat)) = T := by
      rw [Rat.mul_comm T, ← Rat.mul_assoc, Rat.div_mul_cancel (Rat.ne_of_gt hB), Rat.one_mul]
    rw [hl, hr]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hC (Rat.le_of_lt hB)) hmul
  exact Rat.le_trans hbound (one_div_den_succ_le_of_pos eps.property)

/-- Executable rational frequency modulus, common to both transform components. -/
def lineFrequencyModulus {f : JointLipschitzSampler 1} (D : LineDecay f) (eps : QPos) : QPos :=
  let e := third eps
  let A := frequencyRate f (lineTailStage D.bound e)
  ⟨e.val / (A + 1), Rat.mul_pos e.property (Rat.inv_pos.mpr (by
    have := frequencyRate_nonneg f (lineTailStage D.bound e)
    change 0 < A + 1
    grind only))⟩

/-- A single rational modulus applies at every rational frequency.
The finite-box phase bound and the two discarded tails are budgeted separately. -/
theorem lineFrequencyModulus_spec {f : JointLipschitzSampler 1} (D : LineDecay f)
    (cosine : Bool) (eps : QPos) (ξ η : QPoint 1)
    (hξη : ∀ i, ξ i ≤ η i + (lineFrequencyModulus D eps).val ∧
      η i ≤ ξ i + (lineFrequencyModulus D eps).val) :
    Small (sub (parameter (lineTransform D ξ cosine) (lineTransform_valid D ξ cosine))
      (parameter (lineTransform D η cosine) (lineTransform_valid D η cosine))) eps.val := by
  let e := third eps
  let n := lineTailStage D.bound e
  have hn := lineTailStage_spec D.bound e
  let A := frequencyRate f n
  have hA : 0 ≤ A := frequencyRate_nonneg f n
  have hp : 0 < A + 1 := by grind only
  let δ := lineFrequencyModulus D eps
  have hmid := component_frequency_bound (expandingBox 1 n) f ξ η cosine δ.val
    (Rat.le_of_lt δ.property) hξη
  have he : Small (sub (expandingComponent f ξ cosine n) (expandingComponent f η cosine n))
      (A * δ.val) := by
    simpa only [expandingComponent, frequencyRate, A, Rat.mul_assoc] using hmid
  have hb : A * δ.val ≤ e.val := by
    have h := Rat.mul_le_mul_of_nonneg_right (show A ≤ A + 1 by grind only)
      (Rat.le_of_lt δ.property)
    have hx : (A + 1) * δ.val = e.val := by
      change (A + 1) * (e.val / (A + 1)) = e.val
      rw [Rat.mul_comm, Rat.div_mul_cancel (Rat.ne_of_gt hp)]
    rwa [hx] at h
  have hξ := (lineTransform_error D ξ cosine n).mono hn
  have hη := ((lineTransform_error D η cosine n).mono hn).neg
  have H := (hξ.add (he.mono hb)).add hη
  have hsum : e.val + e.val + e.val = eps.val := by
    change eps.val / 3 + eps.val / 3 + eps.val / 3 = eps.val
    grind only
  rw [hsum] at H
  exact H.congr (arithmetic_identity _ _ (by
    intro s
    simp only [Value.add, Value.neg, sub]
    grind only))

theorem lineTransform_uniformlyContinuous {f : JointLipschitzSampler 1} (D : LineDecay f)
    (cosine : Bool) (eps : QPos) :
    ∃ δ : QPos, ∀ ξ η : QPoint 1, (∀ i, ξ i ≤ η i + δ.val ∧ η i ≤ ξ i + δ.val) →
      Small (sub (parameter (lineTransform D ξ cosine) (lineTransform_valid D ξ cosine))
        (parameter (lineTransform D η cosine) (lineTransform_valid D η cosine))) eps.val :=
  ⟨lineFrequencyModulus D eps, fun ξ η => lineFrequencyModulus_spec D cosine eps ξ η⟩

private def frequencyTolerance (n : Nat) : QPos :=
  ⟨RawLimit.allowance n, RawLimit.allowance_pos n⟩

private def frequencyStage {f : JointLipschitzSampler 1} (D : LineDecay f)
    (x : RealCompute) (hx : x.Valid) (n : Nat) : Nat :=
  ConvexFTC.WidthSearch.stage x hx (lineFrequencyModulus D (frequencyTolerance n))

private def lineAtBox {f : JointLipschitzSampler 1} (D : LineDecay f) (cosine : Bool)
    (x : RealCompute) (hx : x.Valid) (n : Nat) : QInterval :=
  let q := (x.compute (frequencyStage D x hx n)).lo
  let y := lineTransform D (fun _ => q) cosine
  let m := ConvexFTC.WidthSearch.stage y (lineTransform_valid D (fun _ => q) cosine)
    (frequencyTolerance n)
  QInterval.expand (y.compute m) (frequencyTolerance n).val

/-- Evaluate the whole-line transform at an arbitrary valid represented
frequency using the rational-frequency evaluator and its modulus. -/
def lineTransformAt {f : JointLipschitzSampler 1} (D : LineDecay f) (cosine : Bool)
    (x : RealCompute) (hx : x.Valid) : RealCompute :=
  RawLimit.prefixRaw (lineAtBox D cosine x hx)

private def frequencyTests {f : JointLipschitzSampler 1} (D : LineDecay f) (cosine : Bool)
    (x : RealCompute) (i : Nat) (y : RealCompute) : Prop :=
  ∃ q : Rat, (x.compute i).lo ≤ q ∧ q ≤ (x.compute i).hi ∧
    y = lineTransform D (fun _ => q) cosine

private theorem frequencyTests_anti {f : JointLipschitzSampler 1} (D : LineDecay f) (cosine : Bool)
    (x : RealCompute) (hx : x.Valid) (i j : Nat) (hij : i ≤ j) (y : RealCompute)
    (hy : frequencyTests D cosine x j y) : frequencyTests D cosine x i y := by
  obtain ⟨q, hq, hq', rfl⟩ := hy
  have hn := hx.2.1 i j hij
  exact ⟨q, Rat.le_trans hn.1 hq, Rat.le_trans hq' hn.2.2, rfl⟩

private theorem lineAtBox_covers {f : JointLipschitzSampler 1} (D : LineDecay f) (cosine : Bool)
    (x : RealCompute) (hx : x.Valid) (n : Nat) (y : RealCompute)
    (hy : frequencyTests D cosine x (frequencyStage D x hx n) y) :
    RawLimit.InInterval y (lineAtBox D cosine x hx n) := by
  obtain ⟨q, hl, hr, rfl⟩ := hy
  let i := frequencyStage D x hx n
  let p := (x.compute i).lo
  let e := frequencyTolerance n
  have hw := ConvexFTC.WidthSearch.stage_spec x hx (lineFrequencyModulus D e)
  change (x.compute i).hi - p ≤ (lineFrequencyModulus D e).val at hw
  have hp := (lineFrequencyModulus D e).property
  change p ≤ q at hl
  change q ≤ (x.compute i).hi at hr
  have h := lineFrequencyModulus_spec D cosine e (fun _ => q) (fun _ => p)
    (fun _ => ⟨by grind only, by grind only⟩)
  exact RawLimit.inInterval_of_sub_bound (lineTransform_valid D (fun _ => q) cosine)
    (lineTransform_valid D (fun _ => p) cosine) e.val h.1 h.2 _

theorem lineTransformAt_valid {f : JointLipschitzSampler 1} (D : LineDecay f) (cosine : Bool)
    (x : RealCompute) (hx : x.Valid) : (lineTransformAt D cosine x hx).Valid := by
  refine RawLimit.prefix_valid (frequencyTests_anti D cosine x hx) ?_
    (lineAtBox_covers D cosine x hx) ?_
  · intro i
    let q := (x.compute i).lo
    exact ⟨lineTransform D (fun _ => q) cosine, lineTransform_valid D _ cosine,
      q, Rat.le_refl, RealCompute.interval_order_of_valid _ hx i, rfl⟩
  · intro eps
    let e : QPos := ⟨eps.val / 3, Rat.mul_pos eps.property (by decide +kernel)⟩
    obtain ⟨N, hN⟩ := RawLimit.allowance_shrinks e
    refine ⟨N, fun n hn => ?_⟩
    let q := (x.compute (frequencyStage D x hx n)).lo
    let y := lineTransform D (fun _ => q) cosine
    let m := ConvexFTC.WidthSearch.stage y (lineTransform_valid D _ cosine) (frequencyTolerance n)
    have hw := ConvexFTC.WidthSearch.stage_spec y (lineTransform_valid D _ cosine) (frequencyTolerance n)
    have hh := hN n hn
    change RawLimit.allowance n ≤ eps.val / 3 at hh
    change (y.compute m).hi - (y.compute m).lo ≤ RawLimit.allowance n at hw
    change (y.compute m).hi + RawLimit.allowance n -
      ((y.compute m).lo - RawLimit.allowance n) ≤ eps.val
    grind only

theorem lineTransformAt_congr {f : JointLipschitzSampler 1} (D : LineDecay f) (cosine : Bool)
    {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    (lineTransformAt D cosine x hx).Equiv (lineTransformAt D cosine y hy) := by
  intro n
  let i := RawLimit.runningMax (frequencyStage D x hx) n
  let j := RawLimit.runningMax (frequencyStage D y hy) n
  have ho := (RealCompute.compareAt_overlap_iff x y i j).mp
    (RealCompute.allStagesOverlap_of_equiv hx hy hxy i j)
  let q := max (x.compute i).lo (y.compute j).lo
  have hi := RealCompute.interval_order_of_valid _ hx i
  have hj := RealCompute.interval_order_of_valid _ hy j
  change (x.compute i).lo ≤ (y.compute j).hi ∧ (y.compute j).lo ≤ (x.compute i).hi at ho
  have h₁ : (x.compute i).lo ≤ q ∧ q ≤ (x.compute i).hi := by
    dsimp only [q]
    grind
  have h₂ : (y.compute j).lo ≤ q ∧ q ≤ (y.compute j).hi := by
    dsimp only [q]
    grind
  let r := lineTransform D (fun _ => q) cosine
  have hr := lineTransform_valid D (fun _ => q) cosine
  have hL := RawLimit.prefix_cover (frequencyTests_anti D cosine x hx)
    (lineAtBox_covers D cosine x hx) n r ⟨q, h₁.1, h₁.2, rfl⟩
  have hR := RawLimit.prefix_cover (frequencyTests_anti D cosine y hy)
    (lineAtBox_covers D cosine y hy) n r ⟨q, h₂.1, h₂.2, rfl⟩
  exact (RealCompute.compareAt_overlap_iff _ _ n n).mpr
    ⟨RealCompute.le_trans hr hL.1 hR.2 0 0, RealCompute.le_trans hr hR.1 hL.2 0 0⟩

theorem lineTransformAt_rational {f : JointLipschitzSampler 1} (D : LineDecay f) (cosine : Bool)
    (q : Rat) :
    (lineTransformAt D cosine (RealCompute.ofRat q) (RealCompute.ofRat_valid q)).Equiv
      (lineTransform D (fun _ => q) cosine) := by
  intro n
  let x := RealCompute.ofRat q
  let hx : x.Valid := RealCompute.ofRat_valid q
  let r := lineTransform D (fun _ => q) cosine
  have h := RawLimit.prefix_cover (frequencyTests_anti D cosine x hx)
    (lineAtBox_covers D cosine x hx) n r ⟨q, Rat.le_refl, Rat.le_refl, rfl⟩
  exact (RealCompute.compareAt_overlap_iff _ _ n n).mpr ⟨h.1 0 n, h.2 n 0⟩

section FiniteDifferentiation

open FTCRealCalculus GeometricFTCData
set_option maxHeartbeats 1500000

/-- Real or imaginary Fourier phase, in the negative-phase convention. -/
def lineMode (cosine : Bool) (ξ t : Rat) : Value :=
  family (-2 * ξ) 0 cosine t

/-- Spatial derivative of the geometric phase. This includes the represented
factor of pi and the rational scale from the Fourier convention. -/
def lineModeSpatialDerivative (cosine : Bool) (ξ t : Rat) : Value :=
  family (-2 * ξ) 1 cosine t

private def modeQuadrature (cosine : Bool) (ξ : Rat) (order : Nat)
    {a b : Rat} (hab : a ≤ b) :
    LipschitzQuadrature.Data (family (-2 * ξ) order cosine) a b where
  ordered := hab
  constant := magnitude (-2 * ξ) ^ (order + 1)
  nonnegative := Rat.pow_nonneg (Rat.mul_nonneg (by decide) (qabs_nonneg _))
  lipschitz := by
    let S := step (-2 * ξ) order cosine (a := a) (b := b)
    exact lipschitz_of_firstOrder S.firstOrder S.error_nonnegative S.radius.property
      (fun t _ _ => family_small (-2 * ξ) (order + 1) cosine t)

/-- Finite interval Fourier coefficient of a real-valued rational sampler. -/
def intervalComponent {f : Rat → Value} {a b : Rat} (F : LipschitzQuadrature.Data f a b)
    (cosine : Bool) (ξ M : Rat) (hM : 0 ≤ M)
    (hf : ∀ t, a ≤ t → t ≤ b → Small (f t) M) : Value :=
  (F.mul (modeQuadrature cosine ξ 0 F.ordered) M 1 hM (by decide) hf
    (fun t _ _ => by simpa only [Rat.pow_zero] using family_small (-2 * ξ) 0 cosine t)).value

/-- Integration by parts for a finite Fourier quadrature, with the two
endpoint terms exposed. -/
theorem intervalComponent_spatialDerivative {f df : Rat → Value} {a b : Rat}
    (F : LipschitzQuadrature.Data f a b) (DF : LipschitzQuadrature.Data df a b)
    (S : Step f df a b) (cosine : Bool) (ξ M N : Rat) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hf : ∀ t, a ≤ t → t ≤ b → Small (f t) M)
    (hdf : ∀ t, a ≤ t → t ≤ b → Small (df t) N) :
    Same (intervalComponent DF cosine ξ N hN hdf)
      (sub (sub (Value.mul (f b) (lineMode cosine ξ b)) (Value.mul (f a) (lineMode cosine ξ a)))
        (F.mul (modeQuadrature cosine ξ 1 F.ordered) M (magnitude (-2 * ξ)) hM
          (Rat.mul_nonneg (by decide) (qabs_nonneg _)) hf
          (fun t _ _ => by simpa only [Rat.pow_one] using family_small (-2 * ξ) 1 cosine t)).value) := by
  let T := step (-2 * ξ) 0 cosine (a := a) (b := b)
  have hg (t : Rat) : Small (lineMode cosine ξ t) 1 := by
    unfold lineMode
    simpa only [Rat.pow_zero] using family_small (-2 * ξ) 0 cosine t
  have hdg (t : Rat) : Small (lineModeSpatialDerivative cosine ξ t) (magnitude (-2 * ξ)) := by
    unfold lineModeSpatialDerivative
    simpa only [Rat.pow_one] using family_small (-2 * ξ) 1 cosine t
  apply S.integrationByParts T F.ordered M 1 N (magnitude (-2 * ξ)) hM (by decide) hN
    (Rat.mul_nonneg (by decide) (qabs_nonneg _)) hf (fun t _ _ => hg t) hdf
    (fun t _ _ => hdg t)
  · exact (DF.mul (modeQuadrature cosine ξ 0 DF.ordered) N 1 hN (by decide) hdf
      (fun t _ _ => hg t)).hasIntegral
  · exact (F.mul (modeQuadrature cosine ξ 1 F.ordered) M (magnitude (-2 * ξ)) hM
      (Rat.mul_nonneg (by decide) (qabs_nonneg _)) hf (fun t _ _ => hdg t)).hasIntegral

private theorem lineMode_same (cosine : Bool) (ξ t : Rat) :
    Same (lineMode cosine ξ t) (trigValue cosine (phase (fun _ : Fin 1 => ξ) (fun _ => t))) := by
  change Same (GeometricTrig.valueFor cosine ((-2 * ξ) * t)) _
  change (GeometricTrig.valueFor cosine ((-2 * ξ) * t)).real.preferred.Equiv
    (GeometricTrig.sample cosine (phase (fun _ : Fin 1 => ξ) (fun _ => t)))
  rw [GeometricTrig.valueFor_raw]
  have he : phase (fun _ : Fin 1 => ξ) (fun _ => t) = (-2 * ξ) * t := Rat.zero_add _
  rw [he]
  exact RealCompute.equiv_refl _ (GeometricTrig.sample_valid _ _)

/-- The differentiation laws use the same finite quadrature as the
whole-line construction. -/
theorem intervalComponent_agrees {f : JointLipschitzSampler 1} (D : LineDecay f)
    (cosine : Bool) (ξ : Rat) (n : Nat) :
    Same (expandingComponent f (fun _ => ξ) cosine n)
      (intervalComponent (lineData f ((expandingBox 1 n).ordered (Fin.last 0))) cosine ξ
        D.bound D.nonnegative (fun t _ _ => D.bounded t)) := by
  refine Same.trans (Y := (lineData (linePhaseSampler f (fun _ => ξ) cosine D.bound
    D.nonnegative (lineDecay_all D)) ((expandingBox 1 n).ordered (Fin.last 0))).value)
    (expandingComponent_line f (fun _ => ξ) cosine D.bound D.nonnegative (lineDecay_all D) n) ?_
  unfold intervalComponent
  refine (lineData (linePhaseSampler f (fun _ => ξ) cosine D.bound D.nonnegative
    (lineDecay_all D)) ((expandingBox 1 n).ordered (Fin.last 0))).congr
    ((lineData f ((expandingBox 1 n).ordered (Fin.last 0))).mul
      (modeQuadrature cosine ξ 0 ((expandingBox 1 n).ordered (Fin.last 0)))
      D.bound 1 D.nonnegative (by decide) (fun t _ _ => D.bounded t)
      (fun t _ _ => by simpa only [Rat.pow_zero] using family_small (-2*ξ) 0 cosine t)) ?_
  intro t _ _
  exact (Same.refl (f.value (fun _ => t))).mul (lineMode_same cosine ξ t).symm

/-- Interval data for multiplication by the spatial coordinate. -/
def coordinateData {a b : Rat} (hab : a ≤ b) :
    LipschitzQuadrature.Data Value.rational a b where
  ordered := hab
  constant := 1
  nonnegative := by decide
  lipschitz := by
    intro u v _ huv _
    have h := rational_small (v-u)
    rw [qabs_eq_self_of_nonneg (by grind only)] at h
    rw [Rat.one_mul]
    exact h.congr (arithmetic_identity _ _ (fun _ => rfl))

private def frequencySlope (cosine : Bool) (ξ t : Rat) : Value :=
  scale (-2 * t) (GeometricTrig.derivativeValue cosine ((-2 * ξ) * t))

private theorem modeFrequencyRemainder (cosine : Bool) (ξ h t R : Rat) (hR : 0 ≤ R)
    (ht : qabs t ≤ R) (hh : qabs h ≤ (GeometricFTCData.radius (-2 * t)).val) :
    Small (sub (sub (lineMode cosine (ξ+h) t) (lineMode cosine ξ t))
      (scale h (frequencySlope cosine ξ t))) (7424 * R * R * qabs h * qabs h) := by
  have hgap : qabs (((-2 * (ξ+h)) * t) - ((-2 * ξ) * t)) = 2 * qabs t * qabs h := by
    rw [show (-2 * (ξ+h)) * t - (-2 * ξ) * t = (-2*t)*h by grind only, qabs_mul, qabs_mul,
      show qabs (-2 : Rat) = 2 by decide +kernel]
  have ht' : qabs (-2*t) = 2 * qabs t := by
    rw [qabs_mul, show qabs (-2 : Rat) = 2 by decide +kernel]
  have hδ : 2 * qabs t * qabs h ≤ 1/4 := by
    have hz : 0 ≤ qabs (-2*t) := qabs_nonneg _
    change qabs h ≤ 1/(4*(qabs (-2*t)+1)) at hh
    have hp : 0 < 4*(qabs (-2*t)+1) := by grind only
    have hb := Rat.mul_le_mul_of_nonneg_right hh (Rat.le_of_lt hp)
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hp)] at hb
    have hnon := Rat.mul_nonneg (qabs_nonneg h) (show 0 ≤ 4 by decide)
    rw [← ht']
    grind only
  have H := firstOrder_any cosine ((-2 * ξ) * t) ((-2 * (ξ+h)) * t) (by rwa [hgap])
  rw [hgap] at H
  have hs : 0 ≤ 2 * qabs t * qabs h :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) (qabs_nonneg t)) (qabs_nonneg h)
  have hB : 0 ≤ 2 * R * qabs h :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) hR) (qabs_nonneg h)
  have hp : 2 * qabs t * qabs h ≤ 2 * R * qabs h := by
    exact Rat.mul_le_mul_of_nonneg_right (Rat.mul_le_mul_of_nonneg_left ht (by decide)) (qabs_nonneg h)
  have hsq := Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hp hs) (Rat.mul_le_mul_of_nonneg_left hp hB)
  have hb := Rat.mul_le_mul_of_nonneg_left hsq (show (0 : Rat) ≤ 1856 by decide)
  have Hb := H.mono (show 1856 * (2 * qabs t * qabs h) * (2 * qabs t * qabs h) ≤
      7424 * R * R * qabs h * qabs h by
    calc
      _ = 1856 * ((2 * qabs t * qabs h) * (2 * qabs t * qabs h)) := by grind only
      _ ≤ 1856 * ((2 * R * qabs h) * (2 * R * qabs h)) := hb
      _ = _ := by grind only)
  exact Hb.congr (arithmetic_identity _ _ (by
    intro s
    simp only [lineMode, family, frequencySlope, sub, scale]
    rw [show (-2 * (ξ+h)) * t - (-2 * ξ) * t = h * (-2 * t) by grind only]
    grind only))

/-- The frequency derivative integrand uses the opposite trigonometric
component multiplied by the spatial moment and the represented constant. -/
def frequencyDerivativeData {f : Rat → Value} {a b : Rat}
    (F : LipschitzQuadrature.Data f a b) (cosine : Bool) (ξ M R : Rat)
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hf : ∀ t, a ≤ t → t ≤ b → Small (f t) M)
    (ht : ∀ t, a ≤ t → t ≤ b → qabs t ≤ R) :
    LipschitzQuadrature.Data
      (fun t => Value.mul (scale (if cosine then 2 else -2) GeometricTrig.piValue)
        (Value.mul (Value.mul (Value.rational t) (f t)) (lineMode (!cosine) ξ t))) a b :=
  let c := scale (if cosine then 2 else -2) GeometricTrig.piValue
  have hc : Small c 16 := by
    have he : qabs (if cosine then (2 : Rat) else -2) * 8 = 16 := by
      cases cosine <;> decide +kernel
    exact he ▸ scale_small GeometricTrig.pi_small _
  let W := (coordinateData F.ordered).mul F R M hR hM
    (fun t ha hb => (rational_small t).mono (ht t ha hb)) hf
  let hg := fun t (_ : a ≤ t) (_ : t ≤ b) => show Small (lineMode (!cosine) ξ t) 1 by
    unfold lineMode
    simpa only [Rat.pow_zero] using family_small (-2*ξ) 0 (!cosine) t
  let hw := fun t ha hb => ((rational_small t).mono (ht t ha hb)).mul (hf t ha hb)
  let P := W.mul (modeQuadrature (!cosine) ξ 0 F.ordered) (R*M) 1
    (Rat.mul_nonneg hR hM) (by decide) hw hg
  (LipschitzQuadrature.constantData c a b F.ordered).mul P 16 (R*M*1)
    (by decide) (Rat.mul_nonneg (Rat.mul_nonneg hR hM) (by decide))
    (fun _ _ _ => hc) (fun t ha hb => (hw t ha hb).mul (hg t ha hb))

/-- Quadratic remainder for frequency differentiation of the finite
Fourier integral. The estimate holds for increments of either sign. -/
theorem intervalComponent_frequencyRemainder {f : Rat → Value} {a b : Rat}
    (F : LipschitzQuadrature.Data f a b) (cosine : Bool) (ξ h M R : Rat)
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hf : ∀ t, a ≤ t → t ≤ b → Small (f t) M)
    (ht : ∀ t, a ≤ t → t ≤ b → qabs t ≤ R)
    (hh : ∀ t, a ≤ t → t ≤ b → qabs h ≤ (GeometricFTCData.radius (-2 * t)).val) :
    Small (sub (sub (intervalComponent F cosine (ξ+h) M hM hf)
        (intervalComponent F cosine ξ M hM hf))
      (scale h (frequencyDerivativeData F cosine ξ M R hM hR hf ht).value))
      ((b-a) * (M * (7424 * R * R * qabs h * qabs h))) := by
  let G (u : Rat) := F.mul (modeQuadrature cosine u 0 F.ordered) M 1 hM (by decide) hf
    (fun t _ _ => by simpa only [Rat.pow_zero] using family_small (-2*u) 0 cosine t)
  let E := frequencyDerivativeData F cosine ξ M R hM hR hf ht
  have H := ((G (ξ+h)).subtract (G ξ)).difference_small (E.scale h)
    (M * (7424 * R * R * qabs h * qabs h)) (fun t ha hb => by
      have hs := (hf t ha hb).mul (modeFrequencyRemainder cosine ξ h t R hR (ht t ha hb) (hh t ha hb))
      apply hs.congr
      apply arithmetic_identity
      intro s
      cases cosine <;> simp only [lineMode, family, frequencySlope, GeometricTrig.derivativeValue,
        GeometricTrig.pairSlope, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        if_true, if_false, sub, scale, Value.mul, Value.rational, Value.neg] <;> grind only)
  have hsub : Same ((G (ξ+h)).subtract (G ξ)).value
      (sub (intervalComponent F cosine (ξ+h) M hM hf) (intervalComponent F cosine ξ M hM hf)) :=
    (G (ξ+h)).subtract_identity (G ξ)
  have hscale : Same (E.scale h).value (scale h E.value) := E.scale_identity h
  exact H.congr (hsub.sub hscale)

private theorem frequencyRadius_of_bound {h t R : Rat} (hR : 0 ≤ R) (ht : qabs t ≤ R)
    (hh : qabs h ≤ (GeometricFTCData.radius (2 * R)).val) :
    qabs h ≤ (GeometricFTCData.radius (-2 * t)).val := by
  have hp : 0 < 4 * (qabs (-2 * t) + 1) := by have := qabs_nonneg (-2*t); grind only
  have hle : 4 * (qabs (-2 * t) + 1) ≤ 4 * (qabs (2 * R) + 1) := by
    rw [qabs_mul, qabs_mul, show qabs (-2 : Rat) = 2 by decide +kernel,
      show qabs (2 : Rat) = 2 by decide +kernel, qabs_eq_self_of_nonneg hR]
    grind only
  exact Rat.le_trans hh (reciprocal_mul_mono hp hle)

/-- A whole-line frequency derivative for compactly supported data,
expressed as a finite quadrature of the weighted geometric phase. -/
theorem lineTransform_frequencyRemainder_of_support {f : JointLipschitzSampler 1}
    (D : LineDecay f) (cosine : Bool) (ξ h R : Rat) (k : Nat)
    (hR : R ≤ ((k + 1 : Nat) : Rat))
    (vanishes : ∀ t : Rat, R ≤ qabs t → Same (f.value (fun _ => t)) (Value.rational 0))
    (hh : qabs h ≤ (GeometricFTCData.radius (2 * ((k + 1 : Nat) : Rat))).val) :
    let F := lineData f ((expandingBox 1 k).ordered (Fin.last 0))
    let hrad := fun t (ha : -(((k + 1 : Nat) : Rat)) ≤ t) (hb : t ≤ ((k + 1 : Nat) : Rat)) =>
      qabs_le_of_neg_le_le ha hb
    let E := frequencyDerivativeData F cosine ξ D.bound (((k + 1 : Nat) : Rat)) D.nonnegative
      (Rat.le_of_lt (radius_pos k)) (fun t _ _ => D.bounded t) hrad
    Small (sub
      (sub (parameter (lineTransform D (fun _ => ξ+h) cosine) (lineTransform_valid D _ cosine))
        (parameter (lineTransform D (fun _ => ξ) cosine) (lineTransform_valid D _ cosine)))
      (scale h E.value))
      ((((k + 1 : Nat) : Rat) - -(((k + 1 : Nat) : Rat))) * (D.bound * (7424 * ((k + 1 : Nat) : Rat) * ((k + 1 : Nat) : Rat) * qabs h * qabs h))) := by
  intro F hrad E
  have H := intervalComponent_frequencyRemainder F cosine ξ h D.bound (radius k)
    D.nonnegative (Rat.le_of_lt (radius_pos k)) (fun t _ _ => D.bounded t) hrad
    (fun t ha hb => frequencyRadius_of_bound (Rat.le_of_lt (radius_pos k)) (hrad t ha hb) hh)
  have same (q : Rat) :
      Same (parameter (lineTransform D (fun _ => q) cosine) (lineTransform_valid D _ cosine))
        (intervalComponent F cosine q D.bound D.nonnegative (fun t _ _ => D.bounded t)) :=
    Same.trans (Y := expandingComponent f (fun _ => q) cosine k)
      (lineTransform_of_support D (fun _ => q) cosine R k hR vanishes)
      (intervalComponent_agrees D cosine q k)
  exact H.congr (((same (ξ+h)).symm.sub (same ξ).symm).sub (Same.refl (scale h E.value)))


def lineValue {f : JointLipschitzSampler 1} (D : LineDecay f)
    (cosine : Bool) (ξ : Rat) : Value :=
  (lineTransformData D (fun _ => ξ) cosine).value

def phaseFactor (cosine : Bool) (ξ : Rat) : Value :=
  scale (if cosine then 2 * ξ else -2 * ξ) GeometricTrig.piValue

private theorem phaseFactor_small (cosine : Bool) (ξ : Rat) :
    Small (phaseFactor cosine ξ) (16 * qabs ξ) := by
  have he : qabs (if cosine then 2 * ξ else -2 * ξ) * 8 = 16 * qabs ξ := by
    cases cosine <;> simp only [Bool.false_eq_true, if_false, if_true, qabs_mul,
      show qabs (-2 : Rat) = 2 by decide +kernel, show qabs (2 : Rat) = 2 by decide +kernel] <;> grind only
  exact he ▸ scale_small GeometricTrig.pi_small _

private theorem lineMode_small (cosine : Bool) (ξ t : Rat) : Small (lineMode cosine ξ t) 1 := by
  unfold lineMode
  simpa only [Rat.pow_zero] using family_small (-2 * ξ) 0 cosine t

/-- Spatial integration by parts on the line. The boundary term vanishes
by the input's decay, and the finite quadratures are those of the transform. -/
theorem lineTransform_spatialDerivative {f df : JointLipschitzSampler 1}
    (D : LineDecay f) (DD : LineDecay df)
    (S : ∀ n : Nat, Step (fun t => f.value (fun _ => t)) (fun t => df.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (cosine : Bool) (ξ : Rat) :
    Same (lineValue DD cosine ξ) (Value.neg (Value.mul (phaseFactor cosine ξ) (lineValue D (!cosine) ξ))) := by
  let C := phaseFactor cosine ξ
  let K := 16 * qabs ξ
  have hK : 0 ≤ K := Rat.mul_nonneg (by decide) (qabs_nonneg ξ)
  have hC : Small C K := phaseFactor_small cosine ξ
  let V := lineValue DD cosine ξ
  let W := lineValue D (!cosine) ξ
  let A := 4 * DD.bound + K * (4 * D.bound) + (2 * D.bound)
  have hz : Small (sub V (Value.neg (Value.mul C W))) 0 := by
    apply EffectiveImproperIntegral.small_of_errors _ 0 (fun n => A / radius n)
      (shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl))
    intro n
    let r := radius n
    let F := lineData f ((expandingBox 1 n).ordered (Fin.last 0))
    let DF := lineData df ((expandingBox 1 n).ordered (Fin.last 0))
    let hf := fun t (_ : -r ≤ t) (_ : t ≤ r) => D.bounded t
    let hdf := fun t (_ : -r ≤ t) (_ : t ≤ r) => DD.bounded t
    let G := F.mul (modeQuadrature (!cosine) ξ 0 F.ordered) D.bound 1 D.nonnegative
      (by decide) hf (fun t _ _ => lineMode_small _ ξ t)
    let L := F.mul (modeQuadrature cosine ξ 1 F.ordered) D.bound (magnitude (-2 * ξ)) D.nonnegative
      (Rat.mul_nonneg (by decide) (qabs_nonneg _)) hf
      (fun t _ _ => by simpa only [Rat.pow_one] using family_small (-2 * ξ) 1 cosine t)
    have hg : ∀ t, -r ≤ t → t ≤ r → Small (Value.mul (f.value (fun _ => t)) (lineMode (!cosine) ξ t)) (D.bound * 1) :=
      fun t _ _ => (D.bounded t).mul (lineMode_small _ ξ t)
    let CG := (LipschitzQuadrature.constantData C (-r) r F.ordered).mul G K (D.bound * 1)
      hK (Rat.mul_nonneg D.nonnegative (by decide)) (fun _ _ _ => hC) hg
    have hL : Same L.value (Value.mul C G.value) := by
      refine Same.trans (Y := CG.value) (L.congr CG ?_) (G.mul_constant_identity C _ K
        (Rat.mul_nonneg D.nonnegative (by decide)) hK hC hg)
      intro t _ _
      apply arithmetic_identity
      intro s
      cases cosine <;> simp only [C, phaseFactor, family, Value.mul, Value.neg, scale,
        Bool.false_eq_true, Bool.not_true, Bool.not_false, if_true, if_false] <;> grind only
    let B := sub (Value.mul (f.value (fun _ => r)) (lineMode cosine ξ r))
      (Value.mul (f.value (fun _ => -r)) (lineMode cosine ξ (-r)))
    have he : Same (expandingComponent df (fun _ => ξ) cosine n)
        (sub B (Value.mul C (expandingComponent f (fun _ => ξ) (!cosine) n))) := by
      have h := intervalComponent_spatialDerivative F DF (S n) cosine ξ D.bound DD.bound
        D.nonnegative DD.nonnegative hf hdf
      exact (intervalComponent_agrees DD cosine ξ n).trans (h.trans
        ((Same.refl B).sub (hL.trans ((Same.refl C).mul (intervalComponent_agrees D (!cosine) ξ n).symm))))
    have hr : 1 ≤ r := by
      change (1 : Rat) ≤ ((n+1 : Nat) : Rat)
      exact_mod_cast (show 1 ≤ n+1 by omega)
    have ha : qabs r = r := qabs_eq_self_of_nonneg (by grind only)
    have hb : qabs (-r) = r := (qabs_neg r).trans ha
    have hp := D.outside r (by rwa [ha])
    have hn := D.outside (-r) (by rwa [hb])
    rw [ha] at hp
    rw [hb] at hn
    have hB : Small B (2 * D.bound / r) := by
      have H := ((hp.mul (lineMode_small cosine ξ r)).add
        (hn.mul (lineMode_small cosine ξ (-r))).neg)
      have hrr : r ≤ r*r := by
        have H := Rat.mul_le_mul_of_nonneg_left hr (show 0 ≤ r by grind only)
        grind only
      have Hi := reciprocal_mul_mono (radius_pos n) hrr
      have Hm := Rat.mul_le_mul_of_nonneg_left Hi D.nonnegative
      have H' := H.mono (show D.bound / (r*r)*1 + D.bound / (r*r)*1 ≤ 2*D.bound/r by
        simp only [Rat.div_def, Rat.one_mul] at Hm ⊢
        grind only)
      exact H'.congr (arithmetic_identity _ B (by intro s; simp only [B, sub, Value.add, Value.neg]; grind only))
    have H := ((lineTransform_error DD (fun _ => ξ) cosine n).add
      (hC.mul (lineTransform_error D (fun _ => ξ) (!cosine) n))).add hB
    have HB : 4*DD.bound/r + K*(4*D.bound/r) + 2*D.bound/r = A/r := by
      simp only [A, Rat.div_def]
      grind only
    change Small _ (4*DD.bound/r + K*(4*D.bound/r) + 2*D.bound/r) at H
    rw [HB] at H
    simp only [Rat.zero_add]
    refine H.congr ?_
    have HE := ((Same.refl V).sub he).add
      (Same.refl (Value.mul C (sub W (expandingComponent f (fun _ => ξ) (!cosine) n))))
    refine (HE.add (Same.refl B)).trans ?_
    apply arithmetic_identity
    intro s
    simp only [Value.add, Value.mul, Value.neg, sub]
    grind only
  exact small_sub_zero_same hz


private def inversePhaseFactor (cosine : Bool) (ξ : Rat) : Value :=
  scale ((if cosine then 2*ξ else -2*ξ)⁻¹) GeometricIntegralData.inversePi

private theorem inversePhaseFactor_small (cosine : Bool) (ξ : Rat) (hξ : ξ ≠ 0) :
    Small (inversePhaseFactor cosine ξ) (1 / qabs ξ) := by
  let a : Rat := if cosine then 2*ξ else -2*ξ
  have ha : qabs a = 2 * qabs ξ := by
    cases cosine <;> simp only [a, Bool.false_eq_true, if_false, if_true, qabs_mul,
      show qabs (2 : Rat) = 2 by decide +kernel, show qabs (-2 : Rat) = 2 by decide +kernel]
  have hq := qabs_pos_of_ne hξ
  have hane : a ≠ 0 := by
    intro he
    rw [he, show qabs (0 : Rat) = 0 by decide +kernel] at ha
    grind only
  have he := congrArg qabs (Rat.inv_mul_cancel a hane)
  rw [qabs_mul, ha, show qabs (1 : Rat) = 1 by decide +kernel] at he
  have h := scale_small GeometricIntegralData.inversePi_small a⁻¹
  rw [Rat.mul_one] at h
  apply h.mono
  apply Rat.le_of_mul_le_mul_right (c := qabs ξ) _ hq
  rw [Rat.div_mul_cancel (Rat.ne_of_gt hq)]
  have hnon := qabs_nonneg a⁻¹
  have h := Rat.mul_nonneg hnon (Rat.le_of_lt hq)
  grind only

private theorem inversePhaseFactor_cancel (cosine : Bool) (ξ : Rat) (hξ : ξ ≠ 0)
    (v : Value) :
    Same (Value.mul (inversePhaseFactor cosine ξ) (Value.mul (phaseFactor cosine ξ) v)) v := by
  let a : Rat := if cosine then 2*ξ else -2*ξ
  have ha : a ≠ 0 := by cases cosine <;> simp only [a, Bool.false_eq_true, if_false, if_true] <;> grind only
  have h := GeometricIntegralData.pi_inverse_identity
  have he : Same (Value.mul GeometricTrig.piValue GeometricIntegralData.inversePi) (Value.rational 1) := h
  refine Same.trans (Y := Value.mul (Value.mul GeometricTrig.piValue GeometricIntegralData.inversePi) v) ?_
    ((he.mul (Same.refl v)).trans (arithmetic_identity _ _ (by intro s; simp [Value.mul, Value.rational])))
  apply arithmetic_identity
  intro s
  change (a⁻¹ * GeometricIntegralData.inversePi.sample s) * ((a * GeometricTrig.piValue.sample s) * v.sample s) =
    (GeometricTrig.piValue.sample s * GeometricIntegralData.inversePi.sample s) * v.sample s
  have := Rat.inv_mul_cancel a ha
  grind only

/-- One spatial integration by parts gives inverse-linear frequency decay. -/
theorem lineTransform_decay_of_derivative {f df : JointLipschitzSampler 1}
    (D : LineDecay f) (DD : LineDecay df)
    (S : ∀ n : Nat, Step (fun t => f.value (fun _ => t)) (fun t => df.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (cosine : Bool) (ξ : Rat) (hξ : ξ ≠ 0) (B : Rat)
    (hB : Small (lineValue DD (!cosine) ξ) B) :
    Small (lineValue D cosine ξ) (B / qabs ξ) := by
  let c := inversePhaseFactor (!cosine) ξ
  let v := lineValue D cosine ξ
  have he := lineTransform_spatialDerivative D DD S (!cosine) ξ
  have hd : (!(!cosine)) = cosine := by cases cosine <;> rfl
  rw [hd] at he
  have H := ((inversePhaseFactor_small (!cosine) ξ hξ).mul hB).neg
  rw [show 1 / qabs ξ * B = B / qabs ξ by grind only [Rat.div_def]] at H
  refine H.congr (((Same.refl c).mul he).neg.trans (Same.trans
    (Y := Value.mul c (Value.mul (phaseFactor (!cosine) ξ) v)) ?_
    (inversePhaseFactor_cancel (!cosine) ξ hξ v)))
  apply arithmetic_identity
  intro s
  simp only [Value.neg, Value.mul]
  grind only

/-- Two spatial integrations by parts give the quadratic frequency decay
needed for the inverse integral. -/
theorem lineTransform_quadraticDecay {f df ddf : JointLipschitzSampler 1}
    (D : LineDecay f) (DD : LineDecay df) (DDD : LineDecay ddf)
    (S : ∀ n : Nat, Step (fun t => f.value (fun _ => t)) (fun t => df.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (T : ∀ n : Nat, Step (fun t => df.value (fun _ => t)) (fun t => ddf.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (cosine : Bool) (ξ : Rat) (hξ : ξ ≠ 0) :
    Small (lineValue D cosine ξ) (6 * DDD.bound / (qabs ξ * qabs ξ)) := by
  have h := lineTransform_decay_of_derivative DD DDD T (!cosine) ξ hξ (6 * DDD.bound)
    (lineTransform_small DDD (fun _ => ξ) (!(!cosine)))
  have H := lineTransform_decay_of_derivative D DD S cosine ξ hξ _ h
  simpa only [Rat.div_def, Rat.inv_mul_rev, Rat.mul_assoc] using H


def differenceSampler (f g : JointLipschitzSampler 1) : JointLipschitzSampler 1 where
  value x := sub (f.value x) (g.value x)
  bound := f.bound + g.bound
  nonnegative := Rat.add_nonneg f.nonnegative g.nonnegative
  control := by
    intro x y δ hδ hxy
    have H := (f.control x y δ hδ hxy).add (g.control x y δ hδ hxy).neg
    rw [show f.bound*δ + g.bound*δ = (f.bound+g.bound)*δ by grind only] at H
    exact H.congr (arithmetic_identity _ _ (by
      intro s
      simp only [sub, Value.add, Value.neg]
      grind only))

private theorem mode_frequency_small (cosine : Bool) (ξ h t : Rat) :
    Small (sub (trigValue cosine (phase (fun _ : Fin 1 => ξ+h) (fun _ => t)))
      (trigValue cosine (phase (fun _ : Fin 1 => ξ) (fun _ => t)))) (64 * qabs h * qabs t) := by
  have H := GeometricTrig.sample_lipschitz cosine ((-2*ξ)*t) ((-2*(ξ+h))*t)
  have he : qabs ((-2*(ξ+h))*t - (-2*ξ)*t) = 2*qabs h*qabs t := by
    rw [show (-2*(ξ+h))*t - (-2*ξ)*t = (-2*h)*t by grind only, qabs_mul, qabs_mul,
      show qabs (-2 : Rat) = 2 by decide +kernel]
  rw [he] at H
  have he' : (32 : Rat)*(2*qabs h*qabs t) = 64*qabs h*qabs t := by grind only
  have hn : -(32 : Rat)*(2*qabs h*qabs t) = -(64*qabs h*qabs t) := by grind only
  rw [hn, he'] at H
  simpa only [phase, sumRat, Rat.zero_add, Small, sub, trigValue, parameter,
    Value.parameter, RealCompute.Certified.ofRaw, Rat.neg_mul] using H

private theorem moment_increment_annuli {f m : JointLipschitzSampler 1} (D : LineDecay f)
    (DM : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (cosine : Bool) (ξ h : Rat) (k n : Nat) (hkn : k ≤ n) :
    let P := fun i => sub (expandingComponent f (fun _ => ξ+h) cosine i)
      (expandingComponent f (fun _ => ξ) cosine i)
    Small (sub (P n) (P k)) (4 * (64*qabs h*DM.bound) / radius k) := by
  intro P
  let g (q : Rat) := linePhaseSampler f (fun _ => q) cosine D.bound D.nonnegative (lineDecay_all D)
  let G := differenceSampler (g (ξ+h)) (g ξ)
  let M := 64*qabs h*DM.bound
  have hM : 0 ≤ M := Rat.mul_nonneg (Rat.mul_nonneg (by decide) (qabs_nonneg h)) DM.nonnegative
  have outside (t : Rat) (ht : 1 ≤ qabs t) :
      Small (G.value (fun _ => t)) (M / (qabs t*qabs t)) := by
    have ht' : t ≠ 0 := by intro he; subst t; exact (by decide +kernel : ¬ 1 ≤ qabs (0 : Rat)) ht
    let A := trigValue cosine (phase (fun _ : Fin 1 => ξ+h) (fun _ => t))
    let B := trigValue cosine (phase (fun _ : Fin 1 => ξ) (fun _ => t))
    have hi : qabs t⁻¹ * qabs t = 1 := by
      rw [← qabs_mul, Rat.inv_mul_cancel t ht']
      decide +kernel
    have HH := scale_small (mode_frequency_small cosine ξ h t) t⁻¹
    have he : qabs t⁻¹*(64*qabs h*qabs t) = 64*qabs h := by grind only
    rw [he] at HH
    have H := ((DM.outside t ht).congr (hm t)).mul HH
    have he' : DM.bound / (qabs t*qabs t) * (64*qabs h) = M / (qabs t*qabs t) := by
      simp only [M, Rat.div_def]
      grind only
    rw [he'] at H
    apply H.congr
    apply arithmetic_identity
    intro s
    change (t*(f.value (fun _ => t)).sample s) * (t⁻¹*(A.sample s-B.sample s)) =
      (f.value (fun _ => t)).sample s * A.sample s - (f.value (fun _ => t)).sample s * B.sample s
    have := Rat.mul_inv_cancel t ht'
    grind only
  have agrees (i : Nat) :
      Same (lineData G ((expandingBox 1 i).ordered (Fin.last 0))).value (P i) := by
    let L (q : Rat) := lineData (g q) ((expandingBox 1 i).ordered (Fin.last 0))
    exact Same.trans (Y := ((L (ξ+h)).subtract (L ξ)).value)
      ((lineData G ((expandingBox 1 i).ordered (Fin.last 0))).congr ((L (ξ+h)).subtract (L ξ))
        (fun _ _ _ => Same.refl _))
      (Same.trans (Y := sub (L (ξ+h)).value (L ξ).value)
        ((L (ξ+h)).subtract_identity (L ξ))
        ((expandingComponent_line f (fun _ => ξ+h) cosine D.bound D.nonnegative
          (lineDecay_all D) i).symm.sub
          (expandingComponent_line f (fun _ => ξ) cosine D.bound D.nonnegative
            (lineDecay_all D) i).symm))
  exact annuli_of_step P M hM (fun i =>
    (intervalTail_step G M hM outside i).congr ((agrees (i+1)).sub (agrees i))) k n hkn

private theorem cancel_increment (u v uj vj uk vk : Rat) :
    ((u-uj) + -(v-vj)) + ((uj-vj)-(uk-vk)) = (u-v)-(uk-vk) := by grind only

set_option maxHeartbeats 5000000 in
/-- Taking a frequency increment before removing the spatial cutoff
gains a factor of the increment in the tail error. -/
theorem lineTransform_increment_error {f m : JointLipschitzSampler 1} (D : LineDecay f)
    (DM : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (cosine : Bool) (ξ h : Rat) (k : Nat) :
    Small (sub (sub (lineValue D cosine (ξ+h)) (lineValue D cosine ξ))
      (sub (expandingComponent f (fun _ => ξ+h) cosine k)
        (expandingComponent f (fun _ => ξ) cosine k))) (4*(64*qabs h*DM.bound)/radius k) := by
  let P := fun i => sub (expandingComponent f (fun _ => ξ+h) cosine i)
    (expandingComponent f (fun _ => ξ) cosine i)
  let A := sub (lineValue D cosine (ξ+h)) (lineValue D cosine ξ)
  apply EffectiveImproperIntegral.small_of_errors (sub A (P k)) _
    (fun n => 8*D.bound/radius (max k n))
  · intro eps
    have hs : ShrinksToZero (fun n => 8*D.bound/radius n) :=
      shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl)
    obtain ⟨N, hN⟩ := hs eps
    exact ⟨N, fun n hn => hN _ (by omega)⟩
  · intro n
    let j := max k n
    have h₁ := lineTransform_error D (fun _ => ξ+h) cosine j
    have h₂ := (lineTransform_error D (fun _ => ξ) cosine j).neg
    have h₃ := moment_increment_annuli D DM hm cosine ξ h k j (Nat.le_max_left _ _)
    have H := (h₁.add h₂).add h₃
    refine (H.congr (y := sub A (P k)) (arithmetic_identity _ _ (by
      intro s
      let u := (lineValue D cosine (ξ+h)).sample s
      let v := (lineValue D cosine ξ).sample s
      let uj := (expandingComponent f (fun _ => ξ+h) cosine j).sample s
      let vj := (expandingComponent f (fun _ => ξ) cosine j).sample s
      let uk := (expandingComponent f (fun _ => ξ+h) cosine k).sample s
      let vk := (expandingComponent f (fun _ => ξ) cosine k).sample s
      change ((u-uj) + -(v-vj)) + ((uj-vj)-(uk-vk)) = (u-v)-(uk-vk)
      exact cancel_increment u v uj vj uk vk))).mono ?_
    let B := 4*(64*qabs h*DM.bound)/radius k
    change 4*D.bound/radius j + 4*D.bound/radius j + B ≤ B + 8*D.bound/radius j
    have eq (d x b : Rat) : 4*d/x + 4*d/x + b = b + 8*d/x := by
      simp only [Rat.div_def]
      rw [← Rat.add_mul, ← Rat.add_mul, show (4 : Rat) + 4 = 8 by decide +kernel, Rat.add_comm]
    rw [eq]
    exact Rat.le_refl


private theorem cancel_frequency_remainder (a b d e c h : Rat) :
    ((a-b)+(b-h*(c*d)))+h*(c*(-(e-d))) = a-h*(c*e) := by grind only

/-- Executable radius for the whole-line Fourier derivative. -/
def lineDerivativeModulus {f m : JointLipschitzSampler 1} (D : LineDecay f) (DM : LineDecay m)
    (eps : QPos) : QPos :=
  let e := third eps
  let r := radius (lineTailStage (80*DM.bound) e)
  let A := (r - -r) * (D.bound * (7424 * r * r))
  let ρ := GeometricFTCData.radius (2*r)
  ⟨min ρ.val (e.val/(A+1)), by
    have hr : 0 ≤ r := Rat.le_of_lt (radius_pos _)
    have hA : 0 ≤ A := Rat.mul_nonneg (by grind only) (Rat.mul_nonneg D.nonnegative
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr) hr))
    have hp : 0 < e.val/(A+1) := Rat.mul_pos e.property (Rat.inv_pos.mpr (by grind only))
    rw [Rat.min_def]
    split
    · exact ρ.property
    · exact hp⟩

/-- The whole-line frequency derivative is the transform of the first
spatial moment times the phase factor. The error is relative to the increment. -/
theorem lineTransform_frequencyDerivative_spec {f m : JointLipschitzSampler 1}
    (D : LineDecay f) (DM : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (cosine : Bool) (ξ : Rat) (eps : QPos) :
    ∀ h : Rat, qabs h ≤ (lineDerivativeModulus D DM eps).val →
      Small (sub (sub (lineValue D cosine (ξ+h)) (lineValue D cosine ξ))
        (scale h (Value.mul (phaseFactor cosine 1) (lineValue DM (!cosine) ξ))))
        (eps.val * qabs h) := by
  let e := third eps
  let k := lineTailStage (80*DM.bound) e
  let r := radius k
  let A := (r - -r) * (D.bound * (7424 * r * r))
  let C := phaseFactor cosine 1
  have hA : 0 ≤ A := by
    have hr : 0 ≤ r := Rat.le_of_lt (radius_pos k)
    dsimp only [A]
    exact Rat.mul_nonneg (by grind only) (Rat.mul_nonneg D.nonnegative
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr) hr))
  let ρ := GeometricFTCData.radius (2*r)
  intro h hh
  have hρ : qabs h ≤ ρ.val := by
    change qabs h ≤ min ρ.val (e.val/(A+1)) at hh
    rw [Rat.min_def] at hh
    split at hh <;> grind only
  have hd : qabs h ≤ e.val/(A+1) := by
    change qabs h ≤ min ρ.val (e.val/(A+1)) at hh
    rw [Rat.min_def] at hh
    split at hh <;> grind only
  let F := lineData f ((expandingBox 1 k).ordered (Fin.last 0))
  let MF := lineData m ((expandingBox 1 k).ordered (Fin.last 0))
  let hf := fun t (_ : -r ≤ t) (_ : t ≤ r) => D.bounded t
  let ht := fun t (ha : -r ≤ t) (hb : t ≤ r) => qabs_le_of_neg_le_le ha hb
  let E := frequencyDerivativeData F cosine ξ D.bound r D.nonnegative
    (Rat.le_of_lt (radius_pos k)) hf ht
  let G := MF.mul (modeQuadrature (!cosine) ξ 0 MF.ordered) DM.bound 1 DM.nonnegative
    (by decide) (fun t _ _ => DM.bounded t) (fun t _ _ => lineMode_small _ ξ t)
  let hg := fun t (_ : -r ≤ t) (_ : t ≤ r) => (DM.bounded t).mul (lineMode_small (!cosine) ξ t)
  have hC : Small C 16 := by
    simpa only [qabs_eq_self_of_nonneg (by decide : (0 : Rat) ≤ 1), Rat.mul_one] using
      phaseFactor_small cosine 1
  let CG := (LipschitzQuadrature.constantData C (-r) r F.ordered).mul G 16 (DM.bound*1)
    (by decide) (Rat.mul_nonneg DM.nonnegative (by decide)) (fun _ _ _ => hC) hg
  have hE : Same E.value (Value.mul C (expandingComponent m (fun _ => ξ) (!cosine) k)) := by
    refine Same.trans (Y := CG.value) (E.congr CG ?_) ?_
    · intro t _ _
      refine Same.trans (Y := Value.mul C (Value.mul (scale t (f.value (fun _ => t))) (lineMode (!cosine) ξ t)))
        (arithmetic_identity _ _ ?_) ((Same.refl C).mul ((hm t).symm.mul (Same.refl _)))
      intro s
      cases cosine <;> simp [C, phaseFactor, scale, Value.mul, Value.rational]
    · exact (G.mul_constant_identity C _ 16 (Rat.mul_nonneg DM.nonnegative (by decide))
        (by decide) hC hg).trans ((Same.refl C).mul (intervalComponent_agrees DM (!cosine) ξ k).symm)
  have H := intervalComponent_frequencyRemainder F cosine ξ h D.bound r D.nonnegative
    (Rat.le_of_lt (radius_pos k)) hf ht
    (fun t ha hb => frequencyRadius_of_bound (Rat.le_of_lt (radius_pos k)) (ht t ha hb) hρ)
  have H' := H.congr (((intervalComponent_agrees D cosine (ξ+h) k).symm.sub
    (intervalComponent_agrees D cosine ξ k).symm).sub (hE.scale h))
  have hcut := lineTransform_increment_error D DM hm cosine ξ h k
  have hder := scale_small (hC.mul (lineTransform_error DM (fun _ => ξ) (!cosine) k).neg) h
  have Htotal := (hcut.add H').add hder
  refine (Htotal.congr (arithmetic_identity _ _ (by
    intro s
    simp only [Value.add, Value.mul, Value.neg, sub, scale]
    exact cancel_frequency_remainder _ _ _ _ _ _))).mono ?_
  have hmod : A*qabs h ≤ e.val := by
    have hh' := Rat.mul_le_mul_of_nonneg_right hd (show 0 ≤ A+1 by grind only)
    rw [Rat.div_mul_cancel (by grind only : A+1 ≠ 0)] at hh'
    have := qabs_nonneg h
    grind only
  have hb := lineTailStage_spec (80*DM.bound) e
  change 4*(80*DM.bound)/r ≤ e.val at hb
  rw [show 4*(80*DM.bound) = 320*DM.bound by grind only] at hb
  have htail := Rat.mul_le_mul_of_nonneg_right hb (qabs_nonneg h)
  have hmain := Rat.mul_le_mul_of_nonneg_right hmod (qabs_nonneg h)
  have h₁ : 4*(64*qabs h*DM.bound)/r + qabs h*(16*(4*DM.bound/r)) =
      (320*DM.bound/r)*qabs h := by simp only [Rat.div_def]; grind only
  have h₂ : (r - -r)*(D.bound*(7424*r*r*qabs h*qabs h)) =
      (A*qabs h)*qabs h := by dsimp only [A]; grind only
  change 4*(64*qabs h*DM.bound)/r + (r - -r)*(D.bound*(7424*r*r*qabs h*qabs h)) +
      qabs h*(16*(4*DM.bound/r)) ≤ eps.val*qabs h
  have h₃ : e.val*qabs h + e.val*qabs h ≤ eps.val*qabs h := by
    have := Rat.mul_le_mul_of_nonneg_right
      (show e.val+e.val ≤ eps.val by have := eps.property; change eps.val/3+eps.val/3 ≤ eps.val; grind only)
      (qabs_nonneg h)
    grind only
  grind only


theorem lineTransform_frequencyDerivative {f m : JointLipschitzSampler 1}
    (D : LineDecay f) (DM : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (cosine : Bool) (ξ : Rat) (eps : QPos) :
    ∃ δ : QPos, ∀ h : Rat, qabs h ≤ δ.val →
      Small (sub (sub (lineValue D cosine (ξ+h)) (lineValue D cosine ξ))
        (scale h (Value.mul (phaseFactor cosine 1) (lineValue DM (!cosine) ξ))))
        (eps.val * qabs h) :=
  ⟨lineDerivativeModulus D DM eps, lineTransform_frequencyDerivative_spec D DM hm cosine ξ eps⟩

private def quotientData (d : JointLipschitzSampler 1) (x R : Rat) (hx : qabs x ≤ R) :
    LipschitzQuadrature.Data (fun t => d.value (fun _ => if 0 ≤ x then x*t else x*(1-t))) 0 1 :=
  let F := lineData d (a := -R) (b := R) (by have := qabs_nonneg x; grind only)
  (F.ftcQuotient x ⟨by have := neg_qabs_le_self x; grind only, Rat.le_trans (self_le_qabs x) hx⟩
    ⟨by have := qabs_nonneg x; grind only, by have := qabs_nonneg x; grind only⟩)

/-- The normalized derivative average on the whole rational line. -/
def lineFTCQuotient (d : JointLipschitzSampler 1) (x : Rat) : Value :=
  (quotientData d x (qabs x) Rat.le_refl).value

private theorem quotientOn_agrees {d : JointLipschitzSampler 1} (x R : Rat) (hx : qabs x ≤ R) :
    Same (lineFTCQuotient d x) (quotientData d x R hx).value :=
  (quotientData d x (qabs x) Rat.le_refl).congr (quotientData d x R hx) (fun _ _ _ => Same.refl _)

private theorem quotient_bounded (d : JointLipschitzSampler 1) (M : Rat)
    (hM : ∀ t : Rat, Small (d.value (fun _ => t)) M) (x : Rat) :
    Small (lineFTCQuotient d x) M := by
  have h := (quotientData d x (qabs x) Rat.le_refl).small M (fun t (_ : (0 : Rat) ≤ t) (_ : t ≤ 1) =>
    hM (if 0 ≤ x then x*t else x*(1-t)))
  unfold lineFTCQuotient
  simpa only [show (1 : Rat)-0=1 by grind only, Rat.one_mul] using h

private theorem quotient_near_zero (d : JointLipschitzSampler 1) (x : Rat) :
    Small (sub (lineFTCQuotient d x) (d.value (fun _ => 0))) (d.bound*qabs x) := by
  unfold lineFTCQuotient quotientData
  dsimp only
  exact LipschitzQuadrature.Data.ftcQuotient_error _ _ _ _

private theorem quotient_control (d : JointLipschitzSampler 1) (x y : Rat) :
    Small (sub (lineFTCQuotient d x) (lineFTCQuotient d y)) (d.bound*qabs (x-y)) := by
  by_cases hs : (0 ≤ x ∧ 0 ≤ y) ∨ (x < 0 ∧ y < 0)
  · let F (z : Rat) := lineData d (a := -qabs z) (b := qabs z) (by have := qabs_nonneg z; grind only)
    let Q (z : Rat) := (F z).ftcQuotient z ⟨neg_qabs_le_self z,self_le_qabs z⟩
      ⟨by have := qabs_nonneg z; grind only,qabs_nonneg z⟩
    have H := (Q x).difference_small (Q y) (d.bound*qabs (x-y)) (fun t ht ht' => by
      have ht0 : (0 : Rat) ≤ 1-t := by grind only
      have ht1 : (1 : Rat)-t ≤ 1 := by grind only
      have bound (s : Rat) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
          Small (sub (d.value (fun _ => x*s)) (d.value (fun _ => y*s))) (d.bound*qabs (x-y)) := by
        apply d.control _ _ _ (qabs_nonneg _)
        intro i
        have h₁ := Rat.mul_le_mul_of_nonneg_right (self_le_qabs (x-y)) hs₀
        have h₂ := Rat.mul_le_mul_of_nonneg_right (neg_qabs_le_self (x-y)) hs₀
        have h₃ := Rat.mul_le_mul_of_nonneg_left hs₁ (qabs_nonneg (x-y))
        constructor <;> grind only
      rcases hs with hp | hn
      · simpa only [if_pos hp.1, if_pos hp.2] using bound t ht ht'
      · simpa only [if_neg (show ¬ 0 ≤ x by grind only), if_neg (show ¬ 0 ≤ y by grind only)] using
          bound (1-t) ht0 ht1)
    rw [show (1 : Rat)-0=1 by grind only, Rat.one_mul] at H
    exact H
  · have H := (quotient_near_zero d x).add (quotient_near_zero d y).neg
    have he : qabs x + qabs y = qabs (x-y) := by
      by_cases hx : 0 ≤ x
      · have hy : y ≤ 0 := by grind only
        rw [qabs_eq_self_of_nonneg hx, qabs_eq_neg_of_nonpos hy,
          qabs_eq_self_of_nonneg (show 0 ≤ x-y by grind only)]
        grind only
      · have hy : 0 ≤ y := by grind only
        rw [qabs_eq_neg_of_nonpos (show x ≤ 0 by grind only), qabs_eq_self_of_nonneg hy,
          qabs_eq_neg_of_nonpos (show x-y ≤ 0 by grind only)]
        grind only
    rw [show d.bound*qabs x + d.bound*qabs y = d.bound*qabs (x-y) by
      rw [← he]; grind only] at H
    exact H.congr (arithmetic_identity _ _ (by
      intro s
      simp only [Value.add, Value.neg, sub]
      grind only))

/-- The FTC quotient is globally Lipschitz when its integrand is. -/
def lineFTCQuotientSampler (d : JointLipschitzSampler 1) : JointLipschitzSampler 1 where
  value x := lineFTCQuotient d (x (Fin.last 0))
  bound := d.bound
  nonnegative := d.nonnegative
  control := by
    intro x y δ _ hxy
    have h := hxy (Fin.last 0)
    exact (quotient_control d _ _).mono (Rat.mul_le_mul_of_nonneg_left
      (qabs_le_of_neg_le_le (by grind only) (by grind only)) d.nonnegative)

/-- The first moment of the whole-line FTC quotient is the original
numerator. This supplies the moment agreement in Fourier differentiation. -/
theorem lineFTCQuotient_moment {w d : JointLipschitzSampler 1}
    (S : ∀ n : Nat, Step (fun t => w.value (fun _ => t)) (fun t => d.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (hz : Same (w.value (fun _ => 0)) (Value.rational 0)) (x : Rat) :
    Same (w.value (fun _ => x)) (scale x (lineFTCQuotient d x)) := by
  let n := (qabs x).num.natAbs
  let r := radius n
  have hR : qabs x ≤ r := by
    have H := qabs_le_numNatAbs_succ (qabs x)
    rwa [qabs_eq_self_of_nonneg (qabs_nonneg x)] at H
  let F := lineData d ((expandingBox 1 n).ordered (Fin.last 0))
  have h₀ : -r ≤ 0 ∧ 0 ≤ r := by have := radius_pos n; constructor <;> grind only
  have h₁ : -r ≤ x ∧ x ≤ r :=
    ⟨by have := neg_qabs_le_self x; grind only, Rat.le_trans (self_le_qabs x) hR⟩
  have H : Same (scale x (quotientData d x r hR).value)
      (sub (w.value (fun _ => x)) (w.value (fun _ => 0))) :=
    F.ftcQuotient_identity (S n) x h₁ h₀
  refine ((quotientOn_agrees (d := d) x r hR).scale x |>.trans H |>.trans ?_).symm
  refine Same.trans (Y := sub (w.value (fun _ => x)) (Value.rational 0))
    ((Same.refl _).sub hz) ?_
  apply arithmetic_identity
  intro s
  simp only [sub, Value.rational]
  grind only

/-- Dividing a quadratically decaying numerator by its argument gives
a cubic tail for the integral quotient. -/
theorem lineFTCQuotient_cubicDecay {w d : JointLipschitzSampler 1} (W : LineDecay w)
    (S : ∀ n : Nat, Step (fun t => w.value (fun _ => t)) (fun t => d.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (hz : Same (w.value (fun _ => 0)) (Value.rational 0))
    (t : Rat) (ht : 1 ≤ qabs t) :
    Small (lineFTCQuotient d t) (W.bound / (qabs t*qabs t) / qabs t) := by
  let n := (qabs t).num.natAbs
  have hR : qabs t ≤ radius n := by
    have H := qabs_le_numNatAbs_succ (qabs t)
    rw [qabs_eq_self_of_nonneg (qabs_nonneg t)] at H
    exact H
  let F := lineData d ((expandingBox 1 n).ordered (Fin.last 0))
  have h₀ : -(radius n) ≤ 0 ∧ 0 ≤ radius n := by
    have := radius_pos n
    constructor <;> grind only
  have h₁ : -(radius n) ≤ t ∧ t ≤ radius n := by
    have := neg_qabs_le_self t
    have := self_le_qabs t
    constructor <;> grind only
  have hne : t ≠ 0 := by intro he; subst t; exact (by decide +kernel : ¬ 1 ≤ qabs (0 : Rat)) ht
  have H := F.ftcQuotient_decay (S n) t h₁ h₀ hz hne _ (W.outside t ht)
  exact H.congr (quotientOn_agrees (d := d) t (radius n) hR).symm

/-- A decaying numerator which vanishes at zero gives a decaying FTC
quotient with a separate uniform bound from the derivative. -/
def lineFTCQuotientDecay {w d : JointLipschitzSampler 1} (W : LineDecay w) (D : LineDecay d)
    (S : ∀ n : Nat, Step (fun t => w.value (fun _ => t)) (fun t => d.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (hz : Same (w.value (fun _ => 0)) (Value.rational 0)) :
    LineDecay (lineFTCQuotientSampler d) where
  bound := W.bound + D.bound
  nonnegative := Rat.add_nonneg W.nonnegative D.nonnegative
  bounded t := (quotient_bounded d D.bound D.bounded t).mono (by have := W.nonnegative; grind only)
  outside := by
    intro t ht
    have H' := lineFTCQuotient_cubicDecay W S hz t ht
    refine H'.mono ?_
    have hp : 0 < qabs t := by grind only
    have hi := reciprocal_mul_mono (by decide : (0 : Rat) < 1) ht
    have hb : (qabs t)⁻¹ ≤ 1 := by
      simpa only [Rat.div_def, Rat.one_mul, show (1 : Rat)⁻¹ = 1 by decide +kernel] using hi
    have hW : 0 ≤ W.bound/(qabs t*qabs t) :=
      Rat.mul_nonneg W.nonnegative (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))
    have H₁ := Rat.mul_le_mul_of_nonneg_left hb hW
    have H₂ := Rat.mul_le_mul_of_nonneg_right (show W.bound ≤ W.bound+D.bound by have := D.nonnegative; grind only)
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))
    exact Rat.le_trans (by simpa only [Rat.div_def, Rat.mul_one] using H₁) H₂


/-- The quotient transform has an integrable frequency tail once its first
two derivatives carry spatial decay. The quotient value and its spatial
decay are computed from the original numerator and derivative. -/
theorem lineFTCQuotient_transformDecay {w d v₁ v₂ : JointLipschitzSampler 1}
    (W : LineDecay w) (D : LineDecay d)
    (S : ∀ n : Nat, Step (fun t => w.value (fun _ => t)) (fun t => d.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (hz : Same (w.value (fun _ => 0)) (Value.rational 0))
    (V₁ : LineDecay v₁) (V₂ : LineDecay v₂)
    (T₁ : ∀ n : Nat, Step (lineFTCQuotient d) (fun t => v₁.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (T₂ : ∀ n : Nat, Step (fun t => v₁.value (fun _ => t)) (fun t => v₂.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (cosine : Bool) (ξ : Rat) (hξ : ξ ≠ 0) :
    Small (lineValue (lineFTCQuotientDecay W D S hz) cosine ξ)
      (6 * V₂.bound / (qabs ξ * qabs ξ)) :=
  lineTransform_quadraticDecay (lineFTCQuotientDecay W D S hz) V₁ V₂ T₁ T₂ cosine ξ hξ

/-- Melrose's frequency differentiation step for the FTC quotient.
The Fourier transform of its numerator is the first moment transform. -/
theorem lineFTCQuotient_transformDerivative {w d : JointLipschitzSampler 1}
    (W : LineDecay w) (D : LineDecay d)
    (S : ∀ n : Nat, Step (fun t => w.value (fun _ => t)) (fun t => d.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (hz : Same (w.value (fun _ => 0)) (Value.rational 0))
    (cosine : Bool) (ξ : Rat) (eps : QPos) :
    let V := lineFTCQuotientDecay W D S hz
    ∃ δ : QPos, ∀ h : Rat, qabs h ≤ δ.val →
      Small (sub (sub (lineValue V cosine (ξ+h)) (lineValue V cosine ξ))
        (scale h (Value.mul (phaseFactor cosine 1) (lineValue W (!cosine) ξ))))
        (eps.val * qabs h) :=
  lineTransform_frequencyDerivative (lineFTCQuotientDecay W D S hz) W
    (lineFTCQuotient_moment S hz) cosine ξ eps


/-- A decaying first moment gives a uniform Lipschitz bound in frequency.
The central interval and the increment's omitted tails are estimated separately. -/
theorem lineValue_lipschitz {f m : JointLipschitzSampler 1} (D : LineDecay f)
    (DM : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (cosine : Bool) (ξ η : Rat) :
    Small (sub (lineValue D cosine ξ) (lineValue D cosine η))
      ((128*D.bound+256*DM.bound)*qabs (ξ-η)) := by
  let h := ξ-η
  have he : η+h = ξ := by dsimp only [h]; grind only
  have ht := lineTransform_increment_error D DM hm cosine η h 0
  rw [he] at ht
  let g (q : Rat) := linePhaseSampler f (fun _ => q) cosine D.bound D.nonnegative (lineDecay_all D)
  let L (q : Rat) := lineData (g q) (a := -1) (b := 1) (by decide +kernel)
  have hc := (L ξ).difference_small (L η) (D.bound*(64*qabs h)) (fun t ha hb => by
    have ht : qabs t ≤ 1 := qabs_le_of_neg_le_le ha hb
    have H := mode_frequency_small cosine η h t
    rw [he] at H
    have hcoeff : 0 ≤ 64*qabs h := Rat.mul_nonneg (by decide) (qabs_nonneg h)
    have h' := Rat.mul_le_mul_of_nonneg_left ht hcoeff
    rw [Rat.mul_one] at h'
    have H' := (D.bounded t).mul (H.mono h')
    exact H'.congr (arithmetic_identity _ _ (by
      intro s
      let u := (f.value (fun _ => t)).sample s
      let a := (trigValue cosine (phase (fun _ : Fin 1 => ξ) (fun _ => t))).sample s
      let b := (trigValue cosine (phase (fun _ : Fin 1 => η) (fun _ => t))).sample s
      change u*(a-b)=u*a-u*b
      grind only)))
  have ha (q : Rat) : Same (expandingComponent f (fun _ => q) cosine 0) (L q).value :=
    expandingComponent_line f _ cosine D.bound D.nonnegative (lineDecay_all D) 0
  have H := ht.add (hc.congr ((ha ξ).symm.sub (ha η).symm))
  refine (H.congr (arithmetic_identity _ _ (by
    intro s
    simp only [sub, Value.add]
    grind only))).mono ?_
  change 4*(64*qabs h*DM.bound)/1 + (1 - -1)*(D.bound*(64*qabs h)) ≤
    (128*D.bound+256*DM.bound)*qabs h
  grind only

/-- A Fourier component is a sampler on the frequency line if its input
and first spatial moment have integrable tails. -/
def lineTransformSampler {f m : JointLipschitzSampler 1} (D : LineDecay f) (DM : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (cosine : Bool) : JointLipschitzSampler 1 where
  value x := lineValue D cosine (x (Fin.last 0))
  bound := 128*D.bound+256*DM.bound
  nonnegative := Rat.add_nonneg (Rat.mul_nonneg (by decide) D.nonnegative)
    (Rat.mul_nonneg (by decide) DM.nonnegative)
  control := by
    intro x y δ _ hxy
    have hh := hxy (Fin.last 0)
    apply (lineValue_lipschitz D DM hm cosine _ _).mono
    exact Rat.mul_le_mul_of_nonneg_left (qabs_le_of_neg_le_le (by grind only) (by grind only))
      (Rat.add_nonneg (Rat.mul_nonneg (by decide) D.nonnegative)
        (Rat.mul_nonneg (by decide) DM.nonnegative))

/-- Two spatial derivatives give the decay certificate for the inverse
quadrature of a Fourier component. -/
def lineTransformDecay {f m df ddf : JointLipschitzSampler 1}
    (D : LineDecay f) (DM : LineDecay m) (DD : LineDecay df) (DDD : LineDecay ddf)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (S : ∀ n : Nat, Step (fun t => f.value (fun _ => t)) (fun t => df.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (T : ∀ n : Nat, Step (fun t => df.value (fun _ => t)) (fun t => ddf.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (cosine : Bool) : LineDecay (lineTransformSampler D DM hm cosine) where
  bound := 6*(D.bound+DDD.bound)
  nonnegative := Rat.mul_nonneg (by decide) (Rat.add_nonneg D.nonnegative DDD.nonnegative)
  bounded ξ := (lineTransform_small D (fun _ => ξ) cosine).mono (by
    have := DDD.nonnegative
    grind only)
  outside ξ hξ := by
    have hne : ξ ≠ 0 := by intro he; subst ξ; exact (by decide +kernel : ¬ 1 ≤ qabs (0 : Rat)) hξ
    have hp := qabs_pos_of_ne hne
    apply (lineTransform_quadraticDecay D DD DDD S T cosine ξ hne).mono
    exact Rat.mul_le_mul_of_nonneg_right (show 6*DDD.bound ≤ 6*(D.bound+DDD.bound) by
      have := D.nonnegative
      grind only) (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))


private def unitPullback (d : JointLipschitzSampler 1) (x : Rat) :
    LipschitzQuadrature.Data (fun t => d.value (fun _ => x*t)) 0 1 where
  ordered := by decide
  constant := d.bound*qabs x
  nonnegative := Rat.mul_nonneg d.nonnegative (qabs_nonneg x)
  lipschitz := by
    intro u v _ huv _
    have h := Rat.mul_nonneg (qabs_nonneg x) (show 0 ≤ v-u by grind only)
    have eq : qabs (x*v-x*u) = qabs x*(v-u) := by
      rw [show x*v-x*u=x*(v-u) by grind only, qabs_mul,
        qabs_eq_self_of_nonneg (show 0 ≤ v-u by grind only)]
    have h₁ := self_le_qabs (x*v-x*u)
    have h₂ := neg_qabs_le_self (x*v-x*u)
    rw [eq] at h₁ h₂
    have H := d.control (fun _ => x*v) (fun _ => x*u) (qabs x*(v-u)) h
      (fun _ => ⟨by grind only, by grind only⟩)
    simpa only [Rat.mul_assoc] using H

private def weightedQuotientData (d : JointLipschitzSampler 1) (M : Rat) (hM : 0 ≤ M)
    (hd : ∀ t : Rat, Small (d.value (fun _ => t)) M) (j : Nat) (x : Rat) :
    LipschitzQuadrature.Data (fun t => Value.mul (Value.rational (t^j)) (d.value (fun _ => x*t))) 0 1 :=
  (LipschitzQuadrature.unitPowerData j).mul (unitPullback d x) 1 M (by decide) hM
    (fun t ht ht' => LipschitzQuadrature.unitPower_small j t ht ht') (fun t _ _ => hd (x*t))

/-- The weighted derivative integral in the FTC formula for divided differences. -/
def weightedQuotient (d : JointLipschitzSampler 1) (M : Rat) (hM : 0 ≤ M)
    (hd : ∀ t : Rat, Small (d.value (fun _ => t)) M) (j : Nat) (x : Rat) : Value :=
  (weightedQuotientData d M hM hd j x).value

theorem weightedQuotient_zero_weight (d : JointLipschitzSampler 1) (M : Rat) (hM : 0 ≤ M)
    (hd : ∀ t : Rat, Small (d.value (fun _ => t)) M) (x : Rat) :
    Same (weightedQuotient d M hM hd 0 x) (lineFTCQuotient d x) := by
  let F := unitPullback d x
  have H : Same (weightedQuotient d M hM hd 0 x) F.value :=
    (weightedQuotientData d M hM hd 0 x).congr F (fun _ _ _ =>
      arithmetic_identity _ _ (by intro s; simp [Value.mul, Value.rational, Rat.pow_zero]))
  refine H.trans (Same.symm (X := lineFTCQuotient d x) (Y := F.value) ?_)
  let G := quotientData d x (qabs x) Rat.le_refl
  change Same G.value F.value
  by_cases hx : 0 ≤ x
  · exact G.congr F (fun t _ _ => by rw [if_pos hx]; exact Same.refl _)
  · let E : LipschitzQuadrature.Data (fun t => d.value (fun _ => x*(1-t))) 0 1 := {
      ordered := by decide
      constant := G.constant
      nonnegative := G.nonnegative
      lipschitz := by
        intro u v hu huv hv
        have h := G.lipschitz u v hu huv hv
        simpa only [if_neg hx] using h }
    exact Same.trans (Y := E.value) (G.congr E (fun t _ _ => by rw [if_neg hx]; exact Same.refl _))
      (F.reflect_unit E)

private theorem weightedQuotient_lipschitz (d : JointLipschitzSampler 1) (M : Rat) (hM : 0 ≤ M)
    (hd : ∀ t : Rat, Small (d.value (fun _ => t)) M) (j : Nat) (x y : Rat) :
    Small (sub (weightedQuotient d M hM hd j y) (weightedQuotient d M hM hd j x))
      (d.bound*qabs (y-x)) := by
  have H := (weightedQuotientData d M hM hd j y).difference_small
    (weightedQuotientData d M hM hd j x) (d.bound*qabs (y-x)) (fun t ht ht' => by
      have h₁ := Rat.mul_le_mul_of_nonneg_right (self_le_qabs (y-x)) ht
      have h₂ := Rat.mul_le_mul_of_nonneg_right (neg_qabs_le_self (y-x)) ht
      have h₃ := Rat.mul_le_mul_of_nonneg_left ht' (qabs_nonneg (y-x))
      have H := d.control (fun _ => y*t) (fun _ => x*t) (qabs (y-x)) (qabs_nonneg _)
        (fun _ => ⟨by grind only, by grind only⟩)
      have K := (LipschitzQuadrature.unitPower_small j t ht ht').mul H
      rw [Rat.one_mul] at K
      exact K.congr (arithmetic_identity _ _ (by
        intro s
        simp only [Value.mul, sub]
        grind only)))
  simpa only [weightedQuotient, show (1 : Rat)-0=1 by grind only, Rat.one_mul] using H

/-- Differentiation of the weighted quotient under its unit-interval
integral. Each derivative gains a power of the integration parameter. -/
def weightedQuotient_step {d e : JointLipschitzSampler 1} {a b : Rat}
    (S : Step (fun t => d.value (fun _ => t)) (fun t => e.value (fun _ => t)) a b)
    (h0 : a ≤ 0 ∧ 0 ≤ b) (M N : Rat) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hd : ∀ t : Rat, Small (d.value (fun _ => t)) M)
    (he : ∀ t : Rat, Small (e.value (fun _ => t)) N) (j : Nat) :
    Step (weightedQuotient d M hM hd j) (weightedQuotient e N hN he (j+1)) a b where
  error := S.error
  error_nonnegative := S.error_nonnegative
  radius := S.radius
  firstOrder := by
    intro u v hu huv hv hs
    let A := weightedQuotientData d M hM hd j v
    let B := weightedQuotientData d M hM hd j u
    let C := weightedQuotientData e N hN he (j+1) u
    let E := S.error*(v-u)*(v-u)
    have H := (A.subtract B).difference_small (C.scale (v-u)) E (fun t ht ht' => by
      have interval (x : Rat) (hx : a ≤ x) (hx' : x ≤ b) : a ≤ x*t ∧ x*t ≤ b := by
        have hl := Rat.mul_le_mul_of_nonneg_right hx ht
        have hr := Rat.mul_le_mul_of_nonneg_right hx' ht
        have ha := Rat.mul_le_mul_of_nonneg_left ht' (show 0 ≤ -a by grind only)
        have hb := Rat.mul_le_mul_of_nonneg_left ht' h0.2
        constructor <;> grind only
      have hu' := interval u hu (by grind only)
      have hv' := interval v (by grind only) hv
      have hgap : 0 < v-u := by grind only
      by_cases ht0 : t = 0
      · subst t
        have hz := rational_small 0
        rw [show qabs (0 : Rat) = 0 by decide +kernel] at hz
        apply (hz.mono (show 0 ≤ E from Rat.mul_nonneg
          (Rat.mul_nonneg S.error_nonnegative (Rat.le_of_lt hgap)) (Rat.le_of_lt hgap))).congr
        apply arithmetic_identity
        intro s
        simp only [Value.mul, Value.rational, sub, scale, Rat.pow_succ, Rat.mul_zero,
          Rat.zero_mul, Rat.sub_self]
      · have htpos : 0 < t := by grind only
        have hp := Rat.mul_pos hgap htpos
        have hb := Rat.mul_le_mul_of_nonneg_left ht' (Rat.le_of_lt hgap)
        have H := S.firstOrder (u*t) (v*t) hu'.1 (by grind only) hv'.2 (by grind only)
        have h₁ := Rat.mul_le_mul_of_nonneg_left (show v*t-u*t ≤ v-u by grind only) S.error_nonnegative
        have h₂ := Rat.mul_le_mul_of_nonneg_right h₁ (show 0 ≤ v*t-u*t by grind only)
        have h₃ := Rat.mul_le_mul_of_nonneg_left (show v*t-u*t ≤ v-u by grind only)
          (Rat.mul_nonneg S.error_nonnegative (Rat.le_of_lt hgap))
        have H' := (LipschitzQuadrature.unitPower_small j t ht ht').mul (H.mono (Rat.le_trans h₂ h₃))
        rw [Rat.one_mul] at H'
        exact H'.congr (arithmetic_identity _ _ (by
          intro s
          simp only [Value.mul, Value.rational, sub, scale, Rat.pow_succ]
          grind only)))
    rw [show (1 : Rat)-0=1 by grind only, Rat.one_mul] at H
    have hsub : Same (A.subtract B).value (sub A.value B.value) := A.subtract_identity B
    have hscale : Same (C.scale (v-u)).value (scale (v-u) C.value) := C.scale_identity _
    exact H.congr (hsub.sub hscale)
  variation := e.bound
  variation_nonnegative := e.nonnegative
  lipschitz := by
    intro u v _ huv _
    have H := weightedQuotient_lipschitz e N hN he (j+1) u v
    rwa [qabs_eq_self_of_nonneg (by grind only)] at H


/-- The integral of the Fourier transform of the Gaussian-subtracted
numerator vanishes. This is the boundary cancellation in Melrose's proof. -/
theorem lineFTCQuotient_fourierIntegral_zero {w d v₁ v₂ mw dw ddw : JointLipschitzSampler 1}
    (W : LineDecay w) (D : LineDecay d)
    (S : ∀ n : Nat, Step (fun t => w.value (fun _ => t)) (fun t => d.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (hz : Same (w.value (fun _ => 0)) (Value.rational 0))
    (V₁ : LineDecay v₁) (V₂ : LineDecay v₂)
    (T₁ : ∀ n : Nat, Step (lineFTCQuotient d) (fun t => v₁.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (T₂ : ∀ n : Nat, Step (fun t => v₁.value (fun _ => t)) (fun t => v₂.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (MW : LineDecay mw) (DW : LineDecay dw) (DDW : LineDecay ddw)
    (hm : ∀ t : Rat, Same (mw.value (fun _ => t)) (scale t (w.value (fun _ => t))))
    (U₁ : ∀ n : Nat, Step (fun t => w.value (fun _ => t)) (fun t => dw.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (U₂ : ∀ n : Nat, Step (fun t => dw.value (fun _ => t)) (fun t => ddw.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (cosine : Bool) :
    Same (lineValue (lineTransformDecay W MW DW DDW hm U₁ U₂ (!cosine)) true 0)
      (Value.rational 0) := by
  let V := lineFTCQuotientDecay W D S hz
  let c := phaseFactor cosine 1
  let cInv := inversePhaseFactor cosine 1
  let H := lineTransformDecay W MW DW DDW hm U₁ U₂ (!cosine)
  let F := lineTransformSampler W MW hm (!cosine)
  let primitive (ξ : Rat) := lineValue V cosine ξ
  let I := lineTransformData H (fun _ => 0) true
  have hb : Small c 16 := by
    simpa only [qabs_eq_self_of_nonneg (by decide : (0 : Rat) ≤ 1), Rat.mul_one] using phaseFactor_small cosine 1
  have hInv : Small cInv 1 := by
    have h := inversePhaseFactor_small cosine 1 (by decide)
    simpa only [qabs_eq_self_of_nonneg (by decide : (0 : Rat) ≤ 1), show (1 : Rat)/1 = 1 by decide +kernel] using h
  have compact (n : Nat) : Same (I.compact n)
      (sub (Value.mul cInv (primitive (radius n))) (Value.mul cInv (primitive (-radius n)))) := by
    let r := radius n
    let Q := lineData F ((expandingBox 1 n).ordered (Fin.last 0))
    have hzmode (t : Rat) : Same (lineMode true 0 t) (Value.rational 1) := by
      have he : (-2 * (0 : Rat)) * t = 0 := by grind only
      change (GeometricTrig.valueFor true ((-2 * (0 : Rat))*t)).real.preferred.Equiv (RealCompute.ofRat 1)
      rw [he, GeometricTrig.valueFor_raw]
      exact GeometricTrig.sample_zero true
    have hq : Same (I.compact n) Q.value := by
      refine (lineCompactComponent_agrees H (fun _ => 0) true n).symm.trans
        ((intervalComponent_agrees H true 0 n).trans ?_)
      unfold intervalComponent
      refine LipschitzQuadrature.Data.congr _ Q ?_
      intro t _ _
      exact ((Same.refl _).mul (hzmode t)).trans
        (arithmetic_identity _ _ (by intro s; simp [F, Value.mul, Value.rational]))
    let C := (LipschitzQuadrature.constantData c (-r) r Q.ordered).mul Q 16 H.bound (by decide)
      H.nonnegative (fun _ _ _ => hb) (fun t _ _ => H.bounded t)
    have hf : Same C.value (sub (primitive r) (primitive (-r))) := by
      apply C.ftc_of_uniform_remainder
      intro eps
      refine ⟨lineDerivativeModulus V W eps, ?_⟩
      intro u v _ huv _ hs
      have he : u+(v-u)=v := by grind only
      have ha := qabs_eq_self_of_nonneg (show 0 ≤ v-u by grind only)
      have hh := lineTransform_frequencyDerivative_spec V W (lineFTCQuotient_moment S hz)
        cosine u eps (v-u) (by rwa [ha])
      rwa [he, ha] at hh
    have hc := Q.mul_constant_identity c H.bound 16 H.nonnegative (by decide) hb
      (fun t _ _ => H.bounded t)
    have h := (inversePhaseFactor_cancel cosine 1 (by decide) Q.value).symm.trans
      ((Same.refl cInv).mul (hc.symm.trans hf))
    exact hq.trans (h.trans (arithmetic_identity _ _ (by
      intro s
      simp only [Value.mul, sub]
      grind only)))
  have htail (neg : Bool) (n : Nat) :
      Small (Value.mul cInv (primitive (if neg then -radius n else radius n))) (6*V₂.bound/radius n) := by
    let r := radius n
    have hr : 0 < r := radius_pos n
    have hr' : 1 ≤ r := by
      change (1 : Rat) ≤ ((n+1 : Nat) : Rat)
      exact_mod_cast (show 1 ≤ n+1 by omega)
    let t := if neg then -r else r
    have ht : t ≠ 0 := by dsimp only [t]; split <;> grind only
    have hq : qabs t = r := by
      dsimp only [t]
      split
      · rw [qabs_neg, qabs_eq_self_of_nonneg (Rat.le_of_lt hr)]
      · exact qabs_eq_self_of_nonneg (Rat.le_of_lt hr)
    have hh := hInv.mul (lineFTCQuotient_transformDecay W D S hz V₁ V₂ T₁ T₂ cosine t ht)
    rw [Rat.one_mul, hq] at hh
    have hsq : r ≤ r*r := by
      have h := Rat.mul_le_mul_of_nonneg_left hr' (Rat.le_of_lt hr)
      grind only
    apply hh.mono
    have hi := reciprocal_mul_mono hr hsq
    have hp := Rat.mul_le_mul_of_nonneg_left hi
      (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 6) V₂.nonnegative)
    simpa only [Rat.div_def, Rat.one_mul] using hp
  exact I.integral_eq_zero_of_decaying_boundary
    (fun n => Value.mul cInv (primitive (-radius n))) (fun n => Value.mul cInv (primitive (radius n)))
    (fun n => 6*V₂.bound/radius n) (shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl))
    (htail true) (htail false) compact


/-- The first two derivatives of the FTC quotient are constructed from the
second and third derivatives of the numerator. Both formulas include zero. -/
def lineFTCQuotient_derivativeSteps {d e g : JointLipschitzSampler 1} {a b : Rat}
    (S : Step (fun t => d.value (fun _ => t)) (fun t => e.value (fun _ => t)) a b)
    (T : Step (fun t => e.value (fun _ => t)) (fun t => g.value (fun _ => t)) a b)
    (h0 : a ≤ 0 ∧ 0 ≤ b) (D : LineDecay d) (E : LineDecay e) (G : LineDecay g) :
    Step (lineFTCQuotient d)
        (weightedQuotient e E.bound E.nonnegative E.bounded 1) a b ×
      Step (weightedQuotient e E.bound E.nonnegative E.bounded 1)
        (weightedQuotient g G.bound G.nonnegative G.bounded 2) a b := by
  refine ⟨?_, weightedQuotient_step T h0 E.bound G.bound E.nonnegative G.nonnegative E.bounded G.bounded 1⟩
  exact (weightedQuotient_step S h0 D.bound E.bound D.nonnegative E.nonnegative D.bounded E.bounded 0).congr
    (weightedQuotient_zero_weight d D.bound D.nonnegative D.bounded) (fun _ => Same.refl _)


private def unitPullback_step {d e : JointLipschitzSampler 1} {a b : Rat}
    (S : Step (fun t => d.value (fun _ => t)) (fun t => e.value (fun _ => t)) a b)
    (x : Rat) (h0 : a ≤ 0 ∧ 0 ≤ b) (hx : a ≤ x ∧ x ≤ b) :
    Step (fun t => d.value (fun _ => x*t)) (fun t => scale x (e.value (fun _ => x*t))) 0 1 where
  error := (S.error+e.bound)*qabs x*qabs x
  error_nonnegative := Rat.mul_nonneg (Rat.mul_nonneg (Rat.add_nonneg S.error_nonnegative e.nonnegative) (qabs_nonneg _)) (qabs_nonneg _)
  radius := ⟨S.radius.val/(qabs x+1), Rat.mul_pos S.radius.property
    (Rat.inv_pos.mpr (by have := qabs_nonneg x; grind only))⟩
  firstOrder := by
    intro u v hu huv hv hs
    have hg : 0 < v-u := by grind only
    have hδ : qabs x*(v-u) ≤ S.radius.val := by
      have hp : 0 < qabs x+1 := by have := qabs_nonneg x; grind only
      have H := Rat.mul_le_mul_of_nonneg_right hs (Rat.le_of_lt hp)
      change (v-u)*(qabs x+1) ≤ (S.radius.val/(qabs x+1))*(qabs x+1) at H
      rw [Rat.div_mul_cancel (Rat.ne_of_gt hp)] at H
      grind only
    have inside (t : Rat) (ht : 0 ≤ t) (ht' : t ≤ 1) :
        a ≤ x*t ∧ x*t ≤ b := by
      have hl := Rat.mul_le_mul_of_nonneg_right hx.1 ht
      have hr := Rat.mul_le_mul_of_nonneg_right hx.2 ht
      have ha := Rat.mul_le_mul_of_nonneg_left ht' (show 0 ≤ -a by grind only)
      have hb := Rat.mul_le_mul_of_nonneg_left ht' h0.2
      constructor <;> grind only
    have hu' := inside u hu (by grind only)
    have hv' := inside v (by grind only) hv
    by_cases h : 0 < x
    · have hm := Rat.mul_pos h hg
      have eq : x*v-x*u=x*(v-u) := by grind only
      have H := S.firstOrder (x*u) (x*v) hu'.1 (by grind only) hv'.2 (by
        rwa [eq, ← qabs_eq_self_of_nonneg (Rat.le_of_lt h)] )
      rw [eq] at H
      rw [qabs_eq_self_of_nonneg (Rat.le_of_lt h)]
      have hb : S.error*(x*(v-u))*(x*(v-u)) = S.error*x*x*(v-u)*(v-u) := by grind only
      rw [hb] at H
      have hxx := Rat.mul_nonneg (Rat.mul_nonneg (Rat.le_of_lt h) (Rat.le_of_lt h)) (Rat.le_of_lt hg)
      have hxx' := Rat.mul_nonneg hxx (Rat.le_of_lt hg)
      have hE := Rat.mul_nonneg e.nonnegative hxx'
      exact (H.mono (by grind only)).congr
        (arithmetic_identity _ _ (by intro s; simp only [scale, sub]; grind only))
    · by_cases hz : x = 0
      · subst x
        have H := rational_small 0
        rw [show qabs (0 : Rat) = 0 by decide +kernel] at H ⊢
        simp only [Rat.zero_mul, Rat.mul_zero]
        exact H.congr (arithmetic_identity _ _ (by intro s; simp [scale, sub, Value.rational, Rat.sub_self]))
      · have hn : 0 < -x := by grind only
        have hm := Rat.mul_pos hn hg
        have eq : x*u-x*v=(-x)*(v-u) := by grind only
        have ha := qabs_eq_neg_of_nonpos (show x ≤ 0 by grind only)
        have H := (S.firstOrder (x*v) (x*u) hv'.1 (by grind only) hu'.2 (by
          rw [eq, ← ha]; exact hδ)).neg
        have K := scale_small ((unitPullback e x).lipschitz u v hu (Rat.le_of_lt huv) hv) (x*(v-u))
        have hxabs : qabs (x*(v-u)) = qabs x*(v-u) := by
          rw [qabs_mul, qabs_eq_self_of_nonneg (Rat.le_of_lt hg)]
        rw [eq] at H
        simp only [unitPullback] at K
        rw [hxabs] at K
        have H' := H.add K
        rw [ha] at H' ⊢
        have he : S.error*((-x)*(v-u))*((-x)*(v-u)) +
            (-x)*(v-u)*(e.bound*(-x)*(v-u)) =
            (S.error+e.bound)*(-x)*(-x)*(v-u)*(v-u) := by grind only
        rw [he] at H'
        exact H'.congr (arithmetic_identity _ _ (by
          intro s
          simp only [Value.add, Value.neg, scale, sub]
          grind only))
  variation := qabs x*(e.bound*qabs x)
  variation_nonnegative := Rat.mul_nonneg (qabs_nonneg _) (Rat.mul_nonneg e.nonnegative (qabs_nonneg _))
  lipschitz := by
    intro u v hu huv hv
    have H := scale_small ((unitPullback e x).lipschitz u v hu huv hv) x
    have he : qabs x*(e.bound*qabs x*(v-u)) = qabs x*(e.bound*qabs x)*(v-u) := by grind only
    simp only [unitPullback] at H
    rw [he] at H
    exact H.congr (arithmetic_identity _ _ (by intro s; simp only [sub, scale]; grind only))


/-- Integration by parts in the unit parameter gives the tail recurrence
for the derivatives of the quotient. -/
theorem weightedQuotient_tail_identity {d e : JointLipschitzSampler 1} {a b : Rat}
    (S : Step (fun t => d.value (fun _ => t)) (fun t => e.value (fun _ => t)) a b)
    (x : Rat) (h0 : a ≤ 0 ∧ 0 ≤ b) (hx : a ≤ x ∧ x ≤ b)
    (M N : Rat) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hd : ∀ t : Rat, Small (d.value (fun _ => t)) M)
    (he : ∀ t : Rat, Small (e.value (fun _ => t)) N) (j : Nat) :
    Same (scale x (weightedQuotient e N hN he (j+1) x))
      (sub (d.value (fun _ => x)) (scale ((j+1 : Nat) : Rat) (weightedQuotient d M hM hd j x))) := by
  let c : Rat := ((j+1 : Nat) : Rat)
  let U := unitPullback_step S x h0 hx
  let P := weightedQuotientData d M hM hd j x
  let Q := weightedQuotientData e N hN he (j+1) x
  let poly := fun t : Rat => Value.rational (t^(j+1))
  let dpoly := fun t : Rat => scale c (Value.rational (t^j))
  have hne : c ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr (Nat.succ_pos j))
  let T : Step poly dpoly 0 1 :=
    ((FTCMonomials.normalized j).scale c).congr (fun t => by
      apply arithmetic_identity
      intro s
      simp only [poly, scale, Value.rational]
      have H := Rat.mul_inv_cancel c hne
      change c * (t^(j+1)/c) = t^(j+1)
      grind only [Rat.div_def]) (fun _ => Same.refl _)
  let productStep := T.mul U 1 M (qabs c) (qabs x*N)
    (by decide) hM (qabs_nonneg _) (Rat.mul_nonneg (qabs_nonneg _) hN)
    (fun t ht ht' => LipschitzQuadrature.unitPower_small (j+1) t ht ht') (fun t _ _ => hd (x*t))
    (fun t ht ht' => by
      simpa only [dpoly, Rat.mul_one] using scale_small (LipschitzQuadrature.unitPower_small j t ht ht') c)
    (fun t _ _ => scale_small (he (x*t)) x)
  let I := (P.scale c).add (Q.scale x)
  have HI : Same I.value (sub (Value.mul (poly 1) (d.value (fun _ => x*1)))
      (Value.mul (poly 0) (d.value (fun _ => x*0)))) := by
    apply productStep.ftc
    exact I.hasIntegral.congrFunction ⟨rfl, rfl, fun t _ _ => by
      change Same (Value.add (scale c (Value.mul (Value.rational (t^j)) (d.value (fun _ => x*t))))
        (scale x (Value.mul (Value.rational (t^(j+1))) (e.value (fun _ => x*t)))))
        (Value.add (Value.mul (dpoly t) (d.value (fun _ => x*t)))
          (Value.mul (poly t) (scale x (e.value (fun _ => x*t)))))
      apply arithmetic_identity
      intro s
      simp only [poly, dpoly, Value.rational, Value.mul, Value.add, scale]
      grind only⟩
  have onePow (n : Nat) : (1 : Rat)^n = 1 := by
    induction n with
    | zero => exact Rat.pow_zero 1
    | succ n ih => rw [Rat.pow_succ, ih, Rat.mul_one]
  have h₁ := onePow (j+1)
  have h₀ : (0 : Rat)^(j+1) = 0 := by rw [Rat.pow_succ, Rat.mul_zero]
  have hP : Same (P.scale c).value (scale c P.value) := P.scale_identity c
  have hQ : Same (Q.scale x).value (scale x Q.value) := Q.scale_identity x
  have hI : Same I.value (Value.add (P.scale c).value (Q.scale x).value) :=
    (P.scale c).add_identity (Q.scale x)
  have H : Same (Value.add (scale c P.value) (scale x Q.value)) (d.value (fun _ => x)) :=
    Same.trans (Y := I.value)
      (Same.trans (Y := Value.add (P.scale c).value (Q.scale x).value)
        ((hP.add hQ).symm) hI.symm)
      (HI.trans (arithmetic_identity _ _ (by
        intro s
        simp only [poly, Value.mul, Value.rational, sub, h₁, h₀, Rat.mul_one, Rat.mul_zero, Rat.one_mul,
          Rat.zero_mul]
        grind only)))
  have K := H.sub (Same.refl (scale c P.value))
  exact Same.trans (Y := sub (Value.add (scale c P.value) (scale x Q.value)) (scale c P.value))
    (arithmetic_identity _ _ (by
      intro s
      let u := (scale x Q.value).sample s
      let v := (scale c P.value).sample s
      change u = (v+u)-v
      grind only)) K


/-- A weighted quotient is a globally Lipschitz sampler. -/
def weightedQuotientSampler {d : JointLipschitzSampler 1} (D : LineDecay d) (j : Nat) :
    JointLipschitzSampler 1 where
  value x := weightedQuotient d D.bound D.nonnegative D.bounded j (x (Fin.last 0))
  bound := d.bound
  nonnegative := d.nonnegative
  control := by
    intro x y δ _ hxy
    have h := hxy (Fin.last 0)
    apply (weightedQuotient_lipschitz d D.bound D.nonnegative D.bounded j _ _).mono
    exact Rat.mul_le_mul_of_nonneg_left (qabs_le_of_neg_le_le (by grind only) (by grind only))
      d.nonnegative

private theorem weightedQuotient_bounded {d : JointLipschitzSampler 1} (D : LineDecay d)
    (j : Nat) (x : Rat) : Small (weightedQuotient d D.bound D.nonnegative D.bounded j x) D.bound := by
  unfold weightedQuotient
  have H := (weightedQuotientData d D.bound D.nonnegative D.bounded j x).small D.bound
    (fun t ht ht' => by
      simpa only [Rat.one_mul] using (LipschitzQuadrature.unitPower_small j t ht ht').mul (D.bounded (x*t)))
  simpa only [show (1 : Rat)-0=1 by grind only, Rat.one_mul] using H

private def weightedQuotient_decay_step {d e : JointLipschitzSampler 1}
    (D : LineDecay d) (E : LineDecay e) (j : Nat)
    (P : LineDecay (weightedQuotientSampler D j))
    (S : ∀ n : Nat, Step (fun t => d.value (fun _ => t)) (fun t => e.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat)) :
    LineDecay (weightedQuotientSampler E (j+1)) where
  bound := D.bound + ((j+1 : Nat) : Rat)*P.bound + E.bound
  nonnegative := Rat.add_nonneg
    (Rat.add_nonneg D.nonnegative (Rat.mul_nonneg Rat.natCast_nonneg P.nonnegative)) E.nonnegative
  bounded t := (weightedQuotient_bounded E (j+1) t).mono (by
    have := D.nonnegative
    have := Rat.mul_nonneg (show (0 : Rat) ≤ ((j+1 : Nat) : Rat) from Rat.natCast_nonneg) P.nonnegative
    grind only)
  outside := by
    intro t ht
    let n := (qabs t).num.natAbs
    let r := radius n
    have hR : qabs t ≤ r := by
      have H := qabs_le_numNatAbs_succ (qabs t)
      rwa [qabs_eq_self_of_nonneg (qabs_nonneg t)] at H
    have hr : 0 < r := radius_pos n
    have h₁ : -r ≤ t ∧ t ≤ r :=
      ⟨by have := neg_qabs_le_self t; grind only, Rat.le_trans (self_le_qabs t) hR⟩
    let c : Rat := ((j+1 : Nat) : Rat)
    let U := weightedQuotient d D.bound D.nonnegative D.bounded j t
    let V := weightedQuotient e E.bound E.nonnegative E.bounded (j+1) t
    have he : Same (scale t V) (sub (d.value (fun _ => t)) (scale c U)) :=
      weightedQuotient_tail_identity (S n) t ⟨by grind only, Rat.le_of_lt hr⟩ h₁
        D.bound E.bound D.nonnegative E.nonnegative D.bounded E.bounded j
    have hu : Small U (P.bound/(qabs t*qabs t)) := P.outside t ht
    have H := (D.outside t ht).add (scale_small hu c).neg
    have hcv : 0 ≤ c := Rat.natCast_nonneg
    rw [qabs_eq_self_of_nonneg hcv] at H
    have H' : Small (scale t V) (D.bound/(qabs t*qabs t)+c*(P.bound/(qabs t*qabs t))) :=
      H.congr (Same.trans (Y := sub (d.value (fun _ => t)) (scale c U))
        (arithmetic_identity _ _ (by intro s; simp only [Value.add, Value.neg, sub]; grind only)) he.symm)
    have hne : t ≠ 0 := by intro h; subst t; exact (by decide +kernel : ¬ 1 ≤ qabs (0 : Rat)) ht
    have hi : qabs t⁻¹ * qabs t = 1 := by
      rw [← qabs_mul, Rat.inv_mul_cancel t hne]
      decide +kernel
    have hinv : qabs t⁻¹ ≤ 1 := by
      have hm := Rat.mul_le_mul_of_nonneg_left ht (qabs_nonneg t⁻¹)
      rw [hi, Rat.mul_one] at hm
      exact hm
    have hp := qabs_pos_of_ne hne
    have hden : 0 ≤ (qabs t*qabs t)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
    have hP := Rat.mul_nonneg P.nonnegative hden
    have hD := Rat.mul_nonneg D.nonnegative hden
    have hE := Rat.mul_nonneg E.nonnegative hden
    have hsum : 0 ≤ D.bound/(qabs t*qabs t)+c*(P.bound/(qabs t*qabs t)) :=
      Rat.add_nonneg hD (Rat.mul_nonneg hcv hP)
    have HH := scale_small H' t⁻¹
    have HH' := HH.congr (y := V) (arithmetic_identity _ _ (by
      intro s
      simp only [scale]
      rw [← Rat.mul_assoc, Rat.inv_mul_cancel t hne, Rat.one_mul]))
    apply HH'.mono
    have hb := Rat.mul_le_mul_of_nonneg_right hinv hsum
    rw [Rat.one_mul] at hb
    refine Rat.le_trans hb ?_
    simp only [Rat.div_def]
    grind only

/-- Construct both decay certificates for the derivatives of the quotient
from the decaying numerator and its first three derivatives. -/
def lineFTCQuotient_derivativeDecay {w d e g : JointLipschitzSampler 1}
    (W : LineDecay w) (D : LineDecay d) (E : LineDecay e) (G : LineDecay g)
    (S : ∀ n : Nat, Step (fun t => w.value (fun _ => t)) (fun t => d.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (T : ∀ n : Nat, Step (fun t => d.value (fun _ => t)) (fun t => e.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (U : ∀ n : Nat, Step (fun t => e.value (fun _ => t)) (fun t => g.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (hz : Same (w.value (fun _ => 0)) (Value.rational 0)) :
    LineDecay (weightedQuotientSampler E 1) × LineDecay (weightedQuotientSampler G 2) := by
  let V := lineFTCQuotientDecay W D S hz
  let V₀ : LineDecay (weightedQuotientSampler D 0) := {
    bound := V.bound
    nonnegative := V.nonnegative
    bounded := fun t => (V.bounded t).congr (weightedQuotient_zero_weight d D.bound D.nonnegative D.bounded t).symm
    outside := fun t ht => (V.outside t ht).congr (weightedQuotient_zero_weight d D.bound D.nonnegative D.bounded t).symm }
  let V₁ := weightedQuotient_decay_step D E 0 V₀ T
  exact ⟨V₁, weightedQuotient_decay_step E G 1 V₁ U⟩


/-- Subtraction preserves the spatial decay required for whole-line quadrature. -/
def LineDecay.subtract {f g : JointLipschitzSampler 1} (F : LineDecay f) (G : LineDecay g) :
    LineDecay (differenceSampler f g) where
  bound := F.bound+G.bound
  nonnegative := Rat.add_nonneg F.nonnegative G.nonnegative
  bounded t := ((F.bounded t).add (G.bounded t).neg).congr
    (arithmetic_identity _ _ (by intro s; simp only [differenceSampler, sub, Value.add, Value.neg]; grind only))
  outside t ht := by
    have H := (F.outside t ht).add (G.outside t ht).neg
    have eq : F.bound/(qabs t*qabs t) + G.bound/(qabs t*qabs t) =
        (F.bound+G.bound)/(qabs t*qabs t) := by simp only [Rat.div_def]; grind only
    rw [eq] at H
    exact H.congr (arithmetic_identity _ _ (by intro s; simp only [differenceSampler, sub, Value.add, Value.neg]; grind only))

private def constantMultiple (c : Value) (C : Rat) (hC : 0 ≤ C) (hc : Small c C)
    (f : JointLipschitzSampler 1) : JointLipschitzSampler 1 where
  value x := Value.mul c (f.value x)
  bound := C*f.bound
  nonnegative := Rat.mul_nonneg hC f.nonnegative
  control := by
    intro x y δ hδ hxy
    have H := hc.mul (f.control x y δ hδ hxy)
    rw [← Rat.mul_assoc] at H
    exact H.congr (arithmetic_identity _ _ (by intro s; simp only [sub, Value.mul]; grind only))

/-- Multiplication by a represented scalar preserves spatial decay. -/
def LineDecay.mulConstant {f : JointLipschitzSampler 1} (F : LineDecay f)
    (c : Value) (C : Rat) (hC : 0 ≤ C) (hc : Small c C) :
    LineDecay (constantMultiple c C hC hc f) where
  bound := C*F.bound
  nonnegative := Rat.mul_nonneg hC F.nonnegative
  bounded t := hc.mul (F.bounded t)
  outside t ht := by
    have H := hc.mul (F.outside t ht)
    change Small (Value.mul c (f.value (fun _ => t))) (C*F.bound/(qabs t*qabs t))
    simpa only [Rat.div_def, Rat.mul_assoc] using H


private theorem lineValue_subtract {f g : JointLipschitzSampler 1}
    (F : LineDecay f) (G : LineDecay g) (cosine : Bool) (ξ : Rat) :
    Same (lineValue (F.subtract G) cosine ξ) (sub (lineValue F cosine ξ) (lineValue G cosine ξ)) := by
  let D := F.subtract G
  let A := lineValue D cosine ξ
  let B := lineValue F cosine ξ
  let C := lineValue G cosine ξ
  have compact (n : Nat) : Same (expandingComponent (differenceSampler f g) (fun _ => ξ) cosine n)
      (sub (expandingComponent f (fun _ => ξ) cosine n) (expandingComponent g (fun _ => ξ) cosine n)) := by
    let P (s : JointLipschitzSampler 1) (K : LineDecay s) :=
      lineData (linePhaseSampler s (fun _ => ξ) cosine K.bound K.nonnegative (lineDecay_all K))
        ((expandingBox 1 n).ordered (Fin.last 0))
    have hf := expandingComponent_line f (fun _ => ξ) cosine F.bound F.nonnegative (lineDecay_all F) n
    have hg := expandingComponent_line g (fun _ => ξ) cosine G.bound G.nonnegative (lineDecay_all G) n
    have hd := expandingComponent_line (differenceSampler f g) (fun _ => ξ) cosine D.bound
      D.nonnegative (lineDecay_all D) n
    have h : Same ((P f F).subtract (P g G)).value (sub (P f F).value (P g G).value) :=
      (P f F).subtract_identity (P g G)
    exact Same.trans (Y := (P _ D).value) hd (Same.trans
      (Y := ((P f F).subtract (P g G)).value) ((P _ D).congr ((P f F).subtract (P g G)) (fun t _ _ => by
        apply arithmetic_identity
        intro s
        simp only [differenceSampler, linePhaseSampler, productSampler, Value.mul, sub]
        grind only)) (h.trans (hf.symm.sub hg.symm)))
  apply small_sub_zero_same
  apply EffectiveImproperIntegral.small_of_errors (sub A (sub B C)) 0
    (fun n => (4*D.bound+4*F.bound+4*G.bound)/radius n)
    (shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl))
  intro n
  have H := ((lineTransform_error D (fun _ => ξ) cosine n).congr
    ((Same.refl A).sub (compact n))).add (((lineTransform_error F (fun _ => ξ) cosine n).neg).add
      (lineTransform_error G (fun _ => ξ) cosine n))
  have he (d f g r : Rat) : 4*d/r+(4*f/r+4*g/r)=0+(4*d+4*f+4*g)/r := by
    simp only [Rat.div_def]
    grind only
  change Small _ (4*D.bound/radius n+(4*F.bound/radius n+4*G.bound/radius n)) at H
  rw [he] at H
  apply H.congr
  apply arithmetic_identity
  intro s
  simp only [Value.add, Value.neg, sub]
  let a := A.sample s
  let b := B.sample s
  let c := C.sample s
  let p := (expandingComponent f (fun _ => ξ) cosine n).sample s
  let q := (expandingComponent g (fun _ => ξ) cosine n).sample s
  change (a-(p-q))+(-(b-p)+(c-q))=a-(b-c)
  grind only

private theorem lineValue_mulConstant {f : JointLipschitzSampler 1}
    (F : LineDecay f) (c : Value) (C : Rat) (hC : 0 ≤ C) (hc : Small c C) (cosine : Bool) (ξ : Rat) :
    Same (lineValue (F.mulConstant c C hC hc) cosine ξ) (Value.mul c (lineValue F cosine ξ)) := by
  let D := F.mulConstant c C hC hc
  let A := lineValue D cosine ξ
  let B := lineValue F cosine ξ
  have compact (n : Nat) : Same
      (expandingComponent (constantMultiple c C hC hc f) (fun _ => ξ) cosine n)
      (Value.mul c (expandingComponent f (fun _ => ξ) cosine n)) := by
    let r := radius n
    let P := lineData (linePhaseSampler f (fun _ => ξ) cosine F.bound F.nonnegative (lineDecay_all F))
      ((expandingBox 1 n).ordered (Fin.last 0))
    let Q := lineData (linePhaseSampler _ (fun _ => ξ) cosine D.bound D.nonnegative (lineDecay_all D))
      ((expandingBox 1 n).ordered (Fin.last 0))
    have hp : ∀ t, -r ≤ t → t ≤ r → Small
        (Value.mul (f.value (fun _ => t)) (trigValue cosine (phase (fun _ : Fin 1 => ξ) (fun _ => t)))) (F.bound*1) :=
      fun t _ _ => (F.bounded t).mul (trig_small _ _)
    let K := (LipschitzQuadrature.constantData c (-r) r P.ordered).mul P C (F.bound*1)
      hC (Rat.mul_nonneg F.nonnegative (by decide)) (fun _ _ _ => hc) hp
    have he : Same Q.value K.value := Q.congr K (fun t _ _ => by
      apply arithmetic_identity
      intro s
      simp only [constantMultiple, linePhaseSampler, productSampler, Value.mul]
      grind only)
    have H := P.mul_constant_identity c (F.bound*1) C
      (Rat.mul_nonneg F.nonnegative (by decide)) hC hc hp
    exact Same.trans (Y := Q.value) (expandingComponent_line _ _ cosine D.bound D.nonnegative (lineDecay_all D) n)
      (he.trans (H.trans ((Same.refl c).mul (expandingComponent_line f _ cosine F.bound F.nonnegative
        (lineDecay_all F) n).symm)))
  apply small_sub_zero_same
  apply EffectiveImproperIntegral.small_of_errors (sub A (Value.mul c B)) 0
    (fun n => (4*D.bound+C*(4*F.bound))/radius n)
    (shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl))
  intro n
  have H := ((lineTransform_error D (fun _ => ξ) cosine n).congr
    ((Same.refl A).sub (compact n))).add (hc.mul (lineTransform_error F (fun _ => ξ) cosine n).neg)
  have he (d f c r : Rat) : 4*d/r+c*(4*f/r)=0+(4*d+c*(4*f))/r := by
    simp only [Rat.div_def]
    grind only
  change Small _ (4*D.bound/radius n+C*(4*F.bound/radius n)) at H
  rw [he] at H
  exact H.congr (arithmetic_identity _ _ (by
    intro s
    let a := A.sample s
    let b := B.sample s
    let p := (expandingComponent f (fun _ => ξ) cosine n).sample s
    let k := c.sample s
    change a-k*p+k*(-(b-p)) = a-k*b
    grind only))


/-- The integrated cosine transform is unchanged after removing a numerator
that vanishes at zero, provided its quotient has the constructed decay.
The remaining term is the normalized profile's transform. -/
theorem melrose_origin_reduction
    {f profile w d e g mf mp mw df ddf dp ddp dw ddw : JointLipschitzSampler 1}
    (F : LineDecay f) (P : LineDecay profile) (W : LineDecay w)
    (D : LineDecay d) (E : LineDecay e) (G : LineDecay g)
    (MF : LineDecay mf) (MP : LineDecay mp) (MW : LineDecay mw)
    (DF : LineDecay df) (DDF : LineDecay ddf) (DP : LineDecay dp) (DDP : LineDecay ddp)
    (DW : LineDecay dw) (DDW : LineDecay ddw)
    (hf : ∀ t : Rat, Same (mf.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (hp : ∀ t : Rat, Same (mp.value (fun _ => t)) (scale t (profile.value (fun _ => t))))
    (hw : ∀ t : Rat, Same (mw.value (fun _ => t)) (scale t (w.value (fun _ => t))))
    (SF : ∀ n : Nat, Step (fun t => f.value (fun _ => t)) (fun t => df.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (TF : ∀ n : Nat, Step (fun t => df.value (fun _ => t)) (fun t => ddf.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (SP : ∀ n : Nat, Step (fun t => profile.value (fun _ => t)) (fun t => dp.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (TP : ∀ n : Nat, Step (fun t => dp.value (fun _ => t)) (fun t => ddp.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (S : ∀ n : Nat, Step (fun t => w.value (fun _ => t)) (fun t => d.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (T : ∀ n : Nat, Step (fun t => d.value (fun _ => t)) (fun t => e.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (U : ∀ n : Nat, Step (fun t => e.value (fun _ => t)) (fun t => g.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (SW : ∀ n : Nat, Step (fun t => w.value (fun _ => t)) (fun t => dw.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (TW : ∀ n : Nat, Step (fun t => dw.value (fun _ => t)) (fun t => ddw.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (hz : Same (w.value (fun _ => 0)) (Value.rational 0))
    (hsub : ∀ x, Same (w.value x) (sub (f.value x) (Value.mul (f.value (fun _ => 0)) (profile.value x)))) :
    Same (lineValue (lineTransformDecay F MF DF DDF hf SF TF true) true 0)
      (Value.mul (f.value (fun _ => 0)) (lineValue (lineTransformDecay P MP DP DDP hp SP TP true) true 0)) := by
  let c := f.value (fun _ => 0)
  let C := P.mulConstant c F.bound F.nonnegative (F.bounded 0)
  let A := lineTransformDecay F MF DF DDF hf SF TF true
  let B := lineTransformDecay P MP DP DDP hp SP TP true
  let K := B.mulConstant c F.bound F.nonnegative (F.bounded 0)
  let J := lineTransformDecay W MW DW DDW hw SW TW true
  let Q := lineFTCQuotient_derivativeDecay W D E G S T U hz
  have hSteps (n : Nat) := lineFTCQuotient_derivativeSteps (T n) (U n)
    (by have := radius_pos n; constructor <;> grind only) D E G
  have hzero : Same (lineValue J true 0) (Value.rational 0) :=
    lineFTCQuotient_fourierIntegral_zero W D S hz Q.1 Q.2
      (fun n => (hSteps n).1) (fun n => (hSteps n).2) MW DW DDW hw SW TW false
  have h := lineTransform_congr J (A.subtract K) (fun x => by
    let t := x (Fin.last 0)
    have hq : Same (lineValue W true t) (lineValue (F.subtract C) true t) :=
      lineTransform_congr W (F.subtract C) hsub (fun _ => t) true
    exact hq.trans ((lineValue_subtract F C true t).trans
      ((Same.refl _).sub (lineValue_mulConstant P c F.bound F.nonnegative (F.bounded 0) true t))))
    (fun _ => 0) true
  have hc := lineValue_mulConstant B c F.bound F.nonnegative (F.bounded 0) true 0
  have hd : Same (sub (lineValue A true 0) (Value.mul c (lineValue B true 0))) (Value.rational 0) :=
    (((lineValue_subtract A K true 0).trans ((Same.refl _).sub hc)).symm.trans
      (Same.trans (Y := lineValue J true 0) (Same.symm h) hzero))
  have hz' : Small (Value.rational 0) 0 := by
    simpa only [show qabs (0 : Rat) = 0 by decide +kernel] using rational_small 0
  exact small_sub_zero_same (hz'.congr hd.symm)


/-- Fourier differentiation turns the Gaussian drift equation into a
frequency ODE. The two components satisfy the same scalar equation. -/
theorem gaussianTransform_ode {f m df : JointLipschitzSampler 1}
    (F : LineDecay f) (M : LineDecay m) (DF : LineDecay df)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (S : ∀ n : Nat, Step (fun t => f.value (fun _ => t)) (fun t => df.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat))
    (hd : ∀ x, Same (df.value x) (scale (-2) (m.value x)))
    (cosine : Bool) (ξ : Rat) (eps : QPos) (h : Rat)
    (hh : qabs h ≤ (lineDerivativeModulus F M eps).val) :
    Small (sub (sub (lineValue F cosine (ξ+h)) (lineValue F cosine ξ))
      (scale h (scale (-2*ξ)
        (Value.mul (Value.mul GeometricTrig.piValue GeometricTrig.piValue)
          (lineValue F cosine ξ))))) (eps.val*qabs h) := by
  let c := Value.rational (-2)
  have hc : Small c 2 := by
    simpa only [show qabs (-2 : Rat) = 2 by decide +kernel] using rational_small (-2)
  let D := M.mulConstant c 2 (by decide) hc
  let y := lineValue F cosine ξ
  let z := lineValue M (!cosine) ξ
  have he : Same (lineValue DF (!cosine) ξ) (Value.mul c z) := by
    refine Same.trans (Y := lineValue D (!cosine) ξ)
      (lineTransform_congr DF D (fun x => (hd x).trans (arithmetic_identity _ _ (fun _ => rfl)))
        (fun _ => ξ) (!cosine)) (lineValue_mulConstant M c 2 (by decide) hc (!cosine) ξ)
  have hsp := lineTransform_spatialDerivative F DF S (!cosine) ξ
  have hflip : (!(!cosine)) = cosine := by cases cosine <;> rfl
  rw [hflip] at hsp
  have heq := he.symm.trans hsp
  have hz : Same z (scale (1/2) (Value.mul (phaseFactor (!cosine) ξ) y)) := by
    refine Same.trans (Y := scale (-1/2) (Value.mul c z))
      (arithmetic_identity _ _ (by
        intro s
        change z.sample s = (-1/2 : Rat)*(-2*z.sample s)
        grind only)) ((heq.scale (-1/2)).trans ?_)
    apply arithmetic_identity
    intro s
    simp only [scale, Value.neg]
    grind only
  have hder := lineTransform_frequencyDerivative_spec F M hm cosine ξ eps h hh
  have H : Same (Value.mul (phaseFactor cosine 1) z)
      (scale (-2*ξ) (Value.mul (Value.mul GeometricTrig.piValue GeometricTrig.piValue) y)) := by
    apply ((Same.refl (phaseFactor cosine 1)).mul hz).trans
    apply arithmetic_identity
    intro s
    cases cosine <;> simp only [phaseFactor, scale, Value.mul, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_true, if_false, Rat.mul_one] <;> grind only
  exact hder.congr ((Same.refl _).sub (H.scale h))


/-- Finite derivative data and spatial decay through order three on the line.
The samplers represent actual functions and the steps certify their derivatives. -/
structure LineDerivatives (f : JointLipschitzSampler 1) where
  first : JointLipschitzSampler 1
  second : JointLipschitzSampler 1
  third : JointLipschitzSampler 1
  firstDecay : LineDecay first
  secondDecay : LineDecay second
  thirdDecay : LineDecay third
  firstStep : ∀ n : Nat, Step (fun t => f.value (fun _ => t)) (fun t => first.value (fun _ => t))
    (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat)
  secondStep : ∀ n : Nat, Step (fun t => first.value (fun _ => t)) (fun t => second.value (fun _ => t))
    (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat)
  thirdStep : ∀ n : Nat, Step (fun t => second.value (fun _ => t)) (fun t => third.value (fun _ => t))
    (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat)

/-- Subtract a represented multiple of a profile and construct the three
derivative samplers of the numerator used by the quotient. -/
def LineDerivatives.subtractProfile {f g : JointLipschitzSampler 1}
    (F : LineDerivatives f) (G : LineDerivatives g)
    (c : Value) (C : Rat) (hC : 0 ≤ C) (hc : Small c C) :
    LineDerivatives (differenceSampler f (constantMultiple c C hC hc g)) where
  first := differenceSampler F.first (constantMultiple c C hC hc G.first)
  second := differenceSampler F.second (constantMultiple c C hC hc G.second)
  third := differenceSampler F.third (constantMultiple c C hC hc G.third)
  firstDecay := F.firstDecay.subtract (G.firstDecay.mulConstant c C hC hc)
  secondDecay := F.secondDecay.subtract (G.secondDecay.mulConstant c C hC hc)
  thirdDecay := F.thirdDecay.subtract (G.thirdDecay.mulConstant c C hC hc)
  firstStep n := (F.firstStep n).subtract ((G.firstStep n).mul_constant c C hC hc)
  secondStep n := (F.secondStep n).subtract ((G.secondStep n).mul_constant c C hC hc)
  thirdStep n := (F.thirdStep n).subtract ((G.thirdStep n).mul_constant c C hC hc)

private theorem subtractProfile_at_zero {f g : JointLipschitzSampler 1} (F : LineDecay f)
    (hg : Same (g.value (fun _ => 0)) (Value.rational 1)) :
    Same ((differenceSampler f (constantMultiple (f.value (fun _ => 0))
      F.bound F.nonnegative (F.bounded 0) g)).value (fun _ => 0)) (Value.rational 0) := by
  let c := f.value (fun _ => 0)
  have he : Same (Value.mul c (g.value (fun _ => 0))) c :=
    (((Same.refl c).mul hg).trans (arithmetic_identity _ _ (by
      intro s
      simp only [Value.mul, Value.rational, Rat.mul_one])))
  exact Same.trans (Y := sub c c) ((Same.refl c).sub he)
    (RealCompute.sub_self_equiv_zero c.real.valid)

/-- Melrose's identity at the origin, with an arbitrary normalized profile.
The normalization factor is its own computed integrated cosine transform. -/
theorem melrose_origin_normalized_profile {f g mf mg mw : JointLipschitzSampler 1}
    (F : LineDecay f) (G : LineDecay g) (JF : LineDerivatives f) (JG : LineDerivatives g)
    (MF : LineDecay mf) (MG : LineDecay mg)
    (hf : ∀ t : Rat, Same (mf.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (hg : ∀ t : Rat, Same (mg.value (fun _ => t)) (scale t (g.value (fun _ => t))))
    (h₀ : Same (g.value (fun _ => 0)) (Value.rational 1))
    (MW : LineDecay mw)
    (hw : ∀ t : Rat, Same (mw.value (fun _ => t))
      (scale t (sub (f.value (fun _ => t)) (Value.mul (f.value (fun _ => 0)) (g.value (fun _ => t)))))) :
    Same (lineValue (lineTransformDecay F MF JF.firstDecay JF.secondDecay hf JF.firstStep JF.secondStep true) true 0)
      (Value.mul (f.value (fun _ => 0))
        (lineValue (lineTransformDecay G MG JG.firstDecay JG.secondDecay hg JG.firstStep JG.secondStep true) true 0)) := by
  let c := f.value (fun _ => 0)
  let W := F.subtract (G.mulConstant c F.bound F.nonnegative (F.bounded 0))
  let JW := JF.subtractProfile JG c F.bound F.nonnegative (F.bounded 0)
  exact melrose_origin_reduction F G W JW.firstDecay JW.secondDecay JW.thirdDecay MF MG MW
    JF.firstDecay JF.secondDecay JG.firstDecay JG.secondDecay JW.firstDecay JW.secondDecay
    hf hg hw JF.firstStep JF.secondStep JG.firstStep JG.secondStep JW.firstStep JW.secondStep JW.thirdStep
    JW.firstStep JW.secondStep (subtractProfile_at_zero F h₀) (fun _ => Same.refl _)


/-- The existing normalized Gaussian and its drift, as represented values. -/
def gaussianProfile (x : Rat) : Value :=
  parameter (gaussianNormalizedProfileRaw x) (gaussianNormalizedProfileRaw_valid x)

def gaussianDrift (x : Rat) : Value :=
  Value.neg (scale (2*x) (gaussianProfile x))

private def gaussianError (C : Rat) : Rat :=
  (1 / gaussianFullLineMassLower) * gaussianReciprocalPositiveProfileSecantUniformBound C

/-- Pass the finite Gaussian secant estimates to the exact represented
values, retaining their quadratic remainder on each rational box. -/
theorem gaussianProfile_remainder (C : Rat) (hC : 1 ≤ C)
    (u v : Rat) (hu : qabs u ≤ C) (hv : qabs v ≤ C) (huv : u < v) :
    Small (sub (sub (gaussianProfile v) (gaussianProfile u))
      (scale (v-u) (gaussianDrift u))) (gaussianError C*(v-u)*(v-u)) := by
  let h := v-u
  have hh : 0 < h := by dsimp only [h]; grind only
  have hx : u+h=v := by dsimp only [h]; grind only
  have hCpos : 0 < C := by grind only
  let X := sub (sub (gaussianProfile v) (gaussianProfile u)) (scale h (gaussianDrift u))
  let B := gaussianError C*h*h
  have mem (k : Nat) :
      ∃ z : Rat, (X.real.preferred.compute k).lo ≤ z ∧ z ≤ (X.real.preferred.compute k).hi ∧
        qabs z ≤ B + h*((precisionAtStage k).val/2) := by
    let n := max k (gaussianNormalizedDerivativeTailPrecision C hCpos k)
    let a := gaussianNormalizedDerivativeBaseValue u h n
    let b := gaussianNormalizedDerivativeStepValue u h n
    let d := gaussianNormalizedDerivativeCandidateValue u h n
    let z := b-a-h*d
    have hA := gaussianNormalizedDerivativeBaseValue_mem u h n
    have hB := gaussianNormalizedDerivativeStepValue_mem u h n
    rw [hx] at hB
    have hD := gaussianNormalizedDerivativeCandidateValue_mem u h n
    have hM : (X.real.preferred.compute n).lo ≤ z ∧ z ≤ (X.real.preferred.compute n).hi := by
      have H := QInterval.scaleRat_mem (r := h) hD
      change ((gaussianProfile u).real.preferred.compute n).lo ≤ a ∧
        a ≤ ((gaussianProfile u).real.preferred.compute n).hi at hA
      change ((gaussianProfile v).real.preferred.compute n).lo ≤ b ∧
        b ≤ ((gaussianProfile v).real.preferred.compute n).hi at hB
      change (RealCompute.scaleRatCompute h (gaussianDrift u).real.preferred n).lo ≤ h*d ∧
        h*d ≤ (RealCompute.scaleRatCompute h (gaussianDrift u).real.preferred n).hi at H
      change (((gaussianProfile v).real.preferred.compute n).lo -
        ((gaussianProfile u).real.preferred.compute n).hi) -
        (RealCompute.scaleRatCompute h (gaussianDrift u).real.preferred n).hi ≤ z ∧ z ≤
        (((gaussianProfile v).real.preferred.compute n).hi -
        ((gaussianProfile u).real.preferred.compute n).lo) -
        (RealCompute.scaleRatCompute h (gaussianDrift u).real.preferred n).lo
      dsimp only [z]
      constructor <;> grind only
    have hE := gaussianNormalizedDerivativeFiniteSecantError_le C hC (Rat.ne_of_gt hh)
      hu (by rwa [hx]) n
    change qabs ((b-a)/h-d) ≤ _ at hE
    have he : qabs z = h*qabs ((b-a)/h-d) := by
      have hz : z=h*((b-a)/h-d) := by
        have := Rat.mul_inv_cancel h (Rat.ne_of_gt hh)
        dsimp only [z]
        grind only [Rat.div_def]
      rw [hz, qabs_mul, qabs_eq_self_of_nonneg (Rat.le_of_lt hh)]
    have hs := gaussianReciprocalPositiveProfileSecantBound_errorCoefficient_le_uniform C hC
      (gaussianDerivativeCommonTailIndex u h n) (gaussianDerivativeCommonTailIndex_pos u h n)
    have htail := gaussianNormalizedDerivativeTailBudget_le_half_precision C hCpos u h k
      (stage := n) (Nat.le_max_right _ _)
    have hc₀ : 0 ≤ 1 / gaussianFullLineMassLower :=
      Rat.le_of_lt (Rat.mul_pos (by decide) (Rat.inv_pos.mpr gaussianFullLineMassLower_pos))
    have hc₁ := Rat.mul_le_mul_of_nonneg_left hs
      (Rat.mul_nonneg hc₀ (Rat.le_of_lt hh))
    rw [qabs_eq_self_of_nonneg (Rat.le_of_lt hh)] at hE
    have hb := Rat.mul_le_mul_of_nonneg_left hE (Rat.le_of_lt hh)
    have hk := X.real.valid.2.1 k n (Nat.le_max_left _ _)
    refine ⟨z, Rat.le_trans hk.1 hM.1, Rat.le_trans hM.2 hk.2.2, ?_⟩
    rw [he]
    apply Rat.le_trans hb
    let L := 1 / gaussianFullLineMassLower
    let E := (gaussianReciprocalPositiveProfileSecantBound C
      (gaussianDerivativeCommonTailIndex u h n) hC
      (gaussianDerivativeCommonTailIndex_pos u h n)).errorCoefficient
    let T := RationalMajorant.factorialTailTerm (C*C) (gaussianDerivativeCommonTailIndex u h n)
    change h*(L*(h*E+2*C*T)) ≤ B + h*((precisionAtStage k).val/2)
    change L*h*E ≤ L*h*gaussianReciprocalPositiveProfileSecantUniformBound C at hc₁
    change L*(2*C*T) ≤ (precisionAtStage k).val/2 at htail
    have hleft := Rat.mul_le_mul_of_nonneg_left hc₁ (Rat.le_of_lt hh)
    have hright := Rat.mul_le_mul_of_nonneg_left htail (Rat.le_of_lt hh)
    have eq : h*(L*(h*E+2*C*T)) = h*(L*h*E)+h*(L*(2*C*T)) := by grind only
    rw [eq]
    refine Rat.le_trans (rat_add_le_add hleft hright) ?_
    have heq : h*(L*h*gaussianReciprocalPositiveProfileSecantUniformBound C) = B := by
      dsimp only [B, gaussianError, L]
      grind only
    rw [heq]
    exact Rat.le_refl
  have hs : ShrinksToZero (fun k => h*((precisionAtStage k).val/2)) := by
    intro eps
    let τ : QPos := ⟨eps.val/h, Rat.mul_pos eps.property (Rat.inv_pos.mpr hh)⟩
    obtain ⟨N, hN⟩ := precisionAtStage_shrinksToZero τ
    refine ⟨N, fun n hn => ?_⟩
    have hm := Rat.mul_le_mul_of_nonneg_left (hN n hn) (Rat.le_of_lt hh)
    change h*(precisionAtStage n).val ≤ h*(eps.val/h) at hm
    have he : h*(eps.val/h)=eps.val := by
      rw [Rat.mul_comm, Rat.div_mul_cancel (Rat.ne_of_gt hh)]
    rw [he] at hm
    have hp := (precisionAtStage n).property
    have hd : (precisionAtStage n).val/2 ≤ (precisionAtStage n).val := by grind only
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hd (Rat.le_of_lt hh)) hm
  have H : Small X B := by
    constructor
    · intro _ j
      by_cases he : -B ≤ (X.real.preferred.compute j).hi
      · exact he
      let eps : QPos := ⟨(-B-(X.real.preferred.compute j).hi)/2, by grind only⟩
      obtain ⟨N, hN⟩ := hs eps
      let k := max N j
      obtain ⟨z, _, hright, hz⟩ := mem k
      have hn := X.real.valid.2.1 j k (Nat.le_max_right _ _)
      have herr := hN k (Nat.le_max_left _ _)
      change h*((precisionAtStage k).val/2) ≤ (-B-(X.real.preferred.compute j).hi)/2 at herr
      have ha := neg_qabs_le_self z
      change -B ≤ (X.real.preferred.compute j).hi
      grind only
    · intro i _
      by_cases he : (X.real.preferred.compute i).lo ≤ B
      · exact he
      let eps : QPos := ⟨((X.real.preferred.compute i).lo-B)/2, by grind only⟩
      obtain ⟨N, hN⟩ := hs eps
      let k := max N i
      obtain ⟨z, hleft, _, hz⟩ := mem k
      have hn := X.real.valid.2.1 i k (Nat.le_max_right _ _)
      have herr := hN k (Nat.le_max_left _ _)
      change h*((precisionAtStage k).val/2) ≤ ((X.real.preferred.compute i).lo-B)/2 at herr
      have ha := self_le_qabs z
      change (X.real.preferred.compute i).lo ≤ B
      grind only
  exact H


/-- The normalized Gaussian has the reciprocal quadratic majorant
used in the spatial moment and derivative estimates. -/
theorem gaussianProfile_small (x : Rat) :
    Small (gaussianProfile x) ((1/gaussianFullLineMassLower)/(1+x*x)) := by
  let B := 1/gaussianFullLineMassLower
  let G := parameter (reciprocalGaussianRaw x) (reciprocalGaussianRaw_valid x)
  let C := parameter gaussianFullLineMassReciprocalRaw gaussianFullLineMassReciprocalRaw_valid
  have hC : Small C B := by
    have hb : 0 ≤ B := Rat.le_of_lt (Rat.mul_pos (by decide) (Rat.inv_pos.mpr gaussianFullLineMassLower_pos))
    have h := gaussianFullLineMassReciprocalRaw_nonneg_bounded 0
    exact RawLimit.inInterval_of_contains_compute (I := ⟨-B, B⟩)
      gaussianFullLineMassReciprocalRaw_valid 0 ⟨Rat.le_trans (by grind only) h.1, h.2⟩
  have hG : Small G (1/(1+x*x)) := by
    have hn := rat_square_nonneg_basic x
    have hb : 0 ≤ 1/(1+x*x) := Rat.le_of_lt (Rat.mul_pos (by decide) (Rat.inv_pos.mpr (by grind only)))
    have hl := (reciprocalGaussianRaw_nonneg_bounded_by_one x 0).1
    have hu := reciprocalNegativeExpRaw_compute_hi_le_one_div_one_add (x*x) hn 0
    exact RawLimit.inInterval_of_contains_compute (I := ⟨-(1/(1+x*x)), 1/(1+x*x)⟩)
      (reciprocalGaussianRaw_valid x) 0 ⟨Rat.le_trans (by grind only) hl, hu⟩
  have H := hC.mul hG
  have he : B*(1/(1+x*x)) = B/(1+x*x) := by simp only [Rat.div_def, Rat.one_mul]
  rw [he] at H
  exact H

/-- The drift has a uniform represented bound, since `|x| ≤ 1+x²`. -/
theorem gaussianDrift_small (x : Rat) : Small (gaussianDrift x) (2*(1/gaussianFullLineMassLower)) := by
  let B := 1/gaussianFullLineMassLower
  have hB : 0 ≤ B := Rat.le_of_lt (Rat.mul_pos (by decide) (Rat.inv_pos.mpr gaussianFullLineMassLower_pos))
  have hx : qabs x ≤ 1+x*x := by
    by_cases h : 0 ≤ x
    · rw [qabs_eq_self_of_nonneg h]
      have H := rat_square_nonneg_basic (x-1/2)
      grind only
    · rw [qabs_eq_neg_of_nonpos (by grind only)]
      have H := rat_square_nonneg_basic (x+1/2)
      grind only
  have hd : 0 < 1+x*x := by have := rat_square_nonneg_basic x; grind only
  have hm := Rat.mul_le_mul_of_nonneg_right hx (Rat.le_of_lt (Rat.inv_pos.mpr hd))
  rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt hd)] at hm
  have h := (scale_small (gaussianProfile_small x) (2*x)).neg
  rw [qabs_mul, show qabs (2 : Rat) = 2 by decide +kernel] at h
  apply h.mono
  have H := Rat.mul_le_mul_of_nonneg_left hm (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 2) hB)
  change 2*B*(qabs x*(1+x*x)⁻¹) ≤ 2*B*1 at H
  change (2*qabs x)*(B/(1+x*x)) ≤ 2*B
  simp only [Rat.div_def] at *
  grind only

/-- Exact represented Lipschitz bound for the Gaussian on the line. -/
theorem gaussianProfile_lipschitz {u v : Rat} (huv : u ≤ v) :
    Small (sub (gaussianProfile v) (gaussianProfile u))
      ((2*(1/gaussianFullLineMassLower))*(v-u)) := by
  let C := 1 + qabs u + qabs v
  have hC : 1 ≤ C := by have := qabs_nonneg u; have := qabs_nonneg v; dsimp only [C]; grind only
  have hA : 0 ≤ gaussianError C :=
    Rat.mul_nonneg (Rat.le_of_lt (Rat.mul_pos (by decide) (Rat.inv_pos.mpr gaussianFullLineMassLower_pos)))
      (gaussianReciprocalPositiveProfileSecantUniformBound_nonneg C hC)
  have hab (x : Rat) (hx : u ≤ x) (hx' : x ≤ v) : qabs x ≤ C :=
    qabs_le_of_neg_le_le
      (by have := neg_qabs_le_self u; have := qabs_nonneg v; dsimp only [C]; grind only)
      (by have := self_le_qabs v; have := qabs_nonneg u; dsimp only [C]; grind only)
  have H : FTCRealOrder.FirstOrder gaussianProfile gaussianDrift u v (gaussianError C) 1 := by
    intro a b ha hab' hb _
    exact gaussianProfile_remainder C hC a b (hab a ha (by grind only)) (hab b (by grind only) hb) hab'
  exact lipschitz_of_firstOrder H hA (by decide) (fun t _ _ => gaussianDrift_small t)
    u v Rat.le_refl huv Rat.le_refl


/-- The existing normalized Gaussian, with the global Lipschitz estimate
needed by whole-line quadrature. -/
def gaussianSampler : JointLipschitzSampler 1 where
  value x := gaussianProfile (x (Fin.last 0))
  bound := 2*(1/gaussianFullLineMassLower)
  nonnegative := Rat.mul_nonneg (by decide)
    (Rat.le_of_lt (Rat.mul_pos (by decide) (Rat.inv_pos.mpr gaussianFullLineMassLower_pos)))
  control := by
    intro x y δ _ hxy
    let u := x (Fin.last 0)
    let v := y (Fin.last 0)
    have H := hxy (Fin.last 0)
    have hp : 0 ≤ 2*(1/gaussianFullLineMassLower) := Rat.mul_nonneg (by decide)
      (Rat.le_of_lt (Rat.mul_pos (by decide) (Rat.inv_pos.mpr gaussianFullLineMassLower_pos)))
    change Small (sub (gaussianProfile u) (gaussianProfile v)) _
    by_cases huv : v ≤ u
    · exact (gaussianProfile_lipschitz huv).mono
        (Rat.mul_le_mul_of_nonneg_left (show u-v ≤ δ by change u ≤ v+δ ∧ _ at H; grind only) hp)
    · have h' : u ≤ v := by grind only
      have h := (gaussianProfile_lipschitz h').neg
      apply (h.mono (Rat.mul_le_mul_of_nonneg_left
        (show v-u ≤ δ by change _ ∧ v ≤ u+δ at H; grind only) hp)).congr
      apply arithmetic_identity
      intro s
      simp only [Value.neg, sub]
      grind only

def gaussianDecay : LineDecay gaussianSampler where
  bound := 1/gaussianFullLineMassLower
  nonnegative := Rat.le_of_lt (Rat.mul_pos (by decide) (Rat.inv_pos.mpr gaussianFullLineMassLower_pos))
  bounded x := by
    have hs := rat_square_nonneg_basic x
    have h := reciprocal_mul_mono (by decide : (0 : Rat) < 1) (show 1 ≤ 1+x*x by grind only)
    have h' := Rat.mul_le_mul_of_nonneg_left h
      (show 0 ≤ 1/gaussianFullLineMassLower from Rat.le_of_lt
        (Rat.mul_pos (by decide) (Rat.inv_pos.mpr gaussianFullLineMassLower_pos)))
    apply (gaussianProfile_small x).mono
    simpa only [Rat.div_def, Rat.one_mul, show (1 : Rat)⁻¹ = 1 by decide +kernel, Rat.mul_one] using h'
  outside x hx := by
    have ha := qabs_pos_of_ne (x := x) (by
      intro he
      subst x
      exact (by decide +kernel : ¬ 1 ≤ qabs (0 : Rat)) hx)
    have hs : x*x = qabs x*qabs x := by
      rw [← qabs_mul, qabs_eq_self_of_nonneg (rat_square_nonneg_basic x)]
    have h := reciprocal_mul_mono (Rat.mul_pos ha ha)
      (show qabs x*qabs x ≤ 1+x*x by rw [← hs]; grind only)
    have h' := Rat.mul_le_mul_of_nonneg_left h
      (show 0 ≤ 1/gaussianFullLineMassLower from Rat.le_of_lt
        (Rat.mul_pos (by decide) (Rat.inv_pos.mpr gaussianFullLineMassLower_pos)))
    apply (gaussianProfile_small x).mono
    simpa only [Rat.div_def, Rat.one_mul] using h'

/-- Any one term of the positive exponential series bounds its reciprocal
from above. A later rational prefix witnesses the bound in every raw box. -/
private theorem gaussianReciprocal_power_bound {x : Rat} (hx : x ≠ 0) (j : Nat) :
    Small (parameter (reciprocalGaussianRaw x) (reciprocalGaussianRaw_valid x))
      (factorialRat j / (x*x)^j) := by
  let a := x*x
  let c := factorialRat j
  have ha : 0 < a := by
    by_cases h : 0 < x
    · exact Rat.mul_pos h h
    · have H := Rat.mul_pos (show 0 < -x by grind only) (show 0 < -x by grind only)
      dsimp [a]
      grind only
  have hc : 0 < c := RationalMajorant.factorialRat_pos j
  have hp : 0 < a^j := Rat.pow_pos ha
  have hb : 0 ≤ c/a^j :=
    Rat.le_of_lt (Rat.mul_pos hc (Rat.inv_pos.mpr hp))
  constructor
  · intro i k
    change -(c/a^j) ≤ ((reciprocalGaussianRaw x).compute k).hi
    have H := reciprocalGaussianRaw_nonneg_bounded_by_one x k
    have ho := (reciprocalGaussianRaw_valid x).1 k
    change 0 ≤ ((reciprocalGaussianRaw x).compute k).hi -
      ((reciprocalGaussianRaw x).compute k).lo at ho
    grind only
  · intro i k
    change ((reciprocalNegativeExpRaw a).compute i).lo ≤ c/a^j
    let future := max i (j+1)
    let terms := expPowerSeriesTerms a future
    have hterms : j+1 ≤ terms := by
      unfold terms expPowerSeriesTerms future
      omega
    have h := FiniteExponentialProduct.factorialPrefix_mono (Rat.le_of_lt ha) hterms
    rw [FiniteExponentialProduct.factorialPrefix_succ] at h
    have hn := FiniteExponentialProduct.factorialPrefix_nonneg (Rat.le_of_lt ha) j
    have hm : a^j/c ≤ FiniteExponentialProduct.factorialPrefix terms a := by
      change _ + (1/c)*a^j ≤ _ at h
      rw [Rat.div_def, Rat.one_mul, Rat.mul_comm c⁻¹] at h
      grind only
    have hq : 0 < a^j/c := Rat.mul_pos hp (Rat.inv_pos.mpr hc)
    have H := reciprocal_mul_mono hq hm
    have he : 1/(a^j/c) = c/a^j := by
      simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv, Rat.one_mul]
    rw [he] at H
    have hw := reciprocalNegativeExpRaw_future_inversePrefix_mem a
      (Rat.le_of_lt ha) (futureStage := future) (Nat.le_max_left i (j+1))
    exact Rat.le_trans hw.1 H

/-- Polynomial moments use the same Gaussian evaluator and its normalization. -/
def gaussianMoment (k : Nat) (x : Rat) : Value :=
  scale (x^k) (gaussianProfile x)

private def gaussianMomentBound (k : Nat) : Rat :=
  (1/gaussianFullLineMassLower)*(1+factorialRat (k+1))

private theorem gaussianMomentBound_nonneg (k : Nat) : 0 ≤ gaussianMomentBound k :=
  Rat.mul_nonneg gaussianDecay.nonnegative (Rat.add_nonneg (by decide)
    (Rat.le_of_lt (RationalMajorant.factorialRat_pos _)))

private theorem gaussianMoment_outside (k : Nat) (x : Rat) (hx : 1 ≤ qabs x) :
    Small (gaussianMoment k x) (gaussianMomentBound k/(qabs x*qabs x)) := by
  let r := qabs x
  let a := r*r
  have hr : 0 < r := by dsimp [r]; grind only
  have ha : 0 < a := Rat.mul_pos hr hr
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    exact (by decide +kernel : ¬ 1 ≤ qabs (0 : Rat)) hx
  have he : x*x = a := by
    unfold a r
    rw [← qabs_mul, qabs_eq_self_of_nonneg (rat_square_nonneg_basic x)]
  have hra : r ≤ a := by
    have H := Rat.mul_le_mul_of_nonneg_right hx (Rat.le_of_lt hr)
    change 1*r ≤ a at H
    simpa only [Rat.one_mul] using H
  have hpow (j : Nat) : r^j ≤ a^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Rat.pow_succ, Rat.pow_succ]
      exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih (Rat.le_of_lt hr))
        (Rat.mul_le_mul_of_nonneg_left hra (Rat.pow_nonneg (Rat.le_of_lt ha)))
  let B := 1/gaussianFullLineMassLower
  let C := parameter gaussianFullLineMassReciprocalRaw gaussianFullLineMassReciprocalRaw_valid
  have hC : Small C B := by
    have h := gaussianFullLineMassReciprocalRaw_nonneg_bounded 0
    have hb : 0 ≤ B := gaussianDecay.nonnegative
    exact RawLimit.inInterval_of_contains_compute (I := ⟨-B, B⟩)
      gaussianFullLineMassReciprocalRaw_valid 0 ⟨Rat.le_trans (by grind only) h.1, h.2⟩
  have H := scale_small (hC.mul (gaussianReciprocal_power_bound hx0 (k+1))) (x^k)
  rw [he, RationalMajorant.qabs_pow_eq_pow_qabs] at H
  change Small (gaussianMoment k x) (r^k*(B*(factorialRat (k+1)/a^(k+1)))) at H
  apply H.mono
  have hp : 0 < a^(k+1) := Rat.pow_pos ha
  have hfac := Rat.le_of_lt (RationalMajorant.factorialRat_pos (k+1))
  have hB : 0 ≤ B := gaussianDecay.nonnegative
  apply Rat.le_of_mul_le_mul_right (c := a^(k+1)) _ hp
  have hleft : (r^k*(B*(factorialRat (k+1)/a^(k+1))))*a^(k+1) =
      r^k*(B*factorialRat (k+1)) := by
    have H := Rat.mul_inv_cancel _ (Rat.ne_of_gt hp)
    grind only [Rat.div_def]
  have hright : (gaussianMomentBound k/a)*a^(k+1) = gaussianMomentBound k*a^k := by
    rw [Rat.pow_succ]
    have H := Rat.mul_inv_cancel a (Rat.ne_of_gt ha)
    grind only [Rat.div_def]
  change _ ≤ (gaussianMomentBound k/a)*a^(k+1)
  rw [hleft, hright]
  refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (hpow k) (Rat.mul_nonneg hB hfac)) ?_
  rw [Rat.mul_comm (a^k)]
  exact Rat.mul_le_mul_of_nonneg_right
      (Rat.mul_le_mul_of_nonneg_left (by grind only : factorialRat (k+1) ≤ 1+factorialRat (k+1)) hB)
      (Rat.pow_nonneg (Rat.le_of_lt ha))

private theorem gaussianMoment_bounded (k : Nat) (x : Rat) :
    Small (gaussianMoment k x) (gaussianMomentBound k) := by
  have hB := gaussianDecay.nonnegative
  by_cases h : 1 ≤ qabs x
  · apply (gaussianMoment_outside k x h).mono
    have ha : 1 ≤ qabs x*qabs x := by
      have H := Rat.mul_le_mul_of_nonneg_right h (qabs_nonneg x)
      rw [Rat.one_mul] at H
      grind only
    have H := reciprocal_mul_mono (by decide : (0 : Rat) < 1) ha
    simpa only [Rat.div_def, Rat.one_mul, show (1 : Rat)⁻¹ = 1 by decide +kernel, Rat.mul_one]
      using Rat.mul_le_mul_of_nonneg_left H (gaussianMomentBound_nonneg k)
  · have H := scale_small (gaussianDecay.bounded x) (x^k)
    change Small (gaussianMoment k x) _ at H
    apply H.mono
    have hp := RationalMajorant.qabs_pow_le_pow (by decide : (0 : Rat) ≤ 1)
      (show qabs x ≤ 1 by grind only) k
    have hone : ∀ m : Nat, (1 : Rat)^m = 1 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [Rat.pow_succ, ih, Rat.mul_one]
    rw [hone] at hp
    refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hp hB) ?_
    rw [Rat.one_mul]
    have H := Rat.mul_le_mul_of_nonneg_left
      (show (1 : Rat) ≤ 1+factorialRat (k+1) by
        have := RationalMajorant.factorialRat_pos (k+1)
        grind only) hB
    change (1/gaussianFullLineMassLower)*1 ≤
      (1/gaussianFullLineMassLower)*(1+factorialRat (k+1)) at H
    change 1/gaussianFullLineMassLower ≤
      (1/gaussianFullLineMassLower)*(1+factorialRat (k+1))
    simpa only [Rat.mul_one, gaussianMomentBound] using H

private theorem gaussianBox_abs {C x : Rat} (hx : -C ≤ x) (hy : x ≤ C) : qabs x ≤ C :=
  qabs_le_of_neg_le_le hx hy

private def gaussianBaseStep (C : Rat) (hC : 1 ≤ C) :
    Step gaussianProfile gaussianDrift (-C) C where
  error := gaussianError C
  error_nonnegative := Rat.mul_nonneg gaussianDecay.nonnegative
    (gaussianReciprocalPositiveProfileSecantUniformBound_nonneg C hC)
  radius := ⟨1, by decide⟩
  firstOrder u v hu huv hv _ :=
    gaussianProfile_remainder C hC u v (gaussianBox_abs hu (by grind only))
      (gaussianBox_abs (by grind only) hv) huv
  variation := 2*(C*gaussianSampler.bound + gaussianDecay.bound)
  variation_nonnegative := Rat.mul_nonneg (by decide) (Rat.add_nonneg
    (Rat.mul_nonneg (by grind only) gaussianSampler.nonnegative) gaussianDecay.nonnegative)
  lipschitz := by
    intro u v hu huv hv
    have hvu : 0 ≤ v-u := by grind only
    have h := scale_small (gaussianProfile_lipschitz huv) u
    have h' := scale_small (gaussianDecay.bounded v) (v-u)
    change Small (scale (v-u) (gaussianProfile v)) (qabs (v-u)*gaussianDecay.bound) at h'
    change Small (scale u (sub (gaussianProfile v) (gaussianProfile u)))
      (qabs u*(gaussianSampler.bound*(v-u))) at h
    rw [qabs_eq_self_of_nonneg hvu] at h'
    have H := scale_small (h.add h') (-2)
    rw [show qabs (-2 : Rat) = 2 by decide +kernel] at H
    have K := (H.mono (show _ ≤ 2*(C*gaussianSampler.bound+gaussianDecay.bound)*(v-u) by
      have hb := Rat.mul_le_mul_of_nonneg_right (gaussianBox_abs hu (by grind only : u ≤ C))
        (Rat.mul_nonneg gaussianSampler.nonnegative hvu)
      change qabs u*(gaussianSampler.bound*(v-u)) ≤ C*(gaussianSampler.bound*(v-u)) at hb
      grind only))
    apply K.congr
    apply arithmetic_identity
    intro s
    simp only [scale, gaussianDrift, Value.add, Value.neg, sub]
    grind only

private def rationalPowerStep (C : Rat) (hC : 1 ≤ C) (j : Nat) :
    Step (fun t => Value.rational (t^(j+1)))
      (fun t => Value.rational (((j+1 : Nat) : Rat)*t^j)) (-C) C := by
  let K := FinitePolynomial.monomialSecantDerivativeBound C j hC
  let c : Rat := ((j+1 : Nat) : Rat)
  have hc : 0 ≤ c := Rat.le_of_lt (Rat.natCast_pos.mpr (Nat.succ_pos _))
  have hC0 : 0 ≤ C := by grind only
  refine ⟨K.errorCoefficient, K.errorCoefficient_nonneg, ⟨1, by decide⟩, ?_,
    c*(j : Rat)*C^j, Rat.mul_nonneg (Rat.mul_nonneg hc Rat.natCast_nonneg) (Rat.pow_nonneg hC0), ?_⟩
  · intro u v hu huv hv _
    let h := v-u
    have he : u+h = v := by dsimp [h]; grind only
    have hh : 0 < h := by dsimp [h]; grind only
    have H := K.error_bound u h (Rat.ne_of_gt hh)
      (gaussianBox_abs hu (by grind only)) (he ▸ gaussianBox_abs (by grind only : -C ≤ v) hv)
    change qabs ((((u+h)^(j+1)-u^(j+1))/h)-c*u^j) ≤ _ at H
    rw [he, qabs_eq_self_of_nonneg (Rat.le_of_lt hh)] at H
    have H' := Rat.mul_le_mul_of_nonneg_right H (Rat.le_of_lt hh)
    have hcancel := Rat.mul_inv_cancel h (Rat.ne_of_gt hh)
    have hb : (((v^(j+1)-u^(j+1))/h)-c*u^j)*h =
        (v^(j+1)-u^(j+1))-h*(c*u^j) := by grind only [Rat.div_def]
    have hq := qabs_mul (((v^(j+1)-u^(j+1))/h)-c*u^j) h
    rw [hb, qabs_eq_self_of_nonneg (Rat.le_of_lt hh)] at hq
    rw [← hq] at H'
    apply ((rational_small ((v^(j+1)-u^(j+1))-h*(c*u^j))).mono
      (by change _ ≤ K.errorCoefficient*h*h; grind only)).congr
    apply arithmetic_identity
    intro s
    rfl
  · intro u v hu huv hv
    have H := RationalMajorant.qabs_pow_sub_le_lipschitz hC0 hC
      (gaussianBox_abs (by grind only : -C ≤ v) hv)
      (gaussianBox_abs hu (by grind only : u ≤ C)) j
    rw [qabs_eq_self_of_nonneg (by grind only : 0 ≤ v-u)] at H
    have H' := Rat.mul_le_mul_of_nonneg_left H hc
    apply ((rational_small (c*(v^j-u^j))).mono (by
      rw [qabs_mul, qabs_eq_self_of_nonneg hc]
      grind only)).congr
    apply arithmetic_identity
    intro s
    simp only [Value.rational, sub]
    change c*(v^j-u^j) = c*v^j-c*u^j
    grind only

private def gaussianMomentDerivative (j : Nat) (x : Rat) : Value :=
  sub (scale ((j+1 : Nat) : Rat) (gaussianMoment j x))
    (scale 2 (gaussianMoment (j+2) x))

private theorem gaussianMomentDerivative_bounded (j : Nat) (x : Rat) :
    Small (gaussianMomentDerivative j x)
      (((j+1 : Nat) : Rat)*gaussianMomentBound j + 2*gaussianMomentBound (j+2)) := by
  have hc : 0 ≤ ((j+1 : Nat) : Rat) := Rat.le_of_lt (Rat.natCast_pos.mpr (Nat.succ_pos _))
  have H := (scale_small (gaussianMoment_bounded j x) ((j+1 : Nat) : Rat)).add
    (scale_small (gaussianMoment_bounded (j+2) x) 2).neg
  rw [qabs_eq_self_of_nonneg hc, show qabs (2 : Rat) = 2 by decide +kernel] at H
  exact H.congr (arithmetic_identity _ _ (by
    intro s
    simp only [gaussianMomentDerivative, Value.add, Value.neg, sub]
    grind only))

private def gaussianMomentStep (C : Rat) (hC : 1 ≤ C) (j : Nat) :
    Step (gaussianMoment (j+1)) (gaussianMomentDerivative j) (-C) C := by
  let c : Rat := ((j+1 : Nat) : Rat)
  have hc : 0 ≤ c := Rat.le_of_lt (Rat.natCast_pos.mpr (Nat.succ_pos _))
  have hC0 : 0 ≤ C := by grind only
  have hpow (k : Nat) (t : Rat) (hl : -C ≤ t) (hr : t ≤ C) :
      Small (Value.rational (t^k)) (C^k) :=
    (rational_small _).mono (RationalMajorant.qabs_pow_le_pow hC0 (gaussianBox_abs hl hr) k)
  have hd (t : Rat) (hl : -C ≤ t) (hr : t ≤ C) :
      Small (Value.rational (c*t^j)) (c*C^j) := by
    apply (rational_small _).mono
    rw [qabs_mul, qabs_eq_self_of_nonneg hc]
    exact Rat.mul_le_mul_of_nonneg_left
      (RationalMajorant.qabs_pow_le_pow hC0 (gaussianBox_abs hl hr) j) hc
  let P := (rationalPowerStep C hC j).mul (gaussianBaseStep C hC)
    (C^(j+1)) gaussianDecay.bound (c*C^j) gaussianSampler.bound
    (Rat.pow_nonneg hC0) gaussianDecay.nonnegative
    (Rat.mul_nonneg hc (Rat.pow_nonneg hC0)) gaussianSampler.nonnegative
    (hpow (j+1)) (fun t _ _ => gaussianDecay.bounded t) hd (fun t _ _ => gaussianDrift_small t)
  apply P.congr
  · intro t
    apply arithmetic_identity
    intro s
    rfl
  · intro t
    apply arithmetic_identity
    intro s
    simp only [gaussianMomentDerivative, gaussianMoment, gaussianDrift, sub, scale,
      Value.mul, Value.add, Value.neg, Value.rational, Rat.pow_succ t (j+1)]
    grind only

private def gaussianMomentLipschitz (k : Nat) : Rat :=
  match k with
  | 0 => gaussianSampler.bound
  | j+1 => ((j+1 : Nat) : Rat)*gaussianMomentBound j + 2*gaussianMomentBound (j+2)

private theorem gaussianMomentLipschitz_nonneg (k : Nat) : 0 ≤ gaussianMomentLipschitz k := by
  cases k with
  | zero => exact gaussianSampler.nonnegative
  | succ j =>
    exact Rat.add_nonneg
      (Rat.mul_nonneg (Rat.le_of_lt (Rat.natCast_pos.mpr (Nat.succ_pos _))) (gaussianMomentBound_nonneg _))
      (Rat.mul_nonneg (by decide) (gaussianMomentBound_nonneg _))

private theorem gaussianMoment_lipschitz (k : Nat) {u v : Rat} (huv : u ≤ v) :
    Small (sub (gaussianMoment k v) (gaussianMoment k u)) (gaussianMomentLipschitz k*(v-u)) := by
  cases k with
  | zero =>
    apply (gaussianProfile_lipschitz huv).congr
    apply arithmetic_identity
    intro s
    simp [gaussianMoment, scale, sub, Rat.pow_zero, Rat.one_mul]
  | succ j =>
    let C := 1+qabs u+qabs v
    have hC : 1 ≤ C := by dsimp [C]; have := qabs_nonneg u; have := qabs_nonneg v; grind only
    have hu : -C ≤ u := by dsimp [C]; have := neg_qabs_le_self u; have := qabs_nonneg v; grind only
    have hv : v ≤ C := by dsimp [C]; have := self_le_qabs v; have := qabs_nonneg u; grind only
    let S := gaussianMomentStep C hC j
    exact lipschitz_of_firstOrder S.firstOrder S.error_nonnegative S.radius.property
      (fun t _ _ => gaussianMomentDerivative_bounded j t) u v hu huv hv

/-- Polynomial moments have certified global Lipschitz bounds and line tails. -/
def gaussianMomentSampler (k : Nat) : JointLipschitzSampler 1 where
  value x := gaussianMoment k (x (Fin.last 0))
  bound := gaussianMomentLipschitz k
  nonnegative := gaussianMomentLipschitz_nonneg k
  control := by
    intro x y δ _ hxy
    let u := x (Fin.last 0)
    let v := y (Fin.last 0)
    have H := hxy (Fin.last 0)
    have hp := gaussianMomentLipschitz_nonneg k
    change Small (sub (gaussianMoment k u) (gaussianMoment k v)) _
    by_cases huv : v ≤ u
    · exact (gaussianMoment_lipschitz k huv).mono
        (Rat.mul_le_mul_of_nonneg_left (show u-v ≤ δ by change u ≤ v+δ ∧ _ at H; grind only) hp)
    · have h' : u ≤ v := by grind only
      have h := (gaussianMoment_lipschitz k h').neg
      apply (h.mono (Rat.mul_le_mul_of_nonneg_left
        (show v-u ≤ δ by change _ ∧ v ≤ u+δ at H; grind only) hp)).congr
      apply arithmetic_identity
      intro s
      simp only [Value.neg, sub]
      grind only

def gaussianMomentDecay (k : Nat) : LineDecay (gaussianMomentSampler k) where
  bound := gaussianMomentBound k
  nonnegative := gaussianMomentBound_nonneg k
  bounded := gaussianMoment_bounded k
  outside := gaussianMoment_outside k

private def LineDecay.scaleRat {f : JointLipschitzSampler 1} (F : LineDecay f) (c : Rat) :=
  F.mulConstant (Value.rational c) (qabs c) (qabs_nonneg c) (rational_small c)

private def gaussianFirstDecay := (gaussianMomentDecay 1).scaleRat (-2)
private def gaussianSecondDecay :=
  ((gaussianMomentDecay 2).scaleRat 4).subtract (gaussianDecay.scaleRat 2)
private def gaussianThirdDecay :=
  ((gaussianMomentDecay 1).scaleRat 12).subtract ((gaussianMomentDecay 3).scaleRat 8)

private theorem gaussianRadius_ge_one (n : Nat) : (1 : Rat) ≤ ((n+1 : Nat) : Rat) :=
  Rat.natCast_le_natCast.mpr (Nat.succ_le_succ (Nat.zero_le n))

/-- The first three Gaussian derivatives are sampled by polynomial moments,
with the derivative law and quadratic decay certified for each sampler. -/
def gaussianDerivatives : LineDerivatives gaussianSampler where
  first := _
  second := _
  third := _
  firstDecay := gaussianFirstDecay
  secondDecay := gaussianSecondDecay
  thirdDecay := gaussianThirdDecay
  firstStep n := (gaussianBaseStep _ (gaussianRadius_ge_one n)).congr
    (fun _ => Same.refl _) (fun t => by
      apply arithmetic_identity
      intro s
      simp only [gaussianFirstDecay, LineDecay.scaleRat, LineDecay.mulConstant, constantMultiple,
        gaussianMomentDecay, gaussianMomentSampler, gaussianMoment, gaussianDrift,
        Value.mul, Value.rational, Value.neg, scale, Rat.pow_one]
      grind only)
  secondStep n := ((gaussianMomentStep _ (gaussianRadius_ge_one n) 0).scale (-2)).congr
    (fun t => by
      apply arithmetic_identity
      intro s
      rfl) (fun t => by
      apply arithmetic_identity
      intro s
      simp only [gaussianSecondDecay, LineDecay.scaleRat, LineDecay.mulConstant,
        LineDecay.subtract, constantMultiple, differenceSampler, gaussianMomentDecay,
        gaussianMomentSampler, gaussianSampler, gaussianMomentDerivative, gaussianMoment,
        Value.mul, Value.rational, sub, scale, Rat.pow_zero, Rat.one_mul]
      grind only)
  thirdStep n :=
    (((gaussianMomentStep _ (gaussianRadius_ge_one n) 1).scale 4).subtract
      ((gaussianBaseStep _ (gaussianRadius_ge_one n)).scale 2)).congr
      (fun t => by
        apply arithmetic_identity
        intro s
        rfl) (fun t => by
        apply arithmetic_identity
        intro s
        simp only [gaussianThirdDecay, LineDecay.scaleRat, LineDecay.mulConstant,
          LineDecay.subtract, constantMultiple, differenceSampler, gaussianMomentDecay,
          gaussianMomentSampler, gaussianMomentDerivative, gaussianMoment, gaussianDrift,
          Value.mul, Value.rational, Value.neg, sub, scale, Rat.pow_one]
        grind only)

/-- The concrete Gaussian Fourier transform satisfies the frequency ODE
under the negative-phase convention, for either component. -/
theorem gaussianSampler_transform_ode (cosine : Bool) (ξ : Rat) (eps : QPos) (h : Rat)
    (hh : qabs h ≤ (lineDerivativeModulus gaussianDecay (gaussianMomentDecay 1) eps).val) :
    Small (sub (sub (lineValue gaussianDecay cosine (ξ+h)) (lineValue gaussianDecay cosine ξ))
      (scale h (scale (-2*ξ)
        (Value.mul (Value.mul GeometricTrig.piValue GeometricTrig.piValue)
          (lineValue gaussianDecay cosine ξ))))) (eps.val*qabs h) :=
  gaussianTransform_ode gaussianDecay (gaussianMomentDecay 1) gaussianDerivatives.firstDecay
    (fun t => by
      apply arithmetic_identity
      intro s
      simp [gaussianMomentSampler, gaussianMoment, gaussianSampler, scale, Rat.pow_one])
    gaussianDerivatives.firstStep (fun _ => arithmetic_identity _ _ (fun _ => rfl)) cosine ξ eps h hh

/-- The independently computed full-line integral of the unit-height Gaussian. -/
def gaussianMass : Value :=
  parameter gaussianGrowingRadiusQuadratureFullLineRaw
    gaussianGrowingRadiusQuadratureFullLineRaw_valid_checked

private theorem gaussianMass_inv :
    Same (Value.mul gaussianMass
      (parameter gaussianFullLineMassReciprocalRaw gaussianFullLineMassReciprocalRaw_valid))
      (Value.rational 1) := by
  change (RealCompute.mul gaussianGrowingRadiusQuadratureFullLineRaw
    gaussianFullLineMassReciprocalRaw).Equiv (RealCompute.ofRat 1)
  intro n
  rw [RealCompute.compareAt_overlap_iff]
  let x := gaussianGrowingRadiusQuadratureFullLineRaw
  let b := gaussianFullLineMassLower
  let p := maxRat2 (x.compute n).lo b
  have hbp : 0 < b := gaussianFullLineMassLower_pos
  have hbh : b ≤ (x.compute n).hi := gaussianFullLineMassLower_le_fullLine_hi n
  have horder := RealCompute.interval_order_of_valid x
    gaussianGrowingRadiusQuadratureFullLineRaw_valid_checked n
  have hm : (x.compute n).lo ≤ p ∧ b ≤ p ∧ p ≤ (x.compute n).hi := by
    unfold p maxRat2
    split
    · rename_i h
      exact ⟨h, Rat.le_refl, hbh⟩
    · rename_i h
      exact ⟨Rat.le_refl, (Rat.le_total (a := (x.compute n).lo) (b := b)).resolve_left h, horder⟩
  have hp : 0 < p := by have := hm.2.1; grind only
  have hi : (gaussianFullLineMassReciprocalRaw.compute n).lo ≤ 1/p ∧
      1/p ≤ (gaussianFullLineMassReciprocalRaw.compute n).hi := by
    change ((x.positiveReciprocal b).compute n).lo ≤ 1/p ∧
      1/p ≤ ((x.positiveReciprocal b).compute n).hi
    rw [RealCompute.positiveReciprocal_compute _ _ hbp]
    exact ⟨reciprocal_mul_mono hp hm.2.2, Rat.le_refl⟩
  have H := QBox.mulRealInterval_contains hm.1 hm.2.2 hi.1 hi.2
  rw [show p*(1/p) = 1 by simp only [Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ (Rat.ne_of_gt hp)]] at H
  change (RealCompute.mulCompute x gaussianFullLineMassReciprocalRaw n).lo ≤ 1 ∧
    1 ≤ (RealCompute.mulCompute x gaussianFullLineMassReciprocalRaw n).hi
  simpa only [RealCompute.mulCompute] using H

private def gaussianUnscaled (x : Rat) : Value :=
  parameter (reciprocalGaussianRaw x) (reciprocalGaussianRaw_valid x)

/-- Multiplication by the computed mass recovers the unit-height Gaussian. -/
theorem gaussianProfile_mulMass (x : Rat) :
    Same (Value.mul gaussianMass (gaussianProfile x)) (gaussianUnscaled x) := by
  let c := parameter gaussianFullLineMassReciprocalRaw gaussianFullLineMassReciprocalRaw_valid
  let g := gaussianUnscaled x
  have H : Same (gaussianProfile x) (Value.mul c g) := Same.refl _
  refine ((Same.refl gaussianMass).mul H).trans ?_
  refine Same.trans (arithmetic_identity _ (Value.mul (Value.mul gaussianMass c) g) (by
    intro s
    simp only [Value.mul, Rat.mul_assoc])) ?_
  exact (gaussianMass_inv.mul (Same.refl g)).trans
    (arithmetic_identity _ _ (by
      intro s
      change 1 * g.sample s = g.sample s
      exact Rat.one_mul _))

private def gaussianMassBound : Rat := initialBound gaussianMass

private theorem gaussianMassBound_nonnegative : 0 ≤ gaussianMassBound :=
  initialBound_nonneg gaussianMass

private theorem gaussianMass_small : Small gaussianMass gaussianMassBound :=
  small_initialBound gaussianMass

def gaussianUnitSampler : JointLipschitzSampler 1 :=
  constantMultiple gaussianMass gaussianMassBound gaussianMassBound_nonnegative gaussianMass_small gaussianSampler

def gaussianUnitDecay : LineDecay gaussianUnitSampler :=
  gaussianDecay.mulConstant gaussianMass gaussianMassBound gaussianMassBound_nonnegative gaussianMass_small

def gaussianUnitDerivatives : LineDerivatives gaussianUnitSampler where
  first := _
  second := _
  third := _
  firstDecay := gaussianDerivatives.firstDecay.mulConstant gaussianMass gaussianMassBound
    gaussianMassBound_nonnegative gaussianMass_small
  secondDecay := gaussianDerivatives.secondDecay.mulConstant gaussianMass gaussianMassBound
    gaussianMassBound_nonnegative gaussianMass_small
  thirdDecay := gaussianDerivatives.thirdDecay.mulConstant gaussianMass gaussianMassBound
    gaussianMassBound_nonnegative gaussianMass_small
  firstStep n := (gaussianDerivatives.firstStep n).mul_constant gaussianMass gaussianMassBound
    gaussianMassBound_nonnegative gaussianMass_small
  secondStep n := (gaussianDerivatives.secondStep n).mul_constant gaussianMass gaussianMassBound
    gaussianMassBound_nonnegative gaussianMass_small
  thirdStep n := (gaussianDerivatives.thirdStep n).mul_constant gaussianMass gaussianMassBound
    gaussianMassBound_nonnegative gaussianMass_small

theorem gaussianUnit_at_zero : Same (gaussianUnitSampler.value (fun _ => 0)) (Value.rational 1) := by
  refine (gaussianProfile_mulMass 0).trans ?_
  have H := reciprocalGaussianRaw_equiv_expPowerSeries_neg_square 0
  rw [show -(0*0 : Rat) = 0 by decide +kernel] at H
  exact RealCompute.equiv_trans (reciprocalGaussianRaw_valid 0) (ExpProofs.expPowerSeries_valid 0)
    (RealCompute.ofRat_valid 1) H ExpProofs.expPowerSeries_zero_equiv_one

/-- The unit-height Gaussian has a decaying first spatial moment. -/
def gaussianUnitMomentDecay :=
  (gaussianMomentDecay 1).mulConstant gaussianMass gaussianMassBound
    gaussianMassBound_nonnegative gaussianMass_small

private theorem gaussianUnitMoment_spec (t : Rat) :
    Same
      ((constantMultiple gaussianMass gaussianMassBound gaussianMassBound_nonnegative gaussianMass_small
        (gaussianMomentSampler 1)).value (fun _ => t))
      (scale t (gaussianUnitSampler.value (fun _ => t))) := by
  apply arithmetic_identity
  intro s
  simp only [gaussianUnitSampler, gaussianMomentSampler, gaussianSampler, gaussianMoment,
    constantMultiple, Value.mul, scale, Rat.pow_one]
  grind only

/-- The Gaussian-subtracted quotient gives Melrose's origin reduction
for a sampler with a decaying moment and three certified derivatives.
The Gaussian normalization factor is its integrated cosine transform. -/
theorem melrose_origin_gaussian {f mf : JointLipschitzSampler 1}
    (F : LineDecay f) (JF : LineDerivatives f) (MF : LineDecay mf)
    (hf : ∀ t : Rat, Same (mf.value (fun _ => t)) (scale t (f.value (fun _ => t)))) :
    Same (lineValue (lineTransformDecay F MF JF.firstDecay JF.secondDecay hf JF.firstStep JF.secondStep true) true 0)
      (Value.mul (f.value (fun _ => 0))
        (lineValue (lineTransformDecay gaussianUnitDecay gaussianUnitMomentDecay
          gaussianUnitDerivatives.firstDecay gaussianUnitDerivatives.secondDecay
          gaussianUnitMoment_spec gaussianUnitDerivatives.firstStep gaussianUnitDerivatives.secondStep true) true 0)) := by
  let c := f.value (fun _ => 0)
  let W := MF.subtract (gaussianUnitMomentDecay.mulConstant c F.bound F.nonnegative (F.bounded 0))
  apply melrose_origin_normalized_profile F gaussianUnitDecay JF gaussianUnitDerivatives MF
    gaussianUnitMomentDecay hf gaussianUnitMoment_spec gaussianUnit_at_zero W
  intro t
  have H := (hf t).sub ((Same.refl c).mul (gaussianUnitMoment_spec t))
  apply H.trans
  apply arithmetic_identity
  intro s
  simp only [Value.mul, sub, scale]
  grind only

private theorem same_zero_of_same_neg (x : Value) (h : Same x (Value.neg x)) :
    Same x (Value.rational 0) := by
  have h₁ : Same x (scale (1/2) (sub x (Value.neg x))) := by
    apply arithmetic_identity
    intro s
    simp only [scale, sub, Value.neg]
    grind only
  have h₂ : Same (scale (1/2) (sub x x)) (Value.rational 0) := by
    apply arithmetic_identity
    intro s
    simp only [scale, sub, Value.rational, Rat.sub_self, Rat.mul_zero]
  exact h₁.trans ((((Same.refl x).sub h.symm).scale (1/2)).trans h₂)

private theorem same_scale_zero (x : Value) (a : Rat) (h : Same x (Value.rational 0)) :
    Same (scale a x) (Value.rational 0) :=
  (h.scale a).trans (arithmetic_identity _ _ (by
    intro s
    simp only [Value.rational, scale, Rat.mul_zero]))

/-- Reflection of finite symmetric intervals cancels the sine transform
of every even line sampler with certified tails. -/
theorem lineValue_sine_zero_of_even {f : JointLipschitzSampler 1} (D : LineDecay f)
    (heven : ∀ t : Rat, Same (f.value (fun _ => -t)) (f.value (fun _ => t)))
    (ξ : Rat) : Same (lineValue D false ξ) (Value.rational 0) := by
  have odd (q : Rat) : Same (GeometricTrig.valueFor false (-q)) (Value.neg (GeometricTrig.valueFor false q)) := by
    have h₁ := GeometricIntegralData.sine_difference q 0
    have h₂ := GeometricIntegralData.sine_difference 0 q
    rw [show q-0 = q by grind only] at h₁
    rw [show 0-q = -q by grind only] at h₂
    refine h₂.symm.trans (Same.trans ?_ h₁.neg)
    apply arithmetic_identity
    intro s
    simp only [Value.mul, Value.neg, sub]
    grind only
  let K := linePhaseSampler f (fun _ => ξ) false D.bound D.nonnegative (lineDecay_all D)
  let g := fun t : Rat => K.value (fun _ => t)
  have hodd (t : Rat) : Same (g (-t)) (Value.neg (g t)) := by
    have he : phase (fun _ : Fin 1 => ξ) (fun _ => -t) =
        -phase (fun _ : Fin 1 => ξ) (fun _ => t) := by
      simp only [phase, sumRat, Rat.zero_add, Rat.mul_neg]
    have h (q : Rat) : Same (trigValue false (-q)) (Value.neg (trigValue false q)) := by
      have H := odd q
      change (GeometricTrig.valueFor false (-q)).real.preferred.Equiv
        (RealCompute.neg (GeometricTrig.valueFor false q).real.preferred) at H
      rw [GeometricTrig.valueFor_raw, GeometricTrig.valueFor_raw] at H
      exact H
    change Same (Value.mul (f.value (fun _ => -t)) (trigValue false (phase (fun _ => ξ) (fun _ => -t))))
      (Value.neg (Value.mul (f.value (fun _ => t)) (trigValue false (phase (fun _ => ξ) (fun _ => t)))))
    rw [he]
    exact ((heven t).mul (h _)).trans
      (arithmetic_identity _ _ (by intro s; simp only [Value.mul, Value.neg]; grind only))
  have hzero (n : Nat) : Same (expandingComponent f (fun _ => ξ) false n) (Value.rational 0) := by
    let r := radius n
    have hr := radius_pos n
    let F := lineData K (a := -r) (b := r) (by grind only)
    let G : LipschitzQuadrature.Data (fun t => g (-r+2*r*t)) 0 1 := {
      ordered := by decide
      constant := F.constant*(2*r)
      nonnegative := Rat.mul_nonneg F.nonnegative (by grind only)
      lipschitz := by
        intro u v hu huv hv
        have h := K.control (fun _ => -r+2*r*v) (fun _ => -r+2*r*u)
          (2*r*(v-u)) (Rat.mul_nonneg (by grind only) (by grind only)) (fun _ => by
            have := Rat.mul_nonneg (show 0 ≤ 2*r by grind only) (show 0 ≤ v-u by grind only)
            constructor <;> grind only)
        rw [show K.bound*(2*r*(v-u)) = K.bound*(2*r)*(v-u) by grind only] at h
        exact h }
    let H : LipschitzQuadrature.Data (fun t => g (-r+2*r*(1-t))) 0 1 := {
      ordered := by decide
      constant := G.constant
      nonnegative := G.nonnegative
      lipschitz := by
        intro u v hu huv hv
        have h := (G.lipschitz (1-v) (1-u) (by grind only) (by grind only) (by grind only)).neg
        rw [show 1-u-(1-v) = v-u by grind only] at h
        exact h.congr (arithmetic_identity _ _ (by
          intro s
          simp only [Value.neg, sub]
          grind only)) }
    have hz : Same G.value (Value.neg G.value) := by
      have hneg : Same H.value G.neg.value := by
        change H.integral.Equiv G.neg.integral
        apply H.congr G.neg
        intro t _ _
        change Same (g (-r+2*r*(1-t))) (Value.neg (g (-r+2*r*t)))
        rw [show -r+2*r*(1-t) = -(-r+2*r*t) by grind only]
        exact hodd _
      have hneg' : Same G.neg.value (Value.neg G.value) := by
        change G.neg.integral.Equiv (-G.integral)
        exact G.neg_identity
      exact (G.reflect_unit H).symm.trans (hneg.trans hneg')
    refine (expandingComponent_line f _ _ _ D.nonnegative (lineDecay_all D) n).trans ?_
    have hF : Same F.value (scale (2*r) G.value) := by
      change F.integral.Equiv (RealCompute.scaleRat (2*r) G.integral)
      exact G.affine_identity F (c := -r) (s := 2*r) (by grind only)
        (by grind only) (by grind only) (fun _ _ _ => Same.refl _)
    exact hF.trans (same_scale_zero G.value (2*r) (same_zero_of_same_neg G.value hz))
  apply small_sub_zero_same
  apply EffectiveImproperIntegral.small_of_errors _ 0 (fun n => 4*D.bound/radius n)
    (shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl))
  intro n
  rw [Rat.zero_add]
  exact (lineTransform_error D (fun _ => ξ) false n).congr ((Same.refl _).sub (hzero n))

theorem gaussianSampler_sine_zero (ξ : Rat) :
    Same (lineValue gaussianDecay false ξ) (Value.rational 0) :=
  lineValue_sine_zero_of_even gaussianDecay (fun t => by
    change (gaussianNormalizedProfileRaw (-t)).Equiv (gaussianNormalizedProfileRaw t)
    rw [gaussianNormalizedProfileRaw_neg]
    exact RealCompute.equiv_refl _ (gaussianNormalizedProfileRaw_valid t)) ξ

/-- The vanishing sine component also holds at every represented frequency. -/
theorem gaussianSampler_sine_zero_at (x : RealCompute) (hx : x.Valid) :
    (lineTransformAt gaussianDecay false x hx).Equiv (RealCompute.ofRat 0) := by
  intro n
  let i := RawLimit.runningMax (frequencyStage gaussianDecay x hx) n
  let q := (x.compute i).lo
  let r := lineTransform gaussianDecay (fun _ => q) false
  have hr := lineTransform_valid gaussianDecay (fun _ => q) false
  have hbox := RawLimit.prefix_cover (frequencyTests_anti gaussianDecay false x hx)
    (lineAtBox_covers gaussianDecay false x hx) n r
    ⟨q, Rat.le_refl, RealCompute.interval_order_of_valid x hx i, rfl⟩
  have he : r.Equiv (RealCompute.ofRat 0) := gaussianSampler_sine_zero q
  have hzero : (RealCompute.ofRat 0).Valid := RealCompute.ofRat_valid 0
  apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
  exact ⟨RealCompute.le_trans hr hbox.1 (RealCompute.le_of_equiv hr hzero he) 0 0,
    RealCompute.le_trans hr (RealCompute.le_of_equiv hzero hr (RealCompute.equiv_symm he)) hbox.2 0 0⟩

private theorem small_zero_value : Small (Value.rational 0) 0 :=
  ⟨fun _ _ => Rat.le_refl, fun _ _ => Rat.le_refl⟩

private theorem small_sub_same {a b : Value} (h : Same a b) : Small (sub a b) 0 :=
  small_zero_value.congr (Same.symm (Same.trans (h.sub (Same.refl b))
    (RealCompute.sub_self_equiv_zero b.real.valid)))

private theorem small_unit_damping (C : Value) (B k : Rat) (_hB : 0 ≤ B)
    (hc : (RealCompute.ofRat 0).Le C.real.preferred) (hC : Small C B)
    (hk : 0 ≤ k) (hstep : k*B ≤ 1) :
    Small (sub (Value.rational 1) (scale k C)) 1 := by
  let X := sub (Value.rational 1) (scale k C)
  have points (n : Nat) : ∃ p, 0 ≤ p ∧ p ≤ 1 ∧
      (X.real.compute n).lo ≤ p ∧ p ≤ (X.real.compute n).hi := by
    obtain ⟨q,hq0,hqB,hql,hqr⟩ := RealIntervalImage.common_point C.real.valid
      (I := ⟨0,B⟩) ⟨hc,hC.2⟩ n
    have hm := QInterval.scaleRat_mem (r := k) ⟨hql,hqr⟩
    have hl := Rat.mul_nonneg hk hq0
    have hr := Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hqB hk) hstep
    change ((scale k C).real.compute n).lo ≤ k*q ∧ k*q ≤ ((scale k C).real.compute n).hi at hm
    refine ⟨1-k*q, by grind only, by grind only, ?_, ?_⟩
    · change 1-((scale k C).real.compute n).hi ≤ _
      grind only
    · change _ ≤ 1-((scale k C).real.compute n).lo
      grind only
  constructor
  · intro i j
    obtain ⟨p,hp,_,_,hh⟩ := points j
    exact Rat.le_trans (show -(1 : Rat) ≤ p by grind only) hh
  · intro i j
    obtain ⟨p,_,hp,hh,_⟩ := points i
    exact Rat.le_trans hh hp

/-- Uniqueness for the damped scalar equation on a rational unit interval.
The explicit Euler multipliers lie in the unit interval on sufficiently
fine meshes, so the endpoint error is at most the sum of the cell defects. -/
private theorem damped_mesh_zero (w : Rat → Value) (weight : Rat → Rat)
    (weightBounds : ∀ u : Rat, 0 ≤ u → u ≤ 1 → 0 ≤ weight u ∧ weight u ≤ 2)
    (C : Value) (B : Rat) (hB : 0 ≤ B)
    (hc : (RealCompute.ofRat 0).Le C.real.preferred) (hC : Small C B)
    (hzero : Same (w 0) (Value.rational 0))
    (H : ∀ eps : QPos, ∃ δ : QPos, ∀ u v : Rat, 0 ≤ u → u < v → v ≤ 1 →
      v-u ≤ δ.val → Small
        (Value.add (sub (w v) (w u)) (Value.mul (scale (weight u*(v-u)) C) (w u)))
        (eps.val*(v-u))) :
    Same (w 1) (Value.rational 0) := by
  have bound (eps : QPos) : Small (w 1) eps.val := by
    obtain ⟨δ,hδ⟩ := H eps
    let N := EulerReal.start (δ.val⁻¹ + 2*B)
    let r := (N : Rat)
    let d := r⁻¹
    have hr : 0 < r := EulerReal.start_positive _
    have hd : 0 < d := Rat.inv_pos.mpr hr
    have hinv : 0 < δ.val⁻¹ := Rat.inv_pos.mpr δ.property
    have hlarge : δ.val⁻¹ + 2*B < r := EulerReal.start_large _
    have hprod : r*d = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hr)
    have hstep : d ≤ δ.val := by
      have HH := Rat.mul_le_mul_of_nonneg_right (show δ.val⁻¹ ≤ r by grind only) (Rat.le_of_lt δ.property)
      have hcancel := Rat.inv_mul_cancel δ.val (Rat.ne_of_gt δ.property)
      apply Rat.le_of_mul_le_mul_right (c := r) _ hr
      grind only
    have hb : (2*B)*d ≤ 1 := by
      have hh := Rat.mul_le_mul_of_nonneg_right (show 2*B ≤ r by grind only) (Rat.le_of_lt hd)
      exact Rat.le_trans hh (by rw [hprod]; exact Rat.le_refl)
    let t (k : Nat) : Rat := (k : Rat)*d
    have tsucc (k : Nat) : t (k+1) = t k+d := by
      simp only [t, Rat.natCast_add]
      grind only
    have tzero : t 0 = 0 := by simp [t]
    have tlast : t N = 1 := hprod
    have tnonneg (k : Nat) : 0 ≤ t k := Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt hd)
    have tbound (k : Nat) (hk : k ≤ N) : t k ≤ 1 := by
      rw [← tlast]
      exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hk) (Rat.le_of_lt hd)
    have cell (k : Nat) (hk : k ≤ N) : Small (w (t k)) (eps.val*t k) := by
      induction k with
      | zero =>
        rw [tzero,Rat.mul_zero]
        exact small_zero_value.congr hzero.symm
      | succ k ih =>
        have h0 := tnonneg k
        have hu := tbound k (by omega)
        have hv := tbound (k+1) hk
        have hinc : t (k+1)-t k = d := by rw [tsucc]; grind only
        have he := hδ (t k) (t (k+1)) h0 (by grind only) hv (by rw [hinc]; exact hstep)
        rw [hinc] at he
        let k' := weight (t k)*d
        have hk' : 0 ≤ k' := Rat.mul_nonneg (weightBounds _ h0 hu).1 (Rat.le_of_lt hd)
        have hc' : k'*B ≤ 1 := by
          have hh := Rat.mul_le_mul_of_nonneg_right (weightBounds _ h0 hu).2
            (Rat.mul_nonneg (Rat.le_of_lt hd) hB)
          dsimp only [k']
          grind only
        have hprev := (small_unit_damping C B k' hB hc hC hk' hc').mul (ih (by omega))
        rw [Rat.one_mul] at hprev
        have ht : eps.val*d+eps.val*t k = eps.val*t (k+1) := by rw [tsucc]; grind only
        have hs := he.add hprev
        rw [ht] at hs
        apply hs.congr
        apply arithmetic_identity
        intro s
        simp only [Value.add, Value.mul, Value.rational, sub, scale, k']
        grind only
    simpa only [tlast, Rat.mul_one] using cell N (Nat.le_refl _)
  have h := EffectiveImproperIntegral.small_of_errors (w 1) 0
    (fun n => 1/((n+1 : Nat) : Rat))
    (shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl)) (fun n => by
      rw [Rat.zero_add]
      exact bound ⟨_, one_div_nat_pos (Nat.succ_pos n)⟩)
  exact small_sub_zero_same (h.congr (arithmetic_identity _ _ (by
    intro s
    simp only [sub, Value.rational, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero])))


private def piSquare : Value := Value.mul GeometricTrig.piValue GeometricTrig.piValue

private def gaussianRate (q : Rat) : Value := scale (q*q) piSquare

private theorem gaussianRate_nonneg (q : Rat) : (RealCompute.ofRat 0).Le (gaussianRate q).real.preferred := by
  apply le_of_samples (Value.rational 0) (gaussianRate q) 0
  intro n hn s hs
  change 0 ≤ (q*q)*(GeometricTrig.piValue.sample s*GeometricTrig.piValue.sample s)
  exact Rat.mul_nonneg (rat_square_nonneg_basic _) (rat_square_nonneg_basic _)

private theorem gaussianRate_small (q : Rat) : Small (gaussianRate q) ((q*q)*64) := by
  have H := scale_small (GeometricTrig.pi_small.mul GeometricTrig.pi_small) (q*q)
  simpa only [gaussianRate, piSquare, qabs_eq_self_of_nonneg (rat_square_nonneg_basic q),
    show (8 : Rat)*8 = 64 by decide +kernel] using H

private theorem gaussianExponential_remainder (q u v : Rat)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) (hh : v-u ≤ 1/2) :
    Small (Value.add
      (sub (EulerNegativeRate.evaluate (gaussianRate q) (v*v))
        (EulerNegativeRate.evaluate (gaussianRate q) (u*u)))
      (Value.mul (scale (2*u*(v-u)) (gaussianRate q))
        (EulerNegativeRate.evaluate (gaussianRate q) (u*u))))
      ((4*((q*q)*64)*((q*q)*64)+(q*q)*64)*(v-u)*(v-u)) := by
  let C := gaussianRate q
  let B := (q*q)*64
  let Z := EulerNegativeRate.evaluate C (u*u)
  let h := v-u
  have hp : 0 < h := by dsimp [h]; grind only
  have hB : 0 ≤ B := Rat.mul_nonneg (rat_square_nonneg_basic q) (by decide)
  have hs : 0 < v*v-u*u := Rat.mul_pos (show 0 < v-u by grind only) (show 0 < v+u by grind only) |> fun H => by grind only
  have hs' : v*v-u*u ≤ 2*h := by
    have H := Rat.mul_le_mul_of_nonneg_right (show v+u ≤ 2 by grind only) (Rat.le_of_lt hp)
    dsimp only [h] at *
    grind only
  have hlim : v*v-u*u ≤ 1 := by change h ≤ 1/2 at hh; grind only
  let S := EulerNegativeRate.step C B hB (gaussianRate_nonneg q) (gaussianRate_small q) 1
  have hv' : v*v ≤ 1 := by
    have H := Rat.mul_le_mul_of_nonneg_right hv (show 0 ≤ v by grind only)
    grind only
  have A := S.firstOrder (u*u) (v*v) (rat_square_nonneg_basic u) (by grind only) hv' hlim
  change Small (sub (sub (EulerNegativeRate.evaluate C (v*v)) Z)
    (scale (v*v-u*u) (Value.neg (Value.mul C Z)))) (B*B*(v*v-u*u)*(v*v-u*u)) at A
  have Zs := EulerNegativeRate.bounded C (gaussianRate_nonneg q) (u*u) (rat_square_nonneg_basic u)
  have D := scale_small ((gaussianRate_small q).mul Zs).neg (h*h)
  rw [qabs_eq_self_of_nonneg (rat_square_nonneg_basic h), Rat.mul_one] at D
  have H := A.add D
  have h₁ := Rat.mul_le_mul_of_nonneg_left hs' (Rat.mul_nonneg hB hB)
  have h₂ := Rat.mul_le_mul_of_nonneg_right h₁ (Rat.le_of_lt hs)
  have h₃ := Rat.mul_le_mul_of_nonneg_left hs' (Rat.mul_nonneg (Rat.mul_nonneg hB hB)
    (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 2) (Rat.le_of_lt hp)))
  apply (H.mono (show B*B*(v*v-u*u)*(v*v-u*u)+h*h*B ≤ (4*B*B+B)*h*h by grind only)).congr
  apply arithmetic_identity
  intro s
  simp only [Value.add, Value.mul, Value.neg, scale, sub]
  dsimp only [h]
  grind only

def gaussianCosineShape (x : RealCompute) (hx : x.Valid) : Value :=
  let X := parameter x hx
  let A := Value.neg (Value.mul piSquare (Value.mul X X))
  parameter (EulerReal.eval A.real.preferred) (EulerReal.eval_valid A.real.valid)

private theorem gaussianShape_rational (q : Rat) :
    Same (gaussianCosineShape (RealCompute.ofRat q) (RealCompute.ofRat_valid q))
      (EulerNegativeRate.evaluate (gaussianRate q) 1) := by
  apply EulerReal.eval_congr
    (Value.neg (Value.mul piSquare (Value.mul (parameter (RealCompute.ofRat q) (RealCompute.ofRat_valid q))
      (parameter (RealCompute.ofRat q) (RealCompute.ofRat_valid q))))).real.valid
    (EulerNegativeRate.argument (gaussianRate q) 1).real.valid
  have h : Same (parameter (RealCompute.ofRat q) (RealCompute.ofRat_valid q)) (Value.rational q) :=
    Same.refl (Value.rational q)
  refine Same.trans (Same.neg ((Same.refl piSquare).mul (h.mul h))) ?_
  apply arithmetic_identity
  intro s
  simp only [EulerNegativeRate.argument, gaussianRate, Value.neg, Value.mul, Value.rational, scale, Rat.one_mul]
  grind only

private theorem gaussianShape_initial (q : Rat) :
    Same (EulerNegativeRate.evaluate (gaussianRate q) 0) (Value.rational 1) := by
  have h : Same (EulerNegativeRate.argument (gaussianRate q) 0) (Value.rational 0) := by
    apply arithmetic_identity
    intro s
    simp only [EulerNegativeRate.argument, Value.neg, Value.rational, scale, Rat.zero_mul, Rat.neg_zero]
  exact RealCompute.equiv_trans (EulerReal.eval_valid (EulerNegativeRate.argument (gaussianRate q) 0).real.valid)
    (EulerReal.sample_valid 0) (RealCompute.ofRat_valid 1)
    (EulerReal.eval_congr (EulerNegativeRate.argument (gaussianRate q) 0).real.valid (RealCompute.ofRat_valid 0) h)
    EulerReal.sample_zero

/-- The cosine transform of the computed Gaussian has the exact exponential
shape. Its amplitude is its independently computed zero-frequency value. -/
theorem gaussianSampler_cosine_transform (q : Rat) :
    Same (lineValue gaussianDecay true q)
      (Value.mul (lineValue gaussianDecay true 0)
        (gaussianCosineShape (RealCompute.ofRat q) (RealCompute.ofRat_valid q))) := by
  let C := gaussianRate q
  let B := (q*q)*64
  let F (t : Rat) := lineValue gaussianDecay true (q*t)
  let A := lineValue gaussianDecay true 0
  let G (t : Rat) := EulerNegativeRate.evaluate C (t*t)
  let w (t : Rat) := sub (F t) (Value.mul A (G t))
  let M := 6*gaussianDecay.bound
  have hM : 0 ≤ M := Rat.mul_nonneg (by decide) gaussianDecay.nonnegative
  have hA : Small A M := lineTransform_small gaussianDecay (fun _ => 0) true
  have hB : 0 ≤ B := Rat.mul_nonneg (rat_square_nonneg_basic q) (by decide)
  have h0 : Same (w 0) (Value.rational 0) := by
    have hF : Same (F 0) A := by dsimp only [F,A]; rw [Rat.mul_zero]; exact Same.refl _
    have hG : Same (G 0) (Value.rational 1) := by
      dsimp only [G,C]
      rw [Rat.zero_mul]
      exact gaussianShape_initial q
    have H : Same (Value.mul A (G 0)) A := ((Same.refl A).mul hG).trans
      (arithmetic_identity _ _ (by intro s; simp only [Value.mul,Value.rational,Rat.mul_one]))
    exact (hF.sub H).trans (RealCompute.sub_self_equiv_zero A.real.valid)
  have hz : Same (w 1) (Value.rational 0) := by
    apply damped_mesh_zero w (fun t => 2*t) (by intro t ht ht1; constructor <;> grind only) C B hB (gaussianRate_nonneg q) (gaussianRate_small q) h0
    intro eps
    let e : QPos := ⟨eps.val/(2*(qabs q+1)), by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by have := qabs_nonneg q; grind only))⟩
    let r := lineDerivativeModulus gaussianDecay (gaussianMomentDecay 1) e
    let K := 4*B*B+B
    have hK : 0 ≤ K := Rat.add_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) hB) hB
    let d : QPos := ⟨eps.val/(2*(M*K+1)), by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by have := Rat.mul_nonneg hM hK; grind only))⟩
    let p : QPos := ⟨r.val/(qabs q+1), by
      rw [Rat.div_def]
      exact Rat.mul_pos r.property (Rat.inv_pos.mpr (by have := qabs_nonneg q; grind only))⟩
    have min_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < min a b := by
      rw [Rat.min_def]
      split <;> assumption
    let δ : QPos := ⟨min (1/2) (min p.val d.val),
      min_pos (by decide +kernel) (min_pos p.property d.property)⟩
    refine ⟨δ,?_⟩
    intro u v hu huv hv hd
    let h := v-u
    have hp : 0 < h := by dsimp [h]; grind only
    have hd' : h ≤ 1/2 ∧ h ≤ p.val ∧ h ≤ d.val := by
      change h ≤ min (1/2) (min p.val d.val) at hd
      rw [Rat.min_def, Rat.min_def] at hd
      split at hd <;> split at * <;> grind only
    have hq : qabs (q*h) ≤ r.val := by
      rw [qabs_mul]
      rw [qabs_eq_self_of_nonneg (Rat.le_of_lt hp)]
      have hq0 := qabs_nonneg q
      have H := Rat.mul_le_mul_of_nonneg_right hd'.2.1 (show 0 ≤ qabs q+1 by grind only)
      change h*(qabs q+1) ≤ (r.val/(qabs q+1))*(qabs q+1) at H
      rw [Rat.div_mul_cancel (show qabs q+1 ≠ 0 by grind only)] at H
      grind only
    have L := gaussianSampler_transform_ode true (q*u) e (q*h) hq
    rw [show q*u+q*h = q*v by dsimp [h]; grind only, qabs_mul,
      qabs_eq_self_of_nonneg (Rat.le_of_lt hp)] at L
    have L' : Small (Value.add (sub (F v) (F u))
        (Value.mul (scale (2*u*h) C) (F u))) (e.val*(qabs q*h)) := by
      apply L.congr
      apply arithmetic_identity
      intro s
      simp only [F,C,gaussianRate,piSquare,sub,scale,Value.mul,Value.add]
      grind only
    have R := gaussianExponential_remainder q u v hu huv hv hd'.1
    have H := L'.add (hA.mul R).neg
    have hhalf₁ : e.val*qabs q ≤ eps.val/2 := by
      have hq0 := qabs_nonneg q
      have he := e.property
      have H : e.val*(2*(qabs q+1)) = eps.val :=
        Rat.div_mul_cancel (by grind only)
      grind only
    have hhalf₂ : M*K*h ≤ eps.val/2 := by
      have hk := Rat.mul_nonneg hM hK
      have H := Rat.mul_le_mul_of_nonneg_right hd'.2.2 (show 0 ≤ 2*(M*K+1) by grind only)
      change h*(2*(M*K+1)) ≤ (eps.val/(2*(M*K+1)))*(2*(M*K+1)) at H
      rw [Rat.div_mul_cancel (show 2*(M*K+1) ≠ 0 by grind only)] at H
      grind only
    change Small _ (e.val*(qabs q*h)+M*(K*h*h)) at H
    have H' : e.val*(qabs q*h)+M*(K*h*h) ≤ eps.val*h := by
      have P := Rat.mul_le_mul_of_nonneg_right hhalf₁ (Rat.le_of_lt hp)
      have Q := Rat.mul_le_mul_of_nonneg_right hhalf₂ (Rat.le_of_lt hp)
      grind only
    apply (H.mono H').congr
    apply arithmetic_identity
    intro s
    simp only [w,F,G,C,Value.add,Value.mul,Value.neg,sub,scale]
    grind only
  have he : Same (F 1) (Value.mul A (G 1)) := small_sub_zero_same
    (small_zero_value.congr hz.symm)
  change Same (lineValue gaussianDecay true (q*1)) (Value.mul A (G 1)) at he
  rw [Rat.mul_one] at he
  refine he.trans ((Same.refl A).mul ?_)
  change Same (EulerNegativeRate.evaluate (gaussianRate q) ((1:Rat)*1)) _
  rw [Rat.one_mul]
  exact (gaussianShape_rational q).symm


private theorem euler_eval_cover_of_input {x y : RealCompute} (hx : x.Valid) (hy : y.Valid)
    (n : Nat) (H : RawLimit.InInterval y (x.compute n)) :
    RawLimit.InInterval (EulerReal.eval y) ((EulerReal.eval x).compute n) := by
  have lower (z : RealCompute) (hz : z.Valid) (k : Nat) :
      -(EulerReal.count (EulerReal.inputBound z) k : Rat) < (z.compute k).lo := by
    have h := (EulerReal.input_within hz k).1
    have h' := EulerReal.count_large (EulerReal.inputBound z) k
    grind only
  have upper (z : RealCompute) (hz : z.Valid) (k : Nat) :
      (z.compute k).hi < (EulerReal.count (EulerReal.inputBound z) k : Rat) := by
    have h := (EulerReal.input_within hz k).2
    have h' := EulerReal.count_large (EulerReal.inputBound z) k
    grind only
  constructor
  · intro i j
    change EulerFinite.lower (x.compute n).lo (EulerReal.count (EulerReal.inputBound x) n) ≤
      EulerFinite.upper (y.compute j).hi (EulerReal.count (EulerReal.inputBound y) j)
    exact EulerFinite.cross_bound (EulerReal.count_positive _ _) (EulerReal.count_positive _ _)
      (lower x hx n) (upper y hy j) (H.1 0 j)
  · intro j i
    change EulerFinite.lower (y.compute j).lo (EulerReal.count (EulerReal.inputBound y) j) ≤
      EulerFinite.upper (x.compute n).hi (EulerReal.count (EulerReal.inputBound x) n)
    exact EulerFinite.cross_bound (EulerReal.count_positive _ _) (EulerReal.count_positive _ _)
      (lower y hy j) (upper x hx n) (H.2 j 0)

private theorem gaussianCosineShape_cover (x : RealCompute) (hx : x.Valid) (n : Nat)
    (q : Rat) (hq : (x.compute n).lo ≤ q ∧ q ≤ (x.compute n).hi) :
    RawLimit.InInterval (gaussianCosineShape (RealCompute.ofRat q) (RealCompute.ofRat_valid q)).real.preferred
      ((gaussianCosineShape x hx).real.compute n) := by
  let X := parameter x hx
  let Q := parameter (RealCompute.ofRat q) (RealCompute.ofRat_valid q)
  let A := Value.neg (Value.mul piSquare (Value.mul X X))
  let a := Value.neg (Value.mul piSquare (Value.mul Q Q))
  have hP := RealIntervalImage.current piSquare.real.valid n
  have hQ : RawLimit.InInterval Q.real.preferred (X.real.compute n) := ⟨fun _ _ => hq.1,fun _ _ => hq.2⟩
  have H := RealIntervalImage.neg (RealIntervalImage.mul piSquare.real.valid (Value.mul Q Q).real.valid hP
    (RealIntervalImage.mul Q.real.valid Q.real.valid hQ hQ))
  exact euler_eval_cover_of_input A.real.valid a.real.valid n H

private theorem lineTransformAt_identify {f : JointLipschitzSampler 1} (D : LineDecay f) (c : Bool)
    (x : RealCompute) (hx : x.Valid) (Y : Value)
    (cover : ∀ n q, (x.compute n).lo ≤ q → q ≤ (x.compute n).hi →
      RawLimit.InInterval (lineTransform D (fun _ => q) c) (Y.real.compute n)) :
    (lineTransformAt D c x hx).Equiv Y.real.preferred := by
  intro n
  let j := max n (RawLimit.runningMax (frequencyStage D x hx) n)
  let q := (x.compute j).lo
  let r := lineTransform D (fun _ => q) c
  have hn := hx.2.1 n j (Nat.le_max_left _ _)
  have hm := hx.2.1 (RawLimit.runningMax (frequencyStage D x hx) n) j (Nat.le_max_right _ _)
  have H := RawLimit.prefix_cover (frequencyTests_anti D c x hx)
    (lineAtBox_covers D c x hx) n r ⟨q, hm.1, Rat.le_trans hm.2.1 hm.2.2, rfl⟩
  have K := cover n q hn.1 (Rat.le_trans hn.2.1 hn.2.2)
  have hr := lineTransform_valid D (fun _ => q) c
  exact (RealCompute.compareAt_overlap_iff _ _ n n).mpr
    ⟨RealCompute.le_trans hr H.1 K.2 0 0,RealCompute.le_trans hr K.1 H.2 0 0⟩

private theorem gaussian_transform_cover (A G g : Value) (z : Value) (n : Nat)
    (hs : RawLimit.InInterval g.real.preferred (G.real.compute n))
    (he : Same z (Value.mul A g)) :
    RawLimit.InInterval z.real.preferred ((Value.mul A G).real.compute n) := by
  have hp := RealIntervalImage.mul A.real.valid g.real.valid (RealIntervalImage.current A.real.valid n) hs
  exact RawLimit.inInterval_congr (Value.mul A g).real.valid z.real.valid he.symm hp

/-- The exact Gaussian cosine shape holds at every valid represented frequency. -/
theorem gaussianSampler_cosine_transform_at (x : RealCompute) (hx : x.Valid) :
    (lineTransformAt gaussianDecay true x hx).Equiv
      (Value.mul (lineValue gaussianDecay true 0) (gaussianCosineShape x hx)).real.preferred := by
  apply lineTransformAt_identify gaussianDecay true x hx
  intro n q hl hr
  exact gaussian_transform_cover (lineValue gaussianDecay true 0) (gaussianCosineShape x hx)
    (gaussianCosineShape (RealCompute.ofRat q) (RealCompute.ofRat_valid q)) (lineValue gaussianDecay true q)
    n (gaussianCosineShape_cover x hx n q ⟨hl,hr⟩) (gaussianSampler_cosine_transform q)

private def translateSampler (f : JointLipschitzSampler 1) (x : Rat) : JointLipschitzSampler 1 where
  value t := f.value (fun i => t i+x)
  bound := f.bound
  nonnegative := f.nonnegative
  control u v δ hδ h := f.control _ _ δ hδ (fun i => by
    have H := h i
    constructor <;> grind only)

private def translateDecay {f : JointLipschitzSampler 1} (F : LineDecay f) (x : Rat) :
    LineDecay (translateSampler f x) where
  bound := F.bound*(2*(1+qabs x))*(2*(1+qabs x))
  nonnegative := by
    have H := qabs_nonneg x
    exact Rat.mul_nonneg (Rat.mul_nonneg F.nonnegative (by grind only)) (by grind only)
  bounded t := (F.bounded (t+x)).mono (by
    have H := qabs_nonneg x
    have H' := F.nonnegative
    have C := Rat.mul_le_mul_of_nonneg_left (show 1 ≤ 2*(1+qabs x) by grind only) F.nonnegative
    have C' := Rat.mul_le_mul_of_nonneg_right C (show 0 ≤ 2*(1+qabs x) by grind only)
    grind only)
  outside t ht := by
    let r := qabs t
    let a := 2*(1+qabs x)
    have hr : 0 < r := by dsimp [r]; grind only
    have ha : 1 ≤ a := by dsimp [a]; have := qabs_nonneg x; grind only
    change Small (f.value (fun _ => t+x)) (F.bound*a*a/(r*r))
    have hp : 0 < r*r := Rat.mul_pos hr hr
    by_cases h : r ≤ a
    · apply (F.bounded (t+x)).mono
      apply Rat.le_of_mul_le_mul_right (c := r*r) _ hp
      rw [Rat.div_mul_cancel (Rat.ne_of_gt hp)]
      have H := rat_mul_le_mul_of_nonneg (Rat.le_of_lt hr) h (Rat.le_of_lt hr) h
      have H' := Rat.mul_le_mul_of_nonneg_left H F.nonnegative
      grind only
    · have hh := qabs_add_le (t+x) (-x)
      rw [qabs_neg, show t+x+ -x=t by grind only] at hh
      change r ≤ qabs (t+x)+qabs x at hh
      have hz : 1 ≤ qabs (t+x) := by dsimp only [a] at h; have := qabs_nonneg x; grind only
      have h₂ : r ≤ 2*qabs (t+x) := by dsimp only [a] at h; grind only
      have H := rat_mul_le_mul_of_nonneg (Rat.le_of_lt hr) h₂ (Rat.le_of_lt hr) h₂
      have ha₂ : 2 ≤ a := by dsimp only [a]; have := qabs_nonneg x; grind only
      have hv : 0 < qabs (t+x)*qabs (t+x) := Rat.mul_pos (by grind only) (by grind only)
      have H'' := rat_mul_le_mul_of_nonneg (show (0 : Rat) ≤ 2 by decide) ha₂
        (show (0 : Rat) ≤ 2 by decide) ha₂
      have HR : r*r ≤ (2*2)*(qabs (t+x)*qabs (t+x)) := by grind only
      have HK := Rat.mul_le_mul_of_nonneg_right H'' (Rat.le_of_lt hv)
      have H' := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans HR HK) F.nonnegative
      apply (F.outside (t+x) hz).mono
      apply Rat.le_of_mul_le_mul_right (c := r*r*(qabs (t+x)*qabs (t+x))) _
        (Rat.mul_pos hp hv)
      let z := qabs (t+x)*qabs (t+x)
      let rr := r*r
      change F.bound/z * (rr*z) ≤ F.bound*a*a/rr * (rr*z)
      have Hleft : F.bound/z * (rr*z) = F.bound*rr := by
        have eq := Rat.div_mul_cancel (a := F.bound) (Rat.ne_of_gt hv)
        grind only
      have Hright : F.bound*a*a/rr * (rr*z) = F.bound*(a*a*z) := by
        have eq := Rat.div_mul_cancel (a := F.bound*a*a) (Rat.ne_of_gt hp)
        grind only
      rw [Hleft,Hright]
      exact H' 

private def translatedStep {f d : JointLipschitzSampler 1}
    (S : ∀ n : Nat, Step (fun t => f.value (fun _ => t)) (fun t => d.value (fun _ => t))
      (-((n+1 : Nat) : Rat)) ((n+1 : Nat) : Rat)) (x : Rat) (n : Nat) :
    Step (fun t => (translateSampler f x).value (fun _ => t))
      (fun t => (translateSampler d x).value (fun _ => t)) (-radius n) (radius n) := by
  let m := EulerReal.start (radius n+qabs x)
  have hm := EulerReal.start_large (radius n+qabs x)
  have hm' : (m : Rat) ≤ radius m := by
    change (m : Rat) ≤ ((m+1 : Nat) : Rat)
    exact Rat.natCast_le_natCast.mpr (by omega)
  let T := S m
  have inLeft (t : Rat) (ht : -radius n ≤ t) : -radius m ≤ t+x := by
    have := neg_qabs_le_self x
    change radius n+qabs x < (m : Rat) at hm
    grind only
  have inRight (t : Rat) (ht : t ≤ radius n) : t+x ≤ radius m := by
    have := self_le_qabs x
    change radius n+qabs x < (m : Rat) at hm
    grind only
  refine ⟨T.error,T.error_nonnegative,T.radius,?_,T.variation,T.variation_nonnegative,?_⟩
  · intro u v hu huv hv h
    have he : v+x-(u+x) = v-u := by grind only
    have H := T.firstOrder (u+x) (v+x) (inLeft _ hu) (by grind only) (inRight _ hv) (by rwa [he])
    rw [he] at H
    exact H
  · intro u v hu huv hv
    have H := T.lipschitz (u+x) (v+x) (inLeft _ hu) (by grind only) (inRight _ hv)
    rw [show v+x-(u+x) = v-u by grind only] at H
    exact H

private def translateDerivatives {f : JointLipschitzSampler 1} (J : LineDerivatives f) (x : Rat) :
    LineDerivatives (translateSampler f x) where
  first := translateSampler J.first x
  second := translateSampler J.second x
  third := translateSampler J.third x
  firstDecay := translateDecay J.firstDecay x
  secondDecay := translateDecay J.secondDecay x
  thirdDecay := translateDecay J.thirdDecay x
  firstStep := translatedStep J.firstStep x
  secondStep := translatedStep J.secondStep x
  thirdStep := translatedStep J.thirdStep x

private def translateMoment {f m : JointLipschitzSampler 1} (F : LineDecay f) (M : LineDecay m)
    (x : Rat) :=
  (translateDecay M x).subtract ((translateDecay F x).scaleRat x)

private theorem translateMoment_spec {f m : JointLipschitzSampler 1} (x t : Rat)
    (hm : ∀ s : Rat, Same (m.value (fun _ => s)) (scale s (f.value (fun _ => s)))) :
    Same ((differenceSampler (translateSampler m x)
      (constantMultiple (Value.rational x) (qabs x) (qabs_nonneg x) (rational_small x)
        (translateSampler f x))).value (fun _ => t))
      (scale t ((translateSampler f x).value (fun _ => t))) := by
  apply Same.trans ((hm (t+x)).sub (Same.refl (Value.mul (Value.rational x) (f.value (fun _ => t+x)))))
  apply arithmetic_identity
  intro s
  simp only [sub, Value.mul, Value.rational, scale, translateSampler]
  grind only

private theorem quadrature_edge_error {f : JointLipschitzSampler 1}
    (M R x : Rat) (hR : 0 < R) (hR' : 2*(1+qabs x) ≤ R)
    (H : ∀ t, 1 ≤ qabs t → Small (f.value (fun _ => t)) (M/(qabs t*qabs t))) (hM : 0 ≤ M) :
    Small (sub (lineData f (a := -R+x) (b := R+x) (by grind only)).value
      (lineData f (a := -R) (b := R) (by grind only)).value)
      (2*qabs x*(M/((R/2)*(R/2)))) := by
  let c := R/2
  have hc : 0 < c := by dsimp [c]; grind only
  have hx : qabs x ≤ c := by have := qabs_nonneg x; dsimp [c]; grind only
  have hc₁ : 1 ≤ c := by have := qabs_nonneg x; dsimp [c]; grind only
  have bound (t : Rat) (ht : c ≤ qabs t) : Small (f.value (fun _ => t)) (M/(c*c)) := by
    apply (H t (Rat.le_trans hc₁ ht)).mono
    have S := rat_mul_le_mul_of_nonneg (Rat.le_of_lt hc) ht (Rat.le_of_lt hc) ht
    have J := Rat.mul_le_mul_of_nonneg_left (reciprocal_mul_mono (Rat.mul_pos hc hc) S) hM
    simpa only [Rat.div_def, Rat.one_mul] using J
  let O := lineData f (a := -R) (b := R) (by grind only)
  let T := lineData f (a := -R+x) (b := R+x) (by grind only)
  change Small (sub T.value O.value) (2*qabs x*(M/(c*c)))
  by_cases h : 0 ≤ x
  · let L := lineData f (a := -R) (b := -R+x) (by grind only)
    let I := lineData f (a := -R+x) (b := R) (by
      have := self_le_qabs x; dsimp [c] at hx; grind only)
    let Q := lineData f (a := R) (b := R+x) (by grind only)
    have hO : Same O.value (Value.add L.value I.value) := L.append I O
    have hT : Same T.value (Value.add I.value Q.value) := I.append Q T
    have hl := L.small (M/(c*c)) (fun t _ ht => bound t (by
      have := neg_qabs_le_self t; have := self_le_qabs x; dsimp [c] at hx ⊢; grind only))
    have hq := Q.small (M/(c*c)) (fun t ht _ => bound t (by
      have := self_le_qabs t; dsimp [c]; grind only))
    change Small L.value ((-R+x- -R)*(M/(c*c))) at hl
    change Small Q.value ((R+x-R)*(M/(c*c))) at hq
    have E := hq.add hl.neg
    rw [show (R+x-R)*(M/(c*c))+(-R+x- -R)*(M/(c*c))=2*qabs x*(M/(c*c)) by
      rw [qabs_eq_self_of_nonneg h]; grind only] at E
    apply E.congr
    apply Same.trans ?_ (hT.sub hO).symm
    apply arithmetic_identity
    intro s
    simp only [Value.add, Value.neg, sub]
    grind only
  · have hn : x ≤ 0 := by grind only
    let L := lineData f (a := -R+x) (b := -R) (by grind only)
    let I := lineData f (a := -R) (b := R+x) (by
      have := neg_qabs_le_self x; dsimp [c] at hx; grind only)
    let Q := lineData f (a := R+x) (b := R) (by grind only)
    have hO : Same O.value (Value.add I.value Q.value) := I.append Q O
    have hT : Same T.value (Value.add L.value I.value) := L.append I T
    have hl := L.small (M/(c*c)) (fun t _ ht => bound t (by
      have := neg_qabs_le_self t; dsimp [c]; grind only))
    have hq := Q.small (M/(c*c)) (fun t ht _ => bound t (by
      have := self_le_qabs t; have := neg_qabs_le_self x; dsimp [c] at hx ⊢; grind only))
    change Small L.value ((-R-(-R+x))*(M/(c*c))) at hl
    change Small Q.value ((R-(R+x))*(M/(c*c))) at hq
    have E := hl.add hq.neg
    rw [show (-R-(-R+x))*(M/(c*c))+(R-(R+x))*(M/(c*c))=2*qabs x*(M/(c*c)) by
      rw [qabs_eq_neg_of_nonpos hn]; grind only] at E
    apply E.congr
    apply Same.trans ?_ (hT.sub hO).symm
    apply arithmetic_identity
    intro s
    simp only [Value.add, Value.neg, sub]
    grind only

private theorem lineValue_translate_cosine {f : JointLipschitzSampler 1} (F : LineDecay f) (x ξ : Rat) :
    Same (lineValue (translateDecay F x) true ξ)
      (Value.add (Value.mul (lineMode true x ξ) (lineValue F true ξ))
        (Value.mul (lineMode false x ξ) (lineValue F false ξ))) := by
  let T := translateDecay F x
  let a := lineMode true x ξ
  let b := lineMode false x ξ
  let C := linePhaseSampler f (fun _ => ξ) true F.bound F.nonnegative (lineDecay_all F)
  let S := linePhaseSampler f (fun _ => ξ) false F.bound F.nonnegative (lineDecay_all F)
  let G := linePhaseSampler (translateSampler f x) (fun _ => ξ) true T.bound T.nonnegative (lineDecay_all T)
  have ha : Small a 1 := (trig_small true _).congr (lineMode_same true x ξ).symm
  have hb : Small b 1 := (trig_small false _).congr (lineMode_same false x ξ).symm
  let P := differenceSampler (constantMultiple a 1 (by decide) ha C)
    (constantMultiple (Value.neg b) 1 (by decide) hb.neg S)
  have mode (t : Rat) :
      Same (G.value (fun _ => t)) (P.value (fun _ => t+x)) := by
    have he (c : Bool) (z : Rat) :
        Same (trigValue c z) (GeometricTrig.valueFor c z) := by
      change (GeometricTrig.sample c z).Equiv (GeometricTrig.valueFor c z).real.preferred
      rw [GeometricTrig.valueFor_raw]
      exact RealCompute.equiv_refl _ (GeometricTrig.sample_valid c z)
    have e₁ : phase (fun _ : Fin 1 => ξ) (fun _ => t) = (-2*ξ)*(t+x)-(-2*x)*ξ := by
      simp only [phase,sumRat,Rat.zero_add]
      grind only
    have e₂ : phase (fun _ : Fin 1 => ξ) (fun _ => t+x) = (-2*ξ)*(t+x) := by
      simp only [phase,sumRat,Rat.zero_add]
    have htrig := (GeometricIntegralData.cosine_difference ((-2*ξ)*(t+x)) ((-2*x)*ξ)).symm
    have ha' : Same a (GeometricTrig.valueFor true ((-2*x)*ξ)) := by
      apply arithmetic_identity
      intro s
      simp only [a,lineMode,GeometricFTCData.family,scale,Rat.pow_zero,Rat.one_mul]
    have hb' : Same b (GeometricTrig.valueFor false ((-2*x)*ξ)) := by
      apply arithmetic_identity
      intro s
      simp only [b,lineMode,GeometricFTCData.family,scale,Rat.pow_zero,Rat.one_mul]
    have H := (he true _).trans (e₁ ▸ htrig)
    have H' := H.trans ((ha'.symm.mul (he true _).symm).add (hb'.symm.mul (he false _).symm))
    refine ((Same.refl (f.value (fun _ => t+x))).mul H').trans ?_
    apply arithmetic_identity
    intro s
    simp only [G,P,constantMultiple,differenceSampler,C,S,linePhaseSampler,productSampler,
      Value.mul,Value.add,Value.neg,sub,e₂]
    grind only
  have bm (cosine : Bool) (t : Rat) (h : 1 ≤ qabs t) :
      Small ((linePhaseSampler f (fun _ => ξ) cosine F.bound F.nonnegative (lineDecay_all F)).value
        (fun _ => t)) (F.bound/(qabs t*qabs t)) := by
    simpa only [linePhaseSampler,productSampler,Rat.mul_one] using
      (F.outside t h).mul (trig_small cosine (phase (fun _ => ξ) (fun _ => t)))
  have bp (t : Rat) (h : 1 ≤ qabs t) :
      Small (P.value (fun _ => t)) ((2*F.bound)/(qabs t*qabs t)) := by
    have H := (ha.mul (bm true t h)).add (hb.mul (bm false t h))
    simp only [Rat.one_mul] at H
    apply (H.mono (by simp only [Rat.div_def]; grind only)).congr
    apply arithmetic_identity
    intro s
    simp only [P,differenceSampler,constantMultiple,Value.mul,Value.add,Value.neg,sub]
    grind only
  have bound (cosine : Bool) (t : Rat) :
      Small ((linePhaseSampler f (fun _ => ξ) cosine F.bound F.nonnegative (lineDecay_all F)).value
        (fun _ => t)) F.bound := by
    simpa only [linePhaseSampler,productSampler,Rat.mul_one] using
      (F.bounded t).mul (trig_small cosine (phase (fun _ => ξ) (fun _ => t)))
  have compact (n : Nat) (hn : 2*(1+qabs x) ≤ radius n) :
      Small (sub (expandingComponent (translateSampler f x) (fun _ => ξ) true n)
        (Value.add (Value.mul a (expandingComponent f (fun _ => ξ) true n))
          (Value.mul b (expandingComponent f (fun _ => ξ) false n))))
        (2*qabs x*((2*F.bound)/((radius n/2)*(radius n/2)))) := by
    let R := radius n
    have hR := radius_pos n
    let dG := lineData G (a := -R) (b := R) (by grind only)
    let dP := lineData P (a := -R+x) (b := R+x) (by grind only)
    let dO := lineData P (a := -R) (b := R) (by grind only)
    let dC := lineData C (a := -R) (b := R) (by grind only)
    let dS := lineData S (a := -R) (b := R) (by grind only)
    have hshift : Same dP.value (scale 1 dG.value) := by
      change dP.integral.Equiv (RealCompute.scaleRat 1 dG.integral)
      apply dG.affine_identity dP (c := x) (s := 1) (by decide) (by grind only) (by grind only)
      intro t _ _
      rw [show x+1*t=t+x by grind only]
      exact mode t
    have hi : Same dG.value dP.value := (hshift.trans (arithmetic_identity _ _ (by
      intro s
      simp only [scale,Rat.one_mul]))).symm
    let dA := (LipschitzQuadrature.constantData a (-R) R dC.ordered).mul dC 1 F.bound (by decide)
      F.nonnegative (fun _ _ _ => ha) (fun t _ _ => bound true t)
    let dB := (LipschitzQuadrature.constantData b (-R) R dS.ordered).mul dS 1 F.bound (by decide)
      F.nonnegative (fun _ _ _ => hb) (fun t _ _ => bound false t)
    have hO : Same dO.value (dA.add dB).value := by
      apply dO.congr (dA.add dB)
      intro t _ _
      apply arithmetic_identity
      intro s
      simp only [P,differenceSampler,constantMultiple,Value.mul,Value.add,Value.neg,sub]
      grind only
    have haC : Same dA.value (Value.mul a dC.value) :=
      dC.mul_constant_identity a F.bound 1 F.nonnegative (by decide) ha (fun t _ _ => bound true t)
    have hbS : Same dB.value (Value.mul b dS.value) :=
      dS.mul_constant_identity b F.bound 1 F.nonnegative (by decide) hb (fun t _ _ => bound false t)
    have hAB : Same (dA.add dB).value (Value.add dA.value dB.value) := dA.add_identity dB
    have htarget := hO.trans (hAB.trans (haC.add hbS))
    have hC : Same (expandingComponent f (fun _ => ξ) true n) dC.value :=
      expandingComponent_line f _ _ _ F.nonnegative (lineDecay_all F) n
    have hS : Same (expandingComponent f (fun _ => ξ) false n) dS.value :=
      expandingComponent_line f _ _ _ F.nonnegative (lineDecay_all F) n
    have hG : Same (expandingComponent (translateSampler f x) (fun _ => ξ) true n) dG.value :=
      expandingComponent_line _ _ _ _ T.nonnegative (lineDecay_all T) n
    exact (quadrature_edge_error (2*F.bound) R x hR hn bp (Rat.mul_nonneg (by decide) F.nonnegative)).congr
      ((hG.trans hi).symm.sub (htarget.trans (((Same.refl a).mul hC.symm).add ((Same.refl b).mul hS.symm))))
  let N := EulerReal.start (2*(1+qabs x))
  let r (n : Nat) := radius (N+n)
  have large (n : Nat) : 2*(1+qabs x) ≤ r n := by
    have H := EulerReal.start_large (2*(1+qabs x))
    have K : (N : Rat) ≤ r n := Rat.natCast_le_natCast.mpr (by
      change N ≤ N+n+1
      omega)
    change _ < (N : Rat) at H
    grind only
  let k := 4*T.bound + 8*F.bound + 16*qabs x*F.bound
  have hk : 0 ≤ k := Rat.add_nonneg (Rat.add_nonneg (Rat.mul_nonneg (by decide) T.nonnegative)
    (Rat.mul_nonneg (by decide) F.nonnegative))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (qabs_nonneg x)) F.nonnegative)
  apply small_sub_zero_same
  apply EffectiveImproperIntegral.small_of_errors _ 0 (fun n => k/radius n)
    (shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl))
  intro n
  rw [Rat.zero_add]
  let j := N+n
  have Hj := compact j (large n)
  have H := (lineTransform_error T (fun _ => ξ) true j).add
    (Hj.add ((ha.mul (lineTransform_error F (fun _ => ξ) true j)).neg.add
      (hb.mul (lineTransform_error F (fun _ => ξ) false j)).neg))
  simp only [Rat.one_mul] at H
  have hR := radius_pos j
  have hnR : radius n ≤ radius j := Rat.natCast_le_natCast.mpr (by dsimp only [j]; omega)
  have hR1 : 1 ≤ radius j := gaussianRadius_ge_one _
  have hsmall : 2*qabs x*(2*F.bound/((radius j/2)*(radius j/2))) ≤
      (16*qabs x*F.bound)/radius j := by
    let s := radius j
    have hs : 0 < s := hR
    have ha : 0 ≤ 16*qabs x*F.bound := Rat.mul_nonneg
      (Rat.mul_nonneg (by decide) (qabs_nonneg x)) F.nonnegative
    let C₀ := 16*qabs x*F.bound
    have hs₂ : 0 < s*s := Rat.mul_pos hs hs
    have hh : (s/2)*(s/2) = (s*s)/4 := by
      simp only [Rat.div_def]
      have h₄ : (2:Rat)⁻¹*(2:Rat)⁻¹ = (4:Rat)⁻¹ := by decide +kernel
      grind only
    have he : 2*qabs x*(2*F.bound/((s/2)*(s/2))) = C₀/(s*s) := by
      rw [hh]
      simp only [Rat.div_def,Rat.inv_mul_rev,Rat.inv_inv]
      dsimp only [C₀]
      grind only
    rw [he]
    have hle : s ≤ s*s := by
      simpa only [Rat.one_mul] using Rat.mul_le_mul_of_nonneg_right hR1 (Rat.le_of_lt hs)
    have hh := Rat.mul_le_mul_of_nonneg_left (reciprocal_mul_mono hs hle) ha
    simpa only [Rat.div_def,Rat.one_mul] using hh
  have htotal : 4*T.bound/radius j+
      (2*qabs x*(2*F.bound/((radius j/2)*(radius j/2)))+
        (4*F.bound/radius j+4*F.bound/radius j)) ≤ k/radius n := by
    have hb := Rat.mul_le_mul_of_nonneg_left (reciprocal_mul_mono (radius_pos n) hnR) hk
    dsimp only [k] at *
    simp only [Rat.div_def,Rat.one_mul] at *
    grind only
  apply (H.mono htotal).congr
  apply arithmetic_identity
  intro s
  let A₀ := (lineValue T true ξ).sample s
  let A₁ := (expandingComponent (translateSampler f x) (fun _ => ξ) true j).sample s
  let B₀ := (lineValue F true ξ).sample s
  let B₁ := (expandingComponent f (fun _ => ξ) true j).sample s
  let C₀ := (lineValue F false ξ).sample s
  let C₁ := (expandingComponent f (fun _ => ξ) false j).sample s
  let p := a.sample s
  let q := b.sample s
  change (A₀-A₁)+((A₁-(p*B₁+q*C₁))+(-(p*(B₀-B₁)) + -(q*(C₀-C₁)))) =
    A₀-(p*B₀+q*C₀)
  grind only

private def transformDecayOf {f m : JointLipschitzSampler 1}
    (F : LineDecay f) (J : LineDerivatives f) (M : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t)))) (cosine : Bool) :=
  lineTransformDecay F M J.firstDecay J.secondDecay hm J.firstStep J.secondStep cosine

private def inverseLineValue {f m : JointLipschitzSampler 1}
    (F : LineDecay f) (J : LineDerivatives f) (M : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t)))) (x : Rat) : Value :=
  Value.add (lineValue (transformDecayOf F J M hm true) true x)
    (lineValue (transformDecayOf F J M hm false) false x)

private theorem inverseLineValue_translate {f m : JointLipschitzSampler 1}
    (F : LineDecay f) (J : LineDerivatives f) (M : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t)))) (x : Rat) :
    Same (lineValue (transformDecayOf (translateDecay F x) (translateDerivatives J x)
      (translateMoment F M x) (fun t => translateMoment_spec x t hm) true) true 0)
      (inverseLineValue F J M hm x) := by
  let T := transformDecayOf (translateDecay F x) (translateDerivatives J x)
    (translateMoment F M x) (fun t => translateMoment_spec x t hm) true
  let C := transformDecayOf F J M hm true
  let S := transformDecayOf F J M hm false
  let phaseC := linePhaseSampler _ (fun _ => x) true C.bound C.nonnegative (lineDecay_all C)
  let phaseS := linePhaseSampler _ (fun _ => x) false S.bound S.nonnegative (lineDecay_all S)
  have hpoint (ξ : Rat) : Same (lineValue (translateDecay F x) true ξ)
      (Value.add (phaseC.value (fun _ => ξ)) (phaseS.value (fun _ => ξ))) := by
    have h := lineValue_translate_cosine F x ξ
    have c := lineMode_same true x ξ
    have s := lineMode_same false x ξ
    refine h.trans (((c.mul (Same.refl _)).add (s.mul (Same.refl _))).trans ?_)
    apply arithmetic_identity
    intro z
    change (trigValue true (phase (fun _ => x) (fun _ => ξ))).sample z*(lineValue F true ξ).sample z+
      (trigValue false (phase (fun _ => x) (fun _ => ξ))).sample z*(lineValue F false ξ).sample z =
      (lineValue F true ξ).sample z*(trigValue true (phase (fun _ => x) (fun _ => ξ))).sample z+
      (lineValue F false ξ).sample z*(trigValue false (phase (fun _ => x) (fun _ => ξ))).sample z
    grind only
  have comp (n : Nat) :
      Same (expandingComponent (lineTransformSampler (translateDecay F x) (translateMoment F M x)
        (fun t => translateMoment_spec x t hm) true) (fun _ => 0) true n)
        (Value.add (expandingComponent (lineTransformSampler F M hm true) (fun _ => x) true n)
          (expandingComponent (lineTransformSampler F M hm false) (fun _ => x) false n)) := by
    let r := radius n
    have hr := radius_pos n
    let D₀ := linePhaseSampler _ (fun _ => 0) true T.bound T.nonnegative (lineDecay_all T)
    let D := lineData D₀ (a := -r) (b := r) (by grind only)
    let P := lineData phaseC (a := -r) (b := r) (by grind only)
    let Q := lineData phaseS (a := -r) (b := r) (by grind only)
    have hD : Same D.value (P.add Q).value := by
      apply D.congr (P.add Q)
      intro t _ _
      have ht : Same (trigValue true (phase (fun _ : Fin 1 => 0) (fun _ => t))) (Value.rational 1) := by
        change (GeometricTrig.sample true (phase (origin 1) (fun _ => t))).Equiv (RealCompute.ofRat 1)
        rw [phase_origin]
        exact GeometricTrig.sample_zero true
      refine (Same.trans (Y := Value.mul (lineValue (translateDecay F x) true t) (Value.rational 1))
        ((Same.refl _).mul ht) ?_)
      exact (arithmetic_identity _ (lineValue (translateDecay F x) true t) (by
        intro s
        simp only [Value.mul,Value.rational,Rat.mul_one])) |> fun h => Same.trans h (hpoint t)
    have hC : Same (expandingComponent _ (fun _ => x) true n) P.value :=
      expandingComponent_line _ _ _ _ C.nonnegative (lineDecay_all C) n
    have hS : Same (expandingComponent _ (fun _ => x) false n) Q.value :=
      expandingComponent_line _ _ _ _ S.nonnegative (lineDecay_all S) n
    have hT : Same (expandingComponent _ (fun _ => 0) true n) D.value :=
      expandingComponent_line _ _ _ _ T.nonnegative (lineDecay_all T) n
    have hsum : Same (P.add Q).value (Value.add P.value Q.value) := P.add_identity Q
    exact hT.trans (hD.trans (hsum.trans (hC.symm.add hS.symm)))
  change Same (lineValue T true 0) (Value.add (lineValue C true x) (lineValue S false x))
  apply small_sub_zero_same
  apply EffectiveImproperIntegral.small_of_errors _ 0 (fun n => (4*T.bound+4*C.bound+4*S.bound)/radius n)
    (shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl))
  intro n
  have H := ((lineTransform_error T (fun _ => 0) true n).congr
    ((Same.refl _).sub (comp n))).add
    (((lineTransform_error C (fun _ => x) true n).add (lineTransform_error S (fun _ => x) false n)).neg)
  have he : 4*T.bound/radius n+(4*C.bound/radius n+4*S.bound/radius n) =
      0+(4*T.bound+4*C.bound+4*S.bound)/radius n := by simp only [Rat.div_def]; grind only
  change Small _ (4*T.bound/radius n+(4*C.bound/radius n+4*S.bound/radius n)) at H
  rw [he] at H
  apply H.congr
  apply arithmetic_identity
  intro s
  let a := (lineValue T true 0).sample s
  let b := (lineValue C true x).sample s
  let c := (lineValue S false x).sample s
  let p := (expandingComponent (lineTransformSampler F M hm true) (fun _ => x) true n).sample s
  let q := (expandingComponent (lineTransformSampler F M hm false) (fun _ => x) false n).sample s
  change (a-(p+q))+ -((b-p)+(c-q)) = a-(b+c)
  grind only


/-- The Gaussian normalization left by Melrose's origin argument. -/
def melroseGaussianFactor : Value :=
  lineValue (transformDecayOf gaussianUnitDecay gaussianUnitDerivatives gaussianUnitMomentDecay
    gaussianUnitMoment_spec true) true 0

/-- The inverse quadrature, using the real and imaginary components of the
negative-phase transform, evaluated at a valid represented spatial point. -/
def inverseLineAt {f m : JointLipschitzSampler 1}
    (F : LineDecay f) (J : LineDerivatives f) (M : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (x : RealCompute) (hx : x.Valid) : Value :=
  let C := transformDecayOf F J M hm true
  let S := transformDecayOf F J M hm false
  Value.add (parameter (lineTransformAt C true x hx) (lineTransformAt_valid C true x hx))
    (parameter (lineTransformAt S false x hx) (lineTransformAt_valid S false x hx))

private theorem inverseLine_rational_scaled {f m : JointLipschitzSampler 1}
    (F : LineDecay f) (J : LineDerivatives f) (M : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t)))) (q : Rat) :
    Same (inverseLineValue F J M hm q) (Value.mul (f.value (fun _ => q)) melroseGaussianFactor) := by
  refine (inverseLineValue_translate F J M hm q).symm.trans ?_
  have H := melrose_origin_gaussian (translateDecay F q) (translateDerivatives J q) (translateMoment F M q)
    (fun t => translateMoment_spec q t hm)
  change Same _ (Value.mul (f.value (fun _ => 0+q)) melroseGaussianFactor) at H
  simpa only [transformDecayOf,Rat.zero_add] using H

private def spatialInputStage (f : JointLipschitzSampler 1) (x : RealCompute) (hx : x.Valid) (n : Nat) : Nat :=
  ConvexFTC.WidthSearch.stage x hx ⟨(frequencyTolerance n).val/(f.bound+1), by
    rw [Rat.div_def]
    exact Rat.mul_pos (frequencyTolerance n).property (Rat.inv_pos.mpr (by have := f.nonnegative; grind only))⟩

private def spatialBox (f : JointLipschitzSampler 1) (x : RealCompute) (hx : x.Valid) (n : Nat) : QInterval :=
  let q := (x.compute (spatialInputStage f x hx n)).lo
  let F := f.value (fun _ => q)
  let k := ConvexFTC.WidthSearch.stage F.real.preferred F.real.valid (frequencyTolerance n)
  QInterval.expand (F.real.compute k) (frequencyTolerance n).val

private def spatialTests (f : JointLipschitzSampler 1) (x : RealCompute) (n : Nat) (y : RealCompute) : Prop :=
  ∃ q, (x.compute n).lo ≤ q ∧ q ≤ (x.compute n).hi ∧ y = (f.value (fun _ => q)).real.preferred

private theorem spatialTests_anti (f : JointLipschitzSampler 1) (x : RealCompute) (hx : x.Valid)
    (i j : Nat) (hij : i ≤ j) (y : RealCompute) (h : spatialTests f x j y) : spatialTests f x i y := by
  obtain ⟨q,hq,hq',rfl⟩ := h
  have H := hx.2.1 i j hij
  exact ⟨q, Rat.le_trans H.1 hq, Rat.le_trans hq' H.2.2,rfl⟩

private theorem spatialBox_cover (f : JointLipschitzSampler 1) (x : RealCompute) (hx : x.Valid)
    (n : Nat) (y : RealCompute) (h : spatialTests f x (spatialInputStage f x hx n) y) :
    RawLimit.InInterval y (spatialBox f x hx n) := by
  obtain ⟨q,hq,hq',rfl⟩ := h
  let i := spatialInputStage f x hx n
  let p := (x.compute i).lo
  let e := (frequencyTolerance n).val
  let F := f.value (fun _ => p)
  have w := ConvexFTC.WidthSearch.stage_spec x hx ⟨e/(f.bound+1), by
    rw [Rat.div_def]
    exact Rat.mul_pos (frequencyTolerance n).property (Rat.inv_pos.mpr (by have := f.nonnegative; grind only))⟩
  change (x.compute i).hi-p ≤ e/(f.bound+1) at w
  change p ≤ q at hq
  change q ≤ (x.compute i).hi at hq'
  have hqp : 0 ≤ q-p := by grind only
  have h := f.control (fun _ => q) (fun _ => p) (q-p) hqp (fun _ => by constructor <;> grind only)
  have hb : f.bound*(q-p) ≤ e := by
    have hl := f.nonnegative
    have hh := Rat.mul_le_mul_of_nonneg_right w (show 0 ≤ f.bound+1 by grind only)
    rw [Rat.div_mul_cancel (by grind only : f.bound+1 ≠ 0)] at hh
    have J := Rat.mul_le_mul_of_nonneg_left (show q-p ≤ (x.compute i).hi-p by grind only)
      (show 0 ≤ f.bound+1 by grind only)
    grind only
  have H := h.mono hb
  exact RawLimit.inInterval_of_sub_bound (f.value (fun _ => q)).real.valid F.real.valid e
    H.1 H.2 (ConvexFTC.WidthSearch.stage F.real.preferred F.real.valid (frequencyTolerance n))

/-- Evaluate a line sampler at a represented spatial point. Every output
box covers the evaluations at all rational points in the selected input box. -/
def lineSamplerAt (f : JointLipschitzSampler 1) (x : RealCompute) (hx : x.Valid) : RealCompute :=
  RawLimit.prefixRaw (spatialBox f x hx)

theorem lineSamplerAt_valid (f : JointLipschitzSampler 1) (x : RealCompute) (hx : x.Valid) :
    (lineSamplerAt f x hx).Valid := by
  refine RawLimit.prefix_valid (spatialTests_anti f x hx) ?_ (spatialBox_cover f x hx) ?_
  · intro i
    let q := (x.compute i).lo
    exact ⟨(f.value (fun _ => q)).real.preferred,(f.value (fun _ => q)).real.valid,q,
      Rat.le_refl,RealCompute.interval_order_of_valid x hx i,rfl⟩
  · intro eps
    let e : QPos := ⟨eps.val/3, Rat.mul_pos eps.property (by decide +kernel)⟩
    obtain ⟨N,hN⟩ := RawLimit.allowance_shrinks e
    refine ⟨N,fun n hn => ?_⟩
    let F := f.value (fun _ => (x.compute (spatialInputStage f x hx n)).lo)
    let k := ConvexFTC.WidthSearch.stage F.real.preferred F.real.valid (frequencyTolerance n)
    have h := ConvexFTC.WidthSearch.stage_spec F.real.preferred F.real.valid (frequencyTolerance n)
    have H := hN n hn
    change RawLimit.allowance n ≤ eps.val/3 at H
    change (F.real.compute k).hi-(F.real.compute k).lo ≤ RawLimit.allowance n at h
    change (F.real.compute k).hi+RawLimit.allowance n-((F.real.compute k).lo-RawLimit.allowance n) ≤ eps.val
    grind only

theorem lineSamplerAt_rational (f : JointLipschitzSampler 1) (q : Rat) :
    (lineSamplerAt f (RealCompute.ofRat q) (RealCompute.ofRat_valid q)).Equiv
      (f.value (fun _ => q)).real.preferred := by
  intro n
  have H := RawLimit.prefix_cover (spatialTests_anti f (RealCompute.ofRat q) (RealCompute.ofRat_valid q))
    (spatialBox_cover f (RealCompute.ofRat q) (RealCompute.ofRat_valid q)) n (f.value (fun _ => q)).real.preferred
    ⟨q,Rat.le_refl,Rat.le_refl,rfl⟩
  exact (RealCompute.compareAt_overlap_iff _ _ n n).mpr ⟨H.1 0 n,H.2 n 0⟩

theorem lineSamplerAt_congr (f : JointLipschitzSampler 1) {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (he : x.Equiv y) :
    (lineSamplerAt f x hx).Equiv (lineSamplerAt f y hy) := by
  intro n
  let i := RawLimit.runningMax (spatialInputStage f x hx) n
  let j := RawLimit.runningMax (spatialInputStage f y hy) n
  have H := (RealCompute.compareAt_overlap_iff x y i j).mp
    (RealCompute.allStagesOverlap_of_equiv hx hy he i j)
  change (x.compute i).lo ≤ (y.compute j).hi ∧ (y.compute j).lo ≤ (x.compute i).hi at H
  let q := max (x.compute i).lo (y.compute j).lo
  have h₁ : (x.compute i).lo ≤ q ∧ q ≤ (x.compute i).hi := by
    have := RealCompute.interval_order_of_valid x hx i
    unfold q
    grind
  have h₂ : (y.compute j).lo ≤ q ∧ q ≤ (y.compute j).hi := by
    have := RealCompute.interval_order_of_valid y hy j
    unfold q
    grind
  let r := f.value (fun _ => q)
  have hL := RawLimit.prefix_cover (spatialTests_anti f x hx) (spatialBox_cover f x hx)
    n r.real.preferred ⟨q,h₁.1,h₁.2,rfl⟩
  have hR := RawLimit.prefix_cover (spatialTests_anti f y hy) (spatialBox_cover f y hy)
    n r.real.preferred ⟨q,h₂.1,h₂.2,rfl⟩
  exact (RealCompute.compareAt_overlap_iff _ _ n n).mpr
    ⟨RealCompute.le_trans r.real.valid hL.1 hR.2 0 0,RealCompute.le_trans r.real.valid hR.1 hL.2 0 0⟩

/-- The inverse quadrature at any represented point is the original
sampler's value times Melrose's Gaussian normalization factor. -/
theorem inverseLineAt_eq_scaled {f m : JointLipschitzSampler 1}
    (F : LineDecay f) (J : LineDerivatives f) (M : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (x : RealCompute) (hx : x.Valid) :
    Same (inverseLineAt F J M hm x hx)
      (Value.mul (parameter (lineSamplerAt f x hx) (lineSamplerAt_valid f x hx)) melroseGaussianFactor) := by
  intro n
  let C := transformDecayOf F J M hm true
  let S := transformDecayOf F J M hm false
  let i := RawLimit.runningMax (frequencyStage C x hx) n
  let j := RawLimit.runningMax (frequencyStage S x hx) n
  let k := RawLimit.runningMax (spatialInputStage f x hx) n
  let l := max i (max j k)
  let q := (x.compute l).lo
  have atStage (m : Nat) (hm : m ≤ l) : (x.compute m).lo ≤ q ∧ q ≤ (x.compute m).hi := by
    have H := hx.2.1 m l hm
    exact ⟨H.1,Rat.le_trans H.2.1 H.2.2⟩
  have qi := atStage i (by dsimp [l]; omega)
  have qj := atStage j (by dsimp [l]; omega)
  have qk := atStage k (by dsimp [l]; omega)
  let c := lineValue C true q
  let s := lineValue S false q
  let g := f.value (fun _ => q)
  have hC := RawLimit.prefix_cover (frequencyTests_anti C true x hx) (lineAtBox_covers C true x hx)
    n c.real.preferred ⟨q,qi.1,qi.2,rfl⟩
  have hS := RawLimit.prefix_cover (frequencyTests_anti S false x hx) (lineAtBox_covers S false x hx)
    n s.real.preferred ⟨q,qj.1,qj.2,rfl⟩
  have hF := RawLimit.prefix_cover (spatialTests_anti f x hx) (spatialBox_cover f x hx)
    n g.real.preferred ⟨q,qk.1,qk.2,rfl⟩
  have hleft := RealIntervalImage.add c.real.valid s.real.valid hC hS
  have hright := RealIntervalImage.mul g.real.valid melroseGaussianFactor.real.valid hF
    (RealIntervalImage.current melroseGaussianFactor.real.valid n)
  let r := Value.add c s
  let v := Value.mul g melroseGaussianFactor
  let lhs := inverseLineAt F J M hm x hx
  let rhs := Value.mul (parameter (lineSamplerAt f x hx) (lineSamplerAt_valid f x hx)) melroseGaussianFactor
  change RawLimit.InInterval r.real.preferred (lhs.real.compute n) at hleft
  change RawLimit.InInterval v.real.preferred (rhs.real.compute n) at hright
  have H := RawLimit.inInterval_congr v.real.valid r.real.valid (inverseLine_rational_scaled F J M hm q).symm hright
  exact (RealCompute.compareAt_overlap_iff _ _ n n).mpr
    ⟨RealCompute.le_trans r.real.valid hleft.1 H.2 0 0,RealCompute.le_trans r.real.valid H.1 hleft.2 0 0⟩


private theorem gaussian_prefix_error (R : Rat) (hR : 0 ≤ R) (x : Rat) (hx : qabs x ≤ R)
    (N : Nat) (hN : R*R ≤ (((N+1 : Nat) : Rat)/2)) :
    Small (sub (gaussianUnscaled x) (Value.rational (gaussianEvenProfilePrefix N x)))
      (2*RationalMajorant.factorialTailTerm (R*R) N) := by
  let y := -(x*x)
  let e := expPowerSeries y
  let P := gaussianEvenProfilePrefix N x
  let E := 2*RationalMajorant.factorialTailTerm (R*R) N
  have hE : 0 ≤ E := Rat.mul_nonneg (by decide)
    (RationalMajorant.factorialTailTerm_nonneg (rat_square_nonneg_basic R) _)
  have hxy : qabs y ≤ R*R := by
    dsimp only [y]
    rw [qabs_neg,qabs_mul]
    exact rat_mul_le_mul_of_nonneg (qabs_nonneg x) hx (qabs_nonneg x) hx
  have ebox : RawLimit.InInterval e ⟨P-E,P+E⟩ := by
    have pt (k : Nat) : ∃ a : Rat, (e.compute k).lo ≤ a ∧ a ≤ (e.compute k).hi ∧
        qabs (a-P) ≤ E := by
      let j := max k N
      let t := expPowerSeriesTerms y j
      have ht : N ≤ t := by
        dsimp only [t,j,expPowerSeriesTerms]
        omega
      let a := ExpProofs.powerSeriesCenterAtTerms y t
      have hm := expPowerSeries_future_center_mem y (Nat.le_max_left k N)
      refine ⟨a,hm.1,hm.2,?_⟩
      obtain ⟨m,hm'⟩ := Nat.exists_eq_add_of_le ht
      have he : a-P = FiniteExponentialTaylor.remainderPartial y N m := by
        dsimp only [a,P]
        rw [gaussianEvenProfilePrefix_eq_powerSeriesCenterAtTerms]
        change FiniteExponentialProduct.factorialPrefix t y -
          FiniteExponentialProduct.factorialPrefix N y = _
        rw [hm']
        exact FiniteExponentialProduct.factorialPrefix_add_sub_eq_remainderPartial y N m
      rw [he]
      exact Rat.le_trans
        (FiniteExponentialTaylor.remainderPartial_abs_le_factorialTailPartial (rat_square_nonneg_basic R) hxy N m)
        (RationalMajorant.factorialTailPartial_bound (rat_square_nonneg_basic R) hN m)
    constructor
    · intro i j
      obtain ⟨a,_,ha,hb⟩ := pt j
      have h := neg_qabs_le_self (a-P)
      change P-E ≤ (e.compute j).hi
      grind only
    · intro i j
      obtain ⟨a,ha,_,hb⟩ := pt i
      have h := self_le_qabs (a-P)
      change (e.compute i).lo ≤ P+E
      grind only
  have hxbox := RawLimit.inInterval_congr (ExpProofs.expPowerSeries_valid y) (reciprocalGaussianRaw_valid x)
    (RealCompute.equiv_symm (reciprocalGaussianRaw_equiv_expPowerSeries_neg_square x)) ebox
  constructor
  · intro i j
    have H := hxbox.1 0 j
    change P-E ≤ ((reciprocalGaussianRaw x).compute j).hi at H
    change -E ≤ ((reciprocalGaussianRaw x).compute j).hi-P
    grind only
  · intro i j
    have H := hxbox.2 i 0
    change ((reciprocalGaussianRaw x).compute i).lo ≤ P+E at H
    change ((reciprocalGaussianRaw x).compute i).lo-P ≤ E
    grind only

private def gaussianPrefixPrimitive (n : Nat) (t : Rat) : Value :=
  Value.rational (gaussianEvenIntegralPrefix n t/2)

private def gaussianPrefixStep (R : Rat) (hR : 1 ≤ R) :
    (n : Nat) → Step (gaussianPrefixPrimitive n)
      (fun t => Value.rational (gaussianEvenProfilePrefix n t)) (-R) R
  | 0 => (Step.constant (Value.rational 0) (-R) R).congr
      (fun t => arithmetic_identity _ _ (by
        intro s
        simp only [gaussianPrefixPrimitive,gaussianEvenIntegralPrefix_zero,Value.rational,
          Rat.div_def,Rat.zero_mul]))
      (fun _ => Same.refl _)
  | n+1 => by
    let c := FormalPowerSeries.expCoeff n * (-1 : Rat)^n
    let d := ((2*n+1 : Nat) : Rat)
    let T := (rationalPowerStep R hR (2*n)).scale (c/d)
    apply (gaussianPrefixStep R hR n |>.add T).congr
    · intro t
      apply arithmetic_identity
      intro s
      simp only [gaussianPrefixPrimitive, Value.add, scale, Value.rational, gaussianEvenIntegralPrefix_succ]
      dsimp only [c,d]
      have he : (2:Rat)*(2:Rat)⁻¹=1 := by decide +kernel
      grind only [Rat.div_def]
    · intro t
      apply arithmetic_identity
      intro s
      simp only [Value.add, scale, Value.rational, gaussianEvenProfilePrefix_succ]
      change gaussianEvenProfilePrefix n t + (c/d)*(d*t^(2*n)) =
        gaussianEvenProfilePrefix n t + c*t^(2*n)
      have hd : 0 < d := Rat.natCast_pos.mpr (by omega)
      have he := Rat.mul_inv_cancel d (Rat.ne_of_gt hd)
      grind only [Rat.div_def]

private def gaussianPolynomialData (R : Rat) (hR : 1 ≤ R) (n : Nat) :
    LipschitzQuadrature.Data (fun t => Value.rational (gaussianEvenProfilePrefix n t)) (-R) R where
  ordered := by grind only
  constant := (gaussianPrefixStep R hR n).variation
  nonnegative := (gaussianPrefixStep R hR n).variation_nonnegative
  lipschitz := (gaussianPrefixStep R hR n).lipschitz

private theorem gaussianPrefix_evenPrimitive (n : Nat) (t : Rat) :
    gaussianEvenIntegralPrefix n (-t) = -gaussianEvenIntegralPrefix n t := by
  have pow_odd (k : Nat) : (-t)^(2*k+1) = -(t^(2*k+1)) := by
    induction k with
    | zero =>
      change (-t)^1 = -(t^1)
      simp only [Rat.pow_one]
    | succ k ih =>
      have h (x : Rat) : x^(2*(k+1)+1) = (x^(2*k+1)*x)*x := by
        rw [show 2*(k+1)+1=(2*k+1)+1+1 by omega]
        exact (Rat.pow_succ x ((2*k+1)+1)).trans (congrArg (fun z => z*x) (Rat.pow_succ x (2*k+1)))
      rw [h (-t),h t,ih]
      grind only
  induction n with
  | zero => simp only [gaussianEvenIntegralPrefix_zero,Rat.neg_zero]
  | succ n ih =>
    rw [gaussianEvenIntegralPrefix_succ,gaussianEvenIntegralPrefix_succ,ih,pow_odd]
    grind only [Rat.div_def]

private theorem gaussianPolynomial_integral (R : Rat) (hR : 1 ≤ R) (n : Nat) :
    Same (gaussianPolynomialData R hR n).value (Value.rational (gaussianEvenIntegralPrefix n R)) := by
  have H : Same (gaussianPolynomialData R hR n).value
      (sub (gaussianPrefixPrimitive n R) (gaussianPrefixPrimitive n (-R))) :=
    (gaussianPrefixStep R hR n).ftc (gaussianPolynomialData R hR n).hasIntegral
  apply H.trans
  apply arithmetic_identity
  intro s
  simp only [gaussianPrefixPrimitive, Value.rational, sub, gaussianPrefix_evenPrimitive]
  have he : (2:Rat)*(2:Rat)⁻¹ = 1 := by decide +kernel
  grind only [Rat.div_def]

private theorem gaussianRadius_integral (R : Rat) (hR : 1 ≤ R)
    (D : LipschitzQuadrature.Data gaussianUnscaled (-R) R) :
    Same D.value (parameter (gaussianRadiusTaylorQuadratureRaw R (by grind only))
      (gaussianRadiusTaylorQuadratureRaw_valid R (by grind only))) := by
  let R0 : 0 ≤ R := by grind only
  let Q := gaussianRadiusIntegratedSeriesRaw R R0
  let E := parameter Q (gaussianRadiusIntegratedSeriesRaw_valid R R0)
  let N := gaussianIntegralTailStart R
  let B := 2*RationalMajorant.factorialTailTerm (R*R) N
  have hB : 0 ≤ B := Rat.mul_nonneg (by decide)
    (RationalMajorant.factorialTailTerm_nonneg (rat_square_nonneg_basic R) _)
  have hRs := gaussianIntegralTailStart_satisfies R R0
  have he (n : Nat) : Small (sub D.value E)
      ((2*R*B)*((1 : Rat)/2)^(2*n) + (Q.compute n).width) := by
    let k := N+2*n
    let p := Value.rational (gaussianEvenIntegralPrefix k R)
    have hk := RationalMajorant.factorialTailStart_mono (R*R) N (2*n) hRs
    have Hb (t : Rat) (hl : -R ≤ t) (hr : t ≤ R) :
        Small (sub (gaussianUnscaled t) (Value.rational (gaussianEvenProfilePrefix k t)))
          (B*((1 : Rat)/2)^(2*n)) := by
      have H := RationalMajorant.factorialTailTerm_le_geometric_from_start
        (rat_square_nonneg_basic R) hRs (2*n)
      have H' := Rat.mul_le_mul_of_nonneg_left H (show (0 : Rat) ≤ 2 by decide)
      apply (gaussian_prefix_error R R0 t (qabs_le_of_neg_le_le hl hr) k hk).mono
      change 2*RationalMajorant.factorialTailTerm (R*R) (N+2*n) ≤ B*((1 : Rat)/2)^(2*n) at *
      dsimp only [B]
      grind only
    have Hd := D.difference_small (gaussianPolynomialData R hR k) _ Hb
    have H₁ : Small (sub D.value p) ((2*R*B)*((1 : Rat)/2)^(2*n)) := by
      have h : (R - -R)*(B*((1 : Rat)/2)^(2*n)) = (2*R*B)*((1 : Rat)/2)^(2*n) := by grind only
      rw [h] at Hd
      exact Hd.congr ((Same.refl _).sub (gaussianPolynomial_integral R hR k))
    have Qlo : (Q.compute n).lo = gaussianEvenIntegralPrefix k R := by
      unfold Q k N
      rw [gaussianRadiusIntegratedSeriesRaw_compute_eq_prefix_interval]
    have H₂ : Small (sub p E) (Q.compute n).width := by
      have H := RealIntervalImage.current E.real.valid n
      constructor
      · intro i j
        have h := H.2 j 0
        change (Q.compute j).lo ≤ (Q.compute n).hi at h
        change -(Q.compute n).width ≤ gaussianEvenIntegralPrefix k R-(Q.compute j).lo
        rw [← Qlo]
        unfold QInterval.width
        grind only
      · intro i j
        have h := H.1 0 i
        change (Q.compute n).lo ≤ (Q.compute i).hi at h
        have w := E.real.valid.1 n
        change 0 ≤ (Q.compute n).width at w
        change gaussianEvenIntegralPrefix k R-(Q.compute i).hi ≤ (Q.compute n).width
        rw [← Qlo]
        grind only
    exact (H₁.add H₂).congr (arithmetic_identity _ _ (by
      intro s
      simp only [Value.add,sub]
      grind only))
  have hs : ShrinksToZero (fun n => (2*R*B)*((1 : Rat)/2)^(2*n) + (Q.compute n).width) := by
    have hG : ShrinksToZero (fun n => (2*R*B)*((1 : Rat)/2)^(2*n)) := by
      have hC : 0 ≤ 2*R*B := Rat.mul_nonneg (Rat.mul_nonneg (by decide) R0) hB
      intro eps
      let j := RationalMajorant.halfDecayShift (2*R*B) eps
      refine ⟨j,fun n hn => ?_⟩
      obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show j ≤ 2*n by omega)
      change (2*R*B)*((1 : Rat)/2)^(2*n) ≤ eps.val
      rw [hk]
      exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left (Series.halfPow_add_le_left j k) hC)
        (RationalMajorant.halfDecayShift_spec hC eps)
    intro eps
    let e : QPos := ⟨eps.val/2, Rat.mul_pos eps.property (by decide +kernel)⟩
    obtain ⟨i,hi⟩ := hG e
    obtain ⟨j,hj⟩ := E.real.valid.2.2 e
    refine ⟨max i j,fun n hn => ?_⟩
    have A := hi n (by omega)
    have W := hj n (by omega)
    change 2*R*B* (1/2:Rat)^(2*n) ≤ e.val at A
    change (Q.compute n).width ≤ e.val at W
    change _ + _ ≤ eps.val
    dsimp only [e] at A W
    grind only
  have H := EffectiveImproperIntegral.small_of_errors (sub D.value E) 0 _ hs (fun n => by
    rw [Rat.zero_add]
    exact he n)
  exact (small_sub_zero_same H).trans (RealCompute.equiv_symm (gaussianRadiusTaylorQuadratureRaw_equiv_series R R0))

private theorem gaussianMass_tends :
    RawLimit.TendsTo (fun n => gaussianGrowingRadiusBoundedQuadratureRaw n)
      gaussianGrowingRadiusQuadratureFullLineRaw := by
  let P := gaussianGrowingRadiusQuadratureCandidate
  let a := gaussianGrowingRadiusQuadratureGluingRadius
  let M := gaussianGrowingRadiusQuadratureFullLineRaw
  have hv (n : Nat) : (gaussianGrowingRadiusBoundedQuadratureRaw n).Valid :=
    gaussianRadiusTaylorQuadratureRaw_valid _ _
  refine ⟨gaussianGrowingRadiusQuadratureFullLineRaw_valid_checked,hv,?_⟩
  intro m eps
  let E : QPos := ⟨eps.val/3, Rat.mul_pos eps.property (by decide +kernel)⟩
  obtain ⟨k,hk⟩ := gaussianGrowingRadiusQuadratureGluingRadius_shrinks E
  obtain ⟨j,hj⟩ := gaussianGrowingRadiusQuadratureCandidate_widths_shrink E
  let l := max m (max k j)
  refine ⟨l,fun n hn => ?_⟩
  have hml : m ≤ l := by dsimp [l]; omega
  have hkl : k ≤ l := by dsimp [l]; omega
  have hjl : j ≤ l := by dsimp [l]; omega
  have H := gaussianGrowingRadiusQuadrature_future_contained_of_annularOrder
    gaussianGrowingQuadratureAnnularOrder_checked l n hn
  have Hm := gaussianGrowingRadiusQuadratureFullLineRaw_contains_current l
  have Hn := (gaussianGrowingRadiusQuadratureFullLineRaw_valid_checked).2.1 m l hml
  have ha := hk l hkl
  have hw := hj l hjl
  change a l ≤ E.val at ha
  change (P.compute l).width ≤ E.val at hw
  change (M.compute l).lo ≤ (P.compute l).lo ∧ (P.compute l).hi ≤ (M.compute l).hi at Hm
  change (M.compute m).lo ≤ (M.compute l).lo ∧
    (M.compute l).lo ≤ (M.compute l).hi ∧ (M.compute l).hi ≤ (M.compute m).hi at Hn
  change (P.compute l).lo-a l ≤ (P.compute n).lo ∧ (P.compute n).hi ≤ (P.compute l).hi+a l at H
  apply RawLimit.inInterval_of_contains_compute (hv n) (gaussianGrowingRadiusInternalStage n)
  change (M.compute m).lo-eps.val ≤ (P.compute n).lo ∧ (P.compute n).hi ≤ (M.compute m).hi+eps.val
  have he := eps.property
  dsimp only [E] at ha
  constructor <;> grind only

/-- Compact integral of the unit-height Gaussian on the absolute dyadic
grid in the spatial variable. -/
def gaussianDyadicWindow (n : Nat) :
    LipschitzQuadrature.Data gaussianUnscaled (-radius n) (radius n) := by
  let R := radius n
  let G := lineData gaussianUnitSampler (a := -R) (b := R)
    (by have := radius_pos n; grind only)
  refine ⟨G.ordered, G.constant, G.nonnegative, ?_⟩
  intro u v hu huv hv
  exact (G.lipschitz u v hu huv hv).congr ((gaussianProfile_mulMass v).sub (gaussianProfile_mulMass u))

private theorem gaussianZeroMode_window (n : Nat) :
    Same (expandingComponent gaussianUnitSampler (fun _ => 0) true n)
      (gaussianDyadicWindow n).value := by
  let R := radius n
  have hR := radius_pos n
  let D := gaussianDyadicWindow n
  let G := lineData gaussianUnitSampler (a := -R) (b := R) D.ordered
  let P := linePhaseSampler gaussianUnitSampler (fun _ => 0) true gaussianUnitDecay.bound
    gaussianUnitDecay.nonnegative (lineDecay_all gaussianUnitDecay)
  let T := lineData P (a := -R) (b := R) (by grind only)
  refine (expandingComponent_line _ _ _ _ gaussianUnitDecay.nonnegative
    (lineDecay_all gaussianUnitDecay) n).trans (Same.trans (Y := G.value) (T.congr G ?_)
      (G.congr D (fun t _ _ => gaussianProfile_mulMass t)))
  intro t _ _
  have h : Same (trigValue true (phase (fun _ : Fin 1 => 0) (fun _ => t))) (Value.rational 1) := by
    change (GeometricTrig.sample true (phase (origin 1) (fun _ => t))).Equiv (RealCompute.ofRat 1)
    rw [phase_origin]
    exact GeometricTrig.sample_zero true
  exact (((Same.refl (gaussianUnitSampler.value (fun _ => t))).mul h).trans
    (arithmetic_identity _ _ (by intro s; simp only [Value.mul,Value.rational,Rat.mul_one])))

/-- The finite window error controls the dyadic improper Gaussian integral. -/
def gaussianDyadicImproper : EffectiveImproperIntegral.Data :=
  let D := lineTransformData gaussianUnitDecay (fun _ => 0) true
  { compact := fun n => (gaussianDyadicWindow n).value
    error := D.error
    nonnegative := D.nonnegative
    shrinks := D.shrinks
    tail := fun k n h => (line_annuli gaussianUnitDecay (fun _ => 0) true k n h).congr
      ((gaussianZeroMode_window n).sub (gaussianZeroMode_window k)) }

def gaussianDyadicExhaustion (n : Nat) : FunctionOnInterval :=
  LipschitzIntegralBounds.onInterval gaussianUnscaled (-radius n) (radius n)

theorem gaussianDyadic_hasIntegralLimit :
    Integral.HasIntegralLimit gaussianDyadicExhaustion gaussianDyadicImproper.raw :=
  gaussianDyadicImproper.hasIntegralLimit gaussianDyadicExhaustion (fun n => (gaussianDyadicWindow n).hasIntegral)

private theorem gaussianDyadicWindow_taylor (n : Nat) :
    (gaussianDyadicWindow n).integral.Equiv (gaussianGrowingRadiusBoundedQuadratureRaw n) :=
  gaussianRadius_integral (radius n) (gaussianRadius_ge_one n) (gaussianDyadicWindow n)

/-- The dyadic improper integral and the independent Taylor/quadrature mass agree. -/
theorem gaussianDyadic_equiv_mass : gaussianDyadicImproper.raw.Equiv gaussianMass.real.preferred :=
  RawLimit.unique gaussianDyadicImproper.tendsTo
    (RawLimit.congr_sequence gaussianMass_tends
      (fun n => (gaussianDyadicWindow n).hasIntegral.valid)
      (fun n => RealCompute.equiv_symm (gaussianDyadicWindow_taylor n)))

/-- The separately computed whole-line Gaussian mass equals the Fourier
quadrature of the unit-height Gaussian at zero frequency. -/
theorem gaussianUnit_zero_frequency_mass : Same (lineValue gaussianUnitDecay true 0) gaussianMass := by
  apply RawLimit.unique (lineTransform_tendsTo gaussianUnitDecay (fun _ => 0) true)
  apply RawLimit.congr_sequence gaussianMass_tends (fun n => (expandingComponent gaussianUnitSampler
    (fun _ => 0) true n).real.valid)
  intro n
  let Y := parameter (gaussianGrowingRadiusBoundedQuadratureRaw n)
    (gaussianRadiusTaylorQuadratureRaw_valid _ _)
  have h : Same (gaussianDyadicWindow n).value Y := gaussianDyadicWindow_taylor n
  exact (Same.trans (gaussianZeroMode_window n) h).symm

/-- The mass-normalized Gaussian has exactly unit zero-frequency amplitude. -/
theorem gaussianSampler_zero_frequency_one : Same (lineValue gaussianDecay true 0) (Value.rational 1) := by
  let X := lineValue gaussianDecay true 0
  let M := gaussianMass
  let C := parameter gaussianFullLineMassReciprocalRaw gaussianFullLineMassReciprocalRaw_valid
  have hA : Same (Value.mul M X) M :=
    (lineValue_mulConstant gaussianDecay M gaussianMassBound gaussianMassBound_nonnegative
      gaussianMass_small true 0).symm.trans gaussianUnit_zero_frequency_mass
  have hM : Same (Value.mul C M) (Value.rational 1) := by
    apply Same.trans (Y := Value.mul M C) _ gaussianMass_inv
    apply arithmetic_identity
    intro s
    simp only [Value.mul, Rat.mul_comm]
  have hCX := (Same.refl C).mul hA
  refine Same.trans (Y := Value.mul (Value.rational 1) X) ?_ ?_
  · apply arithmetic_identity
    intro s
    simp only [Value.mul,Value.rational,Rat.one_mul]
    rfl
  refine Same.trans (Y := Value.mul (Value.mul C M) X) (hM.symm.mul (Same.refl X)) ?_
  refine Same.trans (Y := Value.mul C (Value.mul M X)) ?_ (hCX.trans hM)
  apply arithmetic_identity
  intro s
  simp only [Value.mul, Rat.mul_assoc]

/-- The cosine transform of the mass-normalized Gaussian is
`exp (-π² ξ²)` at every valid represented frequency. -/
theorem gaussianSampler_cosine_transform_exact (x : RealCompute) (hx : x.Valid) :
    (lineTransformAt gaussianDecay true x hx).Equiv (gaussianCosineShape x hx).real.preferred := by
  let Y := parameter (lineTransformAt gaussianDecay true x hx) (lineTransformAt_valid gaussianDecay true x hx)
  let G := gaussianCosineShape x hx
  have H : Same Y (Value.mul (lineValue gaussianDecay true 0) G) := gaussianSampler_cosine_transform_at x hx
  refine H.trans ((gaussianSampler_zero_frequency_one.mul (Same.refl G)).trans ?_)
  apply arithmetic_identity
  intro s
  change 1 * G.sample s = G.sample s
  exact Rat.one_mul _

/-- The cosine transform of the unit-height Gaussian is its full-line mass
times the Gaussian frequency profile, also at nonrational frequencies. -/
theorem gaussianUnit_cosine_transform_exact (x : RealCompute) (hx : x.Valid) :
    (lineTransformAt gaussianUnitDecay true x hx).Equiv
      (Value.mul gaussianMass (gaussianCosineShape x hx)).real.preferred := by
  apply lineTransformAt_identify gaussianUnitDecay true x hx
  intro n q hl hr
  let G := gaussianCosineShape x hx
  let g := gaussianCosineShape (RealCompute.ofRat q) (RealCompute.ofRat_valid q)
  let z := lineValue gaussianUnitDecay true q
  have hg : Same (lineValue gaussianDecay true q) g := by
    refine (gaussianSampler_cosine_transform q).trans
      ((gaussianSampler_zero_frequency_one.mul (Same.refl g)).trans ?_)
    apply arithmetic_identity
    intro s
    change 1 * g.sample s = g.sample s
    exact Rat.one_mul _
  have he : Same z (Value.mul gaussianMass g) :=
    (lineValue_mulConstant gaussianDecay gaussianMass gaussianMassBound
      gaussianMassBound_nonnegative gaussianMass_small true q).trans
      ((Same.refl gaussianMass).mul hg)
  exact gaussian_transform_cover gaussianMass G g z n (gaussianCosineShape_cover x hx n q ⟨hl,hr⟩) he

/-- The scalar evaluation is the only additional input needed for inversion
of the supplied real-valued sampler at any valid represented point. -/
theorem inverseLineAt_eq_of_factor_one {f m : JointLipschitzSampler 1}
    (F : LineDecay f) (J : LineDerivatives f) (M : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (x : RealCompute) (hx : x.Valid) (h : Same melroseGaussianFactor (Value.rational 1)) :
    (inverseLineAt F J M hm x hx).real.preferred.Equiv (lineSamplerAt f x hx) := by
  let V := parameter (lineSamplerAt f x hx) (lineSamplerAt_valid f x hx)
  change Same (inverseLineAt F J M hm x hx) V
  refine Same.trans (inverseLineAt_eq_scaled F J M hm x hx)
    (Same.trans ((Same.refl V).mul h) ?_)
  apply arithmetic_identity
  intro s
  change V.sample s*1 = V.sample s
  exact Rat.mul_one _

/-! The Gaussian normalization uses a parameter integral on the unit interval.
Writing $F(r) = \int_0^r e^{-x^2}\,dx$, we compare $F(r)^2$ with
$\int_0^1 (1-e^{-r^2(1+t^2)})/(1+t^2)\,dt$. Their first-order increments
agree by the one-variable FTC and the substitution $x=rt$. The exponential
term in the parameter integral tends to zero with a rational error bound. -/

private abbrev expValue := EulerTaylorFTC.value

private theorem exp_nonpositive_small (q : Rat) (hq : q ≤ 0) : Small (expValue q) 1 :=
  EulerReal.negative_small (x := RealCompute.ofRat q) (RealCompute.ofRat_valid q) (fun _ _ => hq)

private theorem exp_zero_value : Same (expValue 0) (Value.rational 1) := EulerReal.sample_zero

private theorem exp_mul_nonpositive (x y : Rat) (hx : x ≤ 0) (hy : y ≤ 0) :
    Same (Value.mul (expValue x) (expValue y)) (expValue (x+y)) := by
  let X := EulerTaylorFTC.pulled x
  let Y := EulerTaylorFTC.pulled y
  let Z := EulerTaylorFTC.pulled (x+y)
  let w (t : Rat) := sub (Value.mul (X t) (Y t)) (Z t)
  let rate := -(x+y)
  have hr : 0 ≤ rate := by grind only
  have hx' : 0 ≤ -x := by grind only
  have hy' : 0 ≤ -y := by grind only
  have bx (t : Rat) (ht : 0 ≤ t) : Small (X t) 1 :=
    exp_nonpositive_small _ (by
      have := Rat.mul_nonneg hx' ht
      change x*t ≤ 0
      grind only)
  have by' (t : Rat) (ht : 0 ≤ t) : Small (Y t) 1 :=
    exp_nonpositive_small _ (by
      have := Rat.mul_nonneg hy' ht
      change y*t ≤ 0
      grind only)
  let S := (EulerTaylorFTC.pulledStep x).mul (EulerTaylorFTC.pulledStep y)
    1 1 (-x) (-y) (by decide) (by decide) hx' hy'
    (fun t ht _ => bx t ht) (fun t ht _ => by' t ht)
    (fun t ht _ => by
      simpa only [EulerTaylorFTC.derivative, qabs_eq_neg_of_nonpos hx, Rat.mul_one]
        using scale_small (bx t ht) x)
    (fun t ht _ => by
      simpa only [EulerTaylorFTC.derivative, qabs_eq_neg_of_nonpos hy, Rat.mul_one]
        using scale_small (by' t ht) y)
  let T := S.subtract (EulerTaylorFTC.pulledStep (x+y))
  have w0 : Same (w 0) (Value.rational 0) := by
    change Same (sub (Value.mul (expValue (x*0)) (expValue (y*0))) (expValue ((x+y)*0))) _
    simp only [Rat.mul_zero]
    refine ((exp_zero_value.mul exp_zero_value).sub exp_zero_value).trans ?_
    apply arithmetic_identity
    intro s
    simp only [Value.mul,Value.rational,sub,Rat.one_mul,Rat.sub_self]
  have w1 : Same (w 1) (Value.rational 0) := by
    apply damped_mesh_zero w (fun _ => 1) (by intros; decide +kernel)
      (Value.rational rate) rate hr (fun _ _ => hr) _ w0
    · intro eps
      let d := min T.radius.val (eps.val/(T.error+1))
      have hd' : 0 < T.error+1 := by have := T.error_nonnegative; grind only
      have hp : 0 < eps.val/(T.error+1) := Rat.mul_pos eps.property (Rat.inv_pos.mpr hd')
      have hd : 0 < d := by dsimp only [d]; rw [Rat.min_def]; split
                            · exact T.radius.property
                            · exact hp
      refine ⟨⟨d, hd⟩, fun u v hu huv hv h => ?_⟩
      have hrad : v-u ≤ T.radius.val := by dsimp only [d] at h; grind
      have herr : v-u ≤ eps.val/(T.error+1) := by dsimp only [d] at h; grind
      have hs : 0 ≤ v-u := by grind only
      have p := Rat.mul_le_mul_of_nonneg_right herr (Rat.le_of_lt hd')
      rw [Rat.div_mul_cancel (Rat.ne_of_gt hd')] at p
      have q := Rat.mul_le_mul_of_nonneg_right (show T.error*(v-u) ≤ eps.val by grind only) hs
      apply ((T.firstOrder u v hu huv hv hrad).mono q).congr
      apply arithmetic_identity
      intro s
      simp only [w,X,Y,Z,rate,EulerTaylorFTC.derivative,
        RealApproximationOrder.scale,sub,Value.add,Value.mul,Value.rational,Rat.one_mul]
      grind only
    · simpa only [qabs_eq_self_of_nonneg hr] using rational_small rate
  have hh := w1
  change Same (sub (Value.mul (expValue (x*1)) (expValue (y*1))) (expValue ((x+y)*1))) _ at hh
  simp only [Rat.mul_one] at hh
  exact small_sub_zero_same (small_zero_value.congr hh.symm)

private theorem gaussian_exp (t : Rat) : Same (gaussianUnscaled t) (expValue (-(t*t))) :=
  RealCompute.equiv_trans (reciprocalGaussianRaw_valid t) (ExpProofs.expPowerSeries_valid _)
    (EulerReal.sample_valid _) (reciprocalGaussianRaw_equiv_expPowerSeries_neg_square t)
    (EulerLegacySeries.adaptive_equiv_euler _)


private def gaussianParameter (r t : Rat) : Rat := r*r*(1+t*t)

private def gaussianWeighted (r t : Rat) : Value :=
  scale (ArctanGeometry.integralKernel t) (expValue (-(gaussianParameter r t)))

private theorem exp_neg_lipschitz (s t : Rat) (hs : 0≤s) (hst : s≤t) :
    Small (sub (expValue (-t)) (expValue (-s))) (t-s) := by
  by_cases he : s=t
  · subst t
    simpa only [Rat.sub_self] using small_zero_value.congr (by
      apply arithmetic_identity; intro n; simp only [sub, Value.rational, Rat.sub_self])
  have H := EulerTaylorFTC.supports (-t) (-s) (by grind only)
  have h : 0≤t-s := by grind only
  have L : FTCRealOrder.LE (Value.rational 0) (scale ((-s)-(-t)) (expValue (-t))) := by
    have z := FTCRealOrder.le_scale (x := Value.rational 0) (y := expValue (-t)) (EulerReal.eval_nonnegative
      (x := RealCompute.ofRat (-t)) (RealCompute.ofRat_valid _)) (show 0≤(-s)-(-t) by grind only)
    apply FTCRealOrder.le_congr z ?_ (Same.refl _)
    apply arithmetic_identity; intro n; simp only [scale, Value.rational, Rat.mul_zero]
  have U : Small (scale ((-s)-(-t)) (expValue (-s))) (t-s) := by
    have hq : (-s)-(-t)=t-s := by grind only
    simpa only [hq, qabs_eq_self_of_nonneg h, Rat.mul_one] using
      scale_small (exp_nonpositive_small (-s) (by grind only)) ((-s)-(-t))
  have V : Small (sub (expValue (-s)) (expValue (-t))) (t-s) := by
    refine ⟨?_, RealCompute.le_trans (scale ((-s)-(-t)) (expValue (-s))).real.valid H.2 U.2⟩
    intro i j
    have lp := RealCompute.le_trans (scale ((-s)-(-t)) (expValue (-t))).real.valid L H.1 0 j
    change 0 ≤ ((sub (expValue (-s)) (expValue (-t))).real.preferred.compute j).hi at lp
    change -(t-s) ≤ ((sub (expValue (-s)) (expValue (-t))).real.preferred.compute j).hi
    grind only
  apply V.neg.congr
  apply arithmetic_identity; intro n; simp only [sub, Value.neg]; grind only

private theorem exp_neg_remainder (s t : Rat) (hs : 0≤s) (hst : s<t) :
    Small (Value.add (sub (expValue (-t)) (expValue (-s))) (scale (t-s) (expValue (-s))))
      ((t-s)*(t-s)) := by
  let E := EulerReal.parameterRemainder 1 s t
  have H := EulerReal.negative_parameter_remainder 1 s t (by decide) hst
  have h : 0≤(t-s)*(t-s) := rat_square_nonneg_basic _
  have U : Small (scale (1*1*(t-s)*(t-s)) (EulerReal.negativeSample 1 s)) ((t-s)*(t-s)) := by
    simpa only [EulerReal.negativeSample, Rat.neg_mul, Rat.one_mul, qabs_eq_self_of_nonneg h, Rat.mul_one] using
      scale_small (exp_nonpositive_small (-s) (by grind only)) ((t-s)*(t-s))
  have B : Small E ((t-s)*(t-s)) := by
    refine ⟨?_, RealCompute.le_trans (scale (1*1*(t-s)*(t-s)) (EulerReal.negativeSample 1 s)).real.valid H.2 U.2⟩
    intro i j
    have lp := H.1 0 j
    change 0 ≤ (E.real.preferred.compute j).hi at lp
    change -((t-s)*(t-s)) ≤ (E.real.preferred.compute j).hi
    grind only
  apply B.congr
  apply arithmetic_identity; intro n
  simp only [E, EulerReal.parameterRemainder, EulerReal.negativeSample, Rat.neg_mul, Rat.one_mul,
    sub, scale, Value.neg, Value.add]
  grind only

private theorem gaussianParameter_nonnegative (r t : Rat) : 0≤gaussianParameter r t :=
  Rat.mul_nonneg (rat_square_nonneg_basic r)
    (Rat.le_of_lt (RationalCircle.Stage.one_add_square_pos t))

private def gaussianParameterData (r : Rat) :
    LipschitzQuadrature.Data (fun t => expValue (-(gaussianParameter r t))) 0 1 where
  ordered := by decide
  constant := 2*(r*r)
  nonnegative := Rat.mul_nonneg (by decide) (rat_square_nonneg_basic r)
  lipschitz := by
    intro u v hu huv hv
    have hs : 0≤u+v := by grind only
    have hd : 0≤v-u := by grind only
    have hp := Rat.mul_nonneg (rat_square_nonneg_basic r) hd
    have hdiff : gaussianParameter r v-gaussianParameter r u = (r*r)*(v-u)*(u+v) := by
      simp only [gaussianParameter]; grind only
    have hst : gaussianParameter r u≤gaussianParameter r v := by
      have := Rat.mul_nonneg hp hs
      grind only
    apply (exp_neg_lipschitz _ _ (gaussianParameter_nonnegative r u) hst).mono
    rw [hdiff]
    have H := Rat.mul_le_mul_of_nonneg_left (show u+v≤2 by grind only) hp
    grind only

private def gaussianKernelData := ArctanPositiveFTC.kernelData 0 1 (by decide) (by decide)

private def gaussianWeightedData (r : Rat) : LipschitzQuadrature.Data (gaussianWeighted r) 0 1 := by
  let M := gaussianKernelData.mul (gaussianParameterData r) 1 1 (by decide) (by decide)
    (fun t _ _ => by
      have h := Rat.le_of_lt (ArctanGeometry.integralKernel_pos t)
      exact (rational_small _).mono (by
        rw [qabs_eq_self_of_nonneg h]; exact ArctanGeometry.integralKernel_le_one t))
    (fun t _ _ => exp_nonpositive_small _ (by
      have := gaussianParameter_nonnegative r t; grind only))
  exact {
    ordered := M.ordered
    constant := M.constant
    nonnegative := M.nonnegative
    lipschitz := by
      intro u v hu huv hv
      apply (M.lipschitz u v hu huv hv).congr
      apply arithmetic_identity; intro n
      simp only [gaussianWeighted, ArctanPositiveFTC.kernel, Value.rational, Value.mul, scale, sub] }

private theorem gaussian_weighted_remainder (R u v t : Rat)
    (hu : 0≤u) (huv : u<v) (hv : v≤R) (ht : 0≤t) (ht1 : t≤1) :
    Small (Value.add (sub (gaussianWeighted v t) (gaussianWeighted u t))
      (scale (2*u*(v-u)) (expValue (-(gaussianParameter u t)))))
      (((4*R)*(4*R)+1)*((v-u)*(v-u))) := by
  let c := 1+t*t
  let k := ArctanGeometry.integralKernel t
  let d := v-u
  let s := gaussianParameter u t
  let z := gaussianParameter v t
  let U := expValue (-s)
  let Z := expValue (-z)
  have hc : 0<c := RationalCircle.Stage.one_add_square_pos _
  have hk : 0≤k := Rat.le_of_lt (ArctanGeometry.integralKernel_pos t)
  have hk1 : k≤1 := ArctanGeometry.integralKernel_le_one t
  have hkc : k*c=1 := by
    unfold k ArctanGeometry.integralKernel
    simpa only [Rat.div_def, Rat.one_mul, Rat.mul_comm c] using
      Rat.mul_inv_cancel c (Rat.ne_of_gt hc)
  have hd : 0<d := by grind only
  have hUV : 0<u+v := by grind only
  have hdiff : z-s=c*(u+v)*d := by
    simp only [s,z,c,d,gaussianParameter]; grind only
  have hp : 0<z-s := by rw [hdiff]; exact Rat.mul_pos (Rat.mul_pos hc hUV) hd
  have hz : s<z := by grind only
  have hc2 : c≤2 := by
    have := Rat.mul_le_mul_of_nonneg_right ht1 ht
    dsimp only [c]; grind only
  have hcr := rat_mul_le_mul_of_nonneg (Rat.le_of_lt hc) hc2 (Rat.le_of_lt hUV)
    (show u+v≤2*R by grind only)
  have hq : z-s≤4*R*d := by
    rw [hdiff]
    have := Rat.mul_le_mul_of_nonneg_right hcr (Rat.le_of_lt hd)
    grind only
  have hsquare := rat_mul_le_mul_of_nonneg (Rat.le_of_lt hp) hq (Rat.le_of_lt hp) hq
  have B := scale_small (exp_neg_remainder s z (gaussianParameter_nonnegative u t) hz) k
  rw [qabs_eq_self_of_nonneg hk] at B
  have HB : Small (scale k (Value.add (sub Z U) (scale (z-s) U))) ((4*R)*(4*R)*(d*d)) := by
    apply B.mono
    have h := Rat.mul_le_mul_of_nonneg_right hk1 (rat_square_nonneg_basic (z-s))
    grind only
  have D := (scale_small (exp_nonpositive_small (-s) (by
    have := gaussianParameter_nonnegative u t; grind only)) (d*d)).neg
  rw [qabs_eq_self_of_nonneg (rat_square_nonneg_basic d), Rat.mul_one] at D
  have H := HB.add D
  have he : (4*R)*(4*R)*(d*d)+d*d=((4*R)*(4*R)+1)*(d*d) := by grind only
  rw [he] at H
  apply H.congr
  apply arithmetic_identity; intro n
  have hkd : k*(z-s)=(u+v)*d := by rw [hdiff]; grind only
  simp only [gaussianWeighted, Value.add, Value.neg, sub, scale]
  change k*(Z.sample n-U.sample n+(z-s)*U.sample n)+(-(d*d*U.sample n)) =
    k*Z.sample n-k*U.sample n+2*u*d*U.sample n
  dsimp only [d] at *
  grind only


private theorem gaussian_small_one (t : Rat) : Small (gaussianUnscaled t) 1 :=
  (exp_nonpositive_small _ (by have := rat_square_nonneg_basic t; grind only)).congr (gaussian_exp t).symm

private def gaussianScaledData {R : Rat} (D : LipschitzQuadrature.Data gaussianUnscaled 0 R)
    (u : Rat) (hu : 0≤u) (huR : u≤R) :
    LipschitzQuadrature.Data (fun t => gaussianUnscaled (u*t)) 0 1 where
  ordered := by decide
  constant := D.constant*u
  nonnegative := Rat.mul_nonneg D.nonnegative hu
  lipschitz := by
    intro a b ha hab hb
    have H := D.lipschitz (u*a) (u*b) (Rat.mul_nonneg hu ha)
      (Rat.mul_le_mul_of_nonneg_left hab hu)
      (Rat.le_trans (by simpa only [Rat.mul_one] using Rat.mul_le_mul_of_nonneg_left hb hu) huR)
    exact H.mono (by grind only)

private theorem gaussian_parameter_integral {R : Rat} (D : LipschitzQuadrature.Data gaussianUnscaled 0 R)
    (u : Rat) (hu : 0≤u) (huR : u≤R) :
    Same (scale (2*u) (gaussianParameterData u).value)
      (Value.add (Value.mul (gaussianUnscaled u) (D.accumulated u))
        (Value.mul (D.accumulated u) (gaussianUnscaled u))) := by
  let Q := gaussianScaledData D u hu huR
  let f := gaussianUnscaled u
  let F := D.accumulated u
  let G := (gaussianParameterData u).value
  have hF : Same F (scale u Q.value) := by
    change Same (D.accumulated u) _
    simp only [LipschitzQuadrature.Data.accumulated, dif_pos (And.intro hu huR)]
    by_cases h : u=0
    · subst u
      exact (LipschitzQuadrature.zero_value _).trans (arithmetic_identity _ _ (by
        intro n; simp only [scale, Value.rational, Rat.zero_mul]))
    exact Q.affine_identity (D.restrict 0 u Rat.le_refl hu huR) (c := 0) (s := u) (by grind only)
      (by grind only) (by grind only) (by intro t _ _; simp only [Rat.zero_add]; exact Same.refl _)
  have hf := gaussian_small_one u
  have hQ (t : Rat) (_ : 0≤t) (_ : t≤1) := gaussian_small_one (u*t)
  let M := (LipschitzQuadrature.constantData f 0 1 Q.ordered).mul Q 1 1 (by decide)
    (by decide) (fun _ _ _ => hf) hQ
  have hG : Same G (Value.mul f Q.value) := by
    refine Same.trans (Y := M.value) ((gaussianParameterData u).congr M ?_)
      (Q.mul_constant_identity f 1 1 (by decide) (by decide) hf hQ)
    intro t _ _
    have h := exp_mul_nonpositive (-(u*u)) (-((u*t)*(u*t)))
      (by have := rat_square_nonneg_basic u; grind only)
      (by have := rat_square_nonneg_basic (u*t); grind only)
    have he : -(u*u)+(-((u*t)*(u*t))) = -(gaussianParameter u t) := by
      simp only [gaussianParameter]; grind only
    rw [he] at h
    exact Same.symm (((gaussian_exp u).mul (gaussian_exp (u*t))).trans h)
  refine (hG.scale (2*u)).trans (Same.trans ?_
    (((Same.refl f).mul hF.symm).add (hF.symm.mul (Same.refl f))))
  apply arithmetic_identity; intro n; simp only [scale, Value.add, Value.mul]; grind only

private def gaussianArctanDifference (u : Rat) : Value :=
  sub gaussianKernelData.value (gaussianWeightedData u).value

private theorem gaussian_integrated_remainder (R u v : Rat)
    (hu : 0≤u) (huv : u<v) (hv : v≤R) :
    Small (sub (sub (gaussianArctanDifference v) (gaussianArctanDifference u))
      (scale (v-u) (scale (2*u) (gaussianParameterData u).value)))
      (((4*R)*(4*R)+1)*((v-u)*(v-u))) := by
  let U := gaussianWeightedData u
  let V := gaussianWeightedData v
  let E := gaussianParameterData u
  let c := 2*u*(v-u)
  let W := U.subtract (E.scale c)
  let B := ((4*R)*(4*R)+1)*((v-u)*(v-u))
  have h := V.difference_small W B (by
    intro t ht ht1
    apply (gaussian_weighted_remainder R u v t hu huv hv ht ht1).congr
    apply arithmetic_identity; intro n
    simp only [c,sub,scale,Value.add]
    grind only)
  rw [show (1:Rat)-0=1 by grind only, Rat.one_mul] at h
  have hSum : Same W.value (sub U.value (E.scale c).value) := U.subtract_identity (E.scale c)
  have hScale : Same (E.scale c).value (scale c E.value) := E.scale_identity c
  have hW := hSum.trans ((Same.refl U.value).sub hScale)
  apply (h.congr ((Same.refl V.value).sub hW)).neg.congr
  apply arithmetic_identity
  intro n
  simp only [gaussianArctanDifference,U,V,E,c,Value.neg,sub,scale]
  grind only

private theorem gaussian_arctan_square {R : Rat} (D : LipschitzQuadrature.Data gaussianUnscaled 0 R)
    (t : Rat) (ht : 0≤t) (htR : t≤R) :
    Same (Value.mul (D.accumulated t) (D.accumulated t)) (gaussianArctanDifference t) := by
  let F := D.accumulated
  let J := gaussianArctanDifference
  let W (s : Rat) := sub (Value.mul (F s) (F s)) (J s)
  have hR := D.ordered
  have hF (u : Rat) (hu : 0≤u) (huR : u≤R) : Small (F u) R := by
    simp only [F, LipschitzQuadrature.Data.accumulated, dif_pos (And.intro hu huR)]
    exact ((D.restrict 0 u Rat.le_refl hu huR).small 1 (fun t _ _ => gaussian_small_one t)).mono
      (by simpa only [Rat.sub_eq_add_neg,Rat.neg_zero,Rat.add_zero,Rat.mul_one] using huR)
  let T := D.accumulationStep.mul D.accumulationStep R R 1 1 hR hR (by decide) (by decide)
    hF hF (fun s _ _ => gaussian_small_one s) (fun s _ _ => gaussian_small_one s)
  let K := LipschitzQuadrature.constantData (Value.rational 0) 0 t ht
  have hW : Same K.value (sub (W t) (W 0)) := by
    apply K.ftc_of_uniform_remainder
    intro eps
    let B := T.error+((4*R)*(4*R)+1)
    have hB : 0≤B := by
      have := T.error_nonnegative
      have := rat_square_nonneg_basic (4*R)
      dsimp only [B]; grind only
    let d := min T.radius.val (eps.val/(B+1))
    have hBp : 0<B+1 := by grind only
    have hd : 0<d := by
      dsimp only [d]; rw [Rat.min_def]; split
      · exact T.radius.property
      · exact Rat.mul_pos eps.property (Rat.inv_pos.mpr hBp)
    refine ⟨⟨d,hd⟩, fun u v hu huv hv hdUV => ?_⟩
    by_cases he : u=v
    · subst v
      simp only [Rat.sub_self, Rat.mul_zero]
      exact small_zero_value.congr (arithmetic_identity _ _ (by
        intro n; simp only [sub,scale,Value.rational,Rat.sub_self,Rat.zero_mul]))
    have huv' : u<v := by grind only
    have hvR := Rat.le_trans hv htR
    have huR := Rat.le_trans huv hvR
    have hs : 0≤v-u := by grind only
    have hrad : v-u≤T.radius.val := by dsimp only [d] at hdUV; grind
    have herr : v-u≤eps.val/(B+1) := by dsimp only [d] at hdUV; grind
    have bound := Rat.mul_le_mul_of_nonneg_right herr (Rat.le_of_lt hBp)
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hBp)] at bound
    have bound' := Rat.mul_le_mul_of_nonneg_right (show B*(v-u)≤eps.val by grind only) hs
    have A := (T.firstOrder u v hu huv' hvR hrad).congr
      ((Same.refl _).sub ((gaussian_parameter_integral D u hu huR).symm.scale (v-u)))
    have C := A.add (gaussian_integrated_remainder R u v hu huv' hvR).neg
    apply (C.mono (by dsimp only [B] at bound'; grind only)).congr
    apply arithmetic_identity; intro n
    simp only [W,J,F,Value.add,Value.neg,sub,scale,Value.rational,Rat.mul_zero]
    grind only
  have h0 : Same (W 0) (Value.rational 0) := by
    have hzero : Same (F 0) (Value.rational 0) := by
      simp only [F,LipschitzQuadrature.Data.accumulated,dif_pos (And.intro Rat.le_refl hR)]
      exact LipschitzQuadrature.zero_value (D.restrict 0 0 Rat.le_refl Rat.le_refl hR)
    have hu : Same (gaussianWeightedData 0).value gaussianKernelData.value := by
      apply (gaussianWeightedData 0).congr gaussianKernelData
      intro s _ _
      have he : -(gaussianParameter 0 s)=0 := by simp [gaussianParameter]
      change Same (scale (ArctanGeometry.integralKernel s) (expValue (-(gaussianParameter 0 s)))) _
      rw [he]
      refine (exp_zero_value.scale _).trans ?_
      apply arithmetic_identity; intro n
      simp only [scale,ArctanPositiveFTC.kernel,Value.rational,Rat.mul_one]
    refine ((hzero.mul hzero).sub ((Same.refl _).sub hu)).trans ?_
    apply arithmetic_identity; intro n
    simp only [Value.mul,sub,Value.rational,Rat.zero_mul,Rat.sub_self]
  have hK : Same K.value (Value.rational 0) :=
    (LipschitzQuadrature.constant_value _ _ _ ht).trans (arithmetic_identity _ _ (by
      intro n; simp only [scale,Value.rational,Rat.mul_zero]))
  apply small_sub_zero_same
  apply small_zero_value.congr
  refine (hK.symm.trans hW).trans (((Same.refl _).sub h0).trans ?_)
  apply arithmetic_identity; intro n; simp only [W,F,J,sub,Value.rational,Rat.sub_eq_add_neg,Rat.neg_zero,Rat.add_zero]


private theorem gaussian_arctan_tail (r : Rat) (hr : 1≤r) :
    Small (gaussianWeightedData r).value (1/r) := by
  have hrp : 0<r := by grind only
  have hrec : 0≤1/r := Rat.le_of_lt (Rat.mul_pos (by decide) (Rat.inv_pos.mpr hrp))
  have H := (gaussianWeightedData r).small (1/r) (fun t _ _ => by
    let s := gaussianParameter r t
    let k := ArctanGeometry.integralKernel t
    have hs : 0≤s := gaussianParameter_nonnegative r t
    have hk : 0≤k := Rat.le_of_lt (ArctanGeometry.integralKernel_pos t)
    have hk1 : k≤1 := ArctanGeometry.integralKernel_le_one t
    have h := Rat.mul_nonneg (rat_square_nonneg_basic r) (rat_square_nonneg_basic t)
    have hrr := Rat.mul_le_mul_of_nonneg_right hr (Rat.le_of_lt hrp)
    have hcomp : r≤1+s := by simp only [s,gaussianParameter]; grind only
    have hu := EulerReal.sample_negative_decay s hs
    have hl := EulerReal.eval_nonnegative (x := RealCompute.ofRat (-s)) (RealCompute.ofRat_valid _)
    have hinv : 1/(1+s)≤1/r := by
      simpa only [Rat.div_def, Rat.one_mul] using EulerFinite.inv_antitone hrp hcomp
    have U : Small (expValue (-s)) (1/r) := by
      constructor
      · intro i j
        have H := hl 0 j
        change 0≤((EulerReal.sample (-s)).compute j).hi at H
        change -(1/r)≤((EulerReal.sample (-s)).compute j).hi
        grind only
      · intro i j
        exact Rat.le_trans (hu i 0) hinv
    have B := scale_small U k
    rw [qabs_eq_self_of_nonneg hk] at B
    exact B.mono (by simpa only [Rat.one_mul] using Rat.mul_le_mul_of_nonneg_right hk1 hrec))
  simpa only [Rat.sub_eq_add_neg,Rat.neg_zero,Rat.add_zero,Rat.one_mul] using H

private theorem gaussian_window_double (n : Nat) :
    ∃ (D : LipschitzQuadrature.Data gaussianUnscaled 0 (radius n)),
      Same (gaussianDyadicWindow n).value (scale 2 (D.accumulated (radius n))) := by
  let R := radius n
  have hR := radius_pos n
  have hR0 := Rat.le_of_lt hR
  let W := gaussianDyadicWindow n
  let D := W.restrict 0 R (by grind only) hR0 Rat.le_refl
  let N := W.restrict (-R) 0 Rat.le_refl (by grind only) hR0
  refine ⟨D, ?_⟩
  let Q := gaussianScaledData D R hR0 Rat.le_refl
  let P : LipschitzQuadrature.Data (fun t => gaussianUnscaled (R*(1-t))) 0 1 :=
    { ordered := Q.ordered
      constant := Q.constant
      nonnegative := Q.nonnegative
      lipschitz := by
        intro u v hu huv hv
        have H := (Q.lipschitz (1-v) (1-u) (by grind only) (by grind only) (by grind only)).neg
        rw [show 1-u-(1-v)=v-u by grind only] at H
        apply H.congr
        apply arithmetic_identity; intro k; simp only [sub,Value.neg]; grind only }
  have hD : Same D.value (scale R Q.value) := Q.affine_identity D (c := 0) hR (by grind only)
    (by grind only) (by intro t _ _; simp only [Rat.zero_add]; exact Same.refl _)
  have hN : Same N.value (scale R P.value) := P.affine_identity N (c := -R) hR (by grind only)
    (by grind only) (by
      intro t _ _
      refine (gaussian_exp _).trans (Same.trans ?_ (gaussian_exp _).symm)
      rw [show -(R*(1-t)*(R*(1-t))) = -((-R+R*t)*(-R+R*t)) by grind only]
      exact Same.refl _)
  have hND : Same N.value D.value := hN.trans (((Q.reflect_unit P).scale R).trans hD.symm)
  have hF : D.accumulated R = D.value := dif_pos (And.intro hR0 (Rat.le_refl : R≤R))
  rw [hF]
  refine Same.trans (Y := Value.add N.value D.value) (N.append D W)
    ((hND.add (Same.refl D.value)).trans ?_)
  apply arithmetic_identity; intro k; simp only [Value.add,scale]; grind only

private theorem gaussian_four_arctan : Same (scale 4 gaussianKernelData.value) GeometricTrig.piValue := by
  let A := parameter (ArctanGeometry.arctanGeom 1) ArctanGeometry.arctanGeom_one_valid
  have h : Same gaussianKernelData.value A := by
    let T := ArctanPositiveFTC.dyadicIntegral 0 1 (by decide) (by decide) (by decide)
    have I := ArctanPositiveFTC.dyadicIntegral_hasIntegral 0 1 (by decide) (by decide) (by decide)
    let V := parameter T I.valid
    exact Same.trans (Y := V) (gaussianKernelData.identify I)
      (ArctanPositiveFTC.dyadicIntegral_equiv_geometric 1 (by decide) (by decide))
  exact (h.scale 4).trans (RealCompute.equiv_symm GeometricTrig.pi_geometric)

private theorem gaussian_window_square_error (n : Nat) :
    Small (sub (Value.mul (gaussianDyadicWindow n).value (gaussianDyadicWindow n).value)
      GeometricTrig.piValue) (4/radius n) := by
  obtain ⟨D,hD⟩ := gaussian_window_double n
  let F := D.accumulated (radius n)
  have h := gaussian_arctan_square D (radius n) (Rat.le_of_lt (radius_pos n)) Rat.le_refl
  have he : Same (Value.mul (gaussianDyadicWindow n).value (gaussianDyadicWindow n).value)
      (scale 4 (gaussianArctanDifference (radius n))) :=
    (hD.mul hD).trans (Same.trans (Y := scale 4 (Value.mul F F))
      (arithmetic_identity _ _ (by intro k; simp only [scale,Value.mul]; grind only)) (h.scale 4))
  have H := scale_small (gaussian_arctan_tail (radius n) (gaussianRadius_ge_one n)).neg 4
  rw [show qabs (4:Rat)=4 by decide] at H
  have hb : (4:Rat)*(1/radius n)=4/radius n := by simp [Rat.div_def]
  rw [hb] at H
  apply H.congr
  refine Same.trans ?_ ((he.sub gaussian_four_arctan.symm).symm)
  apply arithmetic_identity; intro k
  simp only [gaussianArctanDifference,scale,sub,Value.neg]
  grind only

/-- The integer-first dyadic improper Gaussian integral has square equal to
the geometric value of pi. The calculation uses one-variable FTC only. -/
theorem gaussianDyadic_square_equiv_pi :
    (RealCompute.mul gaussianDyadicImproper.raw gaussianDyadicImproper.raw).Equiv
      GeometricTrig.pi := by
  let D := gaussianDyadicImproper
  let X := D.value
  let c := 4*gaussianUnitDecay.bound
  let B := gaussianMassBound
  have hB := gaussianMassBound_nonnegative
  have hc : 0≤c := Rat.mul_nonneg (by decide) gaussianUnitDecay.nonnegative
  have hX : Small X B := gaussianMass_small.congr (RealCompute.equiv_symm gaussianDyadic_equiv_mass)
  let C := (2*B+c)*c+4
  apply small_sub_zero_same (x := Value.mul X X) (y := GeometricTrig.piValue)
  apply EffectiveImproperIntegral.small_of_errors _ 0 (fun n => C/radius n)
    (shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl))
  intro n
  let Z := (gaussianDyadicWindow n).value
  let r := radius n
  have hr := radius_pos n
  have hi : 0≤r⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hr)
  have hcR : c/r≤c := by
    have h := Rat.mul_le_mul_of_nonneg_right (gaussianRadius_ge_one n) hi
    change 1*r⁻¹≤r*r⁻¹ at h
    rw [Rat.mul_inv_cancel r (Rat.ne_of_gt hr), Rat.one_mul] at h
    simp only [Rat.div_def]
    simpa only [Rat.mul_one] using Rat.mul_le_mul_of_nonneg_left h hc
  have hD : Small (sub X Z) (c/r) := D.distance n
  have hZ : Small Z (B+c) := by
    apply ((hX.add (hD.neg.mono hcR)).congr ?_)
    apply arithmetic_identity; intro k; simp only [Value.add,Value.neg,sub]; grind only
  have hS := hD.mul (hX.add hZ)
  have hE : Same (Value.mul (sub X Z) (Value.add X Z)) (sub (Value.mul X X) (Value.mul Z Z)) := by
    apply arithmetic_identity; intro k
    simp only [Value.add,Value.mul,sub]; grind only
  have H := (hS.congr hE).add (gaussian_window_square_error n)
  have hrate : (c/r)*(B+(B+c))+4/r=0+C/r := by
    simp only [C,Rat.div_def]; grind only
  change Small (Value.add (sub (Value.mul X X) (Value.mul Z Z))
    (sub (Value.mul Z Z) GeometricTrig.piValue)) ((c/r)*(B+(B+c))+4/r) at H
  rw [hrate] at H
  apply H.congr
  apply arithmetic_identity; intro k; simp only [Value.add,sub]; grind only


private theorem gaussian_pi_sqrt_square :
    (RealCompute.mul gaussianPiSquareRootRaw gaussianPiSquareRootRaw).Equiv piCircleArea := by
  let A := gaussianPiSquareRootInput
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  let I := RepresentedPositiveSquareRoot.PositiveInput.approximation A n
  let X := gaussianPiSquareRootRaw.compute n
  let P := piCircleArea.compute n
  have hb : X.ContainsInterval I :=
    RepresentedPositiveSquareRoot.PositiveInput.sqrt_contains_current_approximation A n
  have hs : SqrtIntervalSpec P.midpoint I :=
    RepresentedPositiveSquareRoot.PositiveInput.approximation_spec A n
  have I2 := QBox.mulRealInterval_self_of_nonneg hs.1 hs.2.1
  have H := QBox.mulRealInterval_nested hb.1 hs.2.1 hb.2 hb.1 hs.2.1 hb.2
  rw [I2] at H
  have hp := QInterval.midpoint_mem (RealCompute.interval_order_of_valid _ CauchyPi.piCircleArea_valid n)
  change (QBox.mulRealInterval X.lo X.hi X.lo X.hi).Overlaps P
  unfold SqrtIntervalSpec sq at hs
  exact ⟨Rat.le_trans H.1 (Rat.le_trans hs.2.2.1 hp.2),
    Rat.le_trans hp.1 (Rat.le_trans hs.2.2.2 H.2)⟩

private theorem gaussian_pi_sqrt_lower : (RealCompute.ofRat 1).Le gaussianPiSquareRootRaw := by
  intro i n
  let A := gaussianPiSquareRootInput
  let I := RepresentedPositiveSquareRoot.PositiveInput.approximation A n
  have h := RepresentedPositiveSquareRoot.PositiveInput.sqrt_contains_current_approximation A n
  have hspec := RepresentedPositiveSquareRoot.PositiveInput.approximation_spec A n
  have hc := A.margin_sq_le_center n
  have hl : 0≤I.hi := Rat.le_trans hspec.1 hspec.2.1
  have H : 1≤I.hi*I.hi := by
    rw [show sq (1:Rat)=1 by decide +kernel] at hc
    exact Rat.le_trans hc hspec.2.2.2
  have L : 1≤I.hi := by
    by_cases hge : 1≤I.hi
    · exact hge
    have hle : I.hi≤1 := by grind only
    have hm := Rat.mul_le_mul_of_nonneg_left hle hl
    rw [Rat.mul_one] at hm
    grind only
  exact Rat.le_trans L h.2

private theorem positive_square_injective {x y : RealCompute} (hx : x.Valid) (hy : y.Valid)
    {a b : Rat} (ha : 0<a) (hb : 0<b) (hax : (RealCompute.ofRat a).Le x) (hby : (RealCompute.ofRat b).Le y)
    (H : (RealCompute.mul x x).Equiv (RealCompute.mul y y)) : x.Equiv y := by
  obtain ⟨Nx,hNx⟩ := hx.2.2 ⟨a,ha⟩
  obtain ⟨Ny,hNy⟩ := hy.2.2 ⟨b,hb⟩
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  let m := max n (max Nx Ny)
  have hnm : n≤m := Nat.le_max_left _ _
  have hxm : Nx≤m := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hym : Ny≤m := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have wx := hNx m hxm
  have wy := hNy m hym
  change (x.compute m).hi-(x.compute m).lo≤a at wx
  change (y.compute m).hi-(y.compute m).lo≤b at wy
  have ax : a≤(x.compute m).hi := hax 0 m
  have by' : b≤(y.compute m).hi := hby 0 m
  have lx : 0≤(x.compute m).lo := by grind only
  have ly : 0≤(y.compute m).lo := by grind only
  have ix := RealCompute.interval_order_of_valid x hx m
  have iy := RealCompute.interval_order_of_valid y hy m
  have S := (RealCompute.compareAt_overlap_iff _ _ m m).1 (H m)
  change (QBox.mulRealInterval (x.compute m).lo (x.compute m).hi (x.compute m).lo
    (x.compute m).hi).Overlaps (QBox.mulRealInterval (y.compute m).lo (y.compute m).hi
      (y.compute m).lo (y.compute m).hi) at S
  rw [QBox.mulRealInterval_self_of_nonneg lx ix, QBox.mulRealInterval_self_of_nonneg ly iy] at S
  have back {u v : Rat} (hu : 0≤u) (hv : 0≤v) (h : u*u≤v*v) : u≤v := by
    by_cases hle : u≤v
    · exact hle
    have A := Rat.mul_pos (show 0<u-v by grind only) (show 0<u+v by grind only)
    grind only
  have ox := hx.2.1 n m hnm
  have oy := hy.2.1 n m hnm
  exact ⟨Rat.le_trans ox.1 (Rat.le_trans (back lx (Rat.le_trans ly iy) S.1) oy.2.2),
    Rat.le_trans oy.1 (Rat.le_trans (back ly (Rat.le_trans lx ix) S.2) ox.2.2)⟩

/-- Gaussian normalization for the certified integer-first dyadic improper integral. -/
theorem gaussianDyadic_equiv_sqrt_pi :
    gaussianDyadicImproper.raw.Equiv gaussianPiSquareRootRaw := by
  have hx := gaussianDyadicImproper.valid
  have hy := gaussianPiSquareRootRaw_valid
  have hmass : (RealCompute.ofRat gaussianFullLineMassLower).Le gaussianMass.real.preferred :=
    fun _ n => gaussianFullLineMassLower_le_fullLine_hi n
  have hX := RealCompute.le_trans gaussianMass.real.valid hmass
    (RealCompute.le_of_equiv gaussianMass.real.valid hx (RealCompute.equiv_symm gaussianDyadic_equiv_mass))
  apply positive_square_injective hx hy gaussianFullLineMassLower_pos (by decide) hX gaussian_pi_sqrt_lower
  exact RealCompute.equiv_trans (RealCompute.mul_valid hx hx) GeometricTrig.pi_valid (RealCompute.mul_valid hy hy)
    gaussianDyadic_square_equiv_pi
    (RealCompute.equiv_trans GeometricTrig.pi_valid CauchyPi.piCircleArea_valid (RealCompute.mul_valid hy hy)
      GeometricTrig.pi_circleArea (RealCompute.equiv_symm gaussian_pi_sqrt_square))

/-! The exact cosine transform reduces Melrose’s normalization to a Gaussian
change of scale. Approximate the represented scale by rational dilations
of the finite dyadic windows, with explicit cutoff and scale errors. -/

private def dilateSampler (f : JointLipschitzSampler 1) (c : QPos) : JointLipschitzSampler 1 where
  value t := f.value (fun i => c.val*t i)
  bound := c.val*f.bound
  nonnegative := Rat.mul_nonneg (Rat.le_of_lt c.property) f.nonnegative
  control := by
    intro u v δ hδ h
    have hc := Rat.le_of_lt c.property
    have H := f.control (fun i => c.val*u i) (fun i => c.val*v i) (c.val*δ)
      (Rat.mul_nonneg hc hδ) (fun i => by
        have A := Rat.mul_le_mul_of_nonneg_left (h i).1 hc
        have B := Rat.mul_le_mul_of_nonneg_left (h i).2 hc
        constructor <;> grind only)
    exact H.mono (by grind only)

private theorem gaussianUnit_lipschitz (u v : Rat) :
    Small (sub (gaussianUnitSampler.value (fun _ => u)) (gaussianUnitSampler.value (fun _ => v)))
      (gaussianUnitSampler.bound*qabs (u-v)) := by
  have H := self_le_qabs (u-v)
  have H' := neg_qabs_le_self (u-v)
  exact gaussianUnitSampler.control (fun _ => u) (fun _ => v) (qabs (u-v)) (qabs_nonneg _)
    (fun _ => ⟨by grind only,by grind only⟩)

private theorem gaussianShape_param_cover (ξ : Rat) (n : Nat)
    (p : Rat) (hp : (GeometricTrig.piValue.real.compute n).lo ≤ p ∧
      p ≤ (GeometricTrig.piValue.real.compute n).hi) :
    RawLimit.InInterval (gaussianUnitSampler.value (fun _ => p*ξ)).real.preferred
      ((gaussianCosineShape (RealCompute.ofRat ξ) (RealCompute.ofRat_valid ξ)).real.compute n) := by
  let P := GeometricTrig.piValue
  let X := parameter (RealCompute.ofRat ξ) (RealCompute.ofRat_valid ξ)
  let A := Value.neg (Value.mul (Value.mul P P) (Value.mul X X))
  let a := -(p*ξ*(p*ξ))
  have hp' : RawLimit.InInterval (RealCompute.ofRat p) (P.real.compute n) := ⟨fun _ _ => hp.1,fun _ _ => hp.2⟩
  have hξ : RawLimit.InInterval (RealCompute.ofRat ξ) (X.real.compute n) := ⟨fun _ _ => Rat.le_refl,fun _ _ => Rat.le_refl⟩
  let Q := Value.rational p
  let Z := Value.rational ξ
  let b := Value.neg (Value.mul (Value.mul Q Q) (Value.mul Z Z))
  have H := RealIntervalImage.neg (RealIntervalImage.mul (Value.mul Q Q).real.valid
    (Value.mul Z Z).real.valid
    (RealIntervalImage.mul Q.real.valid Q.real.valid hp' hp')
    (RealIntervalImage.mul Z.real.valid Z.real.valid hξ hξ))
  have hI : RawLimit.InInterval b.real.preferred (A.real.compute n) := H
  have hA : RawLimit.InInterval (RealCompute.ofRat a) (A.real.compute n) := by
    apply RawLimit.inInterval_congr (z := RealCompute.ofRat a) b.real.valid (RealCompute.ofRat_valid a) _ hI
    apply arithmetic_identity b (Value.rational a)
    intro s
    simp only [b,Q,Z,Value.neg,Value.mul,Value.rational,a]
    grind only
  have he := euler_eval_cover_of_input (y := RealCompute.ofRat a) A.real.valid (RealCompute.ofRat_valid a) n hA
  have hG : Same (gaussianUnitSampler.value (fun _ => p*ξ))
      (expValue a) := (gaussianProfile_mulMass (p*ξ)).trans (gaussian_exp (p*ξ))
  exact RawLimit.inInterval_congr (EulerReal.sample_valid a) (gaussianUnitSampler.value (fun _ => p*ξ)).real.valid
    hG.symm he

private theorem small_sub_of_two_enclosures {A B : Value} {I J : QInterval}
    (ha : RawLimit.InInterval A.real.preferred I) (hb : RawLimit.InInterval B.real.preferred J)
    {E : Rat} (he : -E ≤ I.lo-J.hi ∧ I.hi-J.lo ≤ E) :
    Small (sub A B) E := by
  constructor
  · intro i j
    have hA := ha.1 0 j
    have hB := hb.2 j 0
    change I.lo ≤ (A.real.preferred.compute j).hi at hA
    change (B.real.preferred.compute j).lo ≤ J.hi at hB
    change -E ≤ (A.real.preferred.compute j).hi - (B.real.preferred.compute j).lo
    grind only
  · intro i j
    have hA := ha.2 i 0
    have hB := hb.1 0 i
    change (A.real.preferred.compute i).lo ≤ I.hi at hA
    change J.lo ≤ (B.real.preferred.compute i).hi at hB
    change (A.real.preferred.compute i).lo - (B.real.preferred.compute i).hi ≤ E
    grind only

private theorem gaussianShape_vs_rational_dilate (p : Rat)
    (i : Nat) (hi : (GeometricTrig.pi.compute i).lo ≤ p ∧ p ≤ (GeometricTrig.pi.compute i).hi)
    (ξ : Rat) :
    Small (sub (gaussianCosineShape (RealCompute.ofRat ξ) (RealCompute.ofRat_valid ξ))
        (gaussianUnitSampler.value (fun _ => p*ξ)))
      (gaussianUnitSampler.bound*qabs ξ*(GeometricTrig.pi.compute i).width) := by
  let A := gaussianCosineShape (RealCompute.ofRat ξ) (RealCompute.ofRat_valid ξ)
  let B := gaussianUnitSampler.value (fun _ => p*ξ)
  let W := (GeometricTrig.pi.compute i).width
  let E := gaussianUnitSampler.bound*qabs ξ*W
  have h (n : Nat) : Small (sub A B) (E+(A.real.compute n).width) := by
    let j := max i n
    let q := (GeometricTrig.pi.compute j).lo
    let Y := gaussianUnitSampler.value (fun _ => q*ξ)
    have hj := GeometricTrig.pi_valid.2.1 i j (Nat.le_max_left _ _)
    have hn := GeometricTrig.pi_valid.2.1 n j (Nat.le_max_right _ _)
    have H := gaussianShape_param_cover ξ n q ⟨hn.1,Rat.le_trans hn.2.1 hn.2.2⟩
    have hAY : Small (sub A Y) (A.real.compute n).width := by
      have hA : RawLimit.InInterval A.real.preferred (A.real.compute n) :=
        RealIntervalImage.current A.real.valid n
      have hY : RawLimit.InInterval Y.real.preferred (A.real.compute n) := H
      apply small_sub_of_two_enclosures hA hY
      change -((A.real.compute n).hi-(A.real.compute n).lo) ≤
        (A.real.compute n).lo-(A.real.compute n).hi ∧
        (A.real.compute n).hi-(A.real.compute n).lo ≤ (A.real.compute n).hi-(A.real.compute n).lo
      constructor <;> grind only
    have hqp : qabs (q-p) ≤ W :=
      qabs_sub_le_of_common_bounds hj.1 (Rat.le_trans hj.2.1 hj.2.2) hi.1 hi.2
    have hy := gaussianUnit_lipschitz (q*ξ) (p*ξ)
    have he : q*ξ-p*ξ=(q-p)*ξ := by grind only
    rw [he,qabs_mul] at hy
    have hYB : Small (sub Y B) E := hy.mono (by
      have K := Rat.mul_le_mul_of_nonneg_right hqp
        (Rat.mul_nonneg gaussianUnitSampler.nonnegative (qabs_nonneg ξ))
      change _ ≤ gaussianUnitSampler.bound*qabs ξ*W
      grind only)
    have K := hAY.add hYB
    rw [Rat.add_comm] at K
    apply K.congr
    apply arithmetic_identity
    intro s
    simp only [Value.add,sub]
    grind only
  exact EffectiveImproperIntegral.small_of_errors (sub A B) E _
    A.real.valid.2.2 h

private theorem zeroMode_point (t : Rat) :
    Same (trigValue true (phase (fun _ : Fin 1 => 0) (fun _ => t))) (Value.rational 1) := by
  change (GeometricTrig.sample true (phase (origin 1) (fun _ => t))).Equiv (RealCompute.ofRat 1)
  rw [phase_origin]
  exact GeometricTrig.sample_zero true

private theorem compact_zero_mode {f : JointLipschitzSampler 1} (D : LineDecay f) (n : Nat) :
    Same (expandingComponent f (fun _ => 0) true n)
      (lineData f (a := -radius n) (b := radius n) (by have := radius_pos n; grind only)).value := by
  let G := linePhaseSampler f (fun _ => 0) true D.bound D.nonnegative (lineDecay_all D)
  let r := radius n
  have hr := radius_pos n
  let A := lineData G (a := -r) (b := r) (by grind only)
  let B := lineData f (a := -r) (b := r) (by grind only)
  have hA : Same (expandingComponent f (fun _ => 0) true n) A.value :=
    expandingComponent_line f _ _ _ D.nonnegative (lineDecay_all D) n
  refine hA.trans (A.congr B ?_)
  intro t _ _
  let F := f.value (fun _ => t)
  refine ((Same.refl F).mul (zeroMode_point t)).trans ?_
  apply arithmetic_identity
  intro s
  change F.sample s * 1 = F.sample s
  exact Rat.mul_one _

/-- The cutoff error for the Gaussian on the scaled interval. Its length is
at most proportional to the scale, which cancels after the substitution. -/
private theorem gaussian_compact_dilate (p : QPos) (hp : 1 ≤ p.val) (n : Nat) :
    Small (sub ((lineData (dilateSampler gaussianUnitSampler p)
      (a := -radius n) (b := radius n) (by have := radius_pos n; grind only)).value)
      (scale p.val⁻¹ gaussianMass)) (6*gaussianUnitDecay.bound/radius n) := by
  let r := radius n
  let c := p.val
  let s := c*r
  let K := gaussianUnitDecay.bound
  have hc := p.property
  have hr := radius_pos n
  have hrs : r≤s := by
    simpa only [s,c,Rat.one_mul] using Rat.mul_le_mul_of_nonneg_right hp (Rat.le_of_lt hr)
  have hs : 0<s := by grind only
  let D := lineData (dilateSampler gaussianUnitSampler p) (a := -r) (b := r) (by grind only)
  let A := lineData gaussianUnitSampler (a := -s) (b := s) (by grind only)
  let B := lineData gaussianUnitSampler (a := -r) (b := r) (by grind only)
  let L := lineData gaussianUnitSampler (a := -s) (b := -r) (by grind only)
  let U := lineData gaussianUnitSampler (a := r) (b := s) hrs
  let M := lineData gaussianUnitSampler (a := -s) (b := r) (by grind only)
  have he : Same A.value (scale c D.value) :=
    D.affine_identity A (c := 0) (s := c) hc (by dsimp only [s]; grind only)
      (by dsimp only [s]; grind only) (by intro t _ _; simp only [Rat.zero_add]; exact Same.refl _)
  have hind : Same (sub A.value B.value) (Value.add L.value U.value) := by
    have hA : Same A.value (Value.add M.value U.value) := M.append U A
    have hM : Same M.value (Value.add L.value B.value) := L.append B M
    refine ((hA.trans (hM.add (Same.refl U.value))).sub (Same.refl B.value)).trans ?_
    apply arithmetic_identity
    intro k
    simp only [sub, Value.add]
    grind only
  have margin (t : Rat) (ht : r≤qabs t) : Small (gaussianUnitSampler.value (fun _ => t)) (K/(r*r)) := by
    have h := gaussianUnitDecay.outside t (Rat.le_trans (gaussianRadius_ge_one n) ht)
    have e := rat_mul_le_mul_of_nonneg (Rat.le_of_lt hr) ht (Rat.le_of_lt hr) ht
    have b := Rat.mul_le_mul_of_nonneg_left (reciprocal_mul_mono (Rat.mul_pos hr hr) e) gaussianUnitDecay.nonnegative
    exact h.mono (by simpa only [K,Rat.div_def,Rat.one_mul] using b)
  have hL := L.small (K/(r*r)) (fun t _ ht => margin t (by have := neg_qabs_le_self t; grind only))
  have hU := U.small (K/(r*r)) (fun t ht _ => margin t (Rat.le_trans ht (self_le_qabs t)))
  have hsmall : Small (sub A.value B.value) (2*c*K/r) := by
    apply ((hL.add hU).congr hind.symm).mono
    let d := K/(r*r)
    have h := Rat.mul_le_mul_of_nonneg_right (show s-r≤s by grind only)
      (show 0≤d from Rat.mul_nonneg gaussianUnitDecay.nonnegative
        (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hr hr))))
    have h' := Rat.mul_le_mul_of_nonneg_left h (show (0:Rat)≤2 by decide)
    have hcancel := Rat.mul_inv_cancel r (Rat.ne_of_gt hr)
    have hleft : (-r- -s)*d+(s-r)*d = 2*((s-r)*d) := by grind only
    have hright : 2*(s*d) = 2*c*K/r := by
      change 2*((c*r)*(K/(r*r))) = _
      simp only [Rat.div_def,Rat.inv_mul_rev]
      rw [show 2*(c*r*(K*(r⁻¹*r⁻¹))) = (2*c*K)*(r*r⁻¹)*r⁻¹ by grind only,
        hcancel, Rat.mul_one]
    change (-r- -s)*d+(s-r)*d ≤ _
    rw [hleft, ← hright]
    exact h'
  have hcomp : Same (expandingComponent gaussianUnitSampler (fun _ => 0) true n) B.value :=
    compact_zero_mode gaussianUnitDecay n
  have hmass : Small (sub gaussianMass B.value) (4*K/r) :=
    (lineTransform_error gaussianUnitDecay (fun _ => 0) true n).congr
      (gaussianUnit_zero_frequency_mass.sub hcomp)
  have H := (hsmall.add hmass.neg).scale_nonnegative (Rat.le_of_lt (Rat.inv_pos.mpr hc))
  have hcancel := Rat.inv_mul_cancel c (Rat.ne_of_gt hc)
  have hbudget : c⁻¹*(2*c*K/r+4*K/r)= (2*K+4*c⁻¹*K)/r := by
    simp only [Rat.div_def]; grind only
  have hinv : c⁻¹≤1 := by
    have H := reciprocal_mul_mono (show (0:Rat)<1 by decide) hp
    simpa only [Rat.div_def,Rat.one_mul,show (1:Rat)⁻¹=1 by decide +kernel] using H
  have hb := Rat.mul_le_mul_of_nonneg_right hinv (Rat.mul_nonneg (by decide : (0:Rat)≤4)
    (Rat.mul_nonneg gaussianUnitDecay.nonnegative (Rat.le_of_lt (Rat.inv_pos.mpr hr))))
  have hSum : Same (scale c⁻¹ (Value.add (sub A.value B.value) (Value.neg (sub gaussianMass B.value))))
      (scale c⁻¹ (sub A.value gaussianMass)) := by
    apply arithmetic_identity
    intro k
    simp only [scale,sub,Value.add,Value.neg]
    grind only
  have hScale : Same (scale c⁻¹ (sub (scale c D.value) gaussianMass))
      (sub D.value (scale c⁻¹ gaussianMass)) := by
    apply arithmetic_identity
    intro k
    simp only [scale,sub]
    grind only
  have hH := H.congr (hSum.trans (((he.sub (Same.refl gaussianMass)).scale c⁻¹).trans hScale))
  apply hH.mono
  change c⁻¹*(2*c*K/r+4*K/r)≤6*K/r
  rw [hbudget]
  simp only [Rat.div_def]
  grind only

private theorem gaussian_dilate_compare {f : JointLipschitzSampler 1} (D : LineDecay f)
    (hs : ∀ t : Rat, Same (f.value (fun _ => t))
      (gaussianCosineShape (RealCompute.ofRat t) (RealCompute.ofRat_valid t)))
    (p : QPos) (hp : 1 ≤ p.val) (i n : Nat)
    (hi : (GeometricTrig.pi.compute i).lo ≤ p.val ∧ p.val ≤ (GeometricTrig.pi.compute i).hi) :
    Small (sub (lineValue D true 0) (scale p.val⁻¹ gaussianMass))
      ((4*D.bound+6*gaussianUnitDecay.bound)/radius n +
        2*radius n*(gaussianUnitSampler.bound*radius n*(GeometricTrig.pi.compute i).width)) := by
  let R := radius n
  let W := (GeometricTrig.pi.compute i).width
  have hR := radius_pos n
  let A := lineData f (a := -R) (b := R) (by grind only)
  let B := lineData (dilateSampler gaussianUnitSampler p) (a := -R) (b := R) (by grind only)
  have H := A.difference_small B (gaussianUnitSampler.bound*R*W) (fun t ht ht' => by
    have H := gaussianShape_vs_rational_dilate p.val i hi t
    have h := qabs_le_of_neg_le_le ht ht'
    have hW := GeometricTrig.pi_valid.1 i
    change 0 ≤ W at hW
    have C := Rat.mul_le_mul_of_nonneg_right h
      (Rat.mul_nonneg gaussianUnitSampler.nonnegative hW)
    exact (H.mono (by grind only)).congr ((hs t).symm.sub (Same.refl _)))
  have hAB : Small (sub A.value B.value) (2*R*(gaussianUnitSampler.bound*R*W)) := by
    have h : R - -R = 2*R := by grind only
    simpa only [h] using H
  have hD : Small (sub (lineValue D true 0) A.value) (4*D.bound/R) :=
    (lineTransform_error D (fun _ => 0) true n).congr
      ((Same.refl (lineValue D true 0)).sub (compact_zero_mode D n))
  have hP : Small (sub B.value (scale p.val⁻¹ gaussianMass)) (6*gaussianUnitDecay.bound/R) :=
    gaussian_compact_dilate p hp n
  have K := (hD.add hAB).add hP
  change Small _ (4*D.bound/R+2*R*(gaussianUnitSampler.bound*R*W)+6*gaussianUnitDecay.bound/R) at K
  rw [show 4*D.bound/R+2*R*(gaussianUnitSampler.bound*R*W)+6*gaussianUnitDecay.bound/R =
    (4*D.bound+6*gaussianUnitDecay.bound)/R+2*R*(gaussianUnitSampler.bound*R*W) by
    simp only [Rat.div_def]; grind only] at K
  apply K.congr
  apply arithmetic_identity
  intro s
  simp only [sub,Value.add]
  grind only

private theorem inversePi_approx (i : Nat) (p : QPos)
    (hp : 1 ≤ p.val)
    (hi : (GeometricTrig.pi.compute i).lo ≤ p.val ∧ p.val ≤ (GeometricTrig.pi.compute i).hi) :
    Small (sub (Value.rational p.val⁻¹) GeometricIntegralData.inversePi)
      (GeometricTrig.pi.compute i).width := by
  apply small_of_samples _ _ (GeometricTrig.piValue.observation i)
  intro m hm s hs
  let q := GeometricTrig.piValue.sample s
  have H := GeometricTrig.piValue.encloses i m hm s hs
  change (GeometricTrig.pi.compute i).lo ≤ q ∧ q ≤ (GeometricTrig.pi.compute i).hi at H
  have hq := Rat.le_trans (GeometricIntegralData.pi_lower i) H.1
  have hq' : 0 < q := by grind only
  have hc := rat_mul_le_mul_of_nonneg (by decide : (0:Rat) ≤ 1) hp (by decide : (0:Rat) ≤ 1) hq
  have hc' : 1 ≤ p.val*q := by simpa only [Rat.mul_one] using hc
  have hv := reciprocal_mul_mono (by decide : (0:Rat)<1) hc'
  have hn := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos p.property hq'))
  have hsub : p.val⁻¹-q⁻¹=(q-p.val)*(p.val*q)⁻¹ := by
    rw [Rat.inv_mul_rev]
    have E := Rat.mul_inv_cancel p.val (Rat.ne_of_gt p.property)
    have F := Rat.mul_inv_cancel q (Rat.ne_of_gt hq')
    grind only
  change qabs (p.val⁻¹-q⁻¹) ≤ _
  rw [hsub, qabs_mul,qabs_eq_self_of_nonneg hn]
  have hw := qabs_sub_le_of_common_bounds H.1 H.2 hi.1 hi.2
  have h1 : (p.val*q)⁻¹ ≤ 1 := by
    simpa only [Rat.div_def,Rat.one_mul,show (1:Rat)⁻¹=1 by decide +kernel] using hv
  calc
    _ ≤ qabs (q-p.val)*1 := Rat.mul_le_mul_of_nonneg_left h1 (qabs_nonneg _)
    _ ≤ _ := by simpa only [Rat.mul_one, QInterval.width] using hw

private theorem gaussianShape_zero_mode {f : JointLipschitzSampler 1} (D : LineDecay f)
    (hs : ∀ t : Rat, Same (f.value (fun _ => t))
      (gaussianCosineShape (RealCompute.ofRat t) (RealCompute.ofRat_valid t))) :
    Same (lineValue D true 0) (Value.mul GeometricIntegralData.inversePi gaussianMass) := by
  let A := lineValue D true 0
  let B := Value.mul GeometricIntegralData.inversePi gaussianMass
  apply small_sub_zero_same
  apply EffectiveImproperIntegral.small_of_errors (sub A B) 0
    (fun n => (4*D.bound+6*gaussianUnitDecay.bound+2*gaussianUnitSampler.bound+gaussianMassBound)/radius n)
    (shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl))
  intro n
  let R := radius n
  have hr := radius_pos n
  have hR : 1 ≤ R := gaussianRadius_ge_one n
  let d : QPos := ⟨(R*R*R)⁻¹,Rat.inv_pos.mpr (Rat.mul_pos (Rat.mul_pos hr hr) hr)⟩
  obtain ⟨i, hWidth⟩ := GeometricTrig.pi_valid.2.2 d
  let W := (GeometricTrig.pi.compute i).width
  let p : QPos := ⟨(GeometricTrig.pi.compute i).lo, by have := GeometricIntegralData.pi_lower i; grind only⟩
  have hw : W ≤ (R*R*R)⁻¹ := hWidth i (Nat.le_refl _)
  have hp : 1 ≤ p.val := GeometricIntegralData.pi_lower i
  have hi : (GeometricTrig.pi.compute i).lo ≤ p.val ∧ p.val ≤ (GeometricTrig.pi.compute i).hi :=
    ⟨Rat.le_refl, RealCompute.interval_order_of_valid _ GeometricTrig.pi_valid i⟩
  let C := scale p.val⁻¹ gaussianMass
  have H : Small (sub A C)
      ((4*D.bound+6*gaussianUnitDecay.bound)/R+2*R*(gaussianUnitSampler.bound*R*W)) :=
    gaussian_dilate_compare D hs p hp i n hi
  have J : Small (sub C B) (W*gaussianMassBound) := by
    apply ((inversePi_approx i p hp hi).mul gaussianMass_small).congr
    apply arithmetic_identity
    intro s
    simp only [C,B,Value.rational,Value.mul,sub,scale]
    grind only
  have hA := Rat.mul_le_mul_of_nonneg_left hw (Rat.mul_nonneg
    (Rat.mul_nonneg (by decide : (0:Rat) ≤ 2) (Rat.le_of_lt hr))
      (Rat.mul_nonneg gaussianUnitSampler.nonnegative (Rat.le_of_lt hr)))
  have hW : W ≤ R⁻¹ := by
    have hSquare : R ≤ R*R := by
      simpa only [Rat.one_mul] using Rat.mul_le_mul_of_nonneg_right hR (Rat.le_of_lt hr)
    have hCube : R*R ≤ R*R*R := by
      simpa only [Rat.mul_one] using Rat.mul_le_mul_of_nonneg_left hR
        (Rat.mul_nonneg (Rat.le_of_lt hr) (Rat.le_of_lt hr))
    exact Rat.le_trans hw (EulerFinite.inv_antitone hr (Rat.le_trans hSquare hCube))
  have hB := Rat.mul_le_mul_of_nonneg_right hW gaussianMassBound_nonnegative
  have he : (2*R*(gaussianUnitSampler.bound*R))*(R*R*R)⁻¹ =
      (2*gaussianUnitSampler.bound)*R⁻¹ := by
    simp only [Rat.inv_mul_rev]
    have E := Rat.mul_inv_cancel R (Rat.ne_of_gt hr)
    grind only
  rw [he] at hA
  have K := (H.add J).congr (arithmetic_identity (Value.add (sub A C) (sub C B)) (sub A B)
    (by intro s; simp only [Value.add,sub]; grind only))
  have hWindow : 2*R*(gaussianUnitSampler.bound*R*W) ≤ (2*gaussianUnitSampler.bound)*R⁻¹ := by
    rw [show 2*R*(gaussianUnitSampler.bound*R*W) = (2*R*(gaussianUnitSampler.bound*R))*W by
      exact (Rat.mul_assoc _ _ _).symm]
    exact hA
  have bound := rat_add_le_add
    (rat_add_le_add (Rat.le_refl (a := (4*D.bound+6*gaussianUnitDecay.bound)/R)) hWindow) hB
  have regroup (a b c r : Rat) : a/r+b*r⁻¹+r⁻¹*c = 0+(a+b+c)/r := by
    simp only [Rat.div_def,Rat.zero_add]
    grind only
  rw [regroup (4*D.bound+6*gaussianUnitDecay.bound) (2*gaussianUnitSampler.bound) gaussianMassBound R] at bound
  exact K.mono bound

private theorem gaussianMoment_spec (t : Rat) :
    Same ((gaussianMomentSampler 1).value (fun _ => t))
      (scale t (gaussianSampler.value (fun _ => t))) := by
  apply arithmetic_identity
  intro s
  simp only [gaussianMomentSampler,gaussianMoment,gaussianSampler,scale,Rat.pow_one]

/-- Melrose's inverse quadrature factor is the square of the computed
full-line Gaussian mass divided by the geometric value of pi. -/
theorem melroseGaussianFactor_eq_mass_square :
    Same melroseGaussianFactor (Value.mul GeometricIntegralData.inversePi
      (Value.mul gaussianMass gaussianMass)) := by
  let D := transformDecayOf gaussianDecay gaussianDerivatives (gaussianMomentDecay 1)
    gaussianMoment_spec true
  let E := D.mulConstant gaussianMass gaussianMassBound gaussianMassBound_nonnegative gaussianMass_small
  let U := transformDecayOf gaussianUnitDecay gaussianUnitDerivatives gaussianUnitMomentDecay
    gaussianUnitMoment_spec true
  have h : Same (lineValue U true 0) (lineValue E true 0) := by
    change (lineTransform U (fun _ => 0) true).Equiv (lineTransform E (fun _ => 0) true)
    apply lineTransform_congr U E _ _ true
    intro t
    exact lineValue_mulConstant gaussianDecay gaussianMass gaussianMassBound
      gaussianMassBound_nonnegative gaussianMass_small true (t (Fin.last 0))
  have hD : Same (lineValue D true 0) (Value.mul GeometricIntegralData.inversePi gaussianMass) := by
    apply gaussianShape_zero_mode D
    intro t
    let x := RealCompute.ofRat t
    let hx : x.Valid := RealCompute.ofRat_valid t
    let F := parameter (lineTransformAt gaussianDecay true x hx)
      (lineTransformAt_valid gaussianDecay true x hx)
    have hF : Same F (lineValue gaussianDecay true t) := lineTransformAt_rational gaussianDecay true t
    have hShape : Same F (gaussianCosineShape x hx) := gaussianSampler_cosine_transform_exact x hx
    exact hF.symm.trans hShape
  refine h.trans ((lineValue_mulConstant D gaussianMass gaussianMassBound
    gaussianMassBound_nonnegative gaussianMass_small true 0).trans
    (((Same.refl gaussianMass).mul hD).trans ?_))
  apply arithmetic_identity
  intro s
  simp only [Value.mul]
  grind only

/-- The Gaussian mass identity removes the scalar left by Melrose's proof. -/
theorem melroseGaussianFactor_eq_one : Same melroseGaussianFactor (Value.rational 1) := by
  have h : Same gaussianDyadicImproper.value gaussianMass := gaussianDyadic_equiv_mass
  have hMass : Same (Value.mul gaussianMass gaussianMass) GeometricTrig.piValue :=
    (h.symm.mul h.symm).trans gaussianDyadic_square_equiv_pi
  refine melroseGaussianFactor_eq_mass_square.trans
    ((((Same.refl GeometricIntegralData.inversePi).mul hMass).trans ?_).trans
      GeometricIntegralData.pi_inverse_identity)
  apply arithmetic_identity
  intro s
  simp only [Value.mul,Rat.mul_comm]

/-- Melrose inversion for a real sampler with certified derivative, moment,
and decay data, at every valid represented spatial point. -/
theorem inverseLineAt_eq {f m : JointLipschitzSampler 1}
    (F : LineDecay f) (J : LineDerivatives f) (M : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    (x : RealCompute) (hx : x.Valid) :
    (inverseLineAt F J M hm x hx).real.preferred.Equiv (lineSamplerAt f x hx) :=
  inverseLineAt_eq_of_factor_one F J M hm x hx melroseGaussianFactor_eq_one

/-- The inverse quadrature depends on the represented point. -/
theorem inverseLineAt_congr {f m : JointLipschitzSampler 1}
    (F : LineDecay f) (J : LineDerivatives f) (M : LineDecay m)
    (hm : ∀ t : Rat, Same (m.value (fun _ => t)) (scale t (f.value (fun _ => t))))
    {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    Same (inverseLineAt F J M hm x hx) (inverseLineAt F J M hm y hy) := by
  let X := parameter (lineSamplerAt f x hx) (lineSamplerAt_valid f x hx)
  let Y := parameter (lineSamplerAt f y hy) (lineSamplerAt_valid f y hy)
  have hX : Same (inverseLineAt F J M hm x hx) X := inverseLineAt_eq F J M hm x hx
  have hY : Same (inverseLineAt F J M hm y hy) Y := inverseLineAt_eq F J M hm y hy
  have h : Same X Y := lineSamplerAt_congr f hx hy hxy
  exact (hX.trans h).trans hY.symm

end FiniteDifferentiation

end ComputableAnalysis.FourierQuadrature


