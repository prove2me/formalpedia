-- Prove2me | Definitions.Def_ChapterUnboundedSpectralModel
-- name    : ChapterUnboundedSpectralModel
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-21T11:23:42.031557+00:00
-- url     : https://prove2.me/theorems/9fb344e0-df9c-43f7-b78b-0a78c5535658
-- title:
--   Chapter UnboundedSpectralModel
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterUnboundedSpectralModel.lean`): generated def bundle for ChapterUnboundedSpectralModel. See BookProof/ChapterUnboundedSpectralModel.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnboundedSpectralModel.lean

import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSpectralDirectSum
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterUnitaryTransport
import Mathlib
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_eq_zero_iff
import Theorems.Thm_BookProof_ChapterSpectralDirectSum_spectral_multiplication_model_general_inc


/-!
# The spectral theorem in multiplication form for an **unbounded** self-adjoint operator

`BookProof.ChapterSpectralMultiplication` and `BookProof.ChapterSpectralDirectSum` prove
the spectral theorem in multiplication form for a **bounded** normal operator: with a
cyclic vector it is multiplication by the coordinate function `z` on `L²(μ)`, and in
general the space is a Hilbert sum of such models.  `BookProof.ChapterUnitaryTransport`
carries self-adjointness, the unitary group and Stone's relation through a *given*
unitary change of Hilbert space, and recorded the missing step: the **existence** of the
diagonalizing unitary for an *unbounded* self-adjoint operator.

This module supplies that step, by the classical resolvent (Cayley) route.  For a densely
defined self-adjoint `A` (the bundle `UnboundedSelfAdjoint` of
`BookProof.ChapterStoneResolvent`) the resolvent

`R = (A − i)⁻¹`

is a *bounded* operator (`resOp`), it is injective, its range is exactly the domain of `A`,
and it is **normal**: its adjoint is the resolvent at the conjugate point
(`adjoint_resOp`) and resolvents commute (`isStarNormal_resOp`).  So the bounded theory
applies to `R`, and `A` is read off from the model of `R` by `A = R⁻¹ + i`.

## What is proved

* `resOp`, `resOp_mem`, `op_resOp`, `resOp_injective`, `exists_resOp_eq` — the resolvent
  of an unbounded self-adjoint operator as a bounded operator, with `A(Ry) = y + iRy`,
  injective, and with range exactly the domain of `A`;
* `adjoint_resCLM`, `isStarNormal_resOp` — the resolvent is a bounded **normal** operator;
* `model_mem`, `model_apply` — **the model**: whenever an isometric embedding
  `V : L²(μ) → H` carries multiplication by `z` into `R`, every vector `V (z·u)` lies in
  the domain of `A` and `A (V (z·u)) = V (u + i z·u)`, i.e. `A` acts as multiplication by
  `1/z + i`;
* `model_ae_ne_zero`, `model_ae_circle` — `μ` gives no mass to `z = 0`, and is carried by
  the circle `|z|² = Im z`, the Cayley image of the real line; consequently
  `model_ae_real_multiplier`: the multiplier `1/z + i` equals the **real** function
  `Re z / |z|²` `μ`-almost everywhere, so `A` really is multiplication by a real function;
* `unbounded_multiplication_model_cyclic` — **the headline, cyclic case**: an unbounded
  self-adjoint operator whose resolvent has a cyclic unit vector is unitarily equivalent
  to multiplication by `1/z + i` on `L²(μ)` for a Borel probability measure `μ` carried by
  the Cayley circle, the domain being exactly the image of the multiplication-by-`z` range;
* `unbounded_multiplication_model_general` — **the headline, general case**: for *every*
  densely defined self-adjoint operator on a complex Hilbert space there are Borel
  probability measures `μₓ` and isometric embeddings `Vₓ : L²(μₓ) → H` exhibiting `H` as
  their Hilbert sum, on each of which the operator acts as multiplication by `1/z + i`.
  No cyclic vector and no separability is assumed;
* `unbounded_multiplication_model_separable` — the same with a countable family of
  summands, on a separable space.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open MeasureTheory Complex
open scoped InnerProductSpace

namespace BookProof.UnboundedSpectralModel

open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterSpectralDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## 1. The resolvent of an unbounded self-adjoint operator -/

/-- The **resolvent** `R = (A − i)⁻¹` of an unbounded self-adjoint operator, as a bounded
operator on the whole space. -/
def resOp (T : UnboundedSelfAdjoint H) : H →L[ℂ] H := T.resCLM 1

theorem resOp_mem (T : UnboundedSelfAdjoint H) (y : H) : resOp T y ∈ T.domain :=
  T.resCLM_mem 1 y

theorem resOp_eq_res (T : UnboundedSelfAdjoint H) (y : H) :
    (⟨resOp T y, resOp_mem T y⟩ : T.domain) = T.res 1 y := rfl

/-- The defining property: `A (R y) = y + i R y`. -/
theorem op_resOp (T : UnboundedSelfAdjoint H) (y : H) :
    T.op ⟨resOp T y, resOp_mem T y⟩ = y + Complex.I • resOp T y := by
  rw [resOp_eq_res]
  have h := T.op_res (l := 1) one_ne_zero y
  simp at h
  exact h

/-- The resolvent is injective. -/
theorem resOp_injective (T : UnboundedSelfAdjoint H) : Function.Injective (resOp T) := by
  intro y z hyz
  have h1 := op_resOp T y
  have h2 := op_resOp T z
  have hsub : (⟨resOp T y, resOp_mem T y⟩ : T.domain) = ⟨resOp T z, resOp_mem T z⟩ :=
    Subtype.ext hyz
  have h3 : y + Complex.I • resOp T y = z + Complex.I • resOp T z := by
    rw [← h1, ← h2, hsub]
  rw [hyz] at h3
  exact add_right_cancel h3

/-- The range of the resolvent is exactly the domain of `A`. -/
theorem exists_resOp_eq (T : UnboundedSelfAdjoint H) {x : H} (hx : x ∈ T.domain) :
    ∃ y : H, resOp T y = x := by
  refine ⟨T.shift 1 ⟨x, hx⟩, ?_⟩
  have h := T.res_shift (l := 1) one_ne_zero ⟨x, hx⟩
  have := congrArg (fun w : T.domain => (w : H)) h
  simpa [resOp, UnboundedSelfAdjoint.resCLM_apply] using this

/-- The adjoint of the resolvent at `l` is the resolvent at `−l`. -/
theorem adjoint_resCLM (T : UnboundedSelfAdjoint H) {l : ℝ} (hl : l ≠ 0) :
    ContinuousLinearMap.adjoint (T.resCLM l) = T.resCLM (-l) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff (T.resCLM (-l)) (T.resCLM l)).mpr ?_).symm
  intro y z
  simpa using T.inner_res (l := -l) (neg_ne_zero.mpr hl) y z

/-- The resolvent is a bounded **normal** operator. -/
theorem isStarNormal_resOp (T : UnboundedSelfAdjoint H) : IsStarNormal (resOp T) := by
  constructor
  have hstar : star (resOp T) = T.resCLM (-1) := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact adjoint_resCLM T one_ne_zero
  refine ContinuousLinearMap.ext fun y => ?_
  rw [hstar]
  simp only [ContinuousLinearMap.mul_apply]
  exact T.res_comm (l := -1) (m := 1) (by norm_num) one_ne_zero y

/-! ## 2. The Cayley symbol -/

/-- The **Cayley symbol** `Im z − |z|²`, a continuous real function on the spectrum of the
resolvent.  It vanishes exactly on the circle `|z − i/2| = 1/2`, the image of the real line
under the Cayley map `t ↦ 1/(t − i)`. -/
def cayleyFn (T : UnboundedSelfAdjoint H) : C(spectrum ℂ (resOp T), ℂ) where
  toFun z := ((z.1.im - ‖z.1‖ ^ 2 : ℝ) : ℂ)
  continuous_toFun := by fun_prop

@[simp] theorem cayleyFn_apply (T : UnboundedSelfAdjoint H) (z : spectrum ℂ (resOp T)) :
    cayleyFn T z = ((z.1.im - ‖z.1‖ ^ 2 : ℝ) : ℂ) := rfl

/-- The pointwise algebraic identity behind the Cayley circle:
`z − z̄ − 2i z̄z = 2i (Im z − |z|²)`. -/
theorem cayley_pointwise (w : ℂ) :
    w - (starRingEnd ℂ) w - (2 * Complex.I) * ((starRingEnd ℂ) w * w)
      = (2 * Complex.I) * (((w.im - ‖w‖ ^ 2 : ℝ) : ℂ)) := by
  have h : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  simp only [Complex.ext_iff, h, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  constructor <;> ring

/-- The same identity, read as an identity of continuous symbols on the spectrum. -/
theorem cayley_symbol_identity (T : UnboundedSelfAdjoint H) :
    coordFn (resOp T) - star (coordFn (resOp T))
        - (2 * Complex.I) • (star (coordFn (resOp T)) * coordFn (resOp T))
      = (2 * Complex.I) • cayleyFn T := by
  ext z
  exact cayley_pointwise z.1

/-- On the Cayley circle the multiplier `1/z + i` is the **real** number `Re z/|z|²`. -/
theorem cayley_real_multiplier {w : ℂ} (h : ‖w‖ ^ 2 = w.im) (hw : w ≠ 0) :
    1 + Complex.I * w = ((w.re / ‖w‖ ^ 2 : ℝ) : ℂ) * w := by
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hb : w.im ≠ 0 := by
    intro hb0
    apply hw
    have h1 : ‖w‖ ^ 2 = 0 := by rw [h, hb0]
    have : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    exact norm_eq_zero.mp this
  have ha2 : w.re ^ 2 = w.im - w.im ^ 2 := by rw [hsq] at h; nlinarith [h]
  rw [h]
  have hcast : ((w.re / w.im : ℝ) : ℂ) = (w.re : ℂ) / (w.im : ℂ) := by push_cast; ring
  rw [hcast]
  have hbc : (w.im : ℂ) ≠ 0 := by exact_mod_cast hb
  field_simp
  rw [Complex.ext_iff]
  constructor <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [ha2]

/-! ## 3. The model: an embedding intertwining multiplication by `z` with the resolvent -/

section Model

variable (T : UnboundedSelfAdjoint H) {mu : Measure (spectrum ℂ (resOp T))}
  (V : Lp ℂ 2 mu →ₗᵢ[ℂ] H)
  (hV : ∀ u : Lp ℂ 2 mu, V (mulRep mu (coordFn (resOp T)) u) = resOp T (V u))

include hV

/-- Every vector `V (z·u)` lies in the domain of `A`. -/
theorem model_mem (u : Lp ℂ 2 mu) : V (mulRep mu (coordFn (resOp T)) u) ∈ T.domain := by
  rw [hV u]
  exact resOp_mem T _

/-- **The model.**  `A` acts on `V (z·u)` as multiplication by `1/z + i`. -/
theorem model_apply (u : Lp ℂ 2 mu) :
    T.op ⟨V (mulRep mu (coordFn (resOp T)) u), model_mem T V hV u⟩
      = V (u + Complex.I • mulRep mu (coordFn (resOp T)) u) := by
  have hsub : (⟨V (mulRep mu (coordFn (resOp T)) u), model_mem T V hV u⟩ : T.domain)
      = ⟨resOp T (V u), resOp_mem T (V u)⟩ := Subtype.ext (hV u)
  rw [hsub, op_resOp, map_add, map_smul, hV u]

/-- **Symmetry of `A` in the model**: the quadratic form identity
`⟪u, zu⟫ − ⟪zu, u⟫ = 2i ⟪zu, zu⟫`, which says that `Im z = |z|²` in the form sense. -/
theorem model_symmetry_relation (u : Lp ℂ 2 mu) :
    (inner ℂ u (mulRep mu (coordFn (resOp T)) u) : ℂ)
        - inner ℂ (mulRep mu (coordFn (resOp T)) u) u
      = (2 * Complex.I)
          * inner ℂ (mulRep mu (coordFn (resOp T)) u) (mulRep mu (coordFn (resOp T)) u) := by
  set Z := mulRep mu (coordFn (resOp T)) with hZ
  have hx := T.symmetric ⟨V (Z u), model_mem T V hV u⟩ ⟨V (Z u), model_mem T V hV u⟩
  rw [model_apply T V hV u] at hx
  simp only at hx
  rw [V.inner_map_map, V.inner_map_map, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right] at hx
  simp only [Complex.conj_I] at hx
  linear_combination hx

/-- **The multiplication operator by the Cayley symbol vanishes.** -/
theorem mulRep_cayleyFn_eq_zero [IsFiniteMeasure mu] : mulRep mu (cayleyFn T) = 0 := by
  have hdecomp : (2 * Complex.I) • mulRep mu (cayleyFn T)
      = mulRep mu (coordFn (resOp T)) - star (mulRep mu (coordFn (resOp T)))
        - (2 * Complex.I)
            • (star (mulRep mu (coordFn (resOp T))) * mulRep mu (coordFn (resOp T))) := by
    have h := congrArg (mulRepHom mu) (cayley_symbol_identity T)
    simp only [map_sub, map_smul, map_mul, map_star, mulRepHom_apply] at h
    exact h.symm
  have hstar : (star (mulRep mu (coordFn (resOp T))) : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      = ContinuousLinearMap.adjoint (mulRep mu (coordFn (resOp T))) :=
    ContinuousLinearMap.star_eq_adjoint _
  have hform : ∀ u : Lp ℂ 2 mu,
      (inner ℂ u (((2 * Complex.I) • mulRep mu (cayleyFn T)) u) : ℂ) = 0 := by
    intro u
    rw [hdecomp, hstar]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply, inner_sub_right, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right]
    linear_combination model_symmetry_relation T V hV u
  have hP0 : (2 * Complex.I) • mulRep mu (cayleyFn T) = 0 := by
    have hlin : (((2 * Complex.I) • mulRep mu (cayleyFn T) :
        Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) : Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu) = 0 := by
      refine (inner_map_self_eq_zero _).mp fun u => ?_
      have hc := congrArg (starRingEnd ℂ) (hform u)
      rwa [inner_conj_symm, map_zero] at hc
    exact ContinuousLinearMap.coe_injective hlin
  have h2I : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  rcases smul_eq_zero.mp hP0 with h | h
  · exact absurd h h2I
  · exact h

/-- The measure is carried by the Cayley circle `|z|² = Im z`. -/
theorem model_ae_circle [IsFiniteMeasure mu] : ∀ᵐ z ∂mu, ‖z.1‖ ^ 2 = z.1.im := by
  have h0 : mulRep mu (cayleyFn T) = 0 := mulRep_cayleyFn_eq_zero T V hV
  have hae : (fun z => (cayleyFn T z : ℂ)) =ᵐ[mu] 0 :=
    (BookProof.ChapterLinftyMultiplication.multOp_eq_zero_iff (μ := mu)
      (fun z => (cayleyFn T z : ℂ)) (contMemLpTop mu (cayleyFn T))).mp h0
  filter_upwards [hae] with z hz
  have : ((z.1.im - ‖z.1‖ ^ 2 : ℝ) : ℂ) = 0 := hz
  have hr : (z.1.im - ‖z.1‖ ^ 2 : ℝ) = 0 := by exact_mod_cast this
  linarith

/-- The measure gives no mass to `z = 0`. -/
theorem model_ae_ne_zero [IsFiniteMeasure mu] : ∀ᵐ z ∂mu, z.1 ≠ 0 := by
  classical
  set s : Set (spectrum ℂ (resOp T)) := {z | z.1 = 0} with hsdef
  have hsm : MeasurableSet s :=
    continuous_subtype_val.measurable (measurableSet_singleton (0 : ℂ))
  have hzero : mu s = 0 := by
    by_contra hne
    set u : Lp ℂ 2 mu := indicatorConstLp 2 hsm (measure_ne_top mu s) (1 : ℂ) with hu
    have hZu : mulRep mu (coordFn (resOp T)) u = 0 := by
      refine Lp.ext ?_
      filter_upwards [mulRep_coeFn mu (coordFn (resOp T)) u,
        indicatorConstLp_coeFn (p := 2) (hs := hsm) (hμs := measure_ne_top mu s) (c := (1 : ℂ)),
        Lp.coeFn_zero ℂ 2 mu] with z h1 h2 h3
      rw [h1, h3, hu, h2]
      by_cases hz : z ∈ s
      · have : z.1 = 0 := hz
        simp [Set.indicator_of_mem hz, coordFn, this]
      · simp [Set.indicator_of_notMem hz]
    have hVu : V u = 0 := by
      have h := hV u
      rw [hZu, map_zero] at h
      have : resOp T (V u) = resOp T 0 := by simpa using h.symm
      exact resOp_injective T this
    have hnorm : ‖u‖ = 0 := by
      have := V.norm_map u
      rw [hVu] at this
      simpa using this.symm
    have hu0 : u = 0 := by simpa using hnorm
    have hnormu : ‖u‖ = (mu s).toReal ^ (1 / (2 : ℝ)) := by
      rw [hu, norm_indicatorConstLp (by norm_num) (by norm_num)]
      simp [MeasureTheory.measureReal_def]
    rw [hnorm] at hnormu
    have hpos : 0 < (mu s).toReal := by
      refine ENNReal.toReal_pos hne (measure_ne_top mu s)
    have : (0 : ℝ) < (mu s).toReal ^ (1 / (2 : ℝ)) := Real.rpow_pos_of_pos hpos _
    rw [← hnormu] at this
    exact absurd rfl (ne_of_gt this)
  refine (ae_iff).mpr ?_
  simpa [hsdef] using hzero

/-- Consequently the multiplier `1/z + i` is the **real** function `Re z/|z|²`. -/
theorem model_ae_real_multiplier [IsFiniteMeasure mu] :
    ∀ᵐ z ∂mu, 1 + Complex.I * z.1 = ((z.1.re / ‖z.1‖ ^ 2 : ℝ) : ℂ) * z.1 := by
  filter_upwards [model_ae_circle T V hV, model_ae_ne_zero T V hV] with z hcirc hne
  exact cayley_real_multiplier hcirc hne

end Model

/-! ## 3. The headline theorems -/

/-- **The spectral theorem in multiplication form, unbounded and cyclic.** -/
theorem unbounded_multiplication_model_cyclic (T : UnboundedSelfAdjoint H) (xi : H)
    (hxi : ‖xi‖ = 1)
    (hcyc : DenseRange (cfcVec (resOp T) (isStarNormal_resOp T) xi)) :
    ∃ (mu : Measure (spectrum ℂ (resOp T))) (_ : IsProbabilityMeasure mu)
      (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H),
      (∀ᵐ z ∂mu, z.1 ≠ 0 ∧ ‖z.1‖ ^ 2 = z.1.im) ∧
      (∀ u : Lp ℂ 2 mu, ∃ h : U (mulRep mu (coordFn (resOp T)) u) ∈ T.domain,
        T.op ⟨U (mulRep mu (coordFn (resOp T)) u), h⟩
          = U (u + Complex.I • mulRep mu (coordFn (resOp T)) u)) ∧
      (∀ x ∈ T.domain, ∃ u : Lp ℂ 2 mu, x = U (mulRep mu (coordFn (resOp T)) u)) := by
  obtain ⟨mu, hmu, U, h1, _h2⟩ :=
    spectral_multiplication_model (resOp T) (isStarNormal_resOp T) xi hcyc hxi
  have hV : ∀ u : Lp ℂ 2 mu,
      U.toLinearIsometry (mulRep mu (coordFn (resOp T)) u) = resOp T (U.toLinearIsometry u) :=
    h1
  refine ⟨mu, hmu, U, ?_, ?_, ?_⟩
  · exact (model_ae_ne_zero T U.toLinearIsometry hV).and
      (model_ae_circle T U.toLinearIsometry hV)
  · intro u
    exact ⟨model_mem T U.toLinearIsometry hV u, model_apply T U.toLinearIsometry hV u⟩
  · intro x hx
    obtain ⟨y, hy⟩ := exists_resOp_eq T hx
    refine ⟨U.symm y, ?_⟩
    have := hV (U.symm y)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply]
      at this
    rw [this, hy]

/-- **The spectral theorem in multiplication form, unbounded and general.** -/
theorem unbounded_multiplication_model_general (T : UnboundedSelfAdjoint H) :
    ∃ (S : Set H) (mu : S → Measure (spectrum ℂ (resOp T)))
      (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H),
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ x : S, ∀ᵐ z ∂(mu x), z.1 ≠ 0 ∧ ‖z.1‖ ^ 2 = z.1.im) ∧
      (∀ (x : S) (u : Lp ℂ 2 (mu x)),
        ∃ h : V x (mulRep (mu x) (coordFn (resOp T)) u) ∈ T.domain,
          T.op ⟨V x (mulRep (mu x) (coordFn (resOp T)) u), h⟩
            = V x (u + Complex.I • mulRep (mu x) (coordFn (resOp T)) u)) := by
  obtain ⟨S, mu, V, hprob, hsum, hint⟩ :=
    spectral_multiplication_model_general_inc (resOp T) (isStarNormal_resOp T)
  refine ⟨S, mu, V, hprob, hsum, ?_, ?_⟩
  · intro x
    have := hprob x
    exact (model_ae_ne_zero T (V x) (hint x)).and (model_ae_circle T (V x) (hint x))
  · intro x u
    exact ⟨model_mem T (V x) (hint x) u, model_apply T (V x) (hint x) u⟩



end BookProof.UnboundedSpectralModel

end


