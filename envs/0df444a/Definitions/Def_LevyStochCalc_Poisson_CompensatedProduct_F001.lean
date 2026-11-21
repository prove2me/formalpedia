-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProduct_F001
-- name    : LevyStochCalc_Poisson_CompensatedProduct_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:21:36.34224+00:00
-- url     : https://prove2.me/theorems/559a3677-48cf-4c98-96d3-12bd4101fc0f
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProduct
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProduct. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProduct_F000
import Definitions.Def_SourceProof_3120ed1b31912be1868cd154
import Definitions.Def_SourceProof_42f85278a4a3a35e73d229e1
import Definitions.Def_SourceProof_4bd0a8161788e04ae47801f3
import Definitions.Def_SourceProof_5ec07c2fb0eb6432896fc6fe

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated product of two mark profiles over a step

For a mark profile `f : E → ℝ` write `J(f)` for its compensated integral over the step `(a, b]`
against a Poisson random measure `N` with intensity `ν` (`compensatedProfile`). The compensated
product of two mark profiles `f, g` over the step is

  `Q(f, g) = J(f) J(g) − J(f g) − (b − a) ∫ f g dν`.

For bounded square-integrable profiles the product `f g` is again bounded and square integrable,
so each term is a compensated integral of a square-integrable profile.

This file treats simple profiles. The functions of finitely many simple mark profiles are carried
by the mark sets of one simple profile, however the mark sets of different profiles overlap. On
such a common family `A_k`, with coefficient vectors `c, c'`, the compensated product is almost
surely the quadratic element

  `(∑ c_k Ñ(B_k)) (∑ c'_k Ñ(B_k)) − ∑ c_k c'_k N(B_k)`

of the strips `B_k = (a, b] ×ˢ A_k` (`markedSecondChaos`), whose mean, Gram and orthogonality to
the compensated counts come from `Poisson/SecondChaos.lean` and `Poisson/SimpleChaos.lean`. So at
simple profiles `Q` is square integrable and centred, it is orthogonal in `L²(P)` to the
compensated integral of every simple profile, and, with `⟨u, v⟩ = ∫ u v dν`,

  `E[Q(u₁, u₂) Q(u₃, u₄)] = (b − a)² (⟨u₁, u₃⟩ ⟨u₂, u₄⟩ + ⟨u₁, u₄⟩ ⟨u₂, u₃⟩)`.

The profiles need not have disjoint supports, so their compensated integrals need not be
independent. `Poisson/CompensatedProductMoments.lean` extends the identities to bounded
square-integrable profiles.

## Main definitions

* `LevyStochCalc.Poisson.compensatedProduct` — the compensated product of two mark profiles over
  a step.
* `LevyStochCalc.Poisson.SimpleProfile.withCoeff` — the simple profile on the mark sets of a given
  one carrying new coefficients.

## Main statements

* `LevyStochCalc.Poisson.SimpleProfile.exists_refinement` — a common refinement of finitely many
  simple mark profiles.
* `LevyStochCalc.Poisson.SimpleProfile.compensatedProduct_withCoeff_ae_eq` — on a common family
  the compensated product is the quadratic element of the strips.
* `LevyStochCalc.Poisson.SimpleProfile.memLp_compensatedProduct`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct` — square integrability and the
  mean at simple profiles.
* `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct_mul` — the Gram at simple
  profiles.
* `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct_mul_compensatedProfile` —
  orthogonality to the first chaos at simple profiles.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

namespace SimpleProfile

omit [SigmaFinite ν] in
/-- On the mark sets of one simple profile, the product of the functions carried by two
coefficient vectors is the function carried by their product. -/
theorem toFun_withCoeff_mul (H : SimpleProfile E ν) (c c' : Fin H.K → ℝ) (e : E) :
    (H.withCoeff c).toFun e * (H.withCoeff c').toFun e = (H.withCoeff (c * c')).toFun e := by
  by_cases h : ∃ k, e ∈ H.B k
  · obtain ⟨k, hk⟩ := h
    rw [toFun_of_mem (H.withCoeff c) (k := k) hk, toFun_of_mem (H.withCoeff c') (k := k) hk,
      toFun_of_mem (H.withCoeff (c * c')) (k := k) hk]
    rfl
  · simp only [not_exists] at h
    rw [toFun_of_notMem (H.withCoeff c) h, toFun_of_notMem (H.withCoeff (c * c')) h, zero_mul]
omit [SigmaFinite ν] in
/-- The integral of the function of a simple profile. -/
theorem integral_toFun (G : SimpleProfile E ν) :
    ∫ e, G.toFun e ∂ν = ∑ k, G.c k * (ν (G.B k)).toReal := by
  have hint : ∀ k : Fin G.K,
      Integrable (fun e => G.c k * (G.B k).indicator (fun _ => (1 : ℝ)) e) ν := fun k =>
    (memLp_one_iff_integrable.1
      (memLp_indicator_const 1 (G.B_measurable k) (1 : ℝ) (Or.inr (G.B_finite k)))).const_mul _
  simp only [toFun]
  rw [integral_finsetSum _ fun k _ => hint k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_indicator_const (1 : ℝ) (G.B_measurable k), smul_eq_mul,
    mul_one, measureReal_def]
omit [SigmaFinite ν] in
/-- The integral of the function carried by a coefficient vector on the mark sets of a simple
profile. -/
theorem integral_toFun_withCoeff (H : SimpleProfile E ν) (c : Fin H.K → ℝ) :
    ∫ e, (H.withCoeff c).toFun e ∂ν = ∑ k, c k * (ν (H.B k)).toReal :=
  integral_toFun _
/-- The compensated step integral of the function carried by a coefficient vector on the mark
sets of a simple profile. -/
theorem stepIntegral_withCoeff (N : PoissonRandomMeasure P ν) (H : SimpleProfile E ν)
    (c : Fin H.K → ℝ) (a b : ℝ) (ω : Ω) :
    (H.withCoeff c).stepIntegral N a b ω = ∑ k, c k * N.compensated (Set.Ioc a b ×ˢ H.B k) ω :=
  rfl
omit [SigmaFinite ν] in
/-- The `L²(ν)` pairing of the functions carried by two coefficient vectors on the mark sets of
one simple profile. -/
theorem integral_toFun_withCoeff_mul (H : SimpleProfile E ν) (c c' : Fin H.K → ℝ) :
    ∫ e, (H.withCoeff c).toFun e * (H.withCoeff c').toFun e ∂ν
      = ∑ k, c k * c' k * (ν (H.B k)).toReal := by
  simp_rw [toFun_withCoeff_mul, integral_toFun_withCoeff]
  rfl
omit [SigmaFinite ν] in
/-- The strips over the mark sets of a simple profile are measurable. -/
private theorem measurableSet_strip (H : SimpleProfile E ν) (a b : ℝ) (k : Fin H.K) :
    MeasurableSet (Set.Ioc a b ×ˢ H.B k) :=
  measurableSet_Ioc.prod (H.B_measurable k)
omit [SigmaFinite ν] in
/-- The strips over the mark sets of a simple profile are pairwise disjoint. -/
private theorem pairwise_disjoint_strip (H : SimpleProfile E ν) (a b : ℝ) :
    Pairwise fun k l => Disjoint (Set.Ioc a b ×ˢ H.B k) (Set.Ioc a b ×ˢ H.B l) :=
  fun _ _ hkl => Set.disjoint_left.2 fun _ hx hx' =>
    Set.disjoint_left.1 (H.B_disjoint hkl) hx.2 hx'.2
/-- The strips over the mark sets of a simple profile have finite intensity. -/
private theorem referenceIntensity_strip_ne_top' (H : SimpleProfile E ν) {a : ℝ} (ha : 0 ≤ a)
    (b : ℝ) (k : Fin H.K) : referenceIntensity ν (Set.Ioc a b ×ˢ H.B k) ≠ ⊤ :=
  referenceIntensity_strip_ne_top ha (H.B_finite k)
/-- **The compensated product on a common family.** For two coefficient vectors on the mark sets
of one simple profile, the compensated product of the functions they carry is almost surely the
quadratic element of the strips over those mark sets. -/
theorem compensatedProduct_withCoeff_ae_eq (N : PoissonRandomMeasure P ν) (H : SimpleProfile E ν)
    (c c' : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProduct N (H.withCoeff c).toFun (H.withCoeff c').toFun a b
      =ᵐ[P] markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c' := by
  have hfun : (fun e => (H.withCoeff c).toFun e * (H.withCoeff c').toFun e)
      = (H.withCoeff (c * c')).toFun := funext (toFun_withCoeff_mul H c c')
  filter_upwards [_root_.Prove2MeSourceProof.h_42f85278a4a3a35e73d229e1 N (H.withCoeff c) ha hab,
    _root_.Prove2MeSourceProof.h_42f85278a4a3a35e73d229e1 N (H.withCoeff c') ha hab,
    _root_.Prove2MeSourceProof.h_42f85278a4a3a35e73d229e1 N (H.withCoeff (c * c')) ha hab] with ω h1 h2 h3
  have hN : ∀ k, (N.N ω (Set.Ioc a b ×ˢ H.B k)).toReal
      = N.compensated (Set.Ioc a b ×ˢ H.B k) ω + (b - a) * (ν (H.B k)).toReal := by
    intro k
    rw [PoissonRandomMeasure.compensated, referenceIntensity_strip_toReal ha hab]
    ring
  rw [compensatedProduct, hfun, h1, h2, h3, integral_toFun_withCoeff, markedSecondChaos,
    stepIntegral_withCoeff, stepIntegral_withCoeff, stepIntegral_withCoeff]
  simp only [Pi.mul_apply, hN, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [sub_sub]
  congr 2
  exact Finset.sum_congr rfl fun k _ => by ring
/-- The quadratic element of the strips over the mark sets of a simple profile is square
integrable. -/
private theorem memLp_markedSecondChaos_strip (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c c' : Fin H.K → ℝ) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    MemLp (markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c') 2 P := by
  rw [show markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c'
      = fun ω => ∑ k, ∑ l, c k * c' l
        * poissonChaosProd N (pairIndex k l) (fun k => Set.Ioc a b ×ˢ H.B k) ω from
    funext (_root_.Prove2MeSourceProof.h_3120ed1b31912be1868cd154 N _ c c')]
  exact memLp_finsetSum _ fun k _ => memLp_finsetSum _ fun l _ =>
    (memLp_two_poissonChaosProd N (measurableSet_strip H a b) (pairwise_disjoint_strip H a b)
      (referenceIntensity_strip_ne_top' H ha b) _).const_mul _
/-- A pair index is not the multi-degree of a single unit. -/
private theorem pairIndex_ne_single {p : ℕ} (k l m : Fin p) : pairIndex k l ≠ Pi.single m 1 := by
  intro h
  have hs := congrArg (fun α : Fin p → ℕ => ∑ j, α j) h
  simp [pairIndex, Finset.sum_add_distrib] at hs
/-- The quadratic element of the strips over the mark sets of a simple profile is orthogonal to
the compensated count of each strip. -/
private theorem integral_markedSecondChaos_strip_mul_compensated (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c c' : Fin H.K → ℝ) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (m : Fin H.K) :
    ∫ ω, markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c' ω
        * N.compensated (Set.Ioc a b ×ˢ H.B m) ω ∂P = 0 := by
  have hint : ∀ k l : Fin H.K, Integrable (fun ω => c k * c' l
      * poissonChaosProd N (pairIndex k l) (fun k => Set.Ioc a b ×ˢ H.B k) ω
      * N.compensated (Set.Ioc a b ×ˢ H.B m) ω) P := fun k l =>
    (((memLp_two_poissonChaosProd N (measurableSet_strip H a b) (pairwise_disjoint_strip H a b)
      (referenceIntensity_strip_ne_top' H ha b) _).const_mul _).integrable_mul
        (H.memLp_compensated_step N ha b m))
  simp_rw [_root_.Prove2MeSourceProof.h_3120ed1b31912be1868cd154, Finset.sum_mul]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [show (fun ω => c k * c' l
        * poissonChaosProd N (pairIndex k l) (fun k => Set.Ioc a b ×ˢ H.B k) ω
        * N.compensated (Set.Ioc a b ×ˢ H.B m) ω)
      = fun ω => (c k * c' l)
        * (poissonChaosProd N (pairIndex k l) (fun k => Set.Ioc a b ×ˢ H.B k) ω
          * N.compensated ((fun k => Set.Ioc a b ×ˢ H.B k) m) ω) from funext fun ω => by ring,
    integral_const_mul, integral_poissonChaosProd_mul_compensated_eq_zero N
      (measurableSet_strip H a b) (pairwise_disjoint_strip H a b)
      (referenceIntensity_strip_ne_top' H ha b) (pairIndex_ne_single k l m), mul_zero]
/-! ### The compensated product on a common family -/

/-- On a common family, the compensated product is square integrable. -/
theorem memLp_compensatedProduct_withCoeff (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c c' : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MemLp (compensatedProduct N (H.withCoeff c).toFun (H.withCoeff c').toFun a b) 2 P :=
  (memLp_markedSecondChaos_strip N H c c' ha b).ae_eq
    (compensatedProduct_withCoeff_ae_eq N H c c' ha hab).symm
/-- On a common family, the compensated product is centred. -/
theorem integral_compensatedProduct_withCoeff (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c c' : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N (H.withCoeff c).toFun (H.withCoeff c').toFun a b ω ∂P = 0 := by
  rw [integral_congr_ae (compensatedProduct_withCoeff_ae_eq N H c c' ha hab)]
  exact _root_.Prove2MeSourceProof.h_5ec07c2fb0eb6432896fc6fe N (measurableSet_strip H a b) (pairwise_disjoint_strip H a b)
    (referenceIntensity_strip_ne_top' H ha b) c c'
/-- On a common family, the Gram of two compensated products. -/
theorem integral_compensatedProduct_withCoeff_mul (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c₁ c₂ c₃ c₄ : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N (H.withCoeff c₁).toFun (H.withCoeff c₂).toFun a b ω
        * compensatedProduct N (H.withCoeff c₃).toFun (H.withCoeff c₄).toFun a b ω ∂P
      = (b - a) ^ 2
        * ((∫ e, (H.withCoeff c₁).toFun e * (H.withCoeff c₃).toFun e ∂ν)
            * (∫ e, (H.withCoeff c₂).toFun e * (H.withCoeff c₄).toFun e ∂ν)
          + (∫ e, (H.withCoeff c₁).toFun e * (H.withCoeff c₄).toFun e ∂ν)
            * (∫ e, (H.withCoeff c₂).toFun e * (H.withCoeff c₃).toFun e ∂ν)) := by
  rw [integral_congr_ae (by
    filter_upwards [compensatedProduct_withCoeff_ae_eq N H c₁ c₂ ha hab,
      compensatedProduct_withCoeff_ae_eq N H c₃ c₄ ha hab] with ω h1 h2
    rw [h1, h2])]
  have hs : ∀ x y : Fin H.K → ℝ, ∑ k, x k * y k * ((b - a) * (ν (H.B k)).toReal)
      = (b - a) * ∑ k, x k * y k * (ν (H.B k)).toReal := fun x y => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [integral_markedSecondChaos_strip_mul N ha hab H.B_measurable H.B_finite H.B_disjoint,
    hs, hs, hs, hs]
  simp_rw [integral_toFun_withCoeff_mul]
  ring
/-- On a common family, the compensated product is orthogonal to the compensated integral of
every function carried by the family. -/
theorem integral_compensatedProduct_withCoeff_mul_compensatedProfile
    (N : PoissonRandomMeasure P ν) (H : SimpleProfile E ν) (c c' d : Fin H.K → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N (H.withCoeff c).toFun (H.withCoeff c').toFun a b ω
        * compensatedProfile N (H.withCoeff d).toFun a b ω ∂P = 0 := by
  rw [integral_congr_ae (by
    filter_upwards [compensatedProduct_withCoeff_ae_eq N H c c' ha hab,
      _root_.Prove2MeSourceProof.h_42f85278a4a3a35e73d229e1 N (H.withCoeff d) ha hab] with ω h1 h2
    rw [h1, h2])]
  have hint : ∀ m : Fin H.K, Integrable (fun ω =>
      markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c' ω
        * (d m * N.compensated (Set.Ioc a b ×ˢ H.B m) ω)) P := fun m =>
    (memLp_markedSecondChaos_strip N H c c' ha b).integrable_mul
      ((H.memLp_compensated_step N ha b m).const_mul _)
  simp only [stepIntegral_withCoeff, Finset.mul_sum]
  rw [integral_finsetSum _ fun m _ => hint m]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [show (fun ω => markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c' ω
        * (d m * N.compensated (Set.Ioc a b ×ˢ H.B m) ω))
      = fun ω => d m * (markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c' ω
        * N.compensated (Set.Ioc a b ×ˢ H.B m) ω) from funext fun ω => by ring,
    integral_const_mul, integral_markedSecondChaos_strip_mul_compensated N H c c' ha b m,
    mul_zero]
/-! ### The compensated product of simple profiles -/

/-- The compensated product of the functions of two simple mark profiles is square integrable. -/
theorem memLp_compensatedProduct (N : PoissonRandomMeasure P ν) (G₁ G₂ : SimpleProfile E ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MemLp (compensatedProduct N G₁.toFun G₂.toFun a b) 2 P := by
  obtain ⟨H, d, hd⟩ := _root_.Prove2MeSourceProof.h_4bd0a8161788e04ae47801f3 ![G₁, G₂]
  rw [show G₁.toFun = (H.withCoeff (d 0)).toFun from funext fun e => (hd 0 e).symm,
    show G₂.toFun = (H.withCoeff (d 1)).toFun from funext fun e => (hd 1 e).symm]
  exact memLp_compensatedProduct_withCoeff N H _ _ ha hab
/-- The compensated product of the functions of two simple mark profiles is centred. -/
theorem integral_compensatedProduct (N : PoissonRandomMeasure P ν) (G₁ G₂ : SimpleProfile E ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N G₁.toFun G₂.toFun a b ω ∂P = 0 := by
  obtain ⟨H, d, hd⟩ := _root_.Prove2MeSourceProof.h_4bd0a8161788e04ae47801f3 ![G₁, G₂]
  rw [show G₁.toFun = (H.withCoeff (d 0)).toFun from funext fun e => (hd 0 e).symm,
    show G₂.toFun = (H.withCoeff (d 1)).toFun from funext fun e => (hd 1 e).symm]
  exact integral_compensatedProduct_withCoeff N H _ _ ha hab
/-- **The Gram at simple profiles.** The `L²(P)` pairing of the compensated products of the
functions of simple mark profiles, with `⟨u, v⟩ = ∫ u v dν`:
`E[Q(u₁, u₂) Q(u₃, u₄)] = (b − a)² (⟨u₁, u₃⟩ ⟨u₂, u₄⟩ + ⟨u₁, u₄⟩ ⟨u₂, u₃⟩)`. -/
theorem integral_compensatedProduct_mul (N : PoissonRandomMeasure P ν)
    (G₁ G₂ G₃ G₄ : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N G₁.toFun G₂.toFun a b ω
        * compensatedProduct N G₃.toFun G₄.toFun a b ω ∂P
      = (b - a) ^ 2 * ((∫ e, G₁.toFun e * G₃.toFun e ∂ν) * (∫ e, G₂.toFun e * G₄.toFun e ∂ν)
        + (∫ e, G₁.toFun e * G₄.toFun e ∂ν) * (∫ e, G₂.toFun e * G₃.toFun e ∂ν)) := by
  obtain ⟨H, d, hd⟩ := _root_.Prove2MeSourceProof.h_4bd0a8161788e04ae47801f3 ![G₁, G₂, G₃, G₄]
  rw [show G₁.toFun = (H.withCoeff (d 0)).toFun from funext fun e => (hd 0 e).symm,
    show G₂.toFun = (H.withCoeff (d 1)).toFun from funext fun e => (hd 1 e).symm,
    show G₃.toFun = (H.withCoeff (d 2)).toFun from funext fun e => (hd 2 e).symm,
    show G₄.toFun = (H.withCoeff (d 3)).toFun from funext fun e => (hd 3 e).symm]
  exact integral_compensatedProduct_withCoeff_mul N H _ _ _ _ ha hab
/-- **Orthogonality to the first chaos at simple profiles.** The compensated product of the
functions of two simple mark profiles is orthogonal to the compensated integral of the function
of a third. -/
theorem integral_compensatedProduct_mul_compensatedProfile (N : PoissonRandomMeasure P ν)
    (G₁ G₂ G₃ : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N G₁.toFun G₂.toFun a b ω
        * compensatedProfile N G₃.toFun a b ω ∂P = 0 := by
  obtain ⟨H, d, hd⟩ := _root_.Prove2MeSourceProof.h_4bd0a8161788e04ae47801f3 ![G₁, G₂, G₃]
  rw [show G₁.toFun = (H.withCoeff (d 0)).toFun from funext fun e => (hd 0 e).symm,
    show G₂.toFun = (H.withCoeff (d 1)).toFun from funext fun e => (hd 1 e).symm,
    show G₃.toFun = (H.withCoeff (d 2)).toFun from funext fun e => (hd 2 e).symm]
  exact integral_compensatedProduct_withCoeff_mul_compensatedProfile N H _ _ _ ha hab
end SimpleProfile

end LevyStochCalc.Poisson


